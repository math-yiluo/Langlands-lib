import Langlands.GroupScheme.Quaternionic.TorusRowWeightDuality
import Langlands.GroupScheme.Torus.SignedWeightCharacterBasis
import Langlands.GroupScheme.Rational.SplitRankTransport

/-! # Actual isometry torus weights from the rank--Witt equality -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution

open FiniteAlgebraUnits FiniteAlgebraTorusWeights FiniteMatrixAlgebraTorusWeights
  SplitTorusRepresentationWeights

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] (σ : FirstKindInvolution K D)
  {n : Type} [Fintype n] [DecidableEq n]
  {I : Type u} [Fintype I] [DecidableEq I]
  {S : CommGroupScheme (Spec (CommRingCat.of K))}

/-- The finite coordinate support of the row action of a split isometry torus. -/
def isometryTorusWeightSupport (q : σ.QuadraticForms n)
    (i : S.toGrp ⟶ σ.isometryGroup q)
    (e : S.toGrp ≅ splitTorus (Spec (CommRingCat.of K)) I) : Finset (I → ℤ) :=
  weightSupport (rightRegularRepresentation (Module.finBasis K (Matrix n n D))) I
    ((e.inv ≫ i) ≫ σ.isometryGroupι q)

/-- The finite coordinate support spans the whole row module. -/
theorem iSup_isometryTorusWeightSupport_eq_top (q : σ.QuadraticForms n)
    (i : S.toGrp ⟶ σ.isometryGroup q)
    (e : S.toGrp ≅ splitTorus (Spec (CommRingCat.of K)) I) :
    (⨆ m ∈ σ.isometryTorusWeightSupport q i e,
      σ.torusRowWeightSpace q (e.inv ≫ i) m) = ⊤ := by
  apply top_unique
  rw [← iSup_rowWeightSpace_eq_top ((e.inv ≫ i) ≫ σ.isometryGroupι q)]
  refine iSup_le fun m => ?_
  by_cases hm : m ∈ σ.isometryTorusWeightSupport q i e
  · exact le_iSup_of_le m (le_iSup_of_le hm le_rfl)
  · rw [rowWeightSpace_eq_bot _ hm]
    exact bot_le

/-- Cocharacter weight spaces are grouped by the actual characters of `S`. -/
theorem cocharacterWeightSpace_eq_iSup_isometryTorusWeightSupport
    (q : σ.QuadraticForms n) (i : S.toGrp ⟶ σ.isometryGroup q)
    (e : S.toGrp ≅ splitTorus (Spec (CommRingCat.of K)) I)
    (ν : cocharacterLattice S) (c : ℤ) :
    σ.cocharacterWeightSpace q (CommGroupScheme.groupHom ν ≫ i) c =
      ⨆ m ∈ (σ.isometryTorusWeightSupport q i e).filter
        (fun m => latticePairing S (SignedWeightTransport.characterEquiv e m) ν = c),
        σ.torusRowWeightSpace q (e.inv ≫ i) m := by
  let μ : cocharacterLattice
      (splitTorus.commGroupScheme (Spec (CommRingCat.of K)) I) :=
    ν ≫ Additive.ofMul e.hom
  have hμ : CommGroupScheme.groupHom μ ≫ (e.inv ≫ i) =
      CommGroupScheme.groupHom ν ≫ i := by
    change (CommGroupScheme.groupHom ν ≫ e.hom) ≫ (e.inv ≫ i) = _
    simp only [Category.assoc, e.hom_inv_id_assoc]
  rw [← hμ, σ.cocharacterWeightSpace_eq_iSup_torusRowWeightSpace]
  simp only [cocharacterWeightSupport, isometryTorusWeightSupport,
    SignedWeightTransport.latticePairing_characterEquiv, μ]

/-- Rank equal to the quadratic Witt index gives the actual character formula
for any closed split isometry torus. -/
theorem exists_characters_of_isometryTorus_rank_eq
    (q : σ.QuadraticForms n) (hq : σ.IsNondegenerateQuadratic q)
    (i : S.toGrp ⟶ σ.isometryGroup q) (hi : IsClosedSubgroup i)
    (e : S.toGrp ≅ splitTorus (Spec (CommRingCat.of K)) I)
    (hrank : Fintype.card I = σ.quadraticWittIndex q) :
    ∃ χ : Fin (σ.quadraticWittIndex q) → characterLattice S,
      LinearIndependent ℤ χ ∧
      (∀ ν : cocharacterLattice S, (∀ k, latticePairing S (χ k) ν = 0) → ν = 0) ∧
      ∀ (ν : cocharacterLattice S) (c : ℤ),
        Module.finrank D (σ.cocharacterWeightSpace q
            (CommGroupScheme.groupHom ν ≫ i) c) =
          Nat.card {p : Fin (σ.quadraticWittIndex q) × ℤˣ //
            (p.2 : ℤ) * latticePairing S (χ p.1) ν = c} +
            if c = 0 then Fintype.card n - 2 * σ.quadraticWittIndex q else 0 := by
  classical
  let t := e.inv ≫ i
  let j := t ≫ σ.isometryGroupι q
  have hj : IsClosedSubgroup j :=
    (hi.iso_comp e.symm).comp (σ.isClosedSubgroup_isometryGroupι q)
  have hmono : Mono j.hom.hom.left := by
    have : IsClosedImmersion j.hom.hom.left := hj
    infer_instance
  have h := SignedWeightCharacterBasis.exists_characters_of_decomposition
    e (σ.isometryTorusWeightSupport q i e) (σ.torusRowWeightSpace q t)
    (σ.quadraticWittIndex q)
    (rowWeightSpace_iSupIndep j)
    (σ.iSup_isometryTorusWeightSupport_eq_top q i e)
    (rowWeightSpace_ne_bot_iff j)
    (closure_weightSupport j hmono)
    (fun m _ => (σ.finrank_torusRowWeightSpace_eq_neg q hq t m).symm)
    (fun P _ hP => σ.sum_finrank_torusRowWeightSpace_le_quadraticWittIndex q t P hP)
    hrank
    (fun ν c => σ.cocharacterWeightSpace q (CommGroupScheme.groupHom ν ≫ i) c)
    (σ.cocharacterWeightSpace_eq_iSup_isometryTorusWeightSupport q i e)
  simpa only [Module.finrank_fintype_fun_eq_card] using h

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution
