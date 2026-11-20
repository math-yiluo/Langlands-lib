import Langlands.GroupScheme.Chevalley.ActualRepresentationExtension
import Langlands.GroupScheme.Reductive.GaloisPinningIso
import Langlands.GroupScheme.Reductive.GaloisPinningBaseChange
import Langlands.GroupScheme.Reductive.TitsMaximalWeight
import Langlands.GroupScheme.Reductive.PiTensorWeights
import Langlands.GroupScheme.Reductive.TitsDominantClass

/-! # The Tits obstruction of a base change in terms of the original representation -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace StarActionFiniteStage

variable {B SL SK : Scheme.{u}} (bL : SL ⟶ B) (j : SK ⟶ SL) (bK : SK ⟶ B) (hc : j ≫ bL = bK)

/-- The inverse group tower isomorphism intertwines the changes of test-scheme structure along an
endomorphism `a` of `SK` over `SL`. -/
theorem descentPoint_groupTowerIsoOf_inv (G : GroupScheme B) (a : SK ⟶ SK) (ha : a ≫ j = j)
    (haK : a ≫ bK = bK) (U : Over SK)
    (y : U ⟶ ((GroupScheme.baseChange j).obj ((GroupScheme.baseChange bL).obj G)).X) :
    descentPoint j a ha ((GroupScheme.baseChange bL).obj G) U y ≫
        (groupTowerIsoOf bL j bK hc G).inv.hom.hom =
      descentPoint bK a haK G U (y ≫ (groupTowerIsoOf bL j bK hc G).inv.hom.hom) := by
  subst hc
  have hinv : (groupTowerIsoOf bL j (j ≫ bL) rfl G).inv = (baseChangeCompIso bL j G).inv := by
    simp only [groupTowerIsoOf, eqToIso_refl, Iso.refl_trans]
  rw [hinv]
  exact descentPoint_comp_of_fst (j ≫ bL) j a haK ha G ((GroupScheme.baseChange bL).obj G)
    (baseChangeCompIso bL j G).inv (pullback.fst G.X.hom bL) (baseChangeCompIso_inv_fst bL j G)
    U y

theorem groupTowerIso_eq (k E K : Type u) [Field k] [Field E] [Field K]
    [Algebra k E] [Algebra k K] [Algebra E K] [IsScalarTower k E K]
    (G : GroupScheme (Spec (CommRingCat.of k))) :
    groupTowerIso k E K G = groupTowerIsoOf (algebraBaseMap k E) (algebraBaseMap E K)
      (algebraBaseMap k K) (algebraBaseMap_comp_algebraBaseMap k E K) G :=
  rfl

end StarActionFiniteStage

namespace MatrixRepresentation

variable {k E K : Type u} [Field k] [Field E] [Field K] [Algebra k E] [Algebra k K] [Algebra E K]
  [IsScalarTower k E K] {G : GroupScheme (Spec (CommRingCat.of k))}
  {n : Type} [Fintype n] [DecidableEq n]

/-- Restricting along the inverse tower isomorphism commutes with transport along an
endomorphism `a` of `Spec R` over the intermediate base. -/
theorem transport_restrict_groupTowerIsoOf_inv {B SL : Scheme.{u}} {R : CommRingCat.{u}}
    (bL : SL ⟶ B) (j : Spec R ⟶ SL) (bK : Spec R ⟶ B) (hc : j ≫ bL = bK) (H : GroupScheme B)
    (a : Spec R ⟶ Spec R) (ha : a ≫ j = j) (haK : a ≫ bK = bK)
    (ρ : MatrixRepresentation ((GroupScheme.baseChange bK).obj H) n) :
    transport j a ha ((GroupScheme.baseChange bL).obj H)
        (ρ.restrict (StarActionFiniteStage.groupTowerIsoOf bL j bK hc H).inv) =
      (transport bK a haK H ρ).restrict (StarActionFiniteStage.groupTowerIsoOf bL j bK hc H).inv := by
  apply hom_ext_points
  intro T y
  apply (GeneralLinear.pointsEquiv n R T).injective
  change (transport _ a ha _ _).pointMatrix T y = ((transport _ a haK H ρ).restrict _).pointMatrix T y
  rw [pointMatrix_restrict, pointMatrix_transport, pointMatrix_transport, pointMatrix_restrict,
    StarActionFiniteStage.descentPoint_groupTowerIsoOf_inv bL j bK hc H a ha haK T y]

theorem galoisBaseMap_restrictScalars (h : K ≃ₐ[E] K) :
    galoisBaseMap E K h = galoisBaseMap k K (h.restrictScalars k) :=
  rfl

theorem transport_congr_base {B : Scheme.{u}} (b : Spec (CommRingCat.of K) ⟶ B) (H : GroupScheme B)
    {a a' : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K)} (haa : a = a') (ha : a ≫ b = b)
    (ha' : a' ≫ b = b) (ρ : MatrixRepresentation ((GroupScheme.baseChange b).obj H) n) :
    transport b a ha H ρ = transport b a' ha' H ρ := by
  subst haa
  rfl

/-- **Galois twists and the tower.** Restricting along the tower isomorphism
`(G_E)_K ≅ G_K` commutes with Galois twists by `h ∈ Gal(K/E)`. -/
theorem galoisTwist_restrict_groupTowerIso_inv (h : K ≃ₐ[E] K)
    (ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) n) :
    galoisTwist h (ρ.restrict (groupTowerIso k E K G).inv) =
      (galoisTwist (h.restrictScalars k) ρ).restrict (groupTowerIso k E K G).inv := by
  rw [galoisTwist_eq_transport, galoisTwist_eq_transport,
    transport_congr_base (algebraBaseMap k K) G (galoisBaseMap_restrictScalars (k := k) h).symm _
      (by rw [galoisBaseMap_restrictScalars (k := k) h]; exact galoisBaseMap_over k K _),
    StarActionFiniteStage.groupTowerIso_eq]
  exact transport_restrict_groupTowerIsoOf_inv _ _ _ _ G _ _ _ ρ

end MatrixRepresentation

namespace GaloisPinningData

open MatrixRepresentation Langlands.Algebra.GaloisTwistedMatrix Langlands.Brauer

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (d : GaloisPinningData k K G) (E : Type u) [Field E] [Algebra k E] [Algebra E K]
  [IsScalarTower k E K]

local instance transferTwoStepAffine :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap E K)).obj
      ((GroupScheme.baseChange (algebraBaseMap k E)).obj G)).X.hom :=
  inferInstanceAs (IsAffineHom (pullback.snd
    ((GroupScheme.baseChange (algebraBaseMap k E)).obj G).X.hom (algebraBaseMap E K)))

local instance transferOneStepAffine :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom :=
  inferInstanceAs (IsAffineHom (pullback.snd G.X.hom (algebraBaseMap k K)))

/-- Highest weights correspond under restriction along the tower isomorphism and the weight
transport. -/
theorem isHighestWeight_restrict_groupTowerIso_inv_iff {n : Type} [Fintype n] [DecidableEq n]
    (ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) n)
    (lam : characterLattice d.toSplitPinning.torus) :
    (d.baseChange E).toSplitPinning.IsHighestWeight (ρ.restrict (groupTowerIso k E K G).inv)
        (d.weightTransport E lam) ↔ d.toSplitPinning.IsHighestWeight ρ lam := by
  have hsq : d.toSplitPinning.inclusion ≫ (groupTowerIso k E K G).hom =
      CommGroupScheme.groupHom (torusTowerIso k E K d.torus).hom ≫
        (d.baseChange E).toSplitPinning.inclusion :=
    torusTowerIso_square k E K d.torus d.inclusion
  have he : ∀ χ, (d.baseChangeRootDatumEquiv E).weightMap χ =
      characterLattice.congr (torusTowerIso k E K d.torus) χ := fun χ =>
    (d.baseChangeRootDatumEquiv_weightMap E χ).trans
      (congrFun (AddEquiv.coe_toIntLinearEquiv (characterLattice.congr (torusTowerIso k E K d.torus))) χ)
  have h := SplitPinning.isHighestWeight_restrict_iso_iff (p := d.toSplitPinning)
    (q := (d.baseChange E).toSplitPinning) (groupTowerIso k E K G)
    (torusTowerIso k E K d.torus) hsq (d.baseChangeRootDatumEquiv E) he
    (d.mem_baseChange_base_support_iff E) (ρ.restrict (groupTowerIso k E K G).inv) lam
  rw [restrict_comp, Iso.hom_inv_id, restrict_id] at h
  exact h.symm

variable [LocallyOfFiniteType G.X.hom]

/-- A representation of highest weight `lam` is isomorphic to its Galois twist by every `σ`
whose star action fixes `lam`. -/
theorem exists_intertwiner_galoisTwist_of_smul {r : ℕ}
    {ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) (Fin r)}
    {lam : characterLattice d.toSplitPinning.torus}
    (hρ : d.toSplitPinning.IsHighestWeight ρ lam) (σ : K ≃ₐ[k] K)
    (hfix : (d.starAction σ).val • lam = lam) :
    ∃ C : Matrix (Fin r) (Fin r) K, ρ.Intertwines (galoisTwist σ ρ) C ∧ IsUnit C := by
  have hσ := d.isHighestWeight_galoisTwist σ hρ hfix
  obtain ⟨C, hC, hbij⟩ :=
    ((splitHighestWeightClassification K _ d.toSplitPinning).2.1 r r ρ (galoisTwist σ ρ) lam lam
      hρ hσ).mpr rfl
  exact ⟨C, hC, isUnit_of_bijective_mulVecLin hbij⟩

variable [IsGalois E K]

/-- **The base-changed Tits obstruction in terms of the original representation.** Let `ρ` be a
representation of `G_K` of highest weight `lam`, and let invertible `Q h : ρ → ρ^h` intertwine
for `h ∈ Gal(K/E)`. Then the `E`-algebra `twistedFixed Q` spans `M_r(K)`, and the Tits
obstruction of the base change `G_E` at the transported weight is its Brauer class. -/
theorem titsObstructionValue_baseChange_eq_classOf
    (hspanE : (d.baseChange E).toSplitPinning.rootDatum.corootSpan ℤ = ⊤) {r : ℕ}
    [Nonempty (Fin r)] {ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) (Fin r)}
    {lam : characterLattice d.toSplitPinning.torus} (hρ : d.toSplitPinning.IsHighestWeight ρ lam)
    (Q : (K ≃ₐ[E] K) → Matrix (Fin r) (Fin r) K) (hQu : ∀ h, IsUnit (Q h))
    (hQ : ∀ h : K ≃ₐ[E] K, ρ.Intertwines (galoisTwist (h.restrictScalars k) ρ) (Q h))
    (hfixE : (d.baseChange E).IsStarFixedWeight (d.weightTransport E lam)) :
    ∃ hQspan : Submodule.span K
        ((twistedFixed Q : Subalgebra E (Matrix (Fin r) (Fin r) K)) : Set (Matrix (Fin r) (Fin r) K)) = ⊤,
      (d.baseChange E).titsObstructionValue hspanE (d.weightTransport E lam) hfixE =
        classOf (toCSA Q hQu (twistedFixed Q) le_rfl hQspan) := by
  set ρE := ρ.restrict (groupTowerIso k E K G).inv with hρEdef
  have hE : (d.baseChange E).toSplitPinning.IsHighestWeight ρE (d.weightTransport E lam) :=
    (d.isHighestWeight_restrict_groupTowerIso_inv_iff E ρ lam).mpr hρ
  have hPi : ∀ h : K ≃ₐ[E] K, ρE.Intertwines (galoisTwist h ρE) (Q h) := fun h => by
    rw [hρEdef, galoisTwist_restrict_groupTowerIso_inv]
    exact (hQ h).restrict _
  have hle := titsAlgebra_le_twistedFixed Q hPi
  have hspan : Submodule.span K
      ((twistedFixed Q : Subalgebra E (Matrix (Fin r) (Fin r) K)) : Set (Matrix (Fin r) (Fin r) K))
        = ⊤ := by
    refine eq_top_iff.mpr ((span_titsAlgebra_eq_top ρE hE.1
      (SplitPinning.IsHighestWeight.intertwiner_eq_scalar (d.baseChange E).toSplitPinning hE)).ge.trans
      (Submodule.span_mono hle))
  refine ⟨hspan, ?_⟩
  exact (d.baseChange E).titsObstructionValue_of_maximal hspanE Q hPi hQu _ le_rfl hspan hle hfixE
    hE.2.2.1 (fun mu hmu hsub => hE.hasTopWeight.eq_of_sub_mem hmu hsub)

end GaloisPinningData

end Langlands.GroupScheme
