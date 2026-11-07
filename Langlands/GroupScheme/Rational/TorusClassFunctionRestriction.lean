import Langlands.GroupScheme.Torus.SplitCharacterPoint
import Langlands.GroupScheme.Rational.FundamentalCharacters

/-! # Restriction of class functions to the split maximal torus of a pinning -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.SplitPinning

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : SplitPinning G) {A : Type u} [CommRing A] [Algebra k A]

/-- The universal point of the supplied split maximal torus over the group algebra of its
character lattice. -/
def torusUniversalPoint :
    Lie.AffinePoints p.torus.toGrp (AddMonoidAlgebra k (characterLattice p.torus)) :=
  SplitCharacterPoint.universalPoint p.isSplitTorus

/-- Restriction of class functions to the supplied split maximal torus, written in the
monomial basis of the group algebra of its character lattice. -/
def torusRestriction :
    ClassFunctions.algebra G →ₐ[k] AddMonoidAlgebra k (characterLattice p.torus) :=
  (Lie.pointCoordinates G (p.torusUniversalPoint ≫ p.inclusion.hom.hom)).comp
    (ClassFunctions.inclusion G)

theorem torusRestriction_apply (f : ClassFunctions.algebra G) :
    p.torusRestriction f =
      Lie.pointCoordinates G (p.torusUniversalPoint ≫ p.inclusion.hom.hom) f.val := rfl

/-- At every torus point over every coefficient algebra, a class function is obtained from its
torus restriction by evaluating each monomial at the corresponding character value. -/
theorem pointCoordinates_torusPoint (s : Lie.AffinePoints p.torus.toGrp A)
    (f : ClassFunctions.algebra G) :
    Lie.pointCoordinates G (s ≫ p.inclusion.hom.hom) f.val =
      SplitCharacterPoint.pointLift s (p.torusRestriction f) := by
  conv_lhs => rw [← SplitCharacterPoint.affineMap_pointLift p.isSplitTorus s]
  rw [Lie.affineMap_apply, Category.assoc, ← Lie.affineMap_apply,
    Lie.pointCoordinates_naturality]
  rfl

/-- A class function whose torus restriction vanishes vanishes at every torus point. -/
theorem pointCoordinates_torusPoint_eq_zero {f : ClassFunctions.algebra G}
    (hf : p.torusRestriction f = 0) (s : Lie.AffinePoints p.torus.toGrp A) :
    Lie.pointCoordinates G (s ≫ p.inclusion.hom.hom) f.val = 0 := by
  rw [pointCoordinates_torusPoint, hf, map_zero]

/-! ### Invariance under root reflections -/

/-- Torus restrictions of class functions have coefficients invariant under every root
reflection of the supplied root datum. -/
theorem torusRestriction_coeff_reflection (f : ClassFunctions.algebra G) (α : p.rootIndex)
    (ν : characterLattice p.torus) :
    (p.torusRestriction f).coeff (p.rootDatum.reflection α ν) =
      (p.torusRestriction f).coeff ν := by
  obtain ⟨n, σ, hn, hσ⟩ := p.isRootDatum.2.2 α
  let s : Lie.AffinePoints p.torus.toGrp (AddMonoidAlgebra k (characterLattice p.torus)) :=
    p.torusUniversalPoint ≫ (CommGroupScheme.groupHom σ.hom).hom.hom
  have hrefl : ∀ χ : characterLattice p.torus, p.rootDatum.reflection α χ = σ.hom ≫ χ := by
    intro χ
    apply (p.rootDatum.reflection α).injective
    rw [RootPairing.reflection_same]
    conv_rhs => rw [← hσ]
    rw [characterAut_apply, Iso.inv_hom_id_assoc]
  have hs : SplitCharacterPoint.pointLift s =
      (AddMonoidAlgebra.domCongr k k (p.rootDatum.reflection α).toAddEquiv).toAlgHom := by
    refine AddMonoidAlgebra.algHom_ext (fun χ => ?_) (Subsingleton.elim _ _)
    rw [SplitCharacterPoint.pointLift_single, map_one, one_mul]
    have hv : SplitCharacterPoint.value χ s = SplitCharacterPoint.monomialUnit (σ.hom ≫ χ) :=
      (SplitCharacterPoint.value_comp_hom (T' := p.torus) (CommGroupScheme.groupHom σ.hom) χ
        p.torusUniversalPoint).trans
        (SplitCharacterPoint.value_universalPoint p.isSplitTorus _)
    rw [hv, SplitCharacterPoint.monomialUnit_val]
    change _ = AddMonoidAlgebra.domCongr k k (p.rootDatum.reflection α).toAddEquiv
      (AddMonoidAlgebra.single χ 1)
    rw [AddMonoidAlgebra.domCongr_single]
    exact congrArg (fun x => AddMonoidAlgebra.single x (1 : k)) (hrefl χ).symm
  have hinv := (ClassFunctions.mem_algebra_iff_invariant G).mp f.2
    (AddMonoidAlgebra k (characterLattice p.torus))
    (G.constantPoint n _) (p.torusUniversalPoint ≫ p.inclusion.hom.hom)
  have hconj : G.constantPoint n _ * (p.torusUniversalPoint ≫ p.inclusion.hom.hom) *
      (G.constantPoint n _)⁻¹ = s ≫ p.inclusion.hom.hom := by
    rw [← comp_innerIso_hom, Category.assoc, ← Grp.comp_hom_hom, hn, Grp.comp_hom_hom,
      ← Category.assoc]
  rw [hconj, pointCoordinates_torusPoint, hs, ← torusRestriction_apply] at hinv
  change AddMonoidAlgebra.domCongr k k (p.rootDatum.reflection α).toAddEquiv
    (p.torusRestriction f) = p.torusRestriction f at hinv
  have h2 := congrArg (fun g : AddMonoidAlgebra k (characterLattice p.torus) => g.coeff ν) hinv
  simp only [AddMonoidAlgebra.coeff_domCongr] at h2
  have hsymm : (p.rootDatum.reflection α).toAddEquiv.symm ν = p.rootDatum.reflection α ν := by
    change (p.rootDatum.reflection α).symm ν = _
    exact (LinearEquiv.symm_apply_eq _).mpr (RootPairing.reflection_same _ _ _).symm
  rw [hsymm] at h2
  exact h2

/-! ### Torus restrictions of trace characters -/

section Trace

variable {n : Type} [Fintype n] [DecidableEq n]

/-- The matrix of a representation at the image of the universal torus point. -/
def torusUniversalMatrix (ρ : MatrixRepresentation G n) :
    Matrix n n (AddMonoidAlgebra k (characterLattice p.torus)) :=
  (ρ.affineMatrix (CommAlgCat.of (CommRingCat.of k) (AddMonoidAlgebra k (characterLattice p.torus)))
    (p.torusUniversalPoint ≫ p.inclusion.hom.hom) : Matrix n n _)

theorem torusRestriction_traceClassFunction (ρ : MatrixRepresentation G n) :
    p.torusRestriction (MatrixRepresentation.traceClassFunction ρ) =
      (p.torusUniversalMatrix ρ).trace :=
  MatrixRepresentation.traceClassFunction_evaluate ρ _

/-- Torus weight vectors are eigenvectors of the universal torus matrix, with their monomial
as eigenvalue. -/
theorem torusUniversalMatrix_mulVec_of_mem (ρ : MatrixRepresentation G n)
    {ξ : characterLattice p.torus} {v : n → k} (hv : v ∈ p.representationWeightSpace ρ ξ) :
    p.torusUniversalMatrix ρ *ᵥ (fun r => algebraMap k _ (v r)) =
      AddMonoidAlgebra.single ξ (1 : k) • (fun r => algebraMap k _ (v r)) := by
  let _ := p.isSplitTorus.isAffineHom
  have h := MatrixRepresentation.characterSpace_affine hv
    (CommAlgCat.of (CommRingCat.of k) (AddMonoidAlgebra k (characterLattice p.torus)))
    p.torusUniversalPoint
  rw [MatrixRepresentation.affineMatrix_restrict] at h
  have hval := congrArg Units.val (SplitCharacterPoint.value_universalPoint p.isSplitTorus ξ)
  rw [SplitCharacterPoint.monomialUnit_val] at hval
  rw [← hval]
  exact h

omit [IsAffineHom G.X.hom] [DecidableEq n] in
theorem coeff_mulVec_algebraMap {X : Type u} [AddCommGroup X]
    (M : Matrix n n (AddMonoidAlgebra k X)) (v : n → k) (ν : X) (r : n) :
    ((M *ᵥ fun s => algebraMap k _ (v s)) r).coeff ν =
      ((M.map fun x => x.coeff ν) *ᵥ v) r := by
  simp only [Matrix.mulVec, dotProduct, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    Matrix.map_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [AddMonoidAlgebra.coe_algebraMap, Function.comp_apply, Algebra.algebraMap_self_apply,
    AddMonoidAlgebra.coeff_mul_single_zero]

/-- For a representation whose torus weight spaces span, each coefficient of the torus
restriction of its trace is the dimension of the corresponding weight space. -/
theorem torusRestriction_traceClassFunction_coeff (ρ : MatrixRepresentation G n)
    (hspan : (⨆ ξ, p.representationWeightSpace ρ ξ) = ⊤) (ν : characterLattice p.torus) :
    (p.torusRestriction (MatrixRepresentation.traceClassFunction ρ)).coeff ν =
      (Module.finrank k (p.representationWeightSpace ρ ν) : k) := by
  classical
  let N : Matrix n n k := (p.torusUniversalMatrix ρ).map fun x => x.coeff ν
  have hN : ∀ (ξ : characterLattice p.torus) (v : n → k),
      v ∈ p.representationWeightSpace ρ ξ → N *ᵥ v = if ξ = ν then v else 0 := by
    intro ξ v hv
    funext r
    have h := congrArg (fun w => (w r).coeff ν) (p.torusUniversalMatrix_mulVec_of_mem ρ hv)
    rw [coeff_mulVec_algebraMap] at h
    rw [h, Pi.smul_apply, smul_eq_mul, AddMonoidAlgebra.coe_algebraMap, Function.comp_apply,
      Algebra.algebraMap_self_apply, AddMonoidAlgebra.single_mul_single, add_zero, one_mul,
      AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    split_ifs <;> rfl
  have hproj : LinearMap.IsProj (p.representationWeightSpace ρ ν) (Matrix.toLin' N) := by
    constructor
    · intro w
      have hw : w ∈ ⨆ ξ, p.representationWeightSpace ρ ξ := hspan ▸ Submodule.mem_top
      refine Submodule.iSup_induction _ (motive := fun w =>
        Matrix.toLin' N w ∈ p.representationWeightSpace ρ ν) hw ?_ ?_ ?_
      · intro ξ v hv
        rw [Matrix.toLin'_apply, hN ξ v hv]
        split_ifs with h
        · subst h
          exact hv
        · exact zero_mem _
      · simp
      · intro x y hx hy
        rw [map_add]
        exact add_mem hx hy
    · intro v hv
      rw [Matrix.toLin'_apply, hN ν v hv, ite_eq_left_iff.mpr (fun h => absurd rfl h)]
  have htr : ((p.torusUniversalMatrix ρ).trace).coeff ν = N.trace := by
    simp only [Matrix.trace, Matrix.diag, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
      N, Matrix.map_apply]
  rw [torusRestriction_traceClassFunction, htr, ← Matrix.trace_toLin'_eq, hproj.trace]

end Trace

/-- The torus restriction of a fundamental character has coefficient one at the supplied
highest weight. -/
theorem torusRestriction_character_coeff_highestWeight {a : p.base.support}
    (F : p.FundamentalRepresentation a) :
    (p.torusRestriction F.character).coeff F.highestWeight = 1 := by
  rw [FundamentalRepresentation.character,
    torusRestriction_traceClassFunction_coeff _ _ F.isHighestWeight.2.1,
    F.isHighestWeight.2.2.1, Nat.cast_one]

/-- Every weight of the torus restriction of a fundamental character lies below the supplied
highest weight. -/
theorem sub_mem_positiveRootMonoid_of_mem_support {a : p.base.support}
    (F : p.FundamentalRepresentation a) {ν : characterLattice p.torus}
    (hν : ν ∈ (p.torusRestriction F.character).coeff.support) :
    F.highestWeight - ν ∈ p.positiveRootMonoid := by
  apply F.isHighestWeight.2.2.2
  intro hbot
  rw [Finsupp.mem_support_iff, FundamentalRepresentation.character,
    torusRestriction_traceClassFunction_coeff _ _ F.isHighestWeight.2.1, hbot, finrank_bot,
    Nat.cast_zero] at hν
  exact hν rfl

end SplitPinning

end Langlands.GroupScheme
