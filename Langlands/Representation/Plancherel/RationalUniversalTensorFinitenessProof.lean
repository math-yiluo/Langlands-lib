import Langlands.Representation.Plancherel.RationalUniversalTensorFinitenessStatement
import Mathlib.RingTheory.TensorProduct.Finite

/-! The compact fixed comparison in the universal unramified tensor. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal TensorProduct BigOperators
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel

universe uG uI uV u

section FixedMap

variable {L : Type uG} [Group L] [TopologicalSpace L]
  {I : Type uI} (ν : I → (L →* ℝ≥0ˣ)) (hν : ∀ i, Continuous (ν i))
  {E : Type uV} [AddCommGroup E] [Module ℂ E]
  (σ : Representation ℂ L E) (J : Subgroup L) (hJ : IsCompact (J : Set L))

local instance tensorProofAddCommGroup (V : Type*) [AddCommGroup V] [Module ℂ V] :
    AddCommGroup (unramifiedRegularFunctions ν ⊗[ℂ] V) := TensorProduct.addCommGroup

/-- No smoothness or admissibility is needed to commute this complex scalar
extension with the invariants of a compact subgroup. -/
theorem universalTensorFixedInclusion_bijective :
    Function.Bijective (universalTensorFixedInclusion ν hν σ J hJ) := by
  classical
  let B : Type _ := unramifiedRegularFunctions ν
  let b := Module.Basis.ofVectorSpace ℂ B
  let : Module.Free ℂ B := Module.Free.of_basis b
  let Ψ := TensorProduct.equivFinsuppOfBasisLeft (N := E) b
  have hnorm (j : J) : unramifiedEvaluationRegular ν (j : L) = 1 := by
    apply unramifiedEvaluationRegular_eq_one_of_mem_commonNormKernel
    apply (mem_commonNormKernel ν _).mpr
    intro i
    exact RankinSelberg.LastRowReduction.eq_one_of_isCompact (ν i) (hν i) J hJ j.property
  have hcoord (j : J) (x : B ⊗[ℂ] E) (i : Module.Basis.ofVectorSpaceIndex ℂ B) :
      Ψ (universalUnramifiedRepresentation ν σ (j : L) x) i = σ (j : L) (Ψ x i) := by
    induction x using TensorProduct.inductionOn with
    | tmul c v =>
        rw [universalUnramifiedRepresentation_tmul, hnorm j, one_mul]
        simp [Ψ]
    | add x y hx hy =>
        simp only [map_add, Finsupp.add_apply, hx, hy]
  constructor
  · have hinj := Module.Flat.lTensor_preserves_injective_linearMap
      (M := B) (fixedVectors σ J).subtype (Submodule.injective_subtype _)
    intro x y hxy
    exact hinj (congrArg Subtype.val hxy)
  · intro t
    let c := Ψ t.val
    have hc (i : Module.Basis.ofVectorSpaceIndex ℂ B) : c i ∈ fixedVectors σ J := by
      intro j
      change σ (j : L) (Ψ t.val i) = Ψ t.val i
      rw [← hcoord]
      exact congrArg (fun x => Ψ x i) (t.property j)
    let s : B ⊗[ℂ] fixedVectors σ J :=
      ∑ i ∈ c.support, b i ⊗ₜ[ℂ] (⟨c i, hc i⟩ : fixedVectors σ J)
    refine ⟨s, Subtype.ext ?_⟩
    change ((fixedVectors σ J).subtype.baseChange B) s = t.val
    dsimp [s]
    simp only [map_sum, LinearMap.baseChange_tmul, Submodule.subtype_apply]
    exact (TensorProduct.equivFinsuppOfBasisLeft_symm_apply b c).symm.trans
      (Ψ.symm_apply_apply t.val)

include hν hJ in
/-- Finite-dimensional original invariants give finite free, hence projective,
invariants of the actual universal tensor action. -/
theorem universalTensorFixed_finite_projective
    (hfin : Module.Finite ℂ (fixedVectors σ J)) :
    Module.Finite (unramifiedRegularFunctions ν)
        (fixedVectors (universalUnramifiedRepresentation ν σ) J) ∧
      Module.Projective (unramifiedRegularFunctions ν)
        (fixedVectors (universalUnramifiedRepresentation ν σ) J) := by
  let := hfin
  let e := LinearEquiv.ofBijective (universalTensorFixedInclusion ν hν σ J hJ)
    (universalTensorFixedInclusion_bijective ν hν σ J hJ)
  exact ⟨Module.Finite.equiv e, Module.Projective.of_equiv e⟩

end FixedMap

namespace RationalNormalized

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {G M P : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine M.X.left]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation p l a)

local instance tensorProofAmbientAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance tensorProofPointTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X
local instance rationalTensorProofAddCommGroup (V : Type*) [AddCommGroup V] [Module ℂ V] :
    AddCommGroup (RegularAlgebra r ⊗[ℂ] V) := TensorProduct.addCommGroup

variable {E : Type uV} [AddCommGroup E] [Module ℂ E]
  (σ : Representation ℂ (parabolicLeviPointSubgroup p l) E)

theorem universalTensorFlatness : UniversalTensorFlatness r σ := by
  unfold UniversalTensorFlatness
  infer_instance

theorem universalTensorFixedComparison
    (J : Subgroup (parabolicLeviPointSubgroup p l))
    (hJ : IsCompact (J : Set (parabolicLeviPointSubgroup p l))) :
    UniversalTensorFixedComparison r σ J hJ := by
  exact ⟨(LinearEquiv.ofBijective (tensorFixedInclusion r σ J hJ)
    (universalTensorFixedInclusion_bijective _
      (continuous_parabolicLeviRationalNormCharacters r) σ J hJ)).symm, rfl⟩

theorem universalTensorFiniteness (hσ : IsAdmissible σ) :
    UniversalTensorFiniteness r σ := by
  refine ⟨universalTensorFlatness r σ, ?_⟩
  intro J hJ
  exact ⟨universalTensorFixedComparison r σ J.toSubgroup hJ,
    universalTensorFixed_finite_projective _
      (continuous_parabolicLeviRationalNormCharacters r) σ J.toSubgroup hJ (hσ.2 J)⟩

/-- Renard VI.8.1, on the complete rational norm family and at independent
field/group and representation-carrier universes. -/
theorem rationalUniversalTensorFiniteness :
    RationalUniversalTensorFinitenessStatement.{uV, u} := by
  intro F _ _ _ _ G hG
  let := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  intro _ _ M P _ A p l a r E _ _ σ hσ
  exact universalTensorFiniteness r σ hσ

end RationalNormalized

end Langlands.Plancherel
