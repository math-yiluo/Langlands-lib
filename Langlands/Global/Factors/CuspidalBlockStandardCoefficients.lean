import Langlands.Automorphic.CuspidalArchimedeanComponentIrreducibleProof
import Langlands.Automorphic.CuspidalArchimedeanDensityModels
import Langlands.Automorphic.LocalComponentEmbeddingReduction

/-! # Standard functions in the actual cuspidal block coefficient factors -/

noncomputable section

open scoped TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.CuspidalBlockInduction

open Automorphic _root_.Langlands.Archimedean LocalFactor.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

private theorem nonempty_gkEquiv_of_isotypic
    {K L V A W : Type*} [Group K] [LieRing L] [LieAlgebra ℂ L]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup A] [Module ℂ A]
    [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ K V) (π : L →ₗ⁅ℂ⁆ Module.End ℂ V)
    (ρA : Representation ℂ K A) (πA : L →ₗ⁅ℂ⁆ Module.End ℂ A)
    (ρW : Representation ℂ K W) (πW : L →ₗ⁅ℂ⁆ Module.End ℂ W)
    (hV : IsIrreducibleGKModule ρ π) (hA : IsIrreducibleGKModule ρA πA)
    (hiso : IsGKIsotypic ρA πA ρW πW)
    (j : V →ₗ[ℂ] W) (hj : j ∈ gkHoms ρ π ρW πW) (hinj : Function.Injective j) :
    Nonempty ((gkFreeRepresentation ρ π).Equiv (gkFreeRepresentation ρA πA)) := by
  let := hV.1
  let := isIrreducible_gkFreeRepresentation ρ π hV
  let := isIrreducible_gkFreeRepresentation ρA πA hA
  let f := gkHomsIntertwiningMap ρ π ρW πW ⟨j, hj⟩
  have hf : f ≠ 0 := by
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    intro h
    apply hx
    apply hinj
    rw [map_zero]
    exact congrArg
      (fun g : (gkFreeRepresentation ρ π).IntertwiningMap (gkFreeRepresentation ρW πW) => g x) h
  obtain ⟨g, hg⟩ := IsotypicEmbedding.exists_intertwiningMap_ne_zero_of_isotypic
    (gkFreeRepresentation ρA πA) (gkFreeRepresentation ρ π) (gkFreeRepresentation ρW πW)
    ((isGKIsotypic_iff _ _ _ _).mp hiso) f hf
  exact ⟨g.ofBijective ((Representation.IsIrreducible.bijective_or_eq_zero g).resolve_right hg)⟩

private theorem intertwines_complexifiedLie
    {L V W : Type*} [AddCommGroup L] [Module ℝ L]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (α : ℂ ⊗[ℝ] L →ₗ[ℂ] Module.End ℂ V) (β : ℂ ⊗[ℝ] L →ₗ[ℂ] Module.End ℂ W)
    (a : V →ₗ[ℂ] W) (h : ∀ X x, a (α (1 ⊗ₜ X) x) = β (1 ⊗ₜ X) (a x))
    (Y : ℂ ⊗[ℝ] L) (x : V) : a (α Y x) = β Y (a x) := by
  induction Y using TensorProduct.inductionOn with
  | tmul z X =>
    have hz : z ⊗ₜ[ℝ] X = z • ((1 : ℂ) ⊗ₜ[ℝ] X) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hz]
    simp only [map_smul, LinearMap.smul_apply, h]
  | add X Y hX hY => simp only [map_add, LinearMap.add_apply, hX, hY]

universe u

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

private local instance : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
private local instance : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
private local instance : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
private local instance : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
private local instance : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
private local instance (S : OperatorRealization F n) : AddCommGroup S.Space := Submodule.addCommGroup _

variable [CompactSpace (AdeleQuotient F)] {r : ℕ} (T : CuspidalOperatorRealization F r)

private local instance (p : InfinitePlaceFamily.Index F) :
    AddCommGroup (T.placeDensityModels.subspace p) := Submodule.addCommGroup _

/-- A real standard parameter gives the very coefficient factor chosen in the
all-place tensor decomposition of the inducing cuspidal block. -/
def realStandardCoefficientEquiv
    (v : {v : NumberField.InfinitePlace F // v.IsReal}) {ds : List RealBlock}
    (hp : T.realization.HasRealPlaceParameter v ds) :
    (gkFreeRepresentation (realStandardRep (r + 1) ds) (realStandardLie (r + 1) ds)).Equiv
      (gkFreeRepresentation (T.placeDensityModels.sourceCompact (.inl v))
        (T.placeDensityModels.sourceLie (.inl v))) := by
  refine Classical.choice ?_
  let D := T.placeDensityModels
  have hI := D.irreducible (.inl v)
  have hS := T.isIrreducibleRealStandard v ds hp
  obtain ⟨_, a, hi, hK, hL⟩ := hp
  exact nonempty_gkEquiv_of_isotypic _ _ _ _ _ _ hS
    (PlaceComponent.isIrreducibleGKModule_restrict hI)
    (T.isRealPlaceIsotypic_restrict v hI) a
    ⟨OperatorRealization.realPlaceParameter_compact hK,
      intertwines_complexifiedLie _ _ a (OperatorRealization.realPlaceParameter_lie hL)⟩ hi

/-- A complex standard parameter gives the very coefficient factor chosen in
the all-place tensor decomposition of the inducing cuspidal block. -/
def complexStandardCoefficientEquiv
    (v : {v : NumberField.InfinitePlace F // v.IsComplex}) {ds : List ComplexCharacterData}
    (hp : T.realization.HasComplexPlaceParameter v ds) :
    (gkFreeRepresentation (complexStandardRep (r + 1) ds) (complexStandardLie (r + 1) ds)).Equiv
      (gkFreeRepresentation (T.placeDensityModels.sourceCompact (.inr v))
        (T.placeDensityModels.sourceLie (.inr v))) := by
  refine Classical.choice ?_
  let D := T.placeDensityModels
  have hI := D.irreducible (.inr v)
  have hS := T.isIrreducibleComplexStandard v ds hp
  obtain ⟨_, a, hi, hK, hL⟩ := hp
  exact nonempty_gkEquiv_of_isotypic _ _ _ _ _ _ hS
    (PlaceComponent.isIrreducibleGKModule_restrict hI)
    (T.isComplexPlaceIsotypic_restrict v hI) a
    ⟨OperatorRealization.complexPlaceParameter_compact hK,
      intertwines_complexifiedLie _ _ a (OperatorRealization.complexPlaceParameter_lie hL)⟩ hi

end Langlands.Global.CuspidalBlockInduction
