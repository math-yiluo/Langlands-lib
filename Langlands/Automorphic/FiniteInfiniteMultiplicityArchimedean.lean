import Langlands.Automorphic.FiniteInfiniteMultiplicityIrreducible
import Langlands.Automorphic.CuspidalArchimedeanGenericComponentReduction
import Langlands.Automorphic.PlaceComponentCarrier

/-! # Admissible compact and local Lie structures on finite-factor multiplicities -/

noncomputable section
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open scoped TensorProduct Matrix

namespace Langlands.Automorphic

attribute [local instance 100] LieRing.ofAssociativeRing

private theorem finite_module_of_injective
    {V W : Type*} [AddCommMonoid V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [Module.Finite ℂ W] (i : V →ₗ[ℂ] W) (hi : Function.Injective i) : Module.Finite ℂ V := by
  have : IsNoetherian ℂ W := isNoetherian_of_isNoetherianRing_of_finite ℂ W
  exact Module.Finite.of_injective i hi

private theorem dual_factor_through_injective
    {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (i : V →ₗ[ℂ] W) (hi : Function.Injective i) (ℓ : V →ₗ[ℂ] ℂ) :
    ∃ μ : W →ₗ[ℂ] ℂ, μ.comp i = ℓ := by
  obtain ⟨r, hr⟩ := i.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hi)
  exact ⟨ℓ.comp r, by rw [LinearMap.comp_assoc, hr, LinearMap.comp_id]⟩

private theorem realGK_of_embedding
    {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {n : ℕ}
    {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V}
    {ρ' : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) W}
    {π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V}
    {π' : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ W}
    (i : V →ₗ[ℂ] W) (hi : Function.Injective i)
    (hk : ∀ k v, i (ρ k v) = ρ' k (i v))
    (hl : ∀ X v, i (π X v) = π' X (i v))
    (h : Archimedean.IsRealGKModule n ρ' π') :
    Archimedean.IsRealGKModule n ρ π := by
  let I : ρ.IntertwiningMap ρ' :=
    { toLinearMap := i
      isIntertwining' k := LinearMap.ext (hk k) }
  refine ⟨fun v => (FiniteVectors.isFiniteVector_map_iff I hi v).mp (h.1 (i v)),
    fun v ℓ => ?_, fun γ X hγ0 hγ v ℓ => ?_, fun k X v => ?_⟩
  · obtain ⟨μ, rfl⟩ := dual_factor_through_injective i hi ℓ
    simpa only [LinearMap.comp_apply, hk] using h.2.1 (i v) μ
  · obtain ⟨μ, rfl⟩ := dual_factor_through_injective i hi ℓ
    simpa only [LinearMap.comp_apply, hk, hl] using h.2.2.1 γ X hγ0 hγ (i v) μ
  · apply hi
    simp only [hk, hl]
    exact h.2.2.2 k X (i v)

private theorem complexGK_of_embedding
    {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {n : ℕ}
    {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V}
    {ρ' : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) W}
    {π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V}
    {π' : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ W}
    (i : V →ₗ[ℂ] W) (hi : Function.Injective i)
    (hk : ∀ k v, i (ρ k v) = ρ' k (i v))
    (hl : ∀ X v, i (π X v) = π' X (i v))
    (h : Archimedean.IsComplexGKModule n ρ' π') :
    Archimedean.IsComplexGKModule n ρ π := by
  let I : ρ.IntertwiningMap ρ' :=
    { toLinearMap := i
      isIntertwining' k := LinearMap.ext (hk k) }
  refine ⟨fun v => (FiniteVectors.isFiniteVector_map_iff I hi v).mp (h.1 (i v)),
    fun v ℓ => ?_, fun γ X hγ0 hγ v ℓ => ?_, fun k X v => ?_⟩
  · obtain ⟨μ, rfl⟩ := dual_factor_through_injective i hi ℓ
    simpa only [LinearMap.comp_apply, hk] using h.2.1 (i v) μ
  · obtain ⟨μ, rfl⟩ := dual_factor_through_injective i hi ℓ
    simpa only [LinearMap.comp_apply, hk, hl] using h.2.2.1 γ X hγ0 hγ (i v) μ
  · apply hi
    simp only [hk, hl]
    exact h.2.2.2 k X (i v)

open Langlands.Global

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local instance multArchRationalGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance multArchContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance multArchSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance multArchFormsGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance multArchStableGroup :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance multArchSpaceGroup (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _

namespace OperatorRealization

variable (S : OperatorRealization F n) (A : Subrepresentation S.finiteRepresentation)

local instance multArchSliceGroup : AddCommGroup A.toSubmodule :=
  Submodule.addCommGroup _

local instance multArchJointGroup (U : OpenSubgroup (FiniteAdelicGL F n))
    (m : ℕ) (σ : Representation ℂ (standardInfiniteCompact F n) (Fin m → ℂ)) :
    AddCommGroup (jointMultiplicitySpace S.finiteRepresentation S.compactRepresentation
      U.toSubgroup σ) := Submodule.addCommGroup _

/-- Evaluation at a fixed finite-factor vector places compact intertwiners in
the original joint multiplicity space. -/
def finiteMultiplicityJointEmbedding (U : OpenSubgroup (FiniteAdelicGL F n))
    (a : A.toSubmodule) (ha : (a : S.Space) ∈ fixedVectors S.finiteRepresentation U.toSubgroup)
    {m : ℕ} (σ : Representation ℂ (standardInfiniteCompact F n) (Fin m → ℂ)) :
    σ.IntertwiningMap (S.finiteMultiplicityCompact A) →ₗ[ℂ]
      jointMultiplicitySpace S.finiteRepresentation S.compactRepresentation U.toSubgroup σ where
  toFun f := ⟨(S.finiteMultiplicityEvalAt A a).toLinearMap.comp f.toLinearMap,
    fun x d => by
      change S.finiteRepresentation d ((f x) a) = (f x) a
      rw [← Representation.IntertwiningMap.isIntertwining _ _ (f x)]
      apply congrArg (fun b : A.toSubmodule => (f x) b)
      exact Subtype.ext (ha d),
    fun k x => congrArg (fun g : S.FiniteMultiplicity A => g a)
      (Representation.IntertwiningMap.isIntertwining _ _ f k x)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem finiteMultiplicityJointEmbedding_injective
    (hA : A.toRepresentation.IsIrreducible)
    (U : OpenSubgroup (FiniteAdelicGL F n)) (a : A.toSubmodule) (ha0 : a ≠ 0)
    (ha : (a : S.Space) ∈ fixedVectors S.finiteRepresentation U.toSubgroup)
    {m : ℕ} (σ : Representation ℂ (standardInfiniteCompact F n) (Fin m → ℂ)) :
    Function.Injective (S.finiteMultiplicityJointEmbedding A U a ha σ) := by
  intro f g hfg
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  apply S.finiteMultiplicityEvalAt_injective A hA ha0
  exact LinearMap.congr_fun (congrArg Subtype.val hfg) x

/-- Joint admissibility bounds every compact multiplicity of the finite-factor
multiplicity space. -/
theorem finiteMultiplicityCompact_finiteIntertwiners
    (hS : S.IsJointlyAdmissible) (hne : A ≠ ⊥) (hA : A.toRepresentation.IsIrreducible)
    (m : ℕ) (σ : Representation ℂ (standardInfiniteCompact F n) (Fin m → ℂ)) :
    Module.Finite ℂ (σ.IntertwiningMap (S.finiteMultiplicityCompact A)) := by
  obtain ⟨a, haA, ha0⟩ := TwoFactorExistence.exists_ne_zero_of_ne_bot hne
  obtain ⟨U, hU⟩ := S.finiteRepresentation_isSmooth a
  have ha₀ : (⟨a, haA⟩ : A.toSubmodule) ≠ 0 :=
    fun h => ha0 (congrArg Subtype.val h)
  have := hS U m σ
  exact finite_module_of_injective (S.finiteMultiplicityJointEmbedding A U ⟨a, haA⟩ hU σ)
    (S.finiteMultiplicityJointEmbedding_injective A hA U ⟨a, haA⟩ ha₀ hU σ)

/-- In particular the combined archimedean compact module is admissible. -/
theorem finiteMultiplicityCompact_isAdmissibleGKModule
    (hS : S.IsJointlyAdmissible) (hne : A ≠ ⊥) (hA : A.toRepresentation.IsIrreducible) :
    Archimedean.IsAdmissibleGKModule (S.finiteMultiplicityCompact A) := by
  intro m τ _
  let σ := matrixRep τ
  have := S.finiteMultiplicityCompact_finiteIntertwiners A hS hne hA m σ
  let T : Archimedean.gkIntertwiners (S.finiteMultiplicityCompact A) m τ →ₗ[ℂ]
      σ.IntertwiningMap (S.finiteMultiplicityCompact A) :=
    { toFun := fun f =>
        { toLinearMap := f.val
          isIntertwining' k := LinearMap.ext (f.property k) }
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  exact finite_module_of_injective T fun f g h =>
    Subtype.ext (congrArg (fun q : σ.IntertwiningMap (S.finiteMultiplicityCompact A) =>
      q.toLinearMap) h)

local notation "RP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}
local notation "CP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}

/-- The actual real-place compact action on the multiplicity space. -/
def finiteMultiplicityRealCompact (v : RP) :
    Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) (S.FiniteMultiplicity A) :=
  (S.finiteMultiplicityCompact A).comp (realPlaceCompactInclusion F n v).toMonoidHom

/-- The actual complex-place compact action on the multiplicity space. -/
def finiteMultiplicityComplexCompact (v : CP) :
    Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) (S.FiniteMultiplicity A) :=
  (S.finiteMultiplicityCompact A).comp
    (complexPlaceCompactInclusion F n v).toMonoidHom

/-- Restriction of the genuine Lie action to one real place. -/
def finiteMultiplicityRealLie (v : RP) :
    (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ (S.FiniteMultiplicity A) :=
  (S.finiteMultiplicityLie A).comp (ArchimedeanGL.realPlaceComplexLieInclusion F n v)

/-- Restriction at a complex place retains the full underlying real Lie algebra. -/
def finiteMultiplicityComplexLie (v : CP) :
    (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ (S.FiniteMultiplicity A) :=
  (S.finiteMultiplicityLie A).comp (ArchimedeanGL.complexPlaceComplexLieInclusion F n v)

/-- The real-place restrictions satisfy all four genuine `(g,K)`-module axioms. -/
theorem finiteMultiplicity_isRealGKModule
    (hne : A ≠ ⊥) (hA : A.toRepresentation.IsIrreducible) (v : RP) :
    Archimedean.IsRealGKModule n (S.finiteMultiplicityRealCompact A v)
      (S.finiteMultiplicityRealLie A v) := by
  obtain ⟨a, haA, ha0⟩ := TwoFactorExistence.exists_ne_zero_of_ne_bot hne
  have ha₀ : (⟨a, haA⟩ : A.toSubmodule) ≠ 0 :=
    fun h => ha0 (congrArg Subtype.val h)
  exact realGK_of_embedding (S.finiteMultiplicityEvalAt A ⟨a, haA⟩).toLinearMap
    (S.finiteMultiplicityEvalAt_injective A hA ha₀)
    (fun _ _ => rfl) (fun _ _ => rfl) (S.isRealGKModule_realPlace v)

/-- The complex-place restrictions satisfy the genuine underlying-real `(g,K)` axioms. -/
theorem finiteMultiplicity_isComplexGKModule
    (hne : A ≠ ⊥) (hA : A.toRepresentation.IsIrreducible) (v : CP) :
    Archimedean.IsComplexGKModule n (S.finiteMultiplicityComplexCompact A v)
      (S.finiteMultiplicityComplexLie A v) := by
  obtain ⟨a, haA, ha0⟩ := TwoFactorExistence.exists_ne_zero_of_ne_bot hne
  have ha₀ : (⟨a, haA⟩ : A.toSubmodule) ≠ 0 :=
    fun h => ha0 (congrArg Subtype.val h)
  exact complexGK_of_embedding (S.finiteMultiplicityEvalAt A ⟨a, haA⟩).toLinearMap
    (S.finiteMultiplicityEvalAt_injective A hA ha₀)
    (fun _ _ => rfl) (fun _ _ => rfl) (S.isComplexGKModule_complexPlace v)

end OperatorRealization
end Langlands.Automorphic
