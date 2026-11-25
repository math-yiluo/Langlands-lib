module

public import StacksFrontier.RingTheory.DiscreteValuationRing.EppDegreePrimeBridge
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppCompletionSquare
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppFactorPackage
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppPerfectResidueComplete
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppWildFamilyPreparation

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Per-factor packages and the per-factor obligation over one shared base extension

The `hfactors` payload with `S i = integralClosure B (E i)`, the factor-level square, the
per-factor obligation `FactorSolutions` and its tame, carried and mixed discharges, and the
route `isWeakSolution_of_forall_factorSolutions`.
-/

@[expose] public section

open scoped TensorProduct

namespace Stacks.EppTheorem

universe uA uB uK uL

section Sync

variable (A : Type uA) (B : Type uB) (L : Type uL) (K₁ K₂ R : Type uK)
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [HenselianLocalRing B]
    [Field L] [Field K₁] [Field K₂]
    [Algebra A B] [Algebra B L] [Algebra K₁ K₂]
    [IsDiscreteValuationRing.IsExtension A B] [IsFractionRing B L]
    [Module.Finite K₁ K₂]
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra A R] [Algebra.IsIntegral A R]
    [Algebra R K₁] [IsFractionRing R K₁] [Algebra R K₂] [IsScalarTower R K₁ K₂]
    [IsDiscreteValuationRing.IsExtension A R]
    {n : ℕ} (E : Fin n → Type (max uL uK))
    [∀ i, Field (E i)] [∀ i, Algebra L (E i)] [∀ i, Algebra K₁ (E i)]
    [∀ i, Algebra B (E i)] [∀ i, Algebra R (E i)] [∀ i, Algebra A (E i)]
    [∀ i, IsScalarTower B L (E i)] [∀ i, IsScalarTower R K₁ (E i)]
    [∀ i, IsScalarTower A B (E i)] [∀ i, IsScalarTower A R (E i)]
    [∀ i, FiniteDimensional L (E i)] [∀ i, FaithfulSMul R (E i)]

end Sync

/-! ### The factor-level square -/

section FactorSquare

variable (A : Type uA) (K : Type uK) (L : Type uL) (K₁ : Type uK) [CommRing A] [Field K] [Field L]
  [Field K₁]
    [Algebra A K] [Algebra A L] [Algebra A K₁] [Algebra K L] [Algebra K K₁]
    [IsScalarTower A K L] [IsScalarTower A K K₁]
    {n : ℕ} (E : Fin n → Type (max uL uK)) [∀ i, Field (E i)] [∀ i, Algebra K (E i)]
    [∀ i, Algebra L (E i)] [∀ i, Algebra K₁ (E i)]

include K in
/-- **The two routes from `A` into a conjugate factor agree.**

`A → L → E i` and `A → K₁ → E i` are the same map.  Both `L` and `K₁` reach the factor through
the decomposition, and in the tensor product the images of `A` under the two inclusions already
agree, because `includeLeft` and `includeRight` are `K`-algebra maps and `A` acts through `K` on
both sides.  Projecting along `decomp` at the index `i` and using the two compatibility equations
turns that into the displayed equality.

This is the factor-level analogue of the `hA` hypothesis that
`IsDiscreteValuationRing.isWeakSolution_of_forall_reducedFactorPackages` takes at `K₂`, and it is
what `exists_reducedFactorPackages` needs in order to be fed the combiner's own data: of the
structures over `A`, `B` and `R` that its hypotheses use, every other one is a composite of what
`hfactors` supplies. -/
theorem algebraMap_reducedFactor_base_eq
    (decomp : ReducedTensorTower.Reduction (L ⊗[K] K₁) ≃ₐ[K] ∀ i, E i)
    (hleft : ∀ i (l : L), decomp (Ideal.Quotient.mk _
        ((Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] K₁) l)) i = algebraMap L (E i) l)
    (hright : ∀ i (x : K₁), decomp (Ideal.Quotient.mk _
        ((Algebra.TensorProduct.includeRight : K₁ →ₐ[K] L ⊗[K] K₁) x)) i = algebraMap K₁ (E i) x)
    (i : Fin n) (a : A) :
    algebraMap L (E i) (algebraMap A L a) = algebraMap K₁ (E i) (algebraMap A K₁ a) := by
  have hxy : (Ideal.Quotient.mk (nilradical (L ⊗[K] K₁))
        ((Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] K₁)
          (algebraMap K L (algebraMap A K a)))) =
      (Ideal.Quotient.mk (nilradical (L ⊗[K] K₁))
        ((Algebra.TensorProduct.includeRight : K₁ →ₐ[K] L ⊗[K] K₁)
          (algebraMap K K₁ (algebraMap A K a)))) := by
    congr 1
    rw [AlgHom.commutes, AlgHom.commutes]
  rw [IsScalarTower.algebraMap_apply A K L a, IsScalarTower.algebraMap_apply A K K₁ a,
    ← hleft i _, ← hright i _, hxy]

end FactorSquare

section FactorSquareTower

variable (A : Type uA) (B : Type uB) (K : Type uK) (L : Type uL) (K₁ : Type uK) [CommRing A]
  [CommRing B] [Field K] [Field L] [Field K₁]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra A K₁] [Algebra B L]
    [Algebra K L] [Algebra K K₁]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K K₁]
    {n : ℕ} (E : Fin n → Type (max uL uK)) [∀ i, Field (E i)] [∀ i, Algebra K (E i)]
    [∀ i, Algebra L (E i)] [∀ i, Algebra K₁ (E i)] [∀ i, Algebra B (E i)]
    [∀ i, IsScalarTower B L (E i)]

include K L in
/-- **The same square, read through `B`.**

`A → B → E i` and `A → K₁ → E i` agree.  This is the form `exists_reducedFactorPackages` consumes
— its `IsScalarTower A R (E i)` hypothesis is exactly this equality once the structure maps
`A → E i` and `R → E i` are taken to be the composites through `B` and through `K₁` — and it
follows from `algebraMap_reducedFactor_base_eq` by pushing `A → B → L` down to `A → L`. -/
theorem algebraMap_reducedFactor_base_eq_of_tower
    (decomp : ReducedTensorTower.Reduction (L ⊗[K] K₁) ≃ₐ[K] ∀ i, E i)
    (hleft : ∀ i (l : L), decomp (Ideal.Quotient.mk _
        ((Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] K₁) l)) i = algebraMap L (E i) l)
    (hright : ∀ i (x : K₁), decomp (Ideal.Quotient.mk _
        ((Algebra.TensorProduct.includeRight : K₁ →ₐ[K] L ⊗[K] K₁) x)) i = algebraMap K₁ (E i) x)
    (i : Fin n) (a : A) :
    algebraMap B (E i) (algebraMap A B a) = algebraMap K₁ (E i) (algebraMap A K₁ a) := by
  rw [IsScalarTower.algebraMap_apply B L (E i), ← IsScalarTower.algebraMap_apply A B L]
  exact algebraMap_reducedFactor_base_eq A K L K₁ E decomp hleft hright i a

/-- The two routes `A → B → E i` and `A → K₁ → E i` agreeing makes `E i` a scalar tower over
`A → R`. -/
private theorem isScalarTower_of_reducedFactor_square
    (R : Type uK) [CommRing R] [Algebra A R] [Algebra R K₁] [IsScalarTower A R K₁]
    [∀ i, Algebra A (E i)] [∀ i, IsScalarTower A B (E i)] [∀ i, Algebra R (E i)]
    [∀ i, IsScalarTower R K₁ (E i)]
    (decomp : ReducedTensorTower.Reduction (L ⊗[K] K₁) ≃ₐ[K] ∀ i, E i)
    (hleft : ∀ i (l : L), decomp (Ideal.Quotient.mk _
        ((Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] K₁) l)) i = algebraMap L (E i) l)
    (hright : ∀ i (x : K₁), decomp (Ideal.Quotient.mk _
        ((Algebra.TensorProduct.includeRight : K₁ →ₐ[K] L ⊗[K] K₁) x)) i =
      algebraMap K₁ (E i) x)
    (i : Fin n) : IsScalarTower A R (E i) :=
  .of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply A B (E i),
      algebraMap_reducedFactor_base_eq_of_tower A B K L K₁ E decomp hleft hright i a,
      IsScalarTower.algebraMap_apply R K₁ (E i), ← IsScalarTower.algebraMap_apply A R K₁]

end FactorSquareTower

/-! ### The per-factor obligation, in the context the combiner's data determines -/

section Obligation

variable (A : Type uA) (B : Type uB) (K : Type uK) (L : Type uL) (K₁ K₂ R : Type uK)
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [HenselianLocalRing B]
    [Field K] [Field L] [Field K₁] [Field K₂]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra A K₁] [Algebra B L]
    [Algebra K L] [Algebra K K₁] [Algebra K₁ K₂]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K K₁]
    [IsDiscreteValuationRing.IsExtension A B] [IsFractionRing B L]
    [Module.Finite K₁ K₂]
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra A R] [Algebra.IsIntegral A R] [IsDiscreteValuationRing.IsExtension A R]
    [Algebra R K₁] [IsFractionRing R K₁] [Algebra R K₂] [IsScalarTower R K₁ K₂]
    [IsScalarTower A R K₁]
    {n : ℕ} (E : Fin n → Type (max uL uK))
    [∀ i, Field (E i)] [∀ i, Algebra K (E i)] [∀ i, Algebra L (E i)] [∀ i, Algebra K₁ (E i)]
    [∀ i, Module.Finite L (E i)]

/-- **The per-factor weak-solution obligation of the all-factor route.**

Given a decomposition of `(L ⊗[K] K₁) ⧸ nilradical` into conjugate factors, this is the
proposition that every factor's integral closure over `B` admits a weak solution over one shared
`K₂` — the thing a caller must produce to run
`IsDiscreteValuationRing.isWeakSolution_of_forall_reducedFactorPackages`, and the only thing left
after `exists_reducedFactorPackages`.

It is packaged as a definition because stating it requires fixing eight structures that the
combiner's own data determines but does not hand over: the composites `B → L → E i`,
`A → B → E i` and `R → K₁ → E i` with their three towers, the faithfulness of `R` on the factor,
and `IsScalarTower A R (E i)`, which is the factor-level square
`algebraMap_reducedFactor_base_eq_of_tower`.  Writing those out at each use would bury the
mathematical content; naming them once does not.

No factor is distinguished: the quantifier runs over every index. -/
def FactorSolutions
    (decomp : ReducedTensorTower.Reduction (L ⊗[K] K₁) ≃ₐ[K] ∀ i, E i)
    (hleft : ∀ i (l : L), decomp (Ideal.Quotient.mk _
        ((Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] K₁) l)) i = algebraMap L (E i) l)
    (hright : ∀ i (x : K₁), decomp (Ideal.Quotient.mk _
        ((Algebra.TensorProduct.includeRight : K₁ →ₐ[K] L ⊗[K] K₁) x)) i =
      algebraMap K₁ (E i) x) : Prop :=
  letI : ∀ i, Algebra B (E i) := fun i =>
    ((algebraMap L (E i)).comp (algebraMap B L)).toAlgebra
  letI : ∀ i, IsScalarTower B L (E i) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
  letI : ∀ i, Algebra A (E i) := fun i =>
    ((algebraMap B (E i)).comp (algebraMap A B)).toAlgebra
  letI : ∀ i, IsScalarTower A B (E i) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
  letI : ∀ i, Algebra R (E i) := fun i =>
    ((algebraMap K₁ (E i)).comp (algebraMap R K₁)).toAlgebra
  letI : ∀ i, IsScalarTower R K₁ (E i) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
  letI : ∀ i, FaithfulSMul R (E i) := fun i =>
    (faithfulSMul_iff_algebraMap_injective R (E i)).mpr
      ((algebraMap K₁ (E i)).injective.comp (IsFractionRing.injective R K₁))
  letI : ∀ i, IsScalarTower A R (E i) := fun i =>
    IsScalarTower.of_algebraMap_eq fun a =>
      (algebraMap_reducedFactor_base_eq_of_tower A B K L K₁ E decomp hleft hright i a).trans
        (congrArg (algebraMap K₁ (E i)) (IsScalarTower.algebraMap_apply A R K₁ a))
  letI : ∀ i, IsDiscreteValuationRing (integralClosure B (E i)) := fun i =>
    isDiscreteValuationRing_integralClosure_factor B L (E i)
  letI : ∀ i, Algebra R (integralClosure B (E i)) := fun i =>
    algebraIntegralClosureBase A B R (E i)
  letI : ∀ i, IsFractionRing (integralClosure B (E i)) (E i) := fun i =>
    isFractionRing_integralClosure_factor B L (E i)
  letI : ∀ i, IsScalarTower R (integralClosure B (E i)) (E i) := fun i =>
    isScalarTower_base_integralClosure_factor A B R (E i)
  letI : ∀ i, IsDiscreteValuationRing.IsExtension R (integralClosure B (E i)) := fun i =>
    isExtension_base_integralClosure_factor A B R L (E i)
  ∀ i, ∃ D : IsDiscreteValuationRing.IntegralClosureBaseChange.{uK, max uL uK, uK, max uL uK, uK,
    max uL uK, uK, max uL uK}
    R (integralClosure B (E i)) K₁ (E i) K₂, D.IsWeakSolution

/-- **The per-factor obligation when the complete perfect-residue combiner is available.**

Unlike `FactorSolutions`, the extension field is allowed to depend on the factor.  This is sound
precisely in the setting where the base ring `R` is complete with perfect residue field: the
factorwise weak solutions can then be embedded into one finite overfield and remain weak
solutions, by
`IsDiscreteValuationRing.exists_finite_extension_forall_isWeakSolution_of_perfect_residueField`.

Naming this version prevents the equal-characteristic proof from imposing an unnecessary and
substantially stronger synchronization requirement on its constant and nonconstant Laurent
branches.  The all-conjugates requirement is unchanged: every factor still has to be solved. -/
def IndividualFactorSolutions
    (decomp : ReducedTensorTower.Reduction (L ⊗[K] K₁) ≃ₐ[K] ∀ i, E i)
    (hleft : ∀ i (l : L), decomp (Ideal.Quotient.mk _
        ((Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] K₁) l)) i = algebraMap L (E i) l)
    (hright : ∀ i (x : K₁), decomp (Ideal.Quotient.mk _
        ((Algebra.TensorProduct.includeRight : K₁ →ₐ[K] L ⊗[K] K₁) x)) i =
      algebraMap K₁ (E i) x) : Prop :=
  letI : ∀ i, Algebra B (E i) := fun i =>
    ((algebraMap L (E i)).comp (algebraMap B L)).toAlgebra
  letI : ∀ i, IsScalarTower B L (E i) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
  letI : ∀ i, Algebra A (E i) := fun i =>
    ((algebraMap B (E i)).comp (algebraMap A B)).toAlgebra
  letI : ∀ i, IsScalarTower A B (E i) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
  letI : ∀ i, Algebra R (E i) := fun i =>
    ((algebraMap K₁ (E i)).comp (algebraMap R K₁)).toAlgebra
  letI : ∀ i, IsScalarTower R K₁ (E i) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
  letI : ∀ i, FaithfulSMul R (E i) := fun i =>
    (faithfulSMul_iff_algebraMap_injective R (E i)).mpr
      ((algebraMap K₁ (E i)).injective.comp (IsFractionRing.injective R K₁))
  letI : ∀ i, IsScalarTower A R (E i) := fun i =>
    IsScalarTower.of_algebraMap_eq fun a =>
      (algebraMap_reducedFactor_base_eq_of_tower A B K L K₁ E decomp hleft hright i a).trans
        (congrArg (algebraMap K₁ (E i)) (IsScalarTower.algebraMap_apply A R K₁ a))
  letI : ∀ i, IsDiscreteValuationRing (integralClosure B (E i)) := fun i =>
    isDiscreteValuationRing_integralClosure_factor B L (E i)
  letI : ∀ i, Algebra R (integralClosure B (E i)) := fun i =>
    algebraIntegralClosureBase A B R (E i)
  letI : ∀ i, IsFractionRing (integralClosure B (E i)) (E i) := fun i =>
    isFractionRing_integralClosure_factor B L (E i)
  letI : ∀ i, IsScalarTower R (integralClosure B (E i)) (E i) := fun i =>
    isScalarTower_base_integralClosure_factor A B R (E i)
  letI : ∀ i, IsDiscreteValuationRing.IsExtension R (integralClosure B (E i)) := fun i =>
    isExtension_base_integralClosure_factor A B R L (E i)
  ∀ i, ∃ (F : Type uK) (_ : Field F) (_ : Algebra K₁ F) (_ : Algebra R F)
      (_ : IsScalarTower R K₁ F) (_ : Module.Finite K₁ F),
    ∃ D : IsDiscreteValuationRing.IntegralClosureBaseChange.{uK, max uL uK, uK,
        max uL uK, uK, max uL uK, uK, max uL uK}
      R (integralClosure B (E i)) K₁ (E i) F, D.IsWeakSolution

include A B K L K₁ R in
/-- **The all-factor route with factorwise extension fields.**

When `R` and the factor rings are complete and `ResidueField R` is perfect, every conjugate
factor may first be solved over its own finite extension of `K₁`.  The perfect-residue combiner
then replaces those fields by one finite common overfield while preserving all weak solutions.

This is the appropriate interface for the complete case of Epp's theorem.  It retains the sound
all-conjugates correction to Tag 09ET, but avoids asking the two Laurent branches to manufacture
the same extension before their solutions have been constructed. -/
theorem exists_finite_extension_isWeakSolution_of_forall_individualFactorSolutions
    [Module.Finite K K₁] [IsFractionRing A K]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    [PerfectField (IsLocalRing.ResidueField R)]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    (hA : ∀ a : A, algebraMap K K₁ (algebraMap A K a) =
      algebraMap R K₁ (algebraMap A R a))
    (hsol : ∀ (m : ℕ) (F : Fin m → Type (max uL uK)) (_ : ∀ i, Field (F i))
      (_ : ∀ i, Algebra K (F i)) (_ : ∀ i, Algebra L (F i))
      (_ : ∀ i, Algebra K₁ (F i)) (_ : ∀ i, IsScalarTower K L (F i))
      (_ : ∀ i, IsScalarTower K K₁ (F i)) (_ : ∀ i, Module.Finite L (F i))
      (decomp : ReducedTensorTower.Reduction (L ⊗[K] K₁) ≃ₐ[K] ∀ i, F i)
      (hleft : ∀ i (l : L), decomp (Ideal.Quotient.mk _
          ((Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] K₁) l)) i =
        algebraMap L (F i) l)
      (hright : ∀ i (x : K₁), decomp (Ideal.Quotient.mk _
          ((Algebra.TensorProduct.includeRight : K₁ →ₐ[K] L ⊗[K] K₁) x)) i =
        algebraMap K₁ (F i) x),
      IndividualFactorSolutions A B K L K₁ R F decomp hleft hright) :
    ∃ (F : Type uK) (_ : Field F) (_ : Algebra K F) (_ : Algebra A F)
      (_ : IsScalarTower A K F) (_ : Module.Finite K F),
      ∃ D : IsDiscreteValuationRing.IntegralClosureBaseChange.{uA, uB, uK, uL, uK,
          max uL uK, uK, max uL uK} A B K L F,
        D.IsWeakSolution := by
  refine
    IsDiscreteValuationRing.exists_finite_extension_isWeakSolution_of_forall_reducedFactorSolutions
    A B K L K₁ R hA ?_
  intro m F instFieldF instKF instLF instK₁F instKLF instKK₁F instFinF decomp hleft hright
  let := instFieldF
  let := instKF
  let := instLF
  let := instK₁F
  let := instKLF
  let := instKK₁F
  let := instFinF
  let : ∀ i, Algebra B (F i) := fun i =>
    ((algebraMap L (F i)).comp (algebraMap B L)).toAlgebra
  let : ∀ i, IsScalarTower B L (F i) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
  let : ∀ i, Algebra A (F i) := fun i =>
    ((algebraMap B (F i)).comp (algebraMap A B)).toAlgebra
  let : ∀ i, IsScalarTower A B (F i) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
  let : ∀ i, Algebra R (F i) := fun i =>
    ((algebraMap K₁ (F i)).comp (algebraMap R K₁)).toAlgebra
  let : ∀ i, IsScalarTower R K₁ (F i) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
  let : ∀ i, FaithfulSMul R (F i) := fun i => FaithfulSMul.trans R K₁ (F i)
  let : ∀ i, IsScalarTower A R (F i) := fun i =>
    isScalarTower_of_reducedFactor_square A B K L K₁ F R decomp hleft hright i
  let : ∀ i, IsDiscreteValuationRing (integralClosure B (F i)) := fun i =>
    isDiscreteValuationRing_integralClosure_factor B L (F i)
  let : ∀ i, Algebra R (integralClosure B (F i)) := fun i =>
    algebraIntegralClosureBase A B R (F i)
  let : ∀ i, IsFractionRing (integralClosure B (F i)) (F i) := fun i =>
    isFractionRing_integralClosure_factor B L (F i)
  let : ∀ i, IsScalarTower R (integralClosure B (F i)) (F i) := fun i =>
    isScalarTower_base_integralClosure_factor A B R (F i)
  let : ∀ i, IsDiscreteValuationRing.IsExtension R (integralClosure B (F i)) := fun i =>
    isExtension_base_integralClosure_factor A B R L (F i)
  have hcomplete : ∀ i, IsAdicComplete
      (IsLocalRing.maximalIdeal (integralClosure B (F i))) (integralClosure B (F i)) := by
    intro i
    obtain ⟨_, _, _, hcomp, _⟩ :=
      IsDiscreteValuationRing.integralClosure_isCompleteDVR B L (F i)
    exact hcomp
  refine ⟨fun i => integralClosure B (F i), fun _ => inferInstance, fun _ => inferInstance,
    fun i => isDiscreteValuationRing_integralClosure_factor B L (F i),
    fun i => algebraIntegralClosureBase A B R (F i),
    fun i => isExtension_base_integralClosure_factor A B R L (F i),
    fun _ => inferInstance, fun _ => inferInstance, fun _ => inferInstance,
    fun _ => inferInstance,
    fun i => isFractionRing_integralClosure_factor B L (F i),
    fun i => isScalarTower_base_integralClosure_factor A B R (F i),
    fun _ => inferInstance, hcomplete,
    fun i b => algebraMap_integralClosure_factor_eq_of_tower B L (F i) b,
    fun i a => algebraMap_integralClosureBase_eq A B R (F i) a, ?_⟩
  exact hsol m F instFieldF instKF instLF instK₁F instKLF instKK₁F instFinF
    decomp hleft hright

end Obligation

end Stacks.EppTheorem

end
