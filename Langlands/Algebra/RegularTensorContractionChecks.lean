import Langlands.Algebra.RegularTensorContractionStatements

/-!
# Regular-tensor comparison interface checks

These checks retain the original structures and independent universes. They
check the propositions' scope and exact contents without proving the comparison.
-/

set_option autoImplicit false

namespace Langlands.Algebra.RegularTensorContractionChecks

open RegularTensorContraction

universe uA uM uN

section FullTypes

set_option linter.unusedVariables false

example : ∀ (A : Type uA) (M : Type uM) [NonUnitalRing A]
    [AddCommGroup M] [NonUnitalModule A M], Type (max uA uM) := @Tensor

example : ∀ (A : Type uA) (M : Type uM) [NonUnitalRing A]
    [AddCommGroup M] [NonUnitalModule A M], AddCommGroup (Tensor A M) := @tensorGroup

example : ∀ (A : Type uA) (M : Type uM) [NonUnitalRing A]
    [AddCommGroup M] [NonUnitalModule A M], NonUnitalModule A (Tensor A M) := @tensorModule

example : ∀ (A : Type uA) (M : Type uM) [NonUnitalRing A]
    [AddCommGroup M] [NonUnitalModule A M], A → M → Tensor A M := @pure

example : ∀ (A : Type uA) (M : Type uM) [NonUnitalRing A]
    [AddCommGroup M] [NonUnitalModule A M], Tensor A M →+ M := @contraction

example : ∀ (A : Type uA) (M : Type uM) [NonUnitalRing A]
    [AddCommGroup M] [NonUnitalModule A M], IsIdempotented A → Prop := @Properties

example : ∀ (A : Type uA) (M : Type uM) [NonUnitalRing A]
    [AddCommGroup M] [NonUnitalModule A M] (hA : IsIdempotented A),
    Forward A M hA → Inverse A M hA → Prop := @IsComparison

example : ∀ (A : Type uA) (M : Type uM) [NonUnitalRing A]
    [AddCommGroup M] [NonUnitalModule A M], IsIdempotented A → Prop := @HasComparison

example : ∀ (A : Type uA) (M : Type uM) [NonUnitalRing A]
    [AddCommGroup M] [NonUnitalModule A M], Prop := @NondegenerateComparison

example : ∀ (A : Type uA) (M : Type uM) [NonUnitalRing A]
    [AddCommGroup M] [NonUnitalModule A M], IsIdempotented A → Prop := @ModuleComparison

example : ∀ (A : Type uA) {M : Type uM} [NonUnitalRing A]
    [AddCommGroup M] [NonUnitalModule A M] {N : Type uN}
    [AddCommGroup N] [NonUnitalModule A N],
    NonUnitalModuleHom A M N → (Tensor A M →+ Tensor A N) := @tensorMap

example : ∀ (A : Type uA) {M : Type uM} [NonUnitalRing A]
    [AddCommGroup M] [NonUnitalModule A M] {N : Type uN}
    [AddCommGroup N] [NonUnitalModule A N],
    NonUnitalModuleHom A M N → Prop := @ContractionNaturality

example : ∀ (A : Type uA) {M : Type uM} [NonUnitalRing A]
    [AddCommGroup M] [NonUnitalModule A M] {N : Type uN}
    [AddCommGroup N] [NonUnitalModule A N],
    IsIdempotented A → NonUnitalModuleHom A M N → Prop := @ComparisonNaturality

example : Prop := RegularTensorContractionTheorem.{uA, uM, uN}

end FullTypes

section ExactContents

variable (A : Type uA) (M : Type uM) [NonUnitalRing A]
  [AddCommGroup M] [originalAction : NonUnitalModule A M]

example : Tensor A M =
    (letI := NonUnitalModule.rightRegular A; NonUnitalModuleTensor.Tensor A A M) := rfl

example : tensorGroup A M =
    (letI := NonUnitalModule.rightRegular A;
      NonUnitalModuleTensor.addCommGroup A A M) := rfl

example : tensorModule A M =
    (letI := NonUnitalModule.regular A
     letI := NonUnitalModule.rightRegular A
     NonUnitalBimoduleTensor.leftModule (NonUnitalModule.regular_actionsCommute A) M) := rfl

example : pure A M =
    (letI := NonUnitalModule.rightRegular A; NonUnitalModuleTensor.tmul A A M) := rfl

example : contraction A M =
    (letI := NonUnitalModule.rightRegular A;
      NonUnitalModuleTensor.lift A
        (NonUnitalModule.toEndHom originalAction).toAddMonoidHom (action_balanced A M)) := rfl

example (hA : IsIdempotented A) :
    Properties A M hA =
      (letI := tensorModule A M;
       (∀ (a : A) (m : M), contraction A M (pure A M a m) = a • m) ∧
       (∀ (a : A) (t : Tensor A M), contraction A M (a • t) = a • contraction A M t) ∧
       Function.Injective (contraction A M) ∧
       (contraction A M).range = (nondegeneratePart hA M).toAddSubgroup) := rfl

example (hA : IsIdempotented A) (F : Forward A M hA) (G : Inverse A M hA) :
    IsComparison A M hA F G =
      (letI := tensorModule A M;
       (nondegeneratePart hA M).subtype.toAddMonoidHom.comp F.toAddMonoidHom =
         contraction A M ∧
       G.comp F = NonUnitalModuleHom.id A (Tensor A M) ∧
       F.comp G = NonUnitalModuleHom.id A (nondegeneratePart hA M) ∧
       (∀ (m : nondegeneratePart hA M) (e : Idempotent A),
         (e : A) • m.val = m.val → G m = pure A M (e : A) m.val)) := rfl

example (hA : IsIdempotented A) :
    HasComparison A M hA =
      (∃ (F : Forward A M hA) (G : Inverse A M hA), IsComparison A M hA F G) := rfl

example :
    NondegenerateComparison A M =
      (letI := tensorModule A M;
       ∃ (F : NonUnitalModuleHom A (Tensor A M) M)
         (G : NonUnitalModuleHom A M (Tensor A M)),
         F.toAddMonoidHom = contraction A M ∧
         G.comp F = NonUnitalModuleHom.id A (Tensor A M) ∧
         F.comp G = NonUnitalModuleHom.id A M ∧
         (∀ (m : M) (e : Idempotent A),
           (e : A) • m = m → G m = pure A M (e : A) m)) := rfl

example (hA : IsIdempotented A) :
    ModuleComparison A M hA =
      (Properties A M hA ∧ HasComparison A M hA ∧
        (IsNondegenerate A M → NondegenerateComparison A M)) := rfl

variable {M} {N : Type uN} [AddCommGroup N] [NonUnitalModule A N]

example (f : NonUnitalModuleHom A M N) :
    tensorMap A f =
      (letI := NonUnitalModule.rightRegular A;
       NonUnitalModuleTensor.map A (NonUnitalModuleHom.id Aᵐᵒᵖ A) f) := rfl

example (f : NonUnitalModuleHom A M N) :
    ContractionNaturality A f =
      ((contraction A N).comp (tensorMap A f) =
        f.toAddMonoidHom.comp (contraction A M)) := rfl

example (hA : IsIdempotented A) (f : NonUnitalModuleHom A M N) :
    ComparisonNaturality A hA f =
      (letI := tensorModule A M;
       letI := tensorModule A N;
       ∀ (F_M : Forward A M hA) (G_M : Inverse A M hA)
         (F_N : Forward A N hA) (G_N : Inverse A N hA),
         IsComparison A M hA F_M G_M → IsComparison A N hA F_N G_N →
         (NonUnitalModuleHom.restrictNondegeneratePart hA f).toAddMonoidHom.comp
             F_M.toAddMonoidHom = F_N.toAddMonoidHom.comp (tensorMap A f) ∧
         (tensorMap A f).comp G_M.toAddMonoidHom = G_N.toAddMonoidHom.comp
           (NonUnitalModuleHom.restrictNondegeneratePart hA f).toAddMonoidHom) := rfl

end ExactContents

example :
    RegularTensorContractionTheorem.{uA, uM, uN} =
      (∀ (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A),
        (∀ (M : Type uM) [AddCommGroup M] [NonUnitalModule A M],
          ModuleComparison A M hA) ∧
        (∀ (N : Type uN) [AddCommGroup N] [NonUnitalModule A N],
          ModuleComparison A N hA) ∧
        (∀ (M : Type uM) [AddCommGroup M] [NonUnitalModule A M]
          (N : Type uN) [AddCommGroup N] [NonUnitalModule A N]
          (f : NonUnitalModuleHom A M N),
          ContractionNaturality A f ∧ ComparisonNaturality A hA f)) := rfl

/-! Small ring, larger first ambient module; then the reverse assignment.
The naturality telescope also checks unequal ambient module universes. -/

section UnequalUniverses

set_option linter.unusedVariables false

example : ∀ (A : Type 0) (M : Type 1) [NonUnitalRing A]
    [AddCommGroup M] [NonUnitalModule A M], IsIdempotented A → Prop :=
  @ModuleComparison.{0, 1}

example : ∀ (A : Type 1) (M : Type 0) [NonUnitalRing A]
    [AddCommGroup M] [NonUnitalModule A M], IsIdempotented A → Prop :=
  @ModuleComparison.{1, 0}

example : ∀ (A : Type 0) {M : Type 1} [NonUnitalRing A]
    [AddCommGroup M] [NonUnitalModule A M] {N : Type 0}
    [AddCommGroup N] [NonUnitalModule A N],
    IsIdempotented A → NonUnitalModuleHom A M N → Prop := @ComparisonNaturality.{0, 1, 0}

example : ∀ (A : Type 1) {M : Type 0} [NonUnitalRing A]
    [AddCommGroup M] [NonUnitalModule A M] {N : Type 1}
    [AddCommGroup N] [NonUnitalModule A N],
    IsIdempotented A → NonUnitalModuleHom A M N → Prop := @ComparisonNaturality.{1, 0, 1}

example :
    RegularTensorContractionTheorem.{0, 1, 0} =
      (∀ (A : Type 0) [NonUnitalRing A] (hA : IsIdempotented A),
        (∀ (M : Type 1) [AddCommGroup M] [NonUnitalModule A M],
          ModuleComparison A M hA) ∧
        (∀ (N : Type 0) [AddCommGroup N] [NonUnitalModule A N],
          ModuleComparison A N hA) ∧
        (∀ (M : Type 1) [AddCommGroup M] [NonUnitalModule A M]
          (N : Type 0) [AddCommGroup N] [NonUnitalModule A N]
          (f : NonUnitalModuleHom A M N),
          ContractionNaturality A f ∧ ComparisonNaturality A hA f)) := rfl

example :
    RegularTensorContractionTheorem.{1, 0, 1} =
      (∀ (A : Type 1) [NonUnitalRing A] (hA : IsIdempotented A),
        (∀ (M : Type 0) [AddCommGroup M] [NonUnitalModule A M],
          ModuleComparison A M hA) ∧
        (∀ (N : Type 1) [AddCommGroup N] [NonUnitalModule A N],
          ModuleComparison A N hA) ∧
        (∀ (M : Type 0) [AddCommGroup M] [NonUnitalModule A M]
          (N : Type 1) [AddCommGroup N] [NonUnitalModule A N]
          (f : NonUnitalModuleHom A M N),
          ContractionNaturality A f ∧ ComparisonNaturality A hA f)) := rfl

end UnequalUniverses

section CompetingStructures

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable (A : Type uA) (M : Type uM) (N : Type uN)
  (r₀ : NonUnitalRing A) [r₁ : NonUnitalRing A]
  (gm₀ : AddCommGroup M) [gm₁ : AddCommGroup M]
  (gn₀ : AddCommGroup N) [gn₁ : AddCommGroup N]
  (m₀ : @NonUnitalModule A M r₀ gm₀) [m₁ : @NonUnitalModule A M r₁ gm₁]
  (n₀ : @NonUnitalModule A N r₀ gn₀) [n₁ : @NonUnitalModule A N r₁ gn₁]

local notation "Q" => @Tensor A M r₀ gm₀ m₀
local notation "Q'" => @Tensor A N r₀ gn₀ n₀
local notation "GQ" => @tensorGroup A M r₀ gm₀ m₀
local notation "GQ'" => @tensorGroup A N r₀ gn₀ n₀
local notation "LQ" => @tensorModule A M r₀ gm₀ m₀
local notation "LQ'" => @tensorModule A N r₀ gn₀ n₀

variable [gq₁ : AddCommGroup (@Tensor A M r₀ gm₀ m₀)]
  [q₁ : @NonUnitalModule A (@Tensor A M r₀ gm₀ m₀) r₁ gq₁]
  [gq₁' : AddCommGroup (@Tensor A N r₀ gn₀ n₀)]
  [q₁' : @NonUnitalModule A (@Tensor A N r₀ gn₀ n₀) r₁ gq₁']

include r₁ gm₁ gn₁ m₁ n₁ gq₁ q₁ gq₁' q₁'

example : (inferInstance : NonUnitalRing A) = r₁ := rfl
example : (inferInstance : AddCommGroup M) = gm₁ := rfl
example : (inferInstance : AddCommGroup N) = gn₁ := rfl
example : (inferInstance : NonUnitalModule A M) = m₁ := rfl
example : (inferInstance : NonUnitalModule A N) = n₁ := rfl
example : (inferInstance : AddCommGroup Q) = gq₁ := rfl
example : (inferInstance : NonUnitalModule A Q) = q₁ := rfl
example : (inferInstance : AddCommGroup Q') = gq₁' := rfl
example : (inferInstance : NonUnitalModule A Q') = q₁' := rfl

example :
    Q = (letI := r₀; letI := gm₀; letI := m₀;
      letI := NonUnitalModule.rightRegular A; NonUnitalModuleTensor.Tensor A A M) := rfl

example :
    GQ = (letI := r₀; letI := gm₀; letI := m₀;
      letI := NonUnitalModule.rightRegular A;
      NonUnitalModuleTensor.addCommGroup A A M) := rfl

example :
    LQ = (letI := r₀; letI := gm₀; letI := m₀;
      letI := NonUnitalModule.regular A; letI := NonUnitalModule.rightRegular A;
      NonUnitalBimoduleTensor.leftModule (NonUnitalModule.regular_actionsCommute A) M) := rfl

example :
    @contraction A M r₀ gm₀ m₀ =
      (letI := r₀; letI := gm₀; letI := m₀;
       letI := NonUnitalModule.rightRegular A;
       NonUnitalModuleTensor.lift A
         (NonUnitalModule.toEndHom m₀).toAddMonoidHom
         (@action_balanced A M r₀ gm₀ m₀)) := rfl

example (hA : @IsIdempotented A r₀) :
    @Forward A M r₀ gm₀ m₀ hA =
      (letI := r₀; letI := gm₀; letI := m₀;
       letI : AddCommGroup Q := GQ; letI := LQ;
       NonUnitalModuleHom A Q (nondegeneratePart hA M)) := rfl

example (hA : @IsIdempotented A r₀) :
    @Inverse A M r₀ gm₀ m₀ hA =
      (letI := r₀; letI := gm₀; letI := m₀;
       letI : AddCommGroup Q := GQ; letI := LQ;
       NonUnitalModuleHom A (nondegeneratePart hA M) Q) := rfl

example (hA : @IsIdempotented A r₀) :
    @ModuleComparison A M r₀ gm₀ m₀ hA =
      (letI := r₀; letI := gm₀; letI := m₀;
       letI : AddCommGroup Q := GQ; letI := LQ;
       Properties A M hA ∧ HasComparison A M hA ∧
         (IsNondegenerate A M → NondegenerateComparison A M)) := rfl

example (f : @NonUnitalModuleHom A M N r₀ gm₀ gn₀ m₀ n₀) :
    @tensorMap A M r₀ gm₀ m₀ N gn₀ n₀ f =
      (letI := r₀; letI := gm₀; letI := m₀; letI := gn₀; letI := n₀;
       letI : AddCommGroup Q := GQ; letI : AddCommGroup Q' := GQ';
       letI := LQ; letI := LQ';
       letI := NonUnitalModule.rightRegular A;
       NonUnitalModuleTensor.map A (NonUnitalModuleHom.id Aᵐᵒᵖ A) f) := rfl

example (f : @NonUnitalModuleHom A M N r₀ gm₀ gn₀ m₀ n₀) :
    @ContractionNaturality A M r₀ gm₀ m₀ N gn₀ n₀ f =
      (letI := r₀; letI := gm₀; letI := m₀; letI := gn₀; letI := n₀;
       letI : AddCommGroup Q := GQ; letI : AddCommGroup Q' := GQ';
       (contraction A N).comp (tensorMap A f) =
         f.toAddMonoidHom.comp (contraction A M)) := rfl

example (hA : @IsIdempotented A r₀)
    (F : @Forward A M r₀ gm₀ m₀ hA) (G : @Inverse A M r₀ gm₀ m₀ hA) :
    @IsComparison A M r₀ gm₀ m₀ hA F G =
      (letI := r₀; letI := gm₀; letI := m₀;
       letI : AddCommGroup Q := GQ; letI := LQ;
       (nondegeneratePart hA M).subtype.toAddMonoidHom.comp F.toAddMonoidHom =
         contraction A M ∧
       G.comp F = NonUnitalModuleHom.id A Q ∧
       F.comp G = NonUnitalModuleHom.id A (nondegeneratePart hA M) ∧
       (∀ (m : nondegeneratePart hA M) (e : Idempotent A),
         (e : A) • m.val = m.val → G m = pure A M (e : A) m.val)) := rfl

example (hA : @IsIdempotented A r₀)
    (f : @NonUnitalModuleHom A M N r₀ gm₀ gn₀ m₀ n₀) :
    @ComparisonNaturality A M r₀ gm₀ m₀ N gn₀ n₀ hA f =
      (letI := r₀; letI := gm₀; letI := m₀; letI := gn₀; letI := n₀;
       letI : AddCommGroup Q := GQ; letI : AddCommGroup Q' := GQ';
       letI := LQ; letI := LQ';
       ∀ (F_M : Forward A M hA) (G_M : Inverse A M hA)
         (F_N : Forward A N hA) (G_N : Inverse A N hA),
         IsComparison A M hA F_M G_M → IsComparison A N hA F_N G_N →
         (NonUnitalModuleHom.restrictNondegeneratePart hA f).toAddMonoidHom.comp
             F_M.toAddMonoidHom = F_N.toAddMonoidHom.comp (tensorMap A f) ∧
         (tensorMap A f).comp G_M.toAddMonoidHom = G_N.toAddMonoidHom.comp
           (NonUnitalModuleHom.restrictNondegeneratePart hA f).toAddMonoidHom) := rfl

end CompetingStructures

/-! Concrete scope checks: a zero original action on the nonzero group of
integers, and the regular integer action. No main comparison proof is used. -/

section ZeroIntegerAction

local instance : NonUnitalModule ℤ ℤ := NonUnitalModule.zero
local instance : NonUnitalModule ℤᵐᵒᵖ ℤ := NonUnitalModule.rightRegular ℤ

example : Nontrivial ℤ := inferInstance

example : ¬ IsNondegenerate ℤ ℤ := not_isNondegenerate_zero

example :
    ModuleComparison ℤ ℤ (IsIdempotented.of_ring ℤ) =
      (Properties ℤ ℤ (IsIdempotented.of_ring ℤ) ∧
       HasComparison ℤ ℤ (IsIdempotented.of_ring ℤ) ∧
       (IsNondegenerate ℤ ℤ → NondegenerateComparison ℤ ℤ)) := rfl

example : contraction ℤ ℤ = 0 := by
  apply NonUnitalModuleTensor.hom_ext ℤ
  intro a m
  exact NonUnitalModuleTensor.lift_tmul _ _ _ _ _

/-- Balancing against `1` in the regular source kills every pure tensor. -/
private theorem zeroAction_pure (a m : ℤ) : pure ℤ ℤ a m = 0 := by
  have h := NonUnitalModuleTensor.tmul_balanced ℤ ℤ ℤ a 1 m
  change NonUnitalModuleTensor.tmul ℤ ℤ ℤ (1 * a) m =
    NonUnitalModuleTensor.tmul ℤ ℤ ℤ 1 0 at h
  simpa only [one_mul, NonUnitalModuleTensor.tmul_zero] using h

example : Subsingleton (Tensor ℤ ℤ) := by
  have h : AddMonoidHom.id (Tensor ℤ ℤ) = 0 :=
    NonUnitalModuleTensor.hom_ext ℤ (fun a m => zeroAction_pure a m)
  exact ⟨fun x y => (DFunLike.congr_fun h x).trans (DFunLike.congr_fun h y).symm⟩

example : (nondegeneratePart (IsIdempotented.of_ring ℤ) ℤ).toAddSubgroup = ⊥ := by
  ext m
  change (∃ e : Idempotent ℤ, (0 : ℤ) = m) ↔ m = 0
  constructor
  · rintro ⟨_, hm⟩
    exact hm.symm
  · intro hm
    exact ⟨⟨0, IsIdempotentElem.zero⟩, hm.symm⟩

end ZeroIntegerAction

section RegularIntegerAction

local instance : NonUnitalModule ℤ ℤ := NonUnitalModule.regular ℤ
local instance : NonUnitalModule ℤᵐᵒᵖ ℤ := NonUnitalModule.rightRegular ℤ

example : IsNondegenerate ℤ ℤ :=
  fun m => ⟨⟨1, IsIdempotentElem.one⟩, one_mul m⟩

example (a m : ℤ) : contraction ℤ ℤ (pure ℤ ℤ a m) = a * m :=
  NonUnitalModuleTensor.lift_tmul _ _ _ _ _

example : pure ℤ ℤ 1 1 ≠ 0 := by
  intro h
  have hh := congrArg (contraction ℤ ℤ) h
  rw [map_zero] at hh
  change (1 : ℤ) = 0 at hh
  exact one_ne_zero hh

example :
    ModuleComparison ℤ ℤ (IsIdempotented.of_ring ℤ) =
      (Properties ℤ ℤ (IsIdempotented.of_ring ℤ) ∧
       HasComparison ℤ ℤ (IsIdempotented.of_ring ℤ) ∧
       (IsNondegenerate ℤ ℤ → NondegenerateComparison ℤ ℤ)) := rfl

end RegularIntegerAction

/-! Zero rings at an arbitrary universe remain admissible even when the
ambient additive group is nonzero and in a different universe. -/

example (M : Type uM) [AddCommGroup M] :
    Prop :=
  @ModuleComparison PUnit.{uA + 1} M _ _ NonUnitalModule.zero
    (IsIdempotented.of_ring PUnit.{uA + 1})

end Langlands.Algebra.RegularTensorContractionChecks
