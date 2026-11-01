import Langlands.Algebra.NonUnitalBimoduleTensor

/-!
# Canonical regular-tensor contraction

Statement interfaces for Renard (9 July 2026), I.2.3, (I.2.3.3), printed
p.17/PDF23. These definitions retain the original additive modules and actual
published balancing quotient. The closed comparison target is not proved here.
-/

set_option autoImplicit false

namespace Langlands.Algebra

universe uA uM uN

namespace RegularTensorContraction

variable (A : Type uA) (M : Type uM) [NonUnitalRing A]
  [AddCommGroup M] [originalAction : NonUnitalModule A M]

/-- The published tensor with its specified right regular first factor. -/
abbrev Tensor : Type (max uA uM) :=
  letI := NonUnitalModule.rightRegular A
  NonUnitalModuleTensor.Tensor A A M

/-- Its published inherited additive group. -/
abbrev tensorGroup : AddCommGroup (Tensor A M) :=
  letI := NonUnitalModule.rightRegular A
  NonUnitalModuleTensor.addCommGroup A A M

/-- Exactly the one-sided residual left action from the regular bimodule. -/
abbrev tensorModule : NonUnitalModule A (Tensor A M) :=
  letI := NonUnitalModule.regular A
  letI := NonUnitalModule.rightRegular A
  NonUnitalBimoduleTensor.leftModule (NonUnitalModule.regular_actionsCommute A) M

/-- The actual pure tensor, with no replacement tensor construction. -/
abbrev pure (a : A) (m : M) : Tensor A M :=
  letI := NonUnitalModule.rightRegular A
  NonUnitalModuleTensor.tmul A A M a m

/-- Associativity balances the original action pairing against right multiplication. -/
theorem action_balanced :
    letI := NonUnitalModule.rightRegular A
    NonUnitalModuleTensor.IsBalanced A
      (NonUnitalModule.toEndHom originalAction).toAddMonoidHom := by
  intro b a m
  change (a * b) • m = a • (b • m)
  exact mul_smul a b m

/-- The contraction is the published universal lift of the original action. -/
def contraction : Tensor A M →+ M :=
  letI := NonUnitalModule.rightRegular A
  NonUnitalModuleTensor.lift A
    (NonUnitalModule.toEndHom originalAction).toAddMonoidHom (action_balanced A M)

/-- Original module maps from the specified tensor to the actual part. -/
abbrev Forward (hA : IsIdempotented A) :=
  letI := tensorModule A M
  NonUnitalModuleHom A (Tensor A M) (nondegeneratePart hA M)

/-- Original module maps in the reverse direction, with the same tensor action. -/
abbrev Inverse (hA : IsIdempotented A) :=
  letI := tensorModule A M
  NonUnitalModuleHom A (nondegeneratePart hA M) (Tensor A M)

/-- Pure values, original equivariance, injectivity and exact additive range. -/
def Properties (hA : IsIdempotented A) : Prop :=
  letI := tensorModule A M
  (∀ (a : A) (m : M), contraction A M (pure A M a m) = a • m) ∧
  (∀ (a : A) (t : Tensor A M), contraction A M (a • t) = a • contraction A M t) ∧
  Function.Injective (contraction A M) ∧
  (contraction A M).range = (nondegeneratePart hA M).toAddSubgroup

/-- Both entire inverse maps, factorization through the actual inclusion, and
an inverse formula valid for every idempotent fixing the input vector. -/
def IsComparison (hA : IsIdempotented A) (F : Forward A M hA)
    (G : Inverse A M hA) : Prop :=
  letI := tensorModule A M
  (nondegeneratePart hA M).subtype.toAddMonoidHom.comp F.toAddMonoidHom = contraction A M ∧
  G.comp F = NonUnitalModuleHom.id A (Tensor A M) ∧
  F.comp G = NonUnitalModuleHom.id A (nondegeneratePart hA M) ∧
  (∀ (m : nondegeneratePart hA M) (e : Idempotent A),
    (e : A) • m.val = m.val → G m = pure A M (e : A) m.val)

/-- Existence is a conclusion, without any comparison certificate as a premise. -/
def HasComparison (hA : IsIdempotented A) : Prop :=
  ∃ (F : Forward A M hA) (G : Inverse A M hA), IsComparison A M hA F G

/-- The whole-module specialization, used only under original nondegeneracy. -/
def NondegenerateComparison : Prop :=
  letI := tensorModule A M
  ∃ (F : NonUnitalModuleHom A (Tensor A M) M)
    (G : NonUnitalModuleHom A M (Tensor A M)),
    F.toAddMonoidHom = contraction A M ∧
    G.comp F = NonUnitalModuleHom.id A (Tensor A M) ∧
    F.comp G = NonUnitalModuleHom.id A M ∧
    (∀ (m : M) (e : Idempotent A),
      (e : A) • m = m → G m = pure A M (e : A) m)

/-- The general comparison and its guarded nondegenerate specialization. -/
def ModuleComparison (hA : IsIdempotented A) : Prop :=
  Properties A M hA ∧ HasComparison A M hA ∧
    (IsNondegenerate A M → NondegenerateComparison A M)

variable {M} {N : Type uN} [AddCommGroup N] [NonUnitalModule A N]

/-- Exactly the published tensor map of the regular identity and the original map. -/
abbrev tensorMap (f : NonUnitalModuleHom A M N) : Tensor A M →+ Tensor A N :=
  letI := NonUnitalModule.rightRegular A
  NonUnitalModuleTensor.map A (NonUnitalModuleHom.id Aᵐᵒᵖ A) f

/-- Naturality is an equality of complete additive maps. -/
def ContractionNaturality (f : NonUnitalModuleHom A M N) : Prop :=
  (contraction A N).comp (tensorMap A f) = f.toAddMonoidHom.comp (contraction A M)

/-- Both directions of naturality for any actual comparison witnesses. -/
def ComparisonNaturality (hA : IsIdempotented A) (f : NonUnitalModuleHom A M N) : Prop :=
  letI := tensorModule A M
  letI := tensorModule A N
  ∀ (F_M : Forward A M hA) (G_M : Inverse A M hA)
    (F_N : Forward A N hA) (G_N : Inverse A N hA),
    IsComparison A M hA F_M G_M → IsComparison A N hA F_N G_N →
    (NonUnitalModuleHom.restrictNondegeneratePart hA f).toAddMonoidHom.comp
        F_M.toAddMonoidHom = F_N.toAddMonoidHom.comp (tensorMap A f) ∧
    (tensorMap A f).comp G_M.toAddMonoidHom = G_N.toAddMonoidHom.comp
      (NonUnitalModuleHom.restrictNondegeneratePart hA f).toAddMonoidHom

end RegularTensorContraction

/-- The closed comparison target, with existence in each independent carrier
universe and both naturality equations for every original intertwiner. -/
def RegularTensorContractionTheorem : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A),
    (∀ (M : Type uM) [AddCommGroup M] [NonUnitalModule A M],
      RegularTensorContraction.ModuleComparison A M hA) ∧
    (∀ (N : Type uN) [AddCommGroup N] [NonUnitalModule A N],
      RegularTensorContraction.ModuleComparison A N hA) ∧
    (∀ (M : Type uM) [AddCommGroup M] [NonUnitalModule A M]
      (N : Type uN) [AddCommGroup N] [NonUnitalModule A N]
      (f : NonUnitalModuleHom A M N),
      RegularTensorContraction.ContractionNaturality A f ∧
      RegularTensorContraction.ComparisonNaturality A hA f)

end Langlands.Algebra
