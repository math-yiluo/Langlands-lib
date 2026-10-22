import Langlands.WeilDeligne.FrobeniusStatements
import Langlands.WeilDeligne.SumsTensor
import Langlands.WeilDeligne.Dual
import Langlands.WeilDeligne.Twist
import Langlands.WeilDeligne.Kernels

/-!
# Operation laws for actual Weil–Deligne pairs

These are proposition definitions. The operation constructors and their intrinsic
certificates belong to the companion framework; no correction or decomposition
theorem is an input. Semisimplification is the existing existential relation.
-/

noncomputable section

namespace Langlands.WeilDeligneRepresentation.OperationLaws

universe uG uV uW uX uY

open scoped TensorProduct
open Frobenius

variable {G : Type uG} [Group G] {ν : G →* ℂˣ}

/-- The actual action and monodromy of each operation, including the dual sign. -/
def Formulas : Prop :=
  ∀ (A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν)
    (B : WeilDeligneRepresentation.{0, uG, uW} ℂ G ν),
    (∀ x : A × B, (sum A B).monodromy x = (A.monodromy x.1, B.monodromy x.2)) ∧
    (∀ g (x : A × B), (sum A B).representation g x =
      (A.representation g x.1, B.representation g x.2)) ∧
    (∀ (x : A) (y : B), (tensor A B).monodromy (x ⊗ₜ[ℂ] y) =
      A.monodromy x ⊗ₜ[ℂ] y + x ⊗ₜ[ℂ] B.monodromy y) ∧
    (∀ g (x : A) (y : B), (tensor A B).representation g (x ⊗ₜ[ℂ] y) =
      A.representation g x ⊗ₜ[ℂ] B.representation g y) ∧
    (∀ (l : Module.Dual ℂ A) (x : A),
      Module.Dual.eval ℂ A x ((dual A).monodromy l) = -l (A.monodromy x)) ∧
    (∀ g (l : Module.Dual ℂ A) (x : A),
      Module.Dual.eval ℂ A x ((dual A).representation g l) =
        l (A.representation g⁻¹ x)) ∧
    ∀ χ : G →* ℂˣ,
      (twist χ A).monodromy = A.monodromy ∧
      ∀ g, (twist χ A).representation g = (χ g : ℂ) • A.representation g

/-- Operation maps use the product, tensor, transpose and unchanged linear maps. -/
def MapFormulas : Prop :=
  ∀ (A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν)
    (B : WeilDeligneRepresentation.{0, uG, uW} ℂ G ν)
    (C : WeilDeligneRepresentation.{0, uG, uX} ℂ G ν)
    (D : WeilDeligneRepresentation.{0, uG, uY} ℂ G ν)
    (f : Hom A C) (g : Hom B D),
    (sumMap f g).intertwiner.toLinearMap =
      f.intertwiner.toLinearMap.prodMap g.intertwiner.toLinearMap ∧
    (tensorMap f g).intertwiner.toLinearMap =
      TensorProduct.map f.intertwiner.toLinearMap g.intertwiner.toLinearMap ∧
    (dualMap f).intertwiner.toLinearMap = f.intertwiner.toLinearMap.dualMap ∧
    ∀ χ : G →* ℂˣ,
      (twistMap χ f).intertwiner.toLinearMap = f.intertwiner.toLinearMap

/-- Identity and composition laws retain the reversed order for the dual. -/
def FunctorLaws : Prop :=
  (∀ (A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν)
      (B : WeilDeligneRepresentation.{0, uG, uW} ℂ G ν),
    sumMap (Hom.id A) (Hom.id B) = Hom.id (sum A B) ∧
    tensorMap (Hom.id A) (Hom.id B) = Hom.id (tensor A B) ∧
    dualMap (Hom.id A) = Hom.id (dual A) ∧
    ∀ χ : G →* ℂˣ, twistMap χ (Hom.id A) = Hom.id (twist χ A)) ∧
  ∀ (A C E : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν)
    (B D F : WeilDeligneRepresentation.{0, uG, uW} ℂ G ν)
    (f : Hom A C) (f' : Hom C E) (g : Hom B D) (g' : Hom D F),
    sumMap (Hom.comp f' f) (Hom.comp g' g) =
      Hom.comp (sumMap f' g') (sumMap f g) ∧
    tensorMap (Hom.comp f' f) (Hom.comp g' g) =
      Hom.comp (tensorMap f' g') (tensorMap f g) ∧
    dualMap (Hom.comp f' f) = Hom.comp (dualMap f) (dualMap f') ∧
    ∀ χ : G →* ℂˣ,
      twistMap χ (Hom.comp f' f) = Hom.comp (twistMap χ f') (twistMap χ f)

/-- Genuine isomorphism is preserved, also across different carrier universes. -/
def IsomorphismCompatibility : Prop :=
  ∀ (A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν)
    (B : WeilDeligneRepresentation.{0, uG, uW} ℂ G ν)
    (C : WeilDeligneRepresentation.{0, uG, uX} ℂ G ν)
    (D : WeilDeligneRepresentation.{0, uG, uY} ℂ G ν),
    Equiv A C → Equiv B D →
    Nonempty (Equiv (sum A B) (sum C D)) ∧
    Nonempty (Equiv (tensor A B) (tensor C D)) ∧
    Nonempty (Equiv (dual C) (dual A)) ∧
    ∀ χ : G →* ℂˣ, Nonempty (Equiv (twist χ A) (twist χ C))

/-- Zero monodromy commutes with the actual operations through identity carriers. -/
def ZeroMonodromyCompatibility : Prop :=
  ∀ (A : FiniteRepresentation.{0, uG, uV} ℂ G)
    (B : FiniteRepresentation.{0, uG, uW} ℂ G),
    (∃ e : Equiv (zeroMonodromy ν (FiniteRepresentation.sum A B))
        (sum (zeroMonodromy ν A) (zeroMonodromy ν B)),
      ∀ x, e.representationEquiv x = x) ∧
    (∃ e : Equiv (zeroMonodromy ν (FiniteRepresentation.tensor A B))
        (tensor (zeroMonodromy ν A) (zeroMonodromy ν B)),
      ∀ x, e.representationEquiv x = x) ∧
    (∃ e : Equiv (zeroMonodromy ν (FiniteRepresentation.dual A))
        (dual (zeroMonodromy ν A)),
      ∀ x, e.representationEquiv x = x) ∧
    ∀ χ : G →* ℂˣ,
      ∃ e : Equiv (zeroMonodromy ν (FiniteRepresentation.twist χ A))
          (twist χ (zeroMonodromy ν A)),
        ∀ x, e.representationEquiv x = x

/-- Duality distributes through sum and tensor with the usual evaluation maps.
The tensor equivalence is oriented from the tensor of duals to the dual of tensor. -/
def DualCompatibility : Prop :=
  ∀ (A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν)
    (B : WeilDeligneRepresentation.{0, uG, uW} ℂ G ν),
    (∃ e : Equiv (dual (sum A B)) (sum (dual A) (dual B)),
      (∀ (l : Module.Dual ℂ (A × B)) (x : A),
        Module.Dual.eval ℂ A x (e.representationEquiv l).1 = l (x, 0)) ∧
      (∀ (l : Module.Dual ℂ (A × B)) (y : B),
        Module.Dual.eval ℂ B y (e.representationEquiv l).2 = l (0, y))) ∧
    (∃ e : Equiv (tensor (dual A) (dual B)) (dual (tensor A B)),
      ∀ (l : Module.Dual ℂ A) (m : Module.Dual ℂ B) (x : A) (y : B),
        Module.Dual.eval ℂ (A ⊗[ℂ] B) (x ⊗ₜ[ℂ] y)
          (e.representationEquiv (l ⊗ₜ[ℂ] m)) = l x * m y) ∧
    ∃ e : Equiv A (dual (dual A)),
      ∀ (x : A) (l : Module.Dual ℂ A),
        Module.Dual.eval ℂ (Module.Dual ℂ A) l (e.representationEquiv x) = l x

/-- Character laws use multiplication on tensor factors and inversion on duals. -/
def TwistCompatibility : Prop :=
  ∀ (A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν)
    (B : WeilDeligneRepresentation.{0, uG, uW} ℂ G ν) (χ ψ : G →* ℂˣ),
    Nonempty (Equiv (twist χ (sum A B)) (sum (twist χ A) (twist χ B))) ∧
    Nonempty (Equiv (twist (χ * ψ) (tensor A B)) (tensor (twist χ A) (twist ψ B))) ∧
    Nonempty (Equiv (dual (twist χ A)) (twist χ⁻¹ (dual A))) ∧
    Nonempty (Equiv (twist χ (twist ψ A)) (twist (χ * ψ) A)) ∧
    Nonempty (Equiv (twist 1 A) A)

/-- Corrections transform by product, tensor, inverse transpose, and identity.
These are preservation implications for actual candidates, not chosen outputs. -/
def CorrectionCompatibility : Prop :=
  ∀ (degree : G →* Multiplicative ℤ)
    (A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν)
    (B : WeilDeligneRepresentation.{0, uG, uW} ℂ G ν)
    (u : A ≃ₗ[ℂ] A) (v : B ≃ₗ[ℂ] B),
    IsCorrection degree A u → IsCorrection degree B v →
    IsCorrection degree (sum A B) (u.prodCongr v) ∧
    IsCorrection degree (tensor A B) (TensorProduct.congr u v) ∧
    IsCorrection degree (dual A) u.symm.dualMap ∧
    ∀ χ : G →* ℂˣ, IsCorrection degree (twist χ A) u

/-- The same explicit formulas for the unipotent parts at a selected Frobenius. -/
def CorrectionAtCompatibility : Prop :=
  ∀ (Phi : G)
    (A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν)
    (B : WeilDeligneRepresentation.{0, uG, uW} ℂ G ν)
    (u : A ≃ₗ[ℂ] A) (v : B ≃ₗ[ℂ] B),
    IsCorrectionAt A Phi u → IsCorrectionAt B Phi v →
    IsCorrectionAt (sum A B) Phi (u.prodCongr v) ∧
    IsCorrectionAt (tensor A B) Phi (TensorProduct.congr u v) ∧
    IsCorrectionAt (dual A) Phi u.symm.dualMap ∧
    ∀ χ : G →* ℂˣ, IsCorrectionAt (twist χ A) Phi u

/-- The actual operations preserve the existential semisimplification relation.
No existence hypothesis for a canonical functor and no block classification occurs. -/
def SemisimplificationCompatibility : Prop :=
  ∀ (degree : G →* Multiplicative ℤ)
    (A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν)
    (B : WeilDeligneRepresentation.{0, uG, uW} ℂ G ν)
    (C : WeilDeligneRepresentation.{0, uG, uX} ℂ G ν)
    (D : WeilDeligneRepresentation.{0, uG, uY} ℂ G ν),
    IsSemisimplification degree A C → IsSemisimplification degree B D →
    IsSemisimplification degree (sum A B) (sum C D) ∧
    IsSemisimplification degree (tensor A B) (tensor C D) ∧
    IsSemisimplification degree (dual A) (dual C) ∧
    ∀ χ : G →* ℂˣ,
      IsSemisimplification degree (twist χ A) (twist χ C)

/-- Frobenius semisimplicity is closed under the operations; it still allows N nonzero. -/
def FrobeniusSemisimplicityCompatibility : Prop :=
  ∀ (degree : G →* Multiplicative ℤ)
    (A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν)
    (B : WeilDeligneRepresentation.{0, uG, uW} ℂ G ν),
    ((sum A B).IsFrobeniusSemisimple degree ↔
      A.IsFrobeniusSemisimple degree ∧ B.IsFrobeniusSemisimple degree) ∧
    (A.IsFrobeniusSemisimple degree → B.IsFrobeniusSemisimple degree →
      (tensor A B).IsFrobeniusSemisimple degree) ∧
    ((dual A).IsFrobeniusSemisimple degree ↔ A.IsFrobeniusSemisimple degree) ∧
    ∀ χ : G →* ℂˣ,
      (twist χ A).IsFrobeniusSemisimple degree ↔ A.IsFrobeniusSemisimple degree

/-- Restriction of the actual correction to the actual kernel representation. -/
def KernelCorrection : Prop :=
  ∀ (degree : G →* Multiplicative ℤ)
    (A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν) (u : A ≃ₗ[ℂ] A),
    IsCorrection degree A u →
    ∃ v : A.kernelRepresentation ≃ₗ[ℂ] A.kernelRepresentation,
      A.monodromy.ker.subtype.comp v.toLinearMap =
        u.toLinearMap.comp A.monodromy.ker.subtype ∧
      IsCorrection degree (zeroMonodromy ν A.kernelRepresentation) v

/-- The kernel *action*, not just its dimension, is semisimplified. -/
def KernelSemisimplification : Prop :=
  ∀ (degree : G →* Multiplicative ℤ)
    (A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν)
    (B : WeilDeligneRepresentation.{0, uG, uW} ℂ G ν),
    IsSemisimplification degree A B →
    IsSemisimplification degree (zeroMonodromy ν A.kernelRepresentation)
      (zeroMonodromy ν B.kernelRepresentation)

/-- The finite-inertia premise on a twisting character is explicit.
No finiteness of its whole image or unitarity is demanded. -/
def FiniteInertiaPreservation : Prop :=
  ∀ (I : Subgroup G)
    (A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν)
    (B : WeilDeligneRepresentation.{0, uG, uW} ℂ G ν),
    A.toFiniteRepresentation.HasFiniteInertiaImage I →
    B.toFiniteRepresentation.HasFiniteInertiaImage I →
    (sum A B).toFiniteRepresentation.HasFiniteInertiaImage I ∧
    (tensor A B).toFiniteRepresentation.HasFiniteInertiaImage I ∧
    (dual A).toFiniteRepresentation.HasFiniteInertiaImage I ∧
    A.kernelRepresentation.HasFiniteInertiaImage I ∧
    ∀ χ : G →* ℂˣ, (Set.range (χ.comp I.subtype)).Finite →
      (twist χ A).toFiniteRepresentation.HasFiniteInertiaImage I

/-- Algebraic laws for the existing operation constructors and correction relation. -/
def AlgebraicFamily : Prop :=
  Formulas.{uG, uV, uW} (ν := ν) ∧
  MapFormulas.{uG, uV, uW, uX, uY} (ν := ν) ∧
  FunctorLaws.{uG, uV, uW} (ν := ν) ∧
  IsomorphismCompatibility.{uG, uV, uW, uX, uY} (ν := ν) ∧
  ZeroMonodromyCompatibility.{uG, uV, uW} (ν := ν) ∧
  DualCompatibility.{uG, uV, uW} (ν := ν) ∧
  TwistCompatibility.{uG, uV, uW} (ν := ν) ∧
  CorrectionCompatibility.{uG, uV, uW} (ν := ν) ∧
  CorrectionAtCompatibility.{uG, uV, uW} (ν := ν) ∧
  SemisimplificationCompatibility.{uG, uV, uW, uX, uY} (ν := ν) ∧
  FrobeniusSemisimplicityCompatibility.{uG, uV, uW} (ν := ν) ∧
  KernelCorrection.{uG, uV} (ν := ν) ∧
  KernelSemisimplification.{uG, uV, uW} (ν := ν) ∧
  FiniteInertiaPreservation.{uG, uV, uW} (ν := ν)

section Topology

variable [TopologicalSpace G]

/-- Openness of the inertia kernel is preserved separately from continuity.
The topological-group structure is an explicit binder, so it stays in the type. -/
def ParameterPreservation [IsTopologicalGroup G] : Prop :=
  ∀ (I : Subgroup G)
    (A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν)
    (B : WeilDeligneRepresentation.{0, uG, uW} ℂ G ν),
    IsParameter I A → IsParameter I B →
    IsParameter I (sum A B) ∧ IsParameter I (tensor A B) ∧
    IsParameter I (dual A) ∧ A.kernelRepresentation.HasOpenInertiaKernel I ∧
    ∀ χ : G →* ℂˣ, IsOpen ((χ.comp I.subtype).ker : Set I) →
      IsParameter I (twist χ A)

/-- Usual finite-dimensional complex continuity is preserved with a continuous
twisting character. This does not infer continuity from open inertia kernel. -/
def ContinuityPreservation [IsTopologicalGroup G] : Prop :=
  ∀ (A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν)
    (B : WeilDeligneRepresentation.{0, uG, uW} ℂ G ν),
    A.IsContinuous → B.IsContinuous →
    (sum A B).IsContinuous ∧ (tensor A B).IsContinuous ∧
    (dual A).IsContinuous ∧ A.kernelRepresentation.IsContinuous ∧
    ∀ χ : G →* ℂˣ, Continuous χ → (twist χ A).IsContinuous

/-- Whole operation statement target, including the distinct topology conditions. -/
def Statement [IsTopologicalGroup G] : Prop :=
  AlgebraicFamily.{uG, uV, uW, uX, uY} (ν := ν) ∧
  ParameterPreservation.{uG, uV, uW} (ν := ν) ∧
  ContinuityPreservation.{uG, uV, uW} (ν := ν)

end Topology

end Langlands.WeilDeligneRepresentation.OperationLaws
