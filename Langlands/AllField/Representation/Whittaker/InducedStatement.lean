import Langlands.Representation.Whittaker.InducedStatement
import Langlands.AllField.Group.GL.PadicSupplement
/-!
# Whittaker type of representations induced from block parabolics

Proposition targets for JPSS (1983), Section 2.3, printed pages 386-387,
including the Proposition attributed to Rodier. Induction uses the actual
upper block parabolic, the external tensor product of the block
representations and the published right-translation construction; the paired
Markdown explains the equivalence with the normalized lower-parabolic
induction of the source. Neither proposition is asserted to be proved.
-/

namespace Langlands.AllField

open scoped BigOperators

universe uF uV

/-- JPSS (2.3): induction of admissible representations of finite type from an
actual upper block parabolic is of finite type. -/
def InducedFiniteTypeStatement : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F],
    ∀ (n : ℕ) (B : GeneralLinear.BlockShape (n + 1)),
      letI := (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup (n + 1)
      ∀ (V : Fin B.length → Type uV) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
        (π : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (V i)),
        (∀ i, IsAdmissible (π i)) →
        (∀ i, Module.Finite (MonoidAlgebra ℂ (GeneralLinear (B.size i) F))
          (π i).asModule) →
        Module.Finite (MonoidAlgebra ℂ (GeneralLinear (n + 1) F))
          (Induction.smoothInduced (B.parabolic F)
            ((FiniteTensor.external π).comp (B.leviProjection F))).asModule

/-- JPSS (2.3), Proposition (Rodier): for admissible block representations of
finite type, the induced representation has a one-dimensional space of
Whittaker functionals precisely when every block representation has one.

`unipotent d g` and `θ d g` are the actual upper-unitriangular condition and the
standard character `∏ ψ(g_{a,a+1})` on `GL_d(F)`, written without index
arithmetic. -/
def InducedWhittakerTypeStatement : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F],
    ∀ (n : ℕ) (B : GeneralLinear.BlockShape (n + 1)),
      letI := (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup (n + 1)
      ∀ (V : Fin B.length → Type uV) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
        (π : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (V i))
        (ψ : AddChar F ℂ),
        Continuous ψ → ψ ≠ 1 → (∀ x, ‖ψ x‖ = 1) →
        (∀ i, IsAdmissible (π i)) →
        (∀ i, Module.Finite (MonoidAlgebra ℂ (GeneralLinear (B.size i) F))
          (π i).asModule) →
        let unipotent := fun (d : ℕ) (g : GeneralLinear d F) =>
          (∀ a b, b < a → g.val a b = 0) ∧ ∀ a, g.val a a = 1
        let θ := fun (d : ℕ) (g : GeneralLinear d F) =>
          ∏ a : Fin d, ∏ b : Fin d, if b.val = a.val + 1 then ψ (g.val a b) else 1
        let induced := Induction.smoothInduced (B.parabolic F)
          ((FiniteTensor.external π).comp (B.leviProjection F))
        let inducedEquivariant := fun ℓ : Module.Dual ℂ
            (Induction.SmoothFunctions (B.parabolic F)
              ((FiniteTensor.external π).comp (B.leviProjection F))) =>
          ∀ g, unipotent (n + 1) g → ∀ f, ℓ (induced g f) = θ (n + 1) g * ℓ f
        let blockEquivariant := fun (i : Fin B.length) (ℓ : Module.Dual ℂ (V i)) =>
          ∀ g, unipotent (B.size i) g → ∀ v, ℓ (π i g v) = θ (B.size i) g * ℓ v
        (∃ ℓ, ℓ ≠ 0 ∧ inducedEquivariant ℓ ∧
          ∀ ℓ', inducedEquivariant ℓ' → ∃ c : ℂ, ℓ' = c • ℓ) ↔
        ∀ i, ∃ ℓ : Module.Dual ℂ (V i), ℓ ≠ 0 ∧ blockEquivariant i ℓ ∧
          ∀ ℓ', blockEquivariant i ℓ' → ∃ c : ℂ, ℓ' = c • ℓ

end Langlands.AllField
