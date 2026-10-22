import Langlands.Group.GL.Blocks
import Langlands.Group.GL.Padic
import Langlands.Representation.Induction.Definitions
import Langlands.Representation.Tensor.Finite
import Mathlib.Algebra.Group.AddChar
import Mathlib.Analysis.Complex.Basic

/-!
# Whittaker type of representations induced from block parabolics

Proposition targets for JPSS (1983), Section 2.3, printed pages 386-387,
including the Proposition attributed to Rodier. Induction uses the actual
upper block parabolic, the external tensor product of the block
representations and the published right-translation construction; the paired
Markdown explains the equivalence with the normalized lower-parabolic
induction of the source. Neither proposition is asserted to be proved.
-/

namespace Langlands

open scoped BigOperators

universe uF uV

/-- JPSS (2.3): induction of admissible representations of finite type from an
actual upper block parabolic is of finite type. -/
def InducedFiniteTypeStatement : Prop :=
  ∀ (p : ℕ) (_hp : Fact p.Prime) (F : PadicField.{uF} p),
    letI := F.canonicalTopologicalData.topology
    ∀ (n : ℕ) (B : GeneralLinear.BlockShape (n + 1)),
      letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (n + 1)
      ∀ (V : Fin B.length → Type uV) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
        (π : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i)),
        (∀ i, IsAdmissible (π i)) →
        (∀ i, Module.Finite (MonoidAlgebra ℂ (GeneralLinear (B.size i) F.Carrier))
          (π i).asModule) →
        Module.Finite (MonoidAlgebra ℂ (GeneralLinear (n + 1) F.Carrier))
          (Induction.smoothInduced (B.parabolic F.Carrier)
            ((FiniteTensor.external π).comp (B.leviProjection F.Carrier))).asModule

/-- JPSS (2.3), Proposition (Rodier): for admissible block representations of
finite type, the induced representation has a one-dimensional space of
Whittaker functionals precisely when every block representation has one.

`unipotent d g` and `θ d g` are the actual upper-unitriangular condition and the
standard character `∏ ψ(g_{a,a+1})` on `GL_d(F)`, written without index
arithmetic. -/
def InducedWhittakerTypeStatement : Prop :=
  ∀ (p : ℕ) (_hp : Fact p.Prime) (F : PadicField.{uF} p),
    letI := F.canonicalTopologicalData.topology
    ∀ (n : ℕ) (B : GeneralLinear.BlockShape (n + 1)),
      letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (n + 1)
      ∀ (V : Fin B.length → Type uV) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
        (π : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i))
        (ψ : AddChar F.Carrier ℂ),
        Continuous ψ → ψ ≠ 1 → (∀ x, ‖ψ x‖ = 1) →
        (∀ i, IsAdmissible (π i)) →
        (∀ i, Module.Finite (MonoidAlgebra ℂ (GeneralLinear (B.size i) F.Carrier))
          (π i).asModule) →
        let unipotent := fun (d : ℕ) (g : GeneralLinear d F.Carrier) =>
          (∀ a b, b < a → g.val a b = 0) ∧ ∀ a, g.val a a = 1
        let θ := fun (d : ℕ) (g : GeneralLinear d F.Carrier) =>
          ∏ a : Fin d, ∏ b : Fin d, if b.val = a.val + 1 then ψ (g.val a b) else 1
        let induced := Induction.smoothInduced (B.parabolic F.Carrier)
          ((FiniteTensor.external π).comp (B.leviProjection F.Carrier))
        let inducedEquivariant := fun ℓ : Module.Dual ℂ
            (Induction.SmoothFunctions (B.parabolic F.Carrier)
              ((FiniteTensor.external π).comp (B.leviProjection F.Carrier))) =>
          ∀ g, unipotent (n + 1) g → ∀ f, ℓ (induced g f) = θ (n + 1) g * ℓ f
        let blockEquivariant := fun (i : Fin B.length) (ℓ : Module.Dual ℂ (V i)) =>
          ∀ g, unipotent (B.size i) g → ∀ v, ℓ (π i g v) = θ (B.size i) g * ℓ v
        (∃ ℓ, ℓ ≠ 0 ∧ inducedEquivariant ℓ ∧
          ∀ ℓ', inducedEquivariant ℓ' → ∃ c : ℂ, ℓ' = c • ℓ) ↔
        ∀ i, ∃ ℓ : Module.Dual ℂ (V i), ℓ ≠ 0 ∧ blockEquivariant i ℓ ∧
          ∀ ℓ', blockEquivariant i ℓ' → ∃ c : ℂ, ℓ' = c • ℓ

/-- Both induced Whittaker-type targets, with the same independent universes. -/
def InducedWhittakerPrerequisitesStatement : Prop :=
  InducedFiniteTypeStatement.{uF, uV} ∧ InducedWhittakerTypeStatement.{uF, uV}

end Langlands
