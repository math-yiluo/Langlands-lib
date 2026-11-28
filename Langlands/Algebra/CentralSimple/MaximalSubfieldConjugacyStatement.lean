import Mathlib.Algebra.Central.Defs
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! # Conjugacy and self-centralization of maximal subfields after scalar extension -/

universe u

open scoped TensorProduct

namespace Langlands.CentralSimple

/-- **Skolem–Noether for maximal subfields after scalar extension.** Let `E/F` be a finite
separable field extension, `B` a finite-dimensional central simple `E`-algebra that is an
`F`-algebra through `E`, `P/E` a finite separable field extension with
`[B : E] = [P : E]²`, and `K/F` a field extension. Any two injective `K`-algebra
homomorphisms `f, g : K ⊗[F] P → K ⊗[F] B` that are the identity on `E` are conjugate by a
unit of `K ⊗[F] B`, and every element of `K ⊗[F] B` commuting with the image of `f` lies in
that image. -/
def MaximalSubfieldConjugacyStatement : Prop :=
  ∀ (F E B P K : Type u) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    [Algebra.IsSeparable F E]
    [Ring B] [Algebra E B] [Algebra F B] [IsScalarTower F E B]
    [FiniteDimensional E B] [Algebra.IsCentral E B] [IsSimpleRing B]
    [Field P] [Algebra E P] [Algebra F P] [IsScalarTower F E P] [FiniteDimensional E P]
    [Algebra.IsSeparable E P] [Field K] [Algebra F K],
    Module.finrank E B = Module.finrank E P ^ 2 →
    ∀ f g : K ⊗[F] P →ₐ[K] K ⊗[F] B, Function.Injective f → Function.Injective g →
      (∀ e : E, f ((1 : K) ⊗ₜ[F] algebraMap E P e) = (1 : K) ⊗ₜ[F] algebraMap E B e) →
      (∀ e : E, g ((1 : K) ⊗ₜ[F] algebraMap E P e) = (1 : K) ⊗ₜ[F] algebraMap E B e) →
      (∃ u : (K ⊗[F] B)ˣ, ∀ y : K ⊗[F] P, g y = u * f y * ↑u⁻¹) ∧
        ∀ x : K ⊗[F] B, (∀ y : K ⊗[F] P, x * f y = f y * x) → x ∈ f.range

end Langlands.CentralSimple
