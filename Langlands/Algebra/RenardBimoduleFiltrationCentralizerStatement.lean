import Mathlib.Algebra.Module.Bimodule
import Mathlib.LinearAlgebra.Quotient.Basic

/-! Renard VI.10.4, the Lemma on bimodule centralizers: for a filtered
bimodule over a commutative ring whose successive quotients admit no nonzero
bimodule morphisms between distinct ones, the centralizer of the bimodule is
the intersection of the centralizers of the quotients.

Following the convention of `Mathlib.Algebra.Module.Bimodule`, an `A`-bimodule
is a module over the enveloping ring `A ⊗[ℕ] Aᵐᵒᵖ`: `a` acts on the left as
`a ⊗ₜ 1` and on the right as `1 ⊗ₜ op a`. Sub-bimodules are submodules and
bimodule morphisms are linear maps over this ring. -/

open scoped TensorProduct

namespace Langlands.Algebra

universe u v

/-- VI.10.4, Lemma (bimodule centralizers). Let `A` be a commutative ring and
`M` a unital `A`-bimodule, viewed as an `A ⊗[ℕ] Aᵐᵒᵖ`-module. Let
`0 = M_{n+1} ⊆ M_n ⊆ ⋯ ⊆ M_1 ⊆ M_0 = M` be a filtration by sub-bimodules whose
successive quotients `Q_i = M_i / M_{i+1}` (`i = 0, …, n`) satisfy
`Hom(Q_i, Q_j) = 0` for `i ≠ j` (bimodule morphisms). Then
`𝒞_A(M) = ⋂_{i=0}^{n} 𝒞_A(Q_i)`, where `𝒞_A(N) = {a ∈ A | a x = x a ∀ x ∈ N}`.

The quotient `Q_i` is `↥(F i) ⧸ (F (i + 1)).comap (F i).subtype`; the additive
group structure of `↥(F i)` is supplied explicitly as `Submodule.addCommGroup`,
since instance search does not find it for submodules over `A ⊗[ℕ] Aᵐᵒᵖ`. -/
def RenardBimoduleFiltrationCentralizerStatement : Prop :=
  ∀ (A : Type u) [CommRing A] (M : Type v) [AddCommGroup M]
    [Module (A ⊗[ℕ] Aᵐᵒᵖ) M] (n : ℕ) (F : ℕ → Submodule (A ⊗[ℕ] Aᵐᵒᵖ) M),
    letI : ∀ i, AddCommGroup ↥(F i) := fun i => (F i).addCommGroup
    F 0 = ⊤ → F (n + 1) = ⊥ → (∀ i ≤ n, F (i + 1) ≤ F i) →
    (∀ i ≤ n, ∀ j ≤ n, i ≠ j →
      ∀ f : (↥(F i) ⧸ (F (i + 1)).comap (F i).subtype) →ₗ[A ⊗[ℕ] Aᵐᵒᵖ]
          (↥(F j) ⧸ (F (j + 1)).comap (F j).subtype), f = 0) →
    {a : A | ∀ x : M,
        (a ⊗ₜ[ℕ] (1 : Aᵐᵒᵖ)) • x = ((1 : A) ⊗ₜ[ℕ] MulOpposite.op a) • x} =
      ⋂ i ∈ Finset.range (n + 1),
        {a : A | ∀ x : ↥(F i) ⧸ (F (i + 1)).comap (F i).subtype,
          (a ⊗ₜ[ℕ] (1 : Aᵐᵒᵖ)) • x = ((1 : A) ⊗ₜ[ℕ] MulOpposite.op a) • x}

end Langlands.Algebra
