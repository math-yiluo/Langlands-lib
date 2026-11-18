import Langlands.Representation.Archimedean.ComplexGenericLargeProof
import Langlands.Representation.Archimedean.ComplexLargePrincipalSeriesProof

/-!
# Generic standard modules of `GL_n(ℂ)` are irreducible

`complexGenericStandardInjective` proves `ComplexGenericStandardInjectiveStatement`. Let `A` be
a surjective intertwining map from the `U(n)`-finite functions of a Langlands-ordered standard
module onto an irreducible admissible generic `(𝔤𝔩_n(ℂ), U(n))`-module. Then `A` is injective.

The proof combines two proved Library theorems:

* `complexGenericLarge` (Kostant 1978, Theorem 3.9; Matumoto 1987, Corollary 5): the target
  module is large;
* `ComplexLargePrincipalSeriesProof.largeLanglandsQuotientInjective` (Vogan 1978, Theorem 6.2,
  proof of (a) ⇒ (f)):
  a nonzero intertwining map from a Langlands-ordered standard module into an irreducible
  admissible large module is injective.

A surjection onto an irreducible module is nonzero, because an irreducible module is nonzero.
-/

set_option autoImplicit false

universe uV

namespace Langlands.Archimedean

/-- **Generic standard modules are irreducible** (Vogan 1978; Kostant 1978; Matumoto 1987):
for `n` complex characters `ds` in the Langlands order, every surjective intertwining map from
the `U(n)`-finite functions of their standard module onto an irreducible admissible generic
`(𝔤𝔩_n(ℂ), U(n))`-module is injective. -/
theorem complexGenericStandardInjective : ComplexGenericStandardInjectiveStatement.{uV} := by
  intro n V _ _ ρ π ds A hgk hirr hadm hgen hlen hord hsurj hA
  -- Kostant's theorem: the generic module `(ρ, π)` is large.
  have hlarge : IsComplexLargeGKModule n π := complexGenericLarge n V ρ π hgk hirr hadm hgen
  -- An irreducible module is nontrivial, so a surjection onto it is nonzero.
  have : Nontrivial V := hirr.1
  have hA0 : A ≠ 0 := by
    intro h
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    obtain ⟨f, rfl⟩ := hsurj v
    exact hv (by rw [h, LinearMap.zero_apply])
  -- Vogan's injectivity theorem for large modules.
  exact ComplexLargePrincipalSeriesProof.largeLanglandsQuotientInjective n V ρ π ds A hgk hirr
    hadm hlarge hlen hord hA0 hA

end Langlands.Archimedean
