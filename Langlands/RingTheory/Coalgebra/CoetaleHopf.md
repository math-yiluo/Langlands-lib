# Coétale subcoalgebras of Hopf algebras without primitive elements

Module `Langlands.RingTheory.Coalgebra.CoetaleHopf`, namespace `Langlands.CoetaleHopf`.
Author: Worker 894.

Internal helper module for the proof of
`Langlands.GroupScheme.MultiplicativeTypeCharacterizationStatement` (Milne,
*Algebraic Groups* (2017), Theorem 12.18). It states the coalgebra content of the
implications (b) ⇒ (c) and (c) ⇒ (d) of that theorem and of "diagonalizable over an
extension ⇒ no primitive elements". It introduces no definitions. Subcoalgebras are the
Library's `Langlands.Subcoalgebra` with their carrier coalgebra `instCoalgebra`; the
convolution dual is Mathlib's `WithConv (D →ₗ[k] k)`, a commutative ring when `D` is
cocommutative (`LinearMap.convCommRing`); scalar extensions `K ⊗[k] D` carry Mathlib's
`TensorProduct.instCoalgebra`.

## Declarations

Throughout `k` is a field.

- `isCocomm_subcoalgebra`: every subcoalgebra `D` of a cocommutative `k`-coalgebra `C` is
  cocommutative (`Coalgebra.IsCocomm k D`).
- `etale_of_formallyUnramified`: for a finite-dimensional cocommutative `k`-coalgebra `D`
  whose convolution dual is `Algebra.FormallyUnramified` over `k`, the dual is
  `Algebra.Etale` over `k`.
- `eq_zero_of_isPrimitiveElem_of_span_baseChange`: for a commutative `k`-bialgebra `A` and
  a field `K` over `k` such that the group-like elements span `K ⊗[k] A` over `K`, every
  primitive element of `A` is `0`.
- `etale_of_noPrimitive` (**(b) ⇒ (c), coalgebra form**): for a commutative Hopf algebra
  `A` over `k` all of whose primitive elements are `0`, and a subcoalgebra `D` of `A` that
  is finite-dimensional and cocommutative (instance arguments), the convolution dual
  `WithConv (D →ₗ[k] k)` is `Algebra.Etale` over `k`.
- `span_baseChange_of_etale`: for a separably closed field `Ks` over `k` and a
  finite-dimensional cocommutative `k`-coalgebra `D` with étale convolution dual, the
  group-like elements span `Ks ⊗[k] D` over `Ks`.
- `span_baseChange_of_coetale` (**(c) ⇒ (d), coalgebra form**): if every element of a
  `k`-coalgebra `C` lies in a subcoalgebra `D` with `FiniteDimensional k D`,
  `Coalgebra.IsCocomm k D` and `Algebra.Etale k (WithConv (D →ₗ[k] k))` (the exact form of
  condition (c) of the target statement), then for every separably closed field `Ks` over
  `k` the group-like elements span `Ks ⊗[k] C` over `Ks`.

## Proofs

**Cocommutativity of subcoalgebras.** Equality in `D ⊗ D` is tested after the injective
tensor-square inclusion `D.tensorSquareInclusion` (Library). The inclusion intertwines
the two swaps (tensor induction), sends `Δ_D x` to `Δ_C x` (`map_comul_subtype`), and
`Δ_C x` is swap-invariant (`Coalgebra.comm_comul`).

**Étale from formally unramified.** The dual is finite over `k`, so Mathlib's
`Algebra.FormallyEtale.of_formallyUnramified_of_field` makes it formally étale, and
`Algebra.FinitePresentation.of_finiteType` gives finite presentation.

**No primitive elements from a split scalar extension.** If `a` is primitive then so is
`1 ⊗ a` in `K ⊗[k] A`, by `TensorProduct.comul_tmul` and `Δ 1 = 1 ⊗ 1`. It lies in the
span of group-like elements, so it is `0` by
`CoetaleHopf.eq_zero_of_isPrimitiveElem_of_mem_span`; injectivity of
`Algebra.TensorProduct.includeRight` (from injectivity of `k → K`) gives `a = 0`.

**(b) ⇒ (c).** Let `k̄ = AlgebraicClosure k` and let
`j = Subcoalgebra.baseChangeMap k̄ D : k̄ ⊗[k] D → k̄ ⊗[k] A`, the Library's injective
coalgebra map. By `CoetaleHopf.eq_zero_of_isPrimitiveElem_baseChange`, the Hopf algebra
`k̄ ⊗[k] A` has no nonzero primitive element. If `a, b ∈ k̄ ⊗[k] D`, `a` is group-like and
`Δ b = a ⊗ b + b ⊗ a`, then `j a` is group-like and `Δ (j b) = j a ⊗ j b + j b ⊗ j a`, so
`j b = 0` by `CoetaleHopf.eq_zero_of_comul_eq_of_isGroupLikeElem` and `b = 0`. The
coalgebra `k̄ ⊗[k] D` is finite-dimensional and cocommutative (Mathlib instances), so
`CoetaleHopf.span_isGroupLikeElem_eq_top_of_skewPrimitive` shows it is spanned by
group-like elements. The library lemma
`Langlands.CoalgebraDescent.exists_finite_convolutionDualEquivPi` then gives a finite
`ι` and `WithConv ((k̄ ⊗ D) →ₗ[k̄] k̄) ≃ₐ[k̄] (ι → k̄)`. Composing with the library's
`Langlands.CoalgebraDescent.convolutionDualBaseChangeEquiv k D k̄` gives
`k̄ ⊗[k] WithConv (D →ₗ[k] k) ≃ₐ[k̄] (ι → k̄)`, so the library lemma
`formallyUnramified_of_tensorProduct_algEquiv_pi` makes the dual formally unramified over
`k`, and `etale_of_formallyUnramified` concludes.

**Spanning over a separably closed field.** Mathlib's base-change instance makes
`Ks ⊗[k] WithConv (D →ₗ[k] k)` étale over `Ks`, and
`Algebra.FormallyEtale.equivPiOfIsSepClosed` identifies it with functions on its prime
spectrum. Composing with the inverse of `convolutionDualBaseChangeEquiv k D Ks` gives a
`Ks`-algebra equivalence from `WithConv ((Ks ⊗ D) →ₗ[Ks] Ks)` to a product of copies of
`Ks`, and the library lemma `span_isGroupLikeElem_eq_top_of_algEquiv_pi` gives spanning.

**(c) ⇒ (d).** By tensor induction it suffices to treat `c ⊗ a`. Choose `D ∋ a` as in the
hypothesis. Then `c ⊗ ⟨a, _⟩` lies in the span of group-like elements of `Ks ⊗[k] D`
(`span_baseChange_of_etale`), and `Subcoalgebra.baseChangeMap Ks D`, a coalgebra map
sending `c ⊗ ⟨a, _⟩` to `c ⊗ a` (`baseChangeMap_tmul`), maps group-like elements to
group-like elements.

## Provenance

Internal derivation implementing Milne, *Algebraic Groups* (2017), registered source
`milne-2017-algebraic-groups`, Theorem 12.18 and its proof (printed pp. 237–238), the
definition of coétale coalgebras (printed p. 237), and A.57/A.59 (printed p. 579) for
étale algebras over a field. Milne passes to an algebraic closure in (b) ⇒ (c) and to the
separable closure in (c) ⇒ (d); the Lean proofs do the same, descending formal
unramifiedness along the faithfully flat extension `k → k̄` rather than invoking A.57.
