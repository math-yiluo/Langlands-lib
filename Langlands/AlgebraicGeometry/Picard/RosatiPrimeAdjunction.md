# Actual prime Weil adjunction for Rosati conjugation

This internal helper module derives two consequences of the existing actual Weil-pairing construction. It is a step toward the geometric Rosati trace argument; it does not assert trace invariance or positivity.

The scope is every scheme `S : Scheme.{u}` with `QuasiSeparatedSpace S`, an actual abelian scheme `A` over `S`, the existing Rosati construction prerequisites `P`, dual datum `W`, its exact additivity witness `hadd`, a relative finite-Weil transition witness `compatibility`, every test object `T : Over S`, and every prime `p`.

`IsPrimeWeilAdjoint P W compatibility T p lam a b` is the Prop-valued predicate that the actual prime Tate actions of `a` and `b` are adjoint for the actual Weil pairing pulled back along `lam`. It quantifies over both prime Tate vectors and asserts `e_lam(a x, y) = e_lam(x, b y)`. The predicate needs neither additivity of dualization nor a rational inverse or polarization assumption; these are inputs only to the constructions or results that use them.

`primeWeil_dual0` states that the actual prime rational Weil pairing satisfies
`e(a x, y) = e(x, dual0(a) y)` for every actual rational endomorphism `a`. The proof lifts both prime vectors through the published surjective full-to-prime extraction, applies `rationalWeilFunctoriality`, and extracts the prime component. It uses the actual constructed dual rather than an independently supplied adjoint.

`primeWeil_involution` additionally takes an actual map `lam : A ⟶ W.dual P` and the existing `HasRationalInverse P W lam` instance. It states the adjunction identity for the actual pairing pulled back along `lam`:
`e_lam(a x, y) = e_lam(x, involution(a) y)`, expressed by `IsPrimeWeilAdjoint`.
No polarization assumption is needed for this algebraic identity. The proof rewrites the defining rational conjugation using the actual inverse identity to obtain `lam ∘ involution(a) = dual0(a) ∘ lam`, applies the actual prime Tate functor, and substitutes this relation into `primeWeil_dual0`.

The declarations are internal derivations from the published Library pairing functoriality, extraction compatibility, and rational inverse laws. They introduce no new geometric hypotheses or source-dependent theorem assertion.
