# Ideal-quotient tensor criterion for cokernel flatness

`Langlands.Algebra.IdealTensorCokernelFlatnessStatement` is a `Prop`-valued
definition. It is an **unproved** derived internal support interface: this
file states a proposition only, and supplies no proof and no accepted
mathematical dependency. It must not be used as a known result until an
exact proof of the complete, unchanged proposition is independently
accepted and published.

The Lean statement was drafted by Worker 666 for the exact proof task
`90c1db03-0049-445e-9845-423d7fb17ea0` (Stacks Lemma 10.99.1, target
`Langlands.Algebra.NoetherianLocalFiberInjectivityStatement`) and is
published here unchanged by Worker 281.

## Statement

For every commutative ring `R : Type u`, all `R`-modules `A : Type v` and
`B : Type w` (with `AddCommGroup` structures), and every `R`-linear map
`f : A →ₗ[R] B`, assume:

1. `B` is flat over `R` (`Module.Flat R B`);
2. `f` is injective;
3. for every ideal `I : Ideal R`, the actual tensor map
   `LinearMap.lTensor (R ⧸ I) f : (R ⧸ I) ⊗[R] A →ₗ[R] (R ⧸ I) ⊗[R] B`
   is injective, where `R ⧸ I` carries its quotient `R`-module structure.

Then the actual quotient module `B ⧸ LinearMap.range f` is flat over `R`.

The three universes `u`, `v`, `w` are independent. There are no locality,
Noetherian, finiteness, finite-presentation, flatness-of-`A`, or
nonzero-module hypotheses. The hypothesis and the conclusion use the actual
tensor map `LinearMap.lTensor` and the actual range quotient; no comparison
isomorphisms, Tor modules, or Tor-vanishing data are assumed.

## Provenance

This is a derived, internal interface, not a verbatim statement of the
literature. It isolates the final step of the proof of Stacks Project,
Commutative Algebra, Lemma 10.99.1 (tag 00ME), in the registered source
`stacks-algebra-flatness-criteria-2026-10-22` (content SHA256
`4bc1f2db6141508f6dad2132d4abc7963380cd71497ad20620c0e511b972a949`),
file `00MD.html`, Section 10.99 (Criteria for flatness), the paragraph of
the proof beginning "To show that `M/u(N)` is flat over `R`".

In that lemma `R → S` is a local homomorphism of local rings with `S`
Noetherian, `M` is a flat `R`-module, `N` is a finite `S`-module and
`u : N → M` is `R`-linear. The paragraph shows flatness of `M/u(N)` from
the short exact sequence `0 → N → M → M/u(N) → 0`, the flatness of `M`,
and injectivity of `N/IN → M/IM` for every ideal `I ⊂ R`, using the Tor
criterion for flatness over ideals (Lemma 10.75.8) and the long exact Tor
sequence (Lemma 10.75.2). Stacks deduces the injectivity of every
`N/IN → M/IM` from the first part of its proof; here it is an explicit
hypothesis. Writing `A` for `N`, `B` for `M` and `f` for `u`, and the
module `N/IN` as `(R ⧸ I) ⊗[R] N`, the statement keeps only the data of
that deduction. Once every `N/IN → M/IM` is assumed injective, the ring
`S`, the locality assumptions and the finiteness of `N` are no longer
needed, so they are omitted and `R` is an arbitrary commutative ring.
