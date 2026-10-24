# Lifting injectivity from a local residue fibre

`Langlands.Algebra.LocalFiberInjectivityStatement` states Stacks Project,
Commutative Algebra, Lemma 10.128.4, tag
[046Y](https://stacks.math.columbia.edu/tag/046Y). This is a proposition
definition, not a proof.

Let `R → S` be a local homomorphism of commutative local rings, let `m`
be the maximal ideal of `R`, and let `f : M →ₗ[S] N`. If `S` is
essentially finitely presented over `R`, both modules are finitely
presented over `S`, `N` is flat over `R`, and the induced map
`M/mM → N/mN` is injective, then `f` is injective and its cokernel
`N/f(M)` is flat over `R`.

## Exact Lean objects

The instances `Algebra R S` and `IsLocalHom (algebraMap R S)` express the
local ring map. Each module has its `S`-action and a compatible
`R`-action, expressed by `IsScalarTower R S M` and
`IsScalarTower R S N`. These are the restricted actions in the source.
The existing `EssFinitePresentation R S` predicate uses a localization
of a finite-variable polynomial quotient by a finitely generated ideal.
The two `Module.FinitePresentation` hypotheses concern `S`, whereas
the flatness hypothesis concerns only `N` over `R`.

Write `k = IsLocalRing.ResidueField R = R/m`.
`f.restrictScalars R` is the same map regarded as `R`-linear. Its
base change
`LinearMap.lTensor k (f.restrictScalars R)` is the actual map
`k ⊗[R] M → k ⊗[R] N`, sending `a ⊗ x` to `a ⊗ f(x)`.
The standard quotient-tensor identifications
`k ⊗[R] M ≃ M/mM` and `k ⊗[R] N ≃ N/mN` carry it to the source's
induced quotient map. Thus the stated injectivity is exactly the fourth
source hypothesis. No flatness hypothesis is needed for these
quotient-tensor identifications.

The cokernel in the conclusion is the actual quotient
`N ⧸ LinearMap.range (f.restrictScalars R)`. The range here is an
`R`-submodule, with underlying set `{f(x) | x ∈ M}`.
It is the restriction of the range as an `S`-submodule, so this quotient
is precisely `N/f(M)` with its induced `R`-action. Using the restricted
range makes that action explicit without introducing an abstract
cokernel or an extra comparison assumption.

The four universes for `R`, `S`, `M`, and `N` are independent.
There is no Noetherian, nonzero-module, flatness-of-`M`, field, dimension,
or universe-equality assumption.

## Proof boundary and provenance

This statement is one of the direct prerequisites used by the source
proof of tag 05UV. The source proves 046Y by approximation of the local
ring map and the two finitely presented modules, descent of flatness,
eventual injectivity on the residue fibre, and the Noetherian lifting
criterion. None of those proofs is supplied or assumed by this definition.

The source is `stacks-algebra-flatness-criteria-2026-10-22`, content SHA256
`4bc1f2db6141508f6dad2132d4abc7963380cd71497ad20620c0e511b972a949`.
The exact locator is `046Y.html`, Lemma 10.128.4, in
`literature/Stacks Project - Algebra flatness criteria and essentially finite presentation (HTML snapshot 2026-10-22)/`.
The explicit scalar towers, tensor form of the fibre map, and
restricted-range quotient are internal presentations of the displayed
source statement; the file claims no separate formal comparison theorem.
