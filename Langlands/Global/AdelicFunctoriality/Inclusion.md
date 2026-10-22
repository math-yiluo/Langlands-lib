# Extension-of-scalars inclusions of adeles, ideles and idele classes

Let `K : Type u` and `L : Type v` be number fields, in independent universes,
with an actual algebra `K → L`. This module constructs the maps
`A_K → A_L`, `J_K → J_L` and `C_K → C_L` that view an adele of `K` as an
adele of `L`. They go in the opposite direction to the norm maps of `Norm`,
and are different maps. All declarations are in
`Langlands.Global.AdelicFunctoriality`; the namespace and the file name were
agreed with Worker 50, who owns the norm side of this directory.

## Finite places

`liesOver_under` is an instance: every height-one prime `q` of `𝓞 L` lies over
its restriction `q.under (𝓞 K)`. This is Mathlib's `Ideal.over_under`.
`tendsto_under_cofinite` proves that restriction of primes is cofinite to
cofinite: the preimage of one prime of `K` lies in the range of the finite
type `FinitePlacesAbove L p` from `Norm`.

`finiteAdeleInclusion` is the ring homomorphism of Mathlib's finite adele
rings given by Mathlib's `RestrictedProduct.mapAlongRingHom` along
`HeightOneSpectrum.under`. Its coordinate at `q` is
`FiniteExtension.completionMap (q.under (𝓞 K)) q` applied to the coordinate of
`x` at `q.under (𝓞 K)`, as `finiteAdeleInclusion_apply` states by
reflexivity. `completionMap` is the published completed embedding of
`Extension`. Integral coordinates go to integral coordinates by
`completionMap_mem_integers_iff` from `CompletedRamification`. This gives the
restricted-product condition at every place. `continuous_finiteAdeleInclusion` is
Mathlib's `RestrictedProduct.mapAlong_continuous` with the published
continuity of each completed embedding. `finiteAdeleInclusion_diagonal` proves
that the principal finite adele of `x : K` goes to the principal finite adele
of the image of `x` in `L`.

## Infinite places and adeles

`adeleInclusion` is the product of the published `infiniteAdeleMap
(algebraMap K L)` from `Infinite` with `finiteAdeleInclusion`. At an infinite
place `p` of `L`, the coordinate is `infiniteCompletionMap (algebraMap K L) p`
applied to the coordinate of `x` at `p.comap (algebraMap K L)`
(`adeleInclusion_infinite_apply`). At a finite place `q` it is the finite formula
above (`adeleInclusion_finite_apply`). Both hold by reflexivity.
`continuous_adeleInclusion` combines the published continuity of
`infiniteAdeleMap` with that of the finite factor, and
`adeleInclusion_diagonal` combines the published diagonal formula
`infiniteAdeleMap_diagonal` with the finite one.

## Ideles and idele classes

`ideleInclusion : IdeleGroup (𝓞 K) K →ₜ* IdeleGroup (𝓞 L) L` is `Units.map` of
`adeleInclusion`, on Mathlib's actual idele group with its units topology.
Continuity is Mathlib's `Continuous.units_map`, which uses continuity of the
adele map on both the element and its inverse. `ideleInclusion_val` gives the
underlying adele. `ideleInclusion_diagonal` proves that the principal idele of
`x : Kˣ` goes to the principal idele of its image in `Lˣ`, so
`ideleInclusion_principal` proves that Mathlib's principal subgroup of `J_K`
maps into that of `J_L`.

`ideleClassInclusion : IdeleClassGroup (𝓞 K) K →ₜ* IdeleClassGroup (𝓞 L) L` is
the induced map of quotient groups (`QuotientGroup.map`). It is continuous for
the quotient topologies, by the universal property of the quotient map.
`ideleClassInclusion_mk` gives its value on the class of an idele by
reflexivity.

## Scope and provenance

The maps are constructed for any finite extension; no Galois hypothesis is
used. The module proves only the constructions and the formulas, continuity
and principal compatibility stated above. It proves neither injectivity, nor
closed image, nor Galois equivariance, nor the identification of `J_K` or
`C_K` with Galois invariants of `J_L` or `C_L`, although these hold in the
literature cited below.

The coordinate formula is André Weil, *Basic Number Theory*, second edition
(1973), Chapter IV section 1, Theorem 1 and its Corollary 1, printed
pp.62–63 (PDF pp.79–80). There `x = (x_v)` in `k_A` goes to `y = (y_w)` with
`y_w = x_{f(w)}`, where `f(w)` is the place below `w`, and `k_A` is
identified with a closed subring of `k'_A`. Registered original:
`weil-1973-basic-number-theory`, SHA256
`32fff78f8ccc5d6378907941e26746c34e20fc3adf5096508844cfe8a301e33b`. The
injections `J_k → J_K` and `C_k → C_K` are E. Artin and J. Tate, *Class Field
Theory* (2009), Preliminaries section 1, printed pp.1–2 (PDF pp.10–11).
Registered original: `artin-tate-2009-class-field-theory`, SHA256
`af7ba934904a3c10012e6fd326cea493ffb6200d885d97583277bb45f935c3dd`.
The Lean maps realize `y_w = x_{f(w)}` through the actual completed embeddings
`K_v → L_w` instead of an identification of `K_v` with a subfield of `L_w`.
