# Direct limits of free modules over quotient group algebras

Author: Worker 61. Built on the Library modules
`Langlands.Representation.Induction.InvariantRestriction`
(`Induction.invariantsToCoinvariants`,
`Induction.bijective_invariantsToCoinvariants_of_equiv`,
`Induction.bijective_invariantsToCoinvariants_permutation`,
`Induction.isUnit_index_subgroupOf`; Worker 61),
`Langlands.Representation.Induction.PermutationDual`
(`Induction.permutation_asModule_free`; Worker 61),
`Langlands.Representation.Smooth.Definitions` (`Langlands.IsSmooth`,
`Langlands.fixedVectors`),
`Langlands.Cohomology.DivisibleSystem.FreeTorsionProjective`
(`FreeOverPowQuotient`, `torsionQuotientRepresentation`, `torsionQuotientRep`,
`isTorsionBySet_of_powSMul_eq_zero`, `powSMul_hom_apply`,
`powTorsionProjective_of_freeOverPowQuotient`; Worker 61) and
`Langlands.Cohomology.DivisibleSystem.InvariantHomSurjective` (Worker 61).
Through these imports it also uses
`Langlands.Representation.Induction.PermutationInvariants`
(`Induction.invariantsEquivOfEquiv`, `Induction.permutationInvariantsEquiv`,
`Induction.asModuleLinearEquiv`,
`Induction.finiteIndex_subgroupOf_of_isCompact`; Worker 61),
`Langlands.Representation.Induction.PermutationModule`
(`Induction.permutation`, `Induction.permutation_apply`; Worker 61),
`Langlands.Cohomology.DivisibleSystem.InvariantHomSystem`
(`invariantsHomSystemIso`; Worker 61),
`Langlands.Cohomology.DivisibleSystem.HomSystem` (`homSystem`,
`towerHomEval`; Worker 61), `Langlands.Cohomology.DivisibleSystem.HomSurjective`
(`homSystem_map_surjective`, `isMittagLeffler_homSystem`,
`towerHomEval_surjective`; Worker 61) and the Library's `ℓ`-divisible systems
(`DivisibleSystem`, `DivisibleSystem.mapLeftExact`,
`DivisibleSystem.mapComplexes`, `DivisibleSystem.degree`; Worker 61).

Harris's coefficient modules `C^j_m(ẽ)` are direct limits of free
`𝒪/ℓ^m𝒪[S(ẽ)/H(ẽ)]`-modules as the open subgroup `H(ẽ)` shrinks. This module
formalizes such modules and derives from that structure the two hypotheses that
the Library's `InvariantHomSystem`, `InvariantHomSurjective` and
`FreeTorsionProjective` keep explicit:

- bijectivity of `invariantsToCoinvariants`, under which
  `Hom(C, Inf W) = Hom(C^K, W)`; this is Harris's replacement of `C^j_m(ẽ)`
  by its `H_p`-invariants;
- freeness of the invariants over `(R ⧸ (ℓ ^ m))[G ⧸ K]`.

It then restates the Library's conclusions about the Hom inverse systems
(surjective transitions, Mittag-Leffler condition) under the new structure.

The module has two namespaces: `Langlands.Induction` (sections `Comp`,
`Invariants`, `DirectedUnion`, `FreeLimit`, `Topological`) and
`Langlands.Cohomology.DivisibleSystem` (sections `FreeOverPowQuotient`,
`HomSystem`, `Complexes`).

## Conventions

For a commutative ring `R`, a group `G`, an `R`-module `V`,
`ρ : Representation R G V` and a subgroup `H`, `ρ^H` is Mathlib's
`Representation.invariants (ρ.comp H.subtype)`, the `R`-submodule of
`H`-fixed vectors. For `H` normal, Mathlib's `ρ.quotientToInvariants H` is the
representation of `G ⧸ H` on `ρ^H`, and Mathlib's
`Rep.quotientToInvariantsFunctor R H` sends `P : Rep R G` to
`Rep.of (P.ρ.quotientToInvariants H)`.

`Induction.permutation R Γ X M` is the Library's permutation representation of
a group `Γ` on the finitely supported functions `X →₀ M` on a `Γ`-set `X`,
with `(g • φ)(x) = φ(g⁻¹ • x)`. For `X = Γ` acting on itself by left
multiplication and coefficients `I →₀ k`, it is the direct sum `⊕_I k[Γ]` of
`I` copies of the group algebra, i.e. the free `k[Γ]`-module of rank `I`.

`Induction.invariantsToCoinvariants ρ K` is the Library's map from the
`K`-invariants to the `K`-coinvariants of `ρ` (inclusion followed by
projection), as a map of representations of `G ⧸ K`. For
`P : Rep R Γ`, `FreeOverPowQuotient ℓ m P` is the Library's predicate: `P` is
killed by `ℓ ^ m`, and `P` is a free module over `(R ⧸ (ℓ ^ m))[Γ]` through
`torsionQuotientRep`.

For an `ℓ`-divisible system `T` of representations of `G` and a normal
subgroup `K`, `T.mapLeftExact (Rep.quotientToInvariantsFunctor R K) hTK` is
the Library's system `m ↦ (T m)^K` of `K`-invariants, defined given the
hypothesis `hTK` that the projections of `T` stay epimorphisms on
`K`-invariants. The Library's `invariantsSystem R K T hbij` is this system with
`hTK` derived from bijectivity of `invariantsToCoinvariants` at every level,
so the statements below apply to it (`invariantsSystem_eq_mapLeftExact`).
`homSystem R T W` is the Library's inverse system `m ↦ Hom(T m, W m)`,
`towerHomEval R T W n` evaluates a morphism of inverse systems at level `n`,
`W.map (Rep.resFunctor (QuotientGroup.mk' K))` is the inflation `Inf W` of a
system of representations of `G ⧸ K`, and `C.degree j` is the system of degree
`j` terms of an `ℓ`-divisible system `C` of cochain complexes.

## Free invariants

Section `Invariants`: `R : Type uR` commutative, `G : Type uG` a group,
`V : Type uV`, `ρ : Representation R G V`, and an `R`-algebra `k : Type uk`
(commutative).

| Declaration | Statement |
| --- | --- |
| `invariantsInflation ρ H` | For `H` normal, the representation of `G` on `ρ^H`: `(ρ.quotientToInvariants H).comp (QuotientGroup.mk' H)` (abbreviation). |
| `mem_invariants_of_le ρ hH hv` | For subgroups `H' ≤ H`, `v ∈ ρ^H` implies `v ∈ ρ^{H'}`. |
| `invariantsInvariantsEquiv ρ hHK` | For normal `H ≤ K`, an equivalence of representations of `G ⧸ K` from `ρ.quotientToInvariants K` to the `K`-invariants of `invariantsInflation ρ H`, `v ↦ v`. |
| `permutationQuotientEquiv R K M` | For `K` normal and an `R`-module `M`, the identity of `G ⧸ K →₀ M` is an equivalence from the permutation representation of `G ⧸ K` on itself, pulled back along `G → G ⧸ K`, to `Induction.permutation R G (G ⧸ K) M`. |
| `IsFreeOnInvariants ρ k H` | For `H` normal: there are a type `I : Type uV` and an equivalence of representations of `G ⧸ H` over `R` from `ρ.quotientToInvariants H` to `Induction.permutation R (G ⧸ H) (G ⧸ H) (I →₀ k)`, i.e. `ρ^H ≅ ⊕_I k[G ⧸ H]`. |
| `IsFreeOnInvariants.of_le hHK h` | For normal `H ≤ K` with `H` of finite index in `K` (`[(H.subgroupOf K).FiniteIndex]`): `IsFreeOnInvariants ρ k H → IsFreeOnInvariants ρ k K`, with the same `I`. |
| `IsFreeOnInvariants.bijective_invariantsToCoinvariants hHK hu h` | For normal `H ≤ K`, `H` of finite index in `K` with index a unit of `R`, and `IsFreeOnInvariants ρ k H`: `invariantsToCoinvariants (invariantsInflation ρ H) K` is bijective. |
| `IsFreeOnInvariants.free_asModule h` | If `IsFreeOnInvariants ρ R H`, then `(ρ.quotientToInvariants H).asModule` is a free module over `MonoidAlgebra R (G ⧸ H)`. |

The shared `Langlands.Cohomology.HyperextAbutment.equivComp` from
[`EquivalencePullback`](../../Representation/EquivalencePullback.md) pulls
an equivalence of representations back along a group homomorphism.

## Directed unions

Section `DirectedUnion`: `ρ` as above, a family `H : ι → Subgroup G` of normal
subgroups (`ι : Type uι`) and a normal subgroup `K`. The hypotheses are named
`hdir : ∀ i j, ∃ l, H l ≤ H i ⊓ H j` (directed downwards),
`hex : ∀ v, ∃ i, v ∈ ρ^{H i}` (exhaustive) and `h0 : ∃ i, H i ≤ K`.

| Declaration | Statement |
| --- | --- |
| `exists_le_forall_mem_invariants ρ H K hdir hex h0 s` | For a finite set `s : Finset V` there is `i` with `H i ≤ K` and `s ⊆ ρ^{H i}`. (Normality of `H i` and `K` is not needed here.) |
| `invariantsInflationInclusion ρ K H'` | For `H'` normal, the inclusion `ρ^{H'} → V` as a map of the representations of `K` obtained by restriction. |
| `bijective_invariantsToCoinvariants_of_directed ρ H K hdir hex h0 hbij` | If `invariantsToCoinvariants (invariantsInflation ρ (H i)) K` is bijective for every `i` with `H i ≤ K`, then `invariantsToCoinvariants ρ K` is bijective. |

## Direct limits of free modules

Section `FreeLimit`: `ρ`, `k` and the family `H` of normal subgroups as above.

| Declaration | Statement |
| --- | --- |
| `IsFreeLimit ρ k H` | Structure (a proposition) with fields `directed : ∀ i j, ∃ l, H l ≤ H i ⊓ H j`, `exhaustive : ∀ v : V, ∃ i, v ∈ ρ^{H i}` and `free : ∀ i, IsFreeOnInvariants ρ k (H i)`. |
| `IsFreeLimit.isFreeOnInvariants hρ hiK` | For `K` normal and `H i ≤ K` of finite index: `IsFreeOnInvariants ρ k K`. |
| `IsFreeLimit.bijective_invariantsToCoinvariants hρ K h0 hfin hu` | For `K` normal with `h0 : ∃ i, H i ≤ K`, `hfin : ∀ i, H i ≤ K → ((H i).subgroupOf K).FiniteIndex` and `hu : ∀ i, H i ≤ K → IsUnit (((H i).subgroupOf K).index : R)`: `invariantsToCoinvariants ρ K` is bijective. |

Because `ρ^{H i} ⊆ ρ^{H j}` when `H j ≤ H i`, a representation with
`IsFreeLimit ρ k H` is the directed union of the free `k[G ⧸ H i]`-modules
`ρ^{H i}`. This is their direct limit along the inclusions.

## Topological groups

Section `Topological`: `G` also has a topology, and `H : ι → Subgroup G`. The
hypotheses are `hopen : ∀ i, IsOpen (H i : Set G)` and
`hshrink : ∀ U ∈ nhds (1 : G), ∃ i, (H i : Set G) ⊆ U` (the family shrinks to
the identity). Smoothness is the Library's `IsSmooth ρ`: every vector is in
`fixedVectors ρ U` for some open subgroup `U`. The last two rows also assume
`[IsTopologicalGroup G]`.

| Declaration | Statement |
| --- | --- |
| `directed_of_shrink hopen hshrink` | `∀ i j, ∃ l, H l ≤ H i ⊓ H j`. |
| `exists_le_of_isOpen hshrink hK` | For a subgroup `K` with `IsOpen (K : Set G)`: `∃ i, H i ≤ K`. |
| `exhaustive_of_isSmooth ρ hshrink hρ v` | If `IsSmooth ρ`, then `∃ i, v ∈ ρ^{H i}`. |
| `IsFreeLimit.of_isSmooth ρ hopen hshrink hρ hfree` | For `H i` normal, `IsSmooth ρ` and `hfree : ∀ i, IsFreeOnInvariants ρ k (H i)`: `IsFreeLimit ρ k H`. |
| `IsFreeLimit.isFreeOnInvariants_of_isOpen hρ hopen hshrink K hKo hKc` | For `K` normal, open and compact (`IsCompact (K : Set G)`): `IsFreeOnInvariants ρ k K`. |
| `IsFreeLimit.bijective_invariantsToCoinvariants_of_isProP hρ hopen hshrink hp hR K hKo hK` | For a prime `p` with `IsUnit (p : R)` and `K` normal, open, with `[CompactSpace K]` and `hK : ∀ N : OpenNormalSubgroup K, IsPGroup p (K ⧸ N.toSubgroup)`: `invariantsToCoinvariants ρ K` is bijective. |

## `ℓ`-divisible systems

Namespace `Langlands.Cohomology.DivisibleSystem`. Section `FreeOverPowQuotient`:
`R : Type u` commutative, `Γ : Type v` a group, `ℓ m : ℕ`, and
`R ⧸ (ℓ ^ m)` means `R ⧸ Ideal.span {((ℓ : R) ^ m)}`.

| Declaration | Statement |
| --- | --- |
| `powSMul_finsupp_quotient y` | For `y : X →₀ I →₀ R ⧸ (ℓ ^ m)`: `((ℓ : R) ^ m) • y = 0`. |
| `freeOverPowQuotient_of_equiv_permutation Q e` | For `Q : Rep.{w} R Γ` and an equivalence `e` of representations over `R` from `Q.ρ` to `Induction.permutation R Γ Γ (I →₀ R ⧸ (ℓ ^ m))`: `FreeOverPowQuotient ℓ m Q`. |
| `freeOverPowQuotient_quotientToInvariants P K h` | For `P : Rep.{w} R G` (`G : Type v`), `K` normal and `IsFreeOnInvariants P.ρ (R ⧸ (ℓ ^ m)) K`: `FreeOverPowQuotient ℓ m ((Rep.quotientToInvariantsFunctor R K).obj P)`. |

Section `HomSystem`. `map_surjective_of_iso e φ h`: for an isomorphism
`e : F ≅ F'` of functors `ℕᵒᵖ ⥤ ModuleCat.{w} R`, surjectivity of `F'.map φ`
implies surjectivity of `F.map φ`. The remaining declarations take `G : Type v`, an
`ℓ`-divisible system `T : DivisibleSystem (Rep.{w} R G) ℓ`, a family
`H : ι → Subgroup G` of normal subgroups with
`hT : ∀ m, IsFreeLimit (T.obj m).ρ (R ⧸ (ℓ ^ m)) H`, a normal subgroup `K`
with `h0`, `hfin`, `hu` as in `IsFreeLimit.bijective_invariantsToCoinvariants`,
the hypothesis `hTK` of `mapLeftExact` for the `K`-invariants functor, and
`W : DivisibleSystem (Rep.{w} R (G ⧸ K)) ℓ`. Write `T^K` for
`T.mapLeftExact (Rep.quotientToInvariantsFunctor R K) hTK`.

| Declaration | Statement |
| --- | --- |
| `bijective_invariantsToCoinvariants_of_isFreeLimit T H hT K h0 hfin hu m` | `invariantsToCoinvariants (T.obj m).ρ K` is bijective. |
| `freeOverPowQuotient_invariants_of_isFreeLimit T H hT K h0 hfin m` | `FreeOverPowQuotient ℓ m ((Rep.quotientToInvariantsFunctor R K).obj (T.obj m))`. |
| `isFreeLimit_invariants_homSystem_map_surjective T H hT K h0 hfin hTK W φ` | `(homSystem R T^K W).map φ` is surjective. |
| `isMittagLeffler_isFreeLimit_invariants_homSystem T H hT K h0 hfin hTK W` | `homSystem R T^K W ⋙ forget` satisfies Mathlib's `IsMittagLeffler`. |
| `isFreeLimit_invariants_towerHomEval_surjective T H hT K h0 hfin hTK W n` | `towerHomEval R T^K W n` is surjective. |
| `isFreeLimit_homSystem_map_surjective T H hT K h0 hfin hu hTK W φ` | `(homSystem R T (Inf W)).map φ` is surjective. |
| `isMittagLeffler_isFreeLimit_homSystem T H hT K h0 hfin hu hTK W` | `homSystem R T (Inf W) ⋙ forget` satisfies `IsMittagLeffler`. |

Section `Complexes`: an `ℓ`-divisible system
`C : DivisibleSystem (CochainComplex (Rep.{w} R G) ℕ) ℓ`, a degree `j`,
`hC : ∀ m, IsFreeLimit ((C.obj m).X j).ρ (R ⧸ (ℓ ^ m)) H`, `K`, `h0`, `hfin`,
`hu`, `W` as above, and the hypothesis `hCK` of `mapComplexes` for the
`K`-invariants functor; `C^K` is
`C.mapComplexes (Rep.quotientToInvariantsFunctor R K) hCK`.

| Declaration | Statement |
| --- | --- |
| `isFreeLimit_degree_invariants_homSystem_map_surjective C H j hC K h0 hfin hCK W φ` | `(homSystem R ((C^K).degree j) W).map φ` is surjective. |
| `isMittagLeffler_isFreeLimit_degree_invariants_homSystem C H j hC K h0 hfin hCK W` | `homSystem R ((C^K).degree j) W ⋙ forget` satisfies `IsMittagLeffler`. |
| `isFreeLimit_degree_homSystem_map_surjective C H j hC K h0 hfin hu hCK W φ` | `(homSystem R (C.degree j) (Inf W)).map φ` is surjective. |
| `isMittagLeffler_isFreeLimit_degree_homSystem C H j hC K h0 hfin hu hCK W` | `homSystem R (C.degree j) (Inf W) ⋙ forget` satisfies `IsMittagLeffler`. |

## Proofs

- `IsFreeOnInvariants.of_le` composes `invariantsInvariantsEquiv`, the
  invariants of the pulled-back equivalence (Library `invariantsEquivOfEquiv`),
  `permutationQuotientEquiv` and the Library's `permutationInvariantsEquiv`
  (`K`-invariants of the permutation representation on `G ⧸ H` are the
  permutation representation of `G ⧸ K` on itself, same coefficients).
- `IsFreeOnInvariants.bijective_invariantsToCoinvariants` transports the
  Library's `bijective_invariantsToCoinvariants_permutation` along the
  equivalence (`bijective_invariantsToCoinvariants_of_equiv`).
- `bijective_invariantsToCoinvariants_of_directed`. For injectivity, a
  `K`-invariant vector `x` with zero class is a finite combination
  `Σ c (k, v) • (ρ k v - v)`. All the `v` and `x` lie in some `ρ^{H i}` with
  `H i ≤ K`, so `x` has zero class already in the `K`-coinvariants of
  `ρ^{H i}`, and injectivity there gives `x = 0`. For surjectivity, a class
  `[w]` with `w ∈ ρ^{H i}`, `H i ≤ K`, comes from a `K`-invariant vector of
  `ρ^{H i}`, and the inclusion `ρ^{H i} → V` maps coinvariant classes to
  coinvariant classes (Mathlib's `Coinvariants.map`).
- `freeOverPowQuotient_of_equiv_permutation`: `ℓ ^ m` kills the target of `e`,
  hence `Q`. The same additive equivalence is `(R ⧸ (ℓ ^ m))`-linear for the
  module structure of `torsionQuotientRepresentation` (Mathlib's
  `Module.IsTorsionBySet.mk_smul` and `algebraMap_smul`). Hence `Q` over
  `R ⧸ (ℓ ^ m)` is equivalent to the permutation representation over
  `R ⧸ (ℓ ^ m)`, which is free over the group algebra by the Library's
  `permutation_asModule_free` (left multiplication has trivial stabilizers).
- The Hom-system statements combine
  `powTorsionProjective_of_freeOverPowQuotient` with the Library's
  `homSystem_map_surjective`, `isMittagLeffler_homSystem` and
  `towerHomEval_surjective` for `T^K`. They transfer to `Hom(T m, Inf (W m))`
  along the Library's isomorphism of inverse systems `invariantsHomSystemIso`
  (which needs the bijectivity) by `map_surjective_of_iso` and Mathlib's
  `Functor.isMittagLeffler_of_surjective`. The degree `j` statements are the
  same statements for `C.degree j`.
- The topological statements: `H i ∩ H j` and an open `K` are neighbourhoods
  of `1`; a smooth vector is fixed by an open subgroup `U`, which contains some
  `H i`; open subgroups have finite index in compact subgroups (Library
  `finiteIndex_subgroupOf_of_isCompact`) and, in a compact subgroup with
  `p`-group quotients, index a power of `p` (Library `isUnit_index_subgroupOf`).

## Provenance and interpretation

The definitions, statements and proofs are ours, from Mathlib and the Library.
The structure `IsFreeLimit` and the use of its consequences are modelled on
the following passages of Harris 1999, read in the rendered scans:

- Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
  J. Math. Kyoto Univ. 39-2 (1999), 299-318 (source
  `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`).
- §2, printed p.306 (one-based PDF page 8): "When we replace `H` by a
  subgroup `H'` which is normal in `S(e)`, we obtain a natural isomorphism
  `C_m^{•,H} = [C_m^{•,H'}]^H`. Taking the direct limit as `H` shrinks to the
  identity, we obtain an `ℓ`-divisible system of complexes `C_m^•` of
  projective `ℤ/ℓ^mℤ[S(e)]`-modules".
- Proof of Proposition 4.10, printed pp.311-312 (one-based PDF pages 13-14):
  "Recall that `C^j(ẽ)` has been chosen to be a direct limit of free
  `𝒪/ℓ^m𝒪[S(ẽ)/H(ẽ)]`-modules as `H(ẽ)` varies over a family of open
  subgroups of `S(ẽ)`. We may replace `C^j_m(ẽ)` by `C^j_m(ẽ)^{H_p}` in
  (4.10.2)."
- Printed p.312 (one-based PDF page 14): "But we have seen in §2 that the maps
  `C^j_{m+1}(ẽ)^{H_p} → C^j_m(ẽ)^{H_p}` are surjective. Since `C^j_m(ẽ)^{H_p}`
  and `Hom(𝒪_m[C_p/H_p]^M, 𝓛_m)` are both free `𝒪/ℓ^m𝒪[S(ẽ)/H_p]`-modules, it
  follows that the maps (4.10.3) are surjective for all `m`."

Interpretation (our reading; explanation only, not formalized). `G` plays the
role of `S(ẽ)`, the family `H` that of the subgroups `H(ẽ)`, `K` that of
`S(ẽ) ∩ H_p`, `T` that of `m ↦ C^j_m(ẽ)` (or `C` that of the complexes
`C_m^•` and `j` the degree), `R` that of `𝒪`, and `W` that of the
coefficients `Hom(𝒪_m[C_p/H_p]^M, 𝓛_m)`. Harris says "open subgroups";
freeness over `𝒪/ℓ^m𝒪[S(ẽ)/H(ẽ)]` needs the group `S(ẽ)/H(ẽ)`, so we take
the `H(ẽ)` normal, as on p.306. On p.306, "`C_m^{•,H} = [C_m^{•,H'}]^H`" is the
relation `ρ^H = (ρ^{H'})^H` of `invariantsInvariantsEquiv`, and the direct limit
as `H` shrinks is the directed union of the `ρ^{H i}`. Harris derives the surjectivity of the maps on
`H_p`-invariants from §2. Here, as in the Library's `InvariantHomSurjective`, the
hypothesis `hTK` (or `hCK`) is explicit. It can be supplied from the bijectivity
proved here through the Library's `epi_quotientToInvariantsFunctor_map_projection`
(that is, by using `invariantsSystem`).

## Scope

- Harris's complexes `C_m^•` and modules `C^j_m(ẽ)` are not constructed, and
  it is not proved that they satisfy `IsFreeLimit`.
- Harris's claim on p.306 that the direct limit consists of projective
  `ℤ/ℓ^mℤ[S(e)]`-modules is not formalized.
- The coefficients `Hom(𝒪_m[C_p/H_p]^M, 𝓛_m)` are an arbitrary `ℓ`-divisible
  system `W` here; their freeness (the Library's `PermutationDual`) is not
  used.
- `IsFreeOnInvariants` asks for an index type in the universe of `V`.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`, printed
pp.306, 311-312 (one-based PDF pages 8, 13-14), read in the rendered scans.
