# Invariants of permutation modules under normal subgroups

Author: Worker 61. Built on the published
`Langlands.Representation.Induction.PermutationModule` (`permutation`,
`permutation_apply`, `permutationFinsuppEquiv`, `finsupp_ofMulAction_quotient`,
`permutationEquiv`) and, through it, on
`Langlands.Representation.Induction.Definitions` (`compactInduced`). From
Mathlib it uses the quotient map between coset spaces
(`Subgroup.quotientMapOfLE`), finitely supported functions
(`Finsupp.ofSupportFinite`), invariants of a normal subgroup as a
representation of the quotient group (`Representation.invariants`,
`Representation.mem_invariants`, `Representation.quotientToInvariants`),
equivalences of representations (`Representation.Equiv`), the comparison
between intertwining maps and module maps over the group algebra
(`Representation.IntertwiningMap.equivLinearMapAsModule`), the free
representation `Representation.free` and its freeness over the group algebra
(`Representation.free_asModule_free`), `Module.Free.of_equiv`, and the
finiteness of quotients of compact groups by open subgroups
(`Subgroup.quotient_finite_of_isOpen`, `Subgroup.finiteIndex_of_finite_quotient`).

All new names are in the namespace `Langlands.Induction`. `R` is a
commutative ring, `M` an `R`-module and `I` a type.

## Conventions

`G ⧸ H` is Mathlib's quotient by the left cosets `x H`, on which `G` acts by
left multiplication. `permutation R G (G ⧸ H) M` is the published
representation of `G` on `G ⧸ H →₀ M` in which `g` moves the value at `x H`
to `g x H`; its value at `x H` after acting by `g` is the value at `g⁻¹ x H`
(`permutation_apply`). For a normal subgroup `K` of `G` and a representation
`ρ` of `G`, `Representation.quotientToInvariants ρ K` is Mathlib's
representation of `G ⧸ K` on the `K`-invariant vectors of `ρ`.
`(H.subgroupOf K).FiniteIndex` says that `H ∩ K` has finite index in `K`;
under `H ≤ K` this is the index of `H` in `K`.

## Fibres of `G ⧸ H → G ⧸ K`

`H ≤ K` are subgroups of a group `G`, with `hHK : H ≤ K`.

- `quotientMapOfLE_fiber_finite hHK q`: if `H` has finite index in `K`, the
  fibre of `Subgroup.quotientMapOfLE hHK : G ⧸ H → G ⧸ K` over every `q` is
  finite. For `q = g K` the fibre is contained in the image of the map
  `K ⧸ H → G ⧸ H`, `k H ↦ g k H`, whose domain is finite.

## Equivalences of representations

- `equiv_apply_mem_invariants K e hv`: an equivalence `e` of representations
  of `G` sends a `K`-invariant vector to a `K`-invariant vector, for any
  subgroup `K`.
- `invariantsEquivOfEquiv K e`: for `K` normal, `e` restricts to an
  equivalence between the representations of `G ⧸ K` on `K`-invariants
  (`Representation.quotientToInvariants`) of source and target.
- `asModuleLinearEquiv e`: an equivalence of representations as a linear
  equivalence of the corresponding modules over the monoid algebra `R[G]`
  (`Representation.asModule`), built from
  `Representation.IntertwiningMap.equivLinearMapAsModule` applied to `e` and
  to its inverse. The Library already has the same construction as
  `Langlands.representationAsModuleEquiv` in
  `Langlands.Representation.RankinSelberg.WhittakerTypeEquivalence`, stated
  for commutative rings, groups and additive groups. This version needs only
  commutative semirings, monoids and additive commutative monoids. A first
  version of this module stated it with the Library's hypotheses, and then
  the proof of `freeInvariants_free` did not elaborate (a type mismatch after
  a heartbeat timeout); with the weaker hypotheses it elaborates. Defining it
  here also avoids importing the Rankin–Selberg module.

## Invariants of the permutation module on `G ⧸ H`

`H ≤ K` are subgroups of a group `G` with `K` normal and `hHK : H ≤ K`.

- `invariantValue φ`: for a `K`-invariant `φ : G ⧸ H →₀ M`, the function on
  `G ⧸ K` whose value at `g K` is `φ (g H)`. It is well defined: if
  `a K = b K` then `b a⁻¹ ∈ K`, and `K`-invariance of `φ` under `b a⁻¹` gives
  `φ (b H) = φ (a H)`. `invariantValue_mk` states the defining equation.
- `invariantValue_support_finite hHK φ`: the support of `invariantValue φ` is
  contained in the image of the support of `φ` under `G ⧸ H → G ⧸ K`, hence
  finite.
- `invariantsToQuotient R M hHK`: the `R`-linear map from the `K`-invariants
  of `permutation R G (G ⧸ H) M` to `G ⧸ K →₀ M` sending `φ` to
  `invariantValue φ`.

The remaining results assume that `H` has finite index in `K`.

- `comp_quotientMapOfLE_support_finite hHK ψ`: for `ψ : G ⧸ K →₀ M`, the
  function `ψ ∘ quotientMapOfLE hHK` on `G ⧸ H` has finite support, since its
  support is the preimage of the finite support of `ψ` and the fibres are
  finite (`quotientMapOfLE_fiber_finite`). Normality of `K` is not used.
- `pullbackInvariant R hHK ψ`: the function `g H ↦ ψ (g K)` as a
  `K`-invariant element of `G ⧸ H →₀ M`. It is `K`-invariant because, for
  `k ∈ K`, its value at `g H` after acting by `k` is `ψ (k⁻¹ g K)`, and
  `k⁻¹ g K = g K` by normality of `K`. `pullbackInvariant_mk` states its
  values.
- `permutationInvariantsLinearEquiv R M hHK`: `invariantsToQuotient` and
  `pullbackInvariant` are inverse `R`-linear equivalences between the
  `K`-invariants of `permutation R G (G ⧸ H) M` and `G ⧸ K →₀ M`. Both
  composites are the identity on values at cosets by definition.
- `permutationInvariantsEquiv R M hHK`: this linear equivalence is an
  equivalence of representations of `G ⧸ K`, from
  `Representation.quotientToInvariants (permutation R G (G ⧸ H) M) K` to the
  permutation representation `permutation R (G ⧸ K) (G ⧸ K) M` of `G ⧸ K` on
  itself. For `g ∈ G` and `y ∈ G`, both sides at `y K` are `φ (g⁻¹ y H)`.
- `permutationInvariantsFreeEquiv R hHK I`: with coefficients `I →₀ R`,
  `permutationInvariantsEquiv` followed by the published
  `permutationFinsuppEquiv R (G ⧸ K) (G ⧸ K) I` is an equivalence from the
  `K`-invariants to `Representation.free R (G ⧸ K) I`, Mathlib's free
  `R[G ⧸ K]`-module of rank `I`. (`permutationFinsuppEquiv` identifies the
  permutation representation of `G ⧸ K` on itself with coefficients `I →₀ R`
  with `(Representation.ofMulAction R (G ⧸ K) (G ⧸ K)).finsupp I`, and this
  representation is `Representation.free R (G ⧸ K) I` by definition, since
  Mathlib defines `Representation.free R (G ⧸ K) I` as
  `(Representation.leftRegular R (G ⧸ K)).finsupp I` and
  `Representation.leftRegular` as `Representation.ofMulAction` of a group on
  itself.)
- `permutationInvariants_free R hHK I`: the `R[G ⧸ K]`-module
  `(Representation.quotientToInvariants (permutation R G (G ⧸ H) (I →₀ R)) K).asModule`
  is free (`Module.Free`), by `asModuleLinearEquiv` of
  `permutationInvariantsFreeEquiv` and `Representation.free_asModule_free`.

## Invariants of free modules

In addition `H` is normal.

- `freeCompEquiv R I`: the free `R[G ⧸ H]`-module of rank `I`, viewed as a
  representation of `G` through `QuotientGroup.mk' H`, is equivalent to
  `permutation R G (G ⧸ H) (I →₀ R)`. It is the inverse of
  `permutationFinsuppEquiv R G (G ⧸ H) I`, with its source rewritten by the
  published `finsupp_ofMulAction_quotient`.
- `freeInvariantsEquiv R hHK I`: the `K`-invariants of the free
  `R[G ⧸ H]`-module of rank `I`, as a representation of `G ⧸ K`, are
  equivalent to the free `R[G ⧸ K]`-module of rank `I`:
  `invariantsEquivOfEquiv K (freeCompEquiv R I)` followed by
  `permutationInvariantsFreeEquiv`.
- `freeInvariants_free R hHK I`: these invariants form a free
  `R[G ⧸ K]`-module (`Module.Free`).

## Compact induction of trivial representations

`G` is a topological group.

- `finiteIndex_subgroupOf_of_isCompact hH hK`: if `H` is open and `K` is
  compact, then `H.subgroupOf K` has finite index in `K`: it is an open
  subgroup of the compact group `K`, so the quotient is finite. This supplies
  the finite-index hypothesis below when `K` is compact.

Now `hH : IsOpen (H : Set G)`, `hHK : H ≤ K`, `K` is normal and `H` has
finite index in `K`.

- `compactInducedInvariantsEquiv R M hH hHK`: the `K`-invariants of the
  published compact induction `compactInduced H (Representation.trivial R H M)`,
  as a representation of `G ⧸ K`, are equivalent to
  `permutation R (G ⧸ K) (G ⧸ K) M`. It is `invariantsEquivOfEquiv` of the
  published `permutationEquiv R M H hH` followed by
  `permutationInvariantsEquiv`.
- `compactInducedInvariantsFreeEquiv R hH hHK I`: with coefficients `I →₀ R`,
  the same invariants are equivalent to `Representation.free R (G ⧸ K) I`.
- `compactInducedInvariants_free R hH hHK I`: they form a free
  `R[G ⧸ K]`-module (`Module.Free`).

`H` need not be normal in this section.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), proof of Proposition 4.10 (Worker 61 read
the rendered scanned pages):

- printed p.311 (one-based PDF page 13): the map (4.10.2) involves
  `Hom_{𝒪/ℓ^m𝒪[S(ẽ)]}(C^j_m(ẽ), Hom(𝒪_m[C_p/H_p]^M, 𝓛_m))`, and "Up to
  conjugacy, we may assume `S(ẽ) ⊂ C_p`";
- printed p.312 (one-based PDF page 14): "We may replace `C^j_m(ẽ)` by
  `C^j_m(ẽ)^{H_p}` in (4.10.2)", and "Since `C^j_m(ẽ)^{H_p}` and
  `Hom(𝒪_m[C_p/H_p]^M, 𝓛_m)` are both free `𝒪/ℓ^m𝒪[S(ẽ)/H_p]`-modules, it
  follows that the maps (4.10.3) are surjective for all m."

On printed pp.311-312, `C^j(ẽ)` is chosen to be a direct limit of free
`𝒪/ℓ^m𝒪[S(ẽ)/H(ẽ)]`-modules as `H(ẽ)` varies over a family of open subgroups
of `S(ẽ)`. The published PermutationModule module identifies such free
modules with compact inductions of trivial representations. This module
proves an algebraic step behind the freeness of the `H_p`-invariants: for a
group `G`, subgroups `H ≤ K` with `K` normal and `H` of finite index in `K`,
and `R` any commutative ring (for example `𝒪/ℓ^m𝒪`), the `K`-invariants of
a free `R[G ⧸ H]`-module (for `H` normal), or of a compact induction from `H`
of a trivial representation with free coefficients (for `H` open), are a free
`R[G ⧸ K]`-module. In the intended application `G` and `K` would
correspond to `S(ẽ)` and `H_p`, and `H` to a member of the family `H(ẽ)`.
This correspondence is our interpretation. The hypotheses that `K` is
normal and that `H ≤ K` with finite index are assumptions of this module,
not statements quoted from the source.

The module is derived: that invariants of a permutation module are the
permutation module on the coarser coset space is standard, and all
definitions and proofs are ours.

## Scope

The module does not prove that Harris's modules `C^j_m(ẽ)^{H_p}` or
`Hom(𝒪_m[C_p/H_p]^M, 𝓛_m)` are free, and it does not connect them to the
Library's objects. Direct limits of free modules are not treated, so the
passage from the free modules in the direct limit to `C^j_m(ẽ)` is not
formalized. The surjectivity of the maps (4.10.3) is not derived here.
Invariants are taken of finitely supported functions, that is, of compact
inductions of trivial representations; compact induction of other
representations is not described.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
