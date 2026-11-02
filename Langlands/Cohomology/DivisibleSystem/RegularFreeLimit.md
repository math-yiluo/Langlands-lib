# The regular representation of a profinite group as a direct limit of free modules

Author: Worker 61. Built on the Library modules
`Langlands.Cohomology.DivisibleSystem.FreeQuotientLimit`
(`Induction.IsFreeOnInvariants`, `Induction.IsFreeLimit`,
`Induction.IsFreeLimit.of_isSmooth`, `Induction.exists_le_of_isOpen`,
`Induction.IsFreeLimit.bijective_invariantsToCoinvariants_of_isProP`,
`isFreeLimit_invariants_homSystem_map_surjective`,
`isMittagLeffler_isFreeLimit_invariants_homSystem`,
`isFreeLimit_homSystem_map_surjective`; Worker 61),
`Langlands.Cohomology.DivisibleSystem.FreeReduction` (`powDiv`,
`powDiv_zero`, `pow_mul_powDiv`; Worker 61) and
`Langlands.Representation.LocallyConstant.CompactAction`
(`CompactAction.LocallyConstantModule.diagonalRepresentation`,
`diagonalRepresentation_apply`, `diagonalRepresentation_isSmooth`). Through
these imports it also uses `Langlands.Representation.Induction.PermutationInvariants`
(`Induction.invariantsEquivOfEquiv`, `Induction.equiv_apply_mem_invariants`,
`Induction.finiteIndex_subgroupOf_of_isCompact`; Worker 61),
`Langlands.Representation.Induction.PermutationModule`
(`Induction.permutation`, `Induction.permutation_apply`; Worker 61),
`Langlands.Representation.Induction.PermutationDual`
(`Induction.permutationCongr`; Worker 61),
`Langlands.Representation.Induction.InvariantRestriction`
(`Induction.invariantsToCoinvariants`, `Induction.isUnit_index_subgroupOf`;
Worker 61), `Langlands.Cohomology.DivisibleSystem.Reduction`
(`reductionSystem`, `mono_powSMul_one_iff_isSMulRegular`; Worker 61),
`Langlands.Cohomology.DivisibleSystem.FreeTorsionProjective`
(`powSMul_hom_apply`; Worker 61),
`Langlands.Cohomology.DivisibleSystem.InvariantHomSurjective`
(`epi_quotientToInvariantsFunctor_map_projection`; Worker 61),
`Langlands.Cohomology.DivisibleSystem.HomSystem` (`homSystem`; Worker 61)
and the Library's `ℓ`-divisible systems (`DivisibleSystem`, `powSMul`,
`DivisibleSystem.mapLeftExact`; Worker 61). From Mathlib it uses
`LocallyConstant` (with `LocallyConstant.mapₗ`, `LocallyConstant.map`),
`IsLocallyConstant.of_discrete`, `QuotientGroup.discreteTopology`,
`Subgroup.quotient_finite_of_isOpen`, `Finsupp.equivFunOnFinite`,
`Finsupp.mapRange.linearMap`, `Finsupp.mapRange_surjective`,
`Finsupp.domLCongr`, `OpenNormalSubgroup`,
`ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one`
(`Mathlib.Topology.Algebra.ClopenNhdofOne`), `Representation.trivial`,
`Representation.equivOfIso`, `Rep.of`, `Rep.ofHom`, `Rep.epi_iff_surjective`,
`ShortComplex.exact_map_iff_of_faithful`, `ShortComplex.moduleCat_exact_iff`,
`ShortComplex.Exact.gIsCokernel`, `IsColimit.coconePointUniqueUpToIso` and
`Functor.isMittagLeffler_of_surjective`.

The Library module `FreeQuotientLimit` formalizes Harris's coefficient modules
"direct limit of free `𝒪/ℓ^m𝒪[S(ẽ)/H(ẽ)]`-modules" as the predicate
`IsFreeLimit` and derives from it the hypotheses of the Library's Hom-system
statements. This module gives an actual instance of that interface: the
regular representation of a profinite group on locally constant functions,
which is smooth, and its `ℓ`-adic reduction system.

The module has two namespaces: `Langlands.Induction` (sections `Transport`,
`Regular`, `Profinite`) and `Langlands.Cohomology.DivisibleSystem` (sections
`Reduction`, `HomSystem`).

## Conventions

For a commutative ring `R`, a group `G`, an `R`-module `V`,
`ρ : Representation R G V` and a subgroup `H`, `ρ^H` is Mathlib's
`Representation.invariants (ρ.comp H.subtype)`. For `H` normal,
`ρ.quotientToInvariants H` is Mathlib's representation of `G ⧸ H` on `ρ^H`.
`Induction.permutation R Γ X M` is the Library's permutation representation of
a group `Γ` on `X →₀ M` for a `Γ`-set `X`, `(g • φ)(x) = φ(g⁻¹ • x)`; for
`X = Γ` and `M = I →₀ k` it is `⊕_I k[Γ]`, the free `k[Γ]`-module of rank `I`.

`IsFreeOnInvariants ρ k H` (Library, for `H` normal and an `R`-algebra `k`):
there is an index type `I` (in the universe of `V`) and an equivalence of
representations of `G ⧸ H` from `ρ.quotientToInvariants H` to
`Induction.permutation R (G ⧸ H) (G ⧸ H) (I →₀ k)`. `IsFreeLimit ρ k H`
(Library, for a family `H : ι → Subgroup G` of normal subgroups): the family is
directed downwards, every vector lies in some `ρ^{H i}`, and
`IsFreeOnInvariants ρ k (H i)` for every `i`; `ρ` is then the directed union of
the free modules `ρ^{H i}`.

`R ⧸ (ℓ ^ m)` means `R ⧸ Ideal.span {((ℓ : R) ^ m)}` for `ℓ m : ℕ`.
`powSMul ℓ m X` is the Library's multiplication by `ℓ ^ m` on an object `X`,
and for `L` with `[Mono (powSMul ℓ 1 L)]`, `reductionSystem ℓ L` is the
Library's `ℓ`-divisible system `m ↦ cokernel (powSMul ℓ m L)`, that is
`m ↦ L / ℓ ^ m L`. For an `ℓ`-divisible system `T`, `homSystem R T W`,
`T.mapLeftExact (Rep.quotientToInvariantsFunctor R K) hTK` (the system
`m ↦ (T m)^K`) and the inflation `W.map (Rep.resFunctor (QuotientGroup.mk' K))`
(written `Inf W`) are as in `FreeQuotientLimit`.

## Transport

Section `Transport`: `ρ : Representation R G V`, `σ : Representation R G W`
with `V W : Type uV`, an `R`-algebra `k`.

| Declaration | Statement |
| --- | --- |
| `IsFreeOnInvariants.of_equiv e h` | For `e : ρ.Equiv σ`, `H` normal and `h : IsFreeOnInvariants σ k H`: `IsFreeOnInvariants ρ k H`. |
| `IsFreeLimit.of_equiv e h` | For `e : ρ.Equiv σ`, a family `H` of normal subgroups and `h : IsFreeLimit σ k H`: `IsFreeLimit ρ k H`. |

## The regular representation on locally constant functions

Section `Regular`: `R : Type uR` commutative, `G : Type uG` a topological
group, `M : Type uM` an `R`-module.

`regularRepresentation R M` is defined for every topological group `G`, as
the left-translation representation on all of `LocallyConstant G M`. It is
smooth (every function is fixed by an open subgroup) when `G` is compact, by
the Library's `diagonalRepresentation_isSmooth`, which is used in
`isFreeLimit_regular`. For a noncompact `G` it need not be smooth: local
constancy is a condition on each function alone, while smoothness asks for an
open subgroup fixing it under translation. No smoothness is asserted for
`regularRepresentation` or for the constructions on it for a general `G`
(this section and the section `Reduction`).

| Declaration | Statement |
| --- | --- |
| `regularRepresentation R M` | The representation of `G` on `LocallyConstant G M` by left translation; defined as `diagonalRepresentation (X := G) (Representation.trivial R G M)` (abbreviation). |
| `regularRepresentation_apply R M g f x` | `regularRepresentation R M g f x = f (g⁻¹ * x)`. |
| `regular_invariant_apply_mul H hf x hh` | For `H` normal, `f ∈ (regularRepresentation R M)^H` and `h ∈ H`: `f (x * h) = f x`. |
| `regularInvariantsDescend H f` | For `H` normal, an `H`-invariant `f` as a function `G ⧸ H → M`, `x H ↦ f x`. |
| `regularInvariantsDescend_mk H f x` | `regularInvariantsDescend H f (QuotientGroup.mk x) = f x`. |
| `regularInvariantsPullback hH φ` | For `H` normal and open (`hH : IsOpen (H : Set G)`) and `φ : G ⧸ H → M`, the `H`-invariant locally constant function `x ↦ φ (x H)`. |
| `regularInvariantsPullback_apply hH φ x` | Its value at `x` is `φ (QuotientGroup.mk x)`. |
| `regularInvariantsEquiv hH` | For `G` compact (`[CompactSpace G]`) and `H` open and normal: an equivalence of representations of `G ⧸ H` from `(regularRepresentation R M).quotientToInvariants H` to `Induction.permutation R (G ⧸ H) (G ⧸ H) M`, `f ↦ regularInvariantsDescend H f`. |
| `isFreeOnInvariants_regular hH k I` | For `G` compact, `H` open and normal, an `R`-algebra `k : Type uk` and `I : Type uI`: `IsFreeOnInvariants (regularRepresentation R (I →₀ k)) k H`. |

## Profinite groups

Section `Profinite`: `G` a compact, totally disconnected topological group
(`[CompactSpace G] [TotallyDisconnectedSpace G]`), `k`, `I` as above.

| Declaration | Statement |
| --- | --- |
| `openNormalSubgroup_shrink G` | For every `U ∈ nhds (1 : G)` there is `N : OpenNormalSubgroup G` with `(N : Set G) ⊆ U`. |
| `isFreeLimit_regular R G k I` | `IsFreeLimit (regularRepresentation R (I →₀ k)) k (fun N : OpenNormalSubgroup G => N.toSubgroup)`. |

## Reduction modulo powers of `ℓ`

Namespace `Langlands.Cohomology.DivisibleSystem`, section `Reduction`: `R`,
`G` a topological group, `ℓ : ℕ`, `I : Type uI`, `m : ℕ`. As above, for a
general `G` the representations `regularRep R G I` and
`regularRepresentation R (I →₀ R ⧸ (ℓ ^ m))` are the left-translation
representations on locally constant functions and are not asserted to be
smooth. Only the last two rows assume `G` compact and totally disconnected,
where the representations are smooth.

| Declaration | Statement |
| --- | --- |
| `regularRep R G I` | `Rep.of (regularRepresentation R (I →₀ R))` in `Rep.{max uG uI uR} R G` (abbreviation). |
| `finsuppReduction R ℓ I m` | The `R`-linear reduction `I →₀ R → I →₀ R ⧸ (ℓ ^ m)` of the coefficients (`Finsupp.mapRange.linearMap` of the quotient map; abbreviation). |
| `regularReduction R G ℓ I m` | The morphism `regularRep R G I ⟶ Rep.of (regularRepresentation R (I →₀ R ⧸ (ℓ ^ m)))`, `f ↦ finsuppReduction R ℓ I m ∘ f`. |
| `regularReduction_hom_apply R G ℓ I m f x` | `(regularReduction R G ℓ I m).hom f x = finsuppReduction R ℓ I m (f x)`. |
| `regularReduction_surjective R G ℓ I m` | `(regularReduction R G ℓ I m).hom` is surjective; an instance gives `Epi (regularReduction R G ℓ I m)`. |
| `exists_pow_smul_of_regularReduction_eq_zero R G ℓ I m hf` | If `(regularReduction R G ℓ I m).hom f = 0`, then `((ℓ : R) ^ m) • g = f` for some `g`. |
| `powSMul_comp_regularReduction R G ℓ I m` | `powSMul ℓ m (regularRep R G I) ≫ regularReduction R G ℓ I m = 0`. |
| `regularReductionComplex R G ℓ I m` | The short complex of these two morphisms (abbreviation). |
| `regularReductionComplex_exact R G ℓ I m` | It is exact. |
| `cokernelRegularIso R G ℓ I m` | An isomorphism `cokernel (powSMul ℓ m (regularRep R G I)) ≅ Rep.of (regularRepresentation R (I →₀ R ⧸ (ℓ ^ m)))`. |
| `cokernelπ_cokernelRegularIso_hom R G ℓ I m` | `cokernel.π _ ≫ (cokernelRegularIso R G ℓ I m).hom = regularReduction R G ℓ I m`. |
| `isSMulRegular_regular R G I hℓ` | For a topological space `G` and `hℓ : IsSMulRegular R (ℓ : R)`: `IsSMulRegular (LocallyConstant G (I →₀ R)) (ℓ : R)`. |
| `mono_powSMul_regular R G I hℓ` | Under `hℓ`: `Mono (powSMul ℓ 1 (regularRep R G I))`. |
| `isFreeLimit_cokernel_powSMul_regular R G ℓ I m` | For `G` compact and totally disconnected: `IsFreeLimit (cokernel (powSMul ℓ m (regularRep R G I))).ρ (R ⧸ (ℓ ^ m)) (fun N : OpenNormalSubgroup G => N.toSubgroup)`. |
| `isFreeLimit_reductionSystem_regular R G ℓ I m` | For `G` compact and totally disconnected and `[Mono (powSMul ℓ 1 (regularRep R G I))]`: `IsFreeLimit ((reductionSystem ℓ (regularRep R G I)).obj m).ρ (R ⧸ (ℓ ^ m)) (fun N : OpenNormalSubgroup G => N.toSubgroup)`. |

## Hom systems

Section `HomSystem`: `G` compact and totally disconnected, `I`,
`[Mono (powSMul ℓ 1 (regularRep R G I))]`, a normal subgroup `K` with
`hKo : IsOpen (K : Set G)`, and `T := reductionSystem ℓ (regularRep R G I)`.
`hTK` is the hypothesis of `mapLeftExact` for the `K`-invariants functor (the
projections of `T` stay epimorphisms on `K`-invariants), `T^K` is
`T.mapLeftExact (Rep.quotientToInvariantsFunctor R K) hTK`, and
`W : DivisibleSystem (Rep.{max uG uI uR} R (G ⧸ K)) ℓ`. For the last three
rows, `p` is a prime (`hp : p.Prime`) with `hR : IsUnit (p : R)`, and
`hK : ∀ N : OpenNormalSubgroup K, IsPGroup p (K ⧸ N.toSubgroup)` (`K` is
pro-`p`).

| Declaration | Statement |
| --- | --- |
| `finiteIndex_openNormalSubgroup_subgroupOf K hKo N` | For `K` open (not necessarily normal) and `N : OpenNormalSubgroup G`: `(N.toSubgroup.subgroupOf K).FiniteIndex`. |
| `regular_invariants_homSystem_map_surjective I K hKo hTK W φ` | `(homSystem R T^K W).map φ` is surjective. |
| `isMittagLeffler_regular_invariants_homSystem I K hKo hTK W` | `homSystem R T^K W ⋙ forget` satisfies Mathlib's `IsMittagLeffler`. |
| `bijective_invariantsToCoinvariants_reductionSystem_regular I K hKo hp hR hK m` | `invariantsToCoinvariants (T.obj m).ρ K` is bijective. |
| `regular_homSystem_map_surjective I K hKo W hp hR hK φ` | `(homSystem R T (Inf W)).map φ` is surjective. |
| `isMittagLeffler_regular_homSystem I K hKo W hp hR hK` | `homSystem R T (Inf W) ⋙ forget` satisfies `IsMittagLeffler`. |

The last two rows have no hypothesis `hTK`: it is derived from the bijectivity
of the fourth row by the Library's
`epi_quotientToInvariantsFunctor_map_projection`.

## Proofs

- Transport: the invariants of an equivalence (Library
  `invariantsEquivOfEquiv`) composed with the given equivalence; exhaustion
  through `equiv_apply_mem_invariants` for `e.symm`.
- `regular_invariant_apply_mul`: invariance under left translation by
  `(x h x⁻¹)⁻¹ ∈ H` evaluated at `x` gives `f (x h) = f x`.
- `regularInvariantsEquiv`: `H` open makes `G ⧸ H` discrete
  (`QuotientGroup.discreteTopology`), hence every function on it locally
  constant, and finite for `G` compact (`Subgroup.quotient_finite_of_isOpen`),
  hence every function finitely supported (`Finsupp.equivFunOnFinite`).
  Descent and pullback are inverse pointwise; the intertwining identity is
  `f (g⁻¹ y) = (f descended) ((g H)⁻¹ (y H))`.
- `isFreeOnInvariants_regular` composes `regularInvariantsEquiv` with
  `permutationCongr` of `Finsupp.domLCongr Equiv.ulift.symm`, which moves the
  index type `I` to `ULift I` in the universe of the representation space.
- `openNormalSubgroup_shrink` is Mathlib's
  `ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one` applied to an
  open neighbourhood of `1` inside `U`. `isFreeLimit_regular` applies the
  Library's `IsFreeLimit.of_isSmooth`; smoothness of the regular
  representation of the compact group `G` is the Library's
  `diagonalRepresentation_isSmooth` (which requires the function domain `G` to
  be compact) for the trivial (hence smooth) representation on `I →₀ k`.
- `regularReductionComplex_exact`: exactness is checked after the faithful
  forgetful functor to `ModuleCat R`. A function whose reduction vanishes has
  all coefficients of all values in `(ℓ ^ m)`; dividing each by `ℓ ^ m` with
  the Library's `powDiv` gives a locally constant `g` (postcomposition with a
  function) with `ℓ ^ m • g = f`. Surjectivity of `regularReduction` lifts
  values through a right inverse of the coefficient reduction.
  `cokernelRegularIso` compares `cokernel` with the cokernel cofork of the
  exact complex with epimorphic second map (`ShortComplex.Exact.gIsCokernel`).
- `isFreeLimit_cokernel_powSMul_regular` transports `isFreeLimit_regular` with
  `k = R ⧸ (ℓ ^ m)` along `Representation.equivOfIso (cokernelRegularIso ..)`;
  the level `m` of `reductionSystem` is this cokernel by definition.
- Hom systems: the statements of `FreeQuotientLimit` with
  `hT := isFreeLimit_reductionSystem_regular`, `h0` from
  `exists_le_of_isOpen` and `openNormalSubgroup_shrink`, `hfin` from
  `finiteIndex_openNormalSubgroup_subgroupOf` (open subgroups have finite index
  in the compact subgroup `K`, closed as an open subgroup, Library
  `finiteIndex_subgroupOf_of_isCompact`), `hu` from the Library's
  `isUnit_index_subgroupOf`. Bijectivity is
  `IsFreeLimit.bijective_invariantsToCoinvariants_of_isProP`; Mittag-Leffler
  for `Hom(T m, Inf (W m))` follows from surjectivity
  (`Functor.isMittagLeffler_of_surjective`).

## Provenance and interpretation

The definitions, statements and proofs are ours, from Mathlib and the Library.
The module instantiates the Library's `IsFreeLimit`, which is modelled on the
following passages of Harris 1999, read in the rendered scans (quoted also in
`FreeQuotientLimit.md`):

- Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
  J. Math. Kyoto Univ. 39-2 (1999), 299-318 (source
  `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`).
- §2, printed p.306 (one-based PDF page 8): "Taking the direct limit as `H`
  shrinks to the identity, we obtain an `ℓ`-divisible system of complexes
  `C_m^•` of projective `ℤ/ℓ^mℤ[S(e)]`-modules".
- Proof of Proposition 4.10, printed pp.311-312 (one-based PDF pages 13-14):
  "Recall that `C^j(ẽ)` has been chosen to be a direct limit of free
  `𝒪/ℓ^m𝒪[S(ẽ)/H(ẽ)]`-modules as `H(ẽ)` varies over a family of open
  subgroups of `S(ẽ)`."
- Printed p.312 (one-based PDF page 14): "Since `C^j_m(ẽ)^{H_p}` and
  `Hom(𝒪_m[C_p/H_p]^M, 𝓛_m)` are both free `𝒪/ℓ^m𝒪[S(ẽ)/H_p]`-modules, it
  follows that the maps (4.10.3) are surjective for all `m`."

Interpretation (our reading; explanation only, not formalized). The regular
representation `LocallyConstant G (I →₀ k)` of a profinite group, which is
smooth, is the
simplest module of the kind Harris describes: its `N`-invariants are the
functions on `G ⧸ N`, that is `⊕_I k[G ⧸ N]`, and it is their union as `N`
shrinks. With `G` in the role of `S(ẽ)`, `R` of `𝒪` and `K` of
`S(ẽ) ∩ H_p`, the Hom-system statements are the surjectivity of the maps
(4.10.3) and the resulting Mittag-Leffler condition for this particular
coefficient system. The reduction system `m ↦ L / ℓ ^ m L` of the lattice
`L = regularRep R G I` is an `ℓ`-divisible system in the Library's sense when
`ℓ` is a non-zero-divisor in `R` (`mono_powSMul_regular`).

## Scope

- Harris's complexes `C_m^•` and modules `C^j_m(ẽ)` are not constructed, and
  it is not claimed that they are regular representations.
- The regular representation is taken with the coefficients `I →₀ k`, a free
  `k`-module with a chosen basis; other coefficient modules are not treated.
- In the section `HomSystem` the coefficients `W` are an arbitrary
  `ℓ`-divisible system; for an open normal `K` that is not pro-`p`, the
  hypothesis `hTK` stays explicit.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`, printed
pp.306, 311-312 (one-based PDF pages 8, 13-14), read in the rendered scans.
