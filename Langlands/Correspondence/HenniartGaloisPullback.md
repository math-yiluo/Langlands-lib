# Pullback of continuous irreducible Galois classes to the local Weil group

Let `K` be a nonarchimedean local field in Mathlib's sense, of either
characteristic, `Ω` a separable closure of `K`, `G_K = Ω ≃ₐ[K] Ω` with its
Krull topology and `W_K = localWeilGroup K Ω`. The module
`Langlands.Correspondence.HenniartGaloisPullback` compares rank-tagged
continuous irreducible complex classes of `G_K` and of `W_K`
(`Weil.IrreducibleBasis`, the disjoint union over positive ranks of
`FiniteRepresentation.ContinuousIrreducibleClasses`) through restriction along
`localProjection K Ω`. It supplies the class-level steps of the proof in
[HenniartGaloisDictionaryProof.md](HenniartGaloisDictionaryProof.md). The
theorems are stated in the namespace `Langlands.Henniart.LocalNumerical`.

## Generic lemmas

- `isIrreducible_comp_iff_of_forall_exists`: if every operator `ρ h` of a
  representation `ρ` of `H` equals some `ρ (f g)`, then `ρ ∘ f` and `ρ` have the
  same subrepresentations, so one is irreducible exactly when the other is.
- `nontrivial_of_isIrreducible`, `rank_pos_of_isIrreducible`: an irreducible
  representation has a nonzero carrier and positive rank.
- `restrictClass_twistClass`: restricting the class of the twist by `χ` is twisting
  the restricted class by `χ ∘ f` (the identity map is an intertwiner).
- `exists_pow_eq_one_of_finite_range`: for two homomorphisms from a group with
  finite images and an element `g`, some positive power `g ^ m` lies in both
  kernels (pigeonhole on `n ↦ (ρ (gⁿ), ρ' (gⁿ))`).
- `underlyingClass_injective`, `irreducibleBasis_mk_injective`: a rank-tagged
  class is determined by its underlying isomorphism class, since the rank is the
  rank of that class.
- `exists_classOf_eq_underlyingClass`, `irreducibleBasisOf`: representatives of
  rank-tagged classes, and the rank-tagged class of a continuous irreducible
  representation.
- `isOpen_ker_of_isContinuous`, `finite_range_of_isContinuous`: on a
  nonarchimedean (and compact) group, a continuous complex representation has an
  open kernel (and finite image), by the Library's
  `Weil.open_kernel_of_continuous_nonarchimedean_representation` and
  `Weil.continuous_compact_nonarchimedean_representation_finite_range` with the
  coordinate norm of `FiniteRepresentation.carrierNormedAddCommGroup`.

## The pullback relation

`IsGaloisPullbackBasis K Ω b c` says that the underlying class of the Weil class
`b` is the restriction of the underlying class of the Galois class `c` along
`localProjection K Ω`. For classes of rank `k + 1` it is definitionally the
predicate `IsGaloisPullback K Ω σ ρ` of the statement module
[HenniartGaloisDictionaryStatement.md](HenniartGaloisDictionaryStatement.md);
it is the representative-free form of Henniart 1980, §2.1.

- `exists_localProjection_eq`: for continuous representations `B`, `B'` of `G_K`
  and `g ∈ G_K` there is `w ∈ W_K` with `B (proj w) = B g` and
  `B' (proj w) = B' g`. The kernels are open, so the coset of `g` modulo their
  intersection is open and meets the dense image of the projection
  (`localProjection_denseRange`).
- `isIrreducible_restrict_iff`, `isContinuous_restrict`: restriction to `W_K`
  preserves continuity and preserves and reflects irreducibility of continuous
  Galois representations.
- `exists_isGaloisPullbackBasis`: every Galois class has a Weil pullback.
- `IsGaloisPullbackBasis.weil_unique`: the pullback is unique, by
  `underlyingClass_injective`.
- `galoisBasis_eq_of_restrictClass_eq`, `IsGaloisPullbackBasis.galois_unique`:
  restriction is injective on Galois classes. A linear equivalence intertwining
  the restrictions intertwines `B g` and `B' g` for every `g`, because by
  `exists_localProjection_eq` both values are attained at one projected Weil
  element.
- `exists_twist_isGaloisPullbackBasis` (Henniart 1980, §2.3, Corollary 3):
  every Weil class has an unramified twist that is the pullback of a Galois
  class. For a continuous irreducible representative `A`, the published
  `Weil.unramifiedReduction` (with the degree map `localDegree K Ω`, whose kernel
  is open, compact and nonarchimedean by
  [SepClosedTopology.md](../Weil/Local/SepClosedTopology.md)) writes the action as
  `χ ⊗ σ₀` with `χ` trivial on inertia and `σ₀` continuous, irreducible and of
  finite image. By `localUnramifiedCharacter_eq_of_on_inertia`,
  `χ = localUnramifiedCharacter K Ω z` with `z = χ(Frob)`. The published
  `Weil.finiteImageExtension` extends `σ₀` to a continuous representation `τ` of
  `G_K` on the same carrier; `τ` is irreducible by `isIrreducible_restrict_iff`.
  The identity map intertwines the twist of `A` by `z⁻¹` with the restriction of
  `τ`.
- `galoisUnramifiedCharacter_comp_localProjection`: the pullback of a character
  in `galoisUnramifiedCharacters K Ω` is trivial on degree zero (the projection of
  degree zero lies in absolute inertia), hence equals
  `localUnramifiedCharacter K Ω` at its value at the projected Frobenius.
- `IsGaloisPullbackBasis.twist`: twisting the Galois class by such a character
  twists its pullback by that unramified character (`restrictClass_twistClass`).
- `exists_galoisCharacter_comp_eq`: a continuous character `ψ` of `W_K` with
  finite image is the pullback of a continuous character of `G_K`. The published
  `Weil.finiteImageExtension` applied to the one-dimensional representation
  `w ↦ ψ w • id` on `ℂ` gives a continuous representation `τ` of `G_K` on `ℂ`;
  `g ↦ τ g 1` is a multiplicative, continuous map to `ℂ` with invertible values
  (`MonoidHom.toHomUnits`, `Units.continuous_iff`).
- `exists_pow_eq_one_of_twist_restrict`: if the restriction of a continuous `B'`
  is isomorphic to the twist by `localUnramifiedCharacter K Ω z` of the
  restriction of a continuous irreducible `B`, then `z` is a root of unity. Both
  `B` and `B'` have finite image, so for `g` the projection of the geometric
  Frobenius some `g ^ m` with `m > 0` acts trivially in both. Evaluating the
  intertwiner at `Frob ^ m`, which has degree `m`, gives `v = z ^ m • v` for a
  nonzero vector `v`, so `z ^ m = 1`. Henniart 1988, Proposition 2.2(a), derives
  the corresponding finiteness from determinants; this file uses the action of a
  power of Frobenius instead.
- `IsGaloisPullbackBasis.exists_galoisUnramified_of_twist`: if `b`, `b'` are the
  pullbacks of `c`, `c'` and `b'` is the twist of `b` by
  `localUnramifiedCharacter K Ω z`, then `z` is a root of unity, the character
  `localUnramifiedCharacter K Ω z` has finite image and extends to a continuous
  character `χ` of `G_K` by `exists_galoisCharacter_comp_eq`. It is trivial on
  absolute inertia because absolute inertia is the projection of degree-zero
  Weil elements (`localInertiaInclusion`). Finally `c'` is the twist of `c` by
  `χ`, since both have the pullback `b'` and restriction is injective.

## Sources

- Guy Henniart, *Représentations du groupe de Weil d'un corps local*,
  L'Enseignement Math. 26 (1980), registered as
  `henniart-1980-weil-representations`: §2.1 (Galois type, density of the Weil
  group, finite image) and §2.3, Corollary 3, printed p. 158.
- Guy Henniart, *La conjecture de Langlands locale numérique pour GL(n)*,
  Ann. Sci. ÉNS 21 (1988), registered as `henniart-1988-numerical`: §2.2 and
  Proposition 2.2(a), printed pp. 503–504.
