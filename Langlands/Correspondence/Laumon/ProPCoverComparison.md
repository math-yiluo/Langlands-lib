# Pro-`p` fundamental groups of affine schemes in characteristic `p`

Katz (1986) proves Proposition (1.4.2), p. 79: for a prime `p` and an `𝔽_p`-algebra `R` with
connected spectrum, `R[T]` and `R((T⁻¹))` have connected spectra, and pullback from
`𝔸¹_R = Spec R[T]` to `Spec R((T⁻¹))` is an equivalence between the finite étale coverings with
monodromy group a `p`-group. The proof shows that the map of fundamental groups
`π₁(Spec R((T⁻¹)), x) → π₁(𝔸¹_R, y)` induces an isomorphism of maximal pro-`p` quotients:

- Lemma (1.4.3), p. 79, proved in (1.4.6), pp. 80–81: for a connected affine `𝔽_p`-scheme `Z`
  with geometric point `z`, `Hᵠ(Z_ét, 𝔽_p) ≅ Hᵠ(π₁(Z, z), 𝔽_p)` for all `q ≥ 0`, and
  `Hᵠ(Z_ét, 𝔽_p) = 0` for `q ≥ 2`; in particular `H²(π₁(Z, z), 𝔽_p) = 0`. The proof uses the
  higher vanishing on every finite étale Galois cover `Z'` (still affine), `lim H¹(Z'_ét, 𝔽_p) = 0`
  over these covers, and the limit of the Hochschild–Serre spectral sequences.
- (1.4.4), pp. 79–80: by (2.3.8.1) the maximal pro-`p` quotients of both fundamental groups are
  free pro-`p` groups. By (2.3.7) a map of free pro-`p` groups is an isomorphism if and only if
  it induces an isomorphism on continuous `𝔽_p`-characters. These are the characters of the
  fundamental group itself (2.3.8.2), that is `H¹(−, 𝔽_p)`. The degree-one Artin–Schreier
  comparison (1.4.5) gives this isomorphism.

The review of pro-`p` groups is (2.3.1)–(2.3.8), pp. 95–97, after Shatz, *Profinite groups,
arithmetic, and geometry*, Chapter III. (2.3.4) defines the free pro-`p` group `F_p(I)` as the
restricted coproduct of copies of `ℤ_p`. (2.3.5) gives the criteria for freeness of a pro-`p`
group (Shatz, Theorem 15 and Corollary 2 of Proposition 23), among them `H²(G, 𝔽_p) = 0`.
(2.3.7) is the isomorphism criterion (Shatz, Proposition 23). (2.3.8) defines the maximal pro-`p`
quotient `G → G(p)` of a profinite group, with (2.3.8.1) `H²(G, 𝔽_p) = 0 ⇒ G(p)` free and
(2.3.8.2) `H¹(G(p), 𝔽_p) ≅ H¹(G, 𝔽_p)`.

## Definitions

- `maximalProPKernel p G` is the intersection of the open normal subgroups `U` of a topological
  group `G` with `G ⧸ U` a `p`-group. It is normal (`maximalProPKernel_normal`).
- `maximalProPQuotient p G = G ⧸ maximalProPKernel p G`, with the quotient topology, is the
  maximal pro-`p` quotient `G(p)` of (2.3.8). For a profinite group every continuous homomorphism
  to a pro-`p` group is trivial on this kernel and factors uniquely through `G(p)`.
- `IsProPGroup p G` takes a prime `p` and a topological group `G`, with continuous multiplication
  and inversion. It requires `G` to be compact, Hausdorff and totally disconnected and
  `G ⧸ U` to be a `p`-group for every open normal subgroup `U`.
- `IsFreeProPGroup p G` has the same prime and topological group hypotheses. It asks for a
  pro-`p` group with a family `x : I → G` converging to `1` (each
  open normal subgroup contains all but finitely many `x i`) such that, for every finite
  `p`-group `H` and every family `h : I → H` with finitely many `h i ≠ 1`, a unique continuous
  homomorphism `G → H` (one with open kernel) sends each `x i` to `h i`. This is the universal
  property of the restricted coproduct `F_p(I)` of (2.3.2)–(2.3.4). It suffices to test it on
  finite `p`-groups, since a continuous homomorphism to a pro-`p` group is a compatible family of
  homomorphisms to its finite quotients, and a family tending to zero in the sense of (2.3.1) has
  finitely many nontrivial images in each finite quotient. The index type and the test groups
  lie in the universe of `G`, which is no restriction for finite groups.
- `HasPGroupMonodromy p t E`: the image of `π₁(Y, t) = Aut (fiber t)` in the permutations of the
  fibre of the finite étale cover `E` at `t` is a `p`-group. This is "monodromy group a
  `p`-group" in the sense of Katz (1.2.1), at the base point `t`.
- `continuousSMul_zmod_ulift` records that `ℤ/p`, discrete and lifted to a universe `u`, is a
  topological `ℤ/p`-module. The continuous cohomology below needs this coefficient module.

Continuous cohomology is Mathlib's `continuousCohomology`, the cohomology of the homogeneous
continuous cochains, with coefficients the trivial representation
`ContRepresentation.trivial (ZMod p) G (ULift (ZMod p))`. The coefficient module is lifted to
the universe of `G`, as `TopRep` requires. For a profinite group and a discrete module these are
the usual continuous cochains `G^{n+1} → 𝔽_p`.

## `AffineEtaleFundamentalGroupCohomologyStatement`

For every prime `p`, every connected affine scheme `Z` with `p = 0` in `Γ(Z, 𝒪_Z)` and every
geometric point `z : Spec Ω → Z` (`Ω` separably closed):

1. for every `q`, the étale cohomology `Hᵠ(Z_ét, ℤ/p)` (weil-conjectures's `Sheaf.H` of
   `Scheme.constantZMod`) is isomorphic, as an additive group, to the continuous cohomology
   `Hᵠ(π₁(Z, z), 𝔽_p)` of `π₁(Z, z) = Aut (fiber z)`;
2. the continuous cohomology vanishes for `q ≥ 2`.

This is Lemma (1.4.3). Clause 2 follows from clause 1 and the affine vanishing of
`ArtinSchreierComparison`. It is the input `H²(π₁(Z, z), 𝔽_p) = 0` of (1.4.4). The statement
asserts an isomorphism in each degree. In degree one, weil-conjectures's
`AlgebraicGeometry.Scheme.EtaleTorsor.sheafHEquivContinuousMonoidHom` already gives the canonical
identification `H¹(Z_ét, M) ≅ Hom_cont(π₁(Z, z), M)` for every finite abelian group `M`.

## `FreeProPComparisonStatement`

For every prime `p`:

1. for a profinite group `G` with `H²(G, 𝔽_p) = 0`, `maximalProPQuotient p G` is a free pro-`p`
   group (2.3.8.1);
2. for a profinite group `G`, every continuous homomorphism `G → 𝔽_p` factors uniquely through a
   continuous homomorphism `G(p) → 𝔽_p` (2.3.8.2);
3. for free pro-`p` groups `G₁`, `G₂` and a continuous homomorphism `φ : G₁ → G₂`, `φ` is
   bijective if and only if precomposition `χ ↦ χ ∘ φ` is a bijection from the continuous
   `𝔽_p`-characters of `G₂` to those of `G₁`, and `φ` is surjective if and only if this
   precomposition is injective (2.3.7).

A continuous bijective homomorphism of profinite groups is a topological isomorphism, so clause
3 is the isomorphism criterion of (2.3.7). The characters are continuous homomorphisms to
`Multiplicative (ZMod p)`, the multiplicative notation for the additive group `𝔽_p`. They form
the group `H¹(−, 𝔽_p)` of Katz.

## `ArtinSchreierCoverComparisonStatement`

For every prime `p` and every ring `R` with `(p : R) = 0` and connected spectrum, let
`f : Spec R((T⁻¹)) → Spec R[T]` be the spectrum of `artinSchreierLaurentHom R` of
`Langlands.Correspondence.Laumon.ArtinSchreierComparison`. Then `Spec R[T]` and
`Spec R((T⁻¹))` are connected, and for every geometric point `x` of `Spec R((T⁻¹))`:

1. weil-conjectures's `pullbackPathHom f x : π₁(Spec R((T⁻¹)), x) → π₁(Spec R[T], f ∘ x)` induces
   a bijective homomorphism of maximal pro-`p` quotients;
2. pullback along `f` (`Scheme.FiniteEtale.pullback f`) is bijective on morphisms between covers
   of `Spec R[T]` with `p`-group monodromy, preserves `p`-group monodromy, and every finite étale
   cover of `Spec R((T⁻¹))` with `p`-group monodromy is isomorphic to the pullback of a cover of
   `Spec R[T]` with `p`-group monodromy.

Clause 2 is Proposition (1.4.2), the equivalence of categories, and clause 1 is the group form in
which Katz proves it. By Galois theory for the finite étale covers of a connected scheme, the
covers with `p`-group monodromy are classified by the maximal pro-`p` quotient of `π₁`, so the two
clauses correspond. The proof route is that of (1.4.4)–(1.4.5). `AffineEtaleFundamentalGroupCohomologyStatement`
applies to both connected affine schemes, so `FreeProPComparisonStatement` (clause 1) makes both
maximal pro-`p` quotients free. By clause 2 of `FreeProPComparisonStatement`, the continuous
`𝔽_p`-characters of these quotients are those of the fundamental groups, that is `H¹(−, ℤ/p)`.
`AffineArtinSchreierCohomologyStatement` and `ArtinSchreierLaurentPolynomialStatement` show that
the map on `H¹` is bijective, and clause 3 of `FreeProPComparisonStatement` concludes.

## Declarations used

The module imports `Langlands.Correspondence.Laumon.ArtinSchreierComparison`, the
weil-conjectures module defining `pullbackPathHom`, and Mathlib's
`Mathlib.RepresentationTheory.Homological.ContCohomology.Basic` and
`Mathlib.Topology.Instances.ZMod`. From weil-conjectures it uses
`AlgebraicGeometry.Scheme.FiniteEtale`, `AlgebraicGeometry.Scheme.FiniteEtale.fiber`,
`AlgebraicGeometry.Scheme.FiniteEtale.pullback`,
`AlgebraicGeometry.Scheme.FiniteEtale.pullbackPathHom` and `AlgebraicGeometry.Scheme.constantZMod`.
Under `#print axioms` each of them depends only on `propext`, `Classical.choice` and `Quot.sound`,
and so does every declaration of this module. The cited
`AlgebraicGeometry.Scheme.EtaleTorsor.sheafHEquivContinuousMonoidHom` has the same status.
