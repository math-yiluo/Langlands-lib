# Tame covers of the punctured line

Laumon (1987), (2.2.2), pp. 156–157, passes from local to global through the punctured line
`𝔾_m = ℙ¹_k − {0, ∞}`. He writes `ξ` for the generic point of the henselization of `𝔸¹_k` at `0`
and `ξ → 𝔾_m` for the map induced by `k[u, u⁻¹] ⊆ k{u}[u⁻¹]`. He considers the quotients
`π₁(𝔾_m, ξ̄) → π₁(𝔾_m, ξ̄)^{mod ∞} → π₁(𝔾_m, ξ̄)^{mod}` classifying the finite étale covers of
`𝔾_m` tamely ramified at `∞`, respectively at `0` and `∞`. Lemme (2.2.2.1), p. 157, says that the
induced maps `ξ^{mod} : π₁(ξ, ξ̄)^{mod} → π₁(𝔾_m, ξ̄)^{mod}` and their geometric versions over
`k̄` are isomorphisms. In its proof both geometric tame groups are identified with
`Ẑ'(1)(k̄) = lim μ_N(k̄)`, `p ∤ N`: the first by (2.1.1), p. 151, the second by the Kummer covers
of Remarque (1.1.3.7), p. 140. The Kummer cover `v^N = u` of `𝔾_m ⊗ k̄` restricts to the Kummer
cover of `ξ ⊗ k̄` with the same equation. Katz (1986), (1.1)–(1.2), pp. 71–74, sets up tameness
at an end, monodromy and geometric monodromy of finite étale coverings of `𝔾_m` and the
constant-field exact sequences (1.1.4.1) and (1.1.5.1).

This module provides `𝔾_m`, the maps of the end traits to it, the local monodromy maps into
`π₁(𝔾_m)`, tameness at an end and the two statements above. Throughout, `k` is a field with
`p = ringChar k`. The end traits, their fields and points are those of
`Langlands.Correspondence.Laumon.Traits`: `endField k` is the separable closure of `k(t)` in
`k((t))`, `Ω = endGenericClosure k` its separable closure, and the four ends `FourierEnd` differ
by the coordinate pulled back to `t`.

## Conventions

- **Fundamental groups.** For a geometric point `t : Spec Ω' → Y`, `π₁(Y, t)` is
  `Aut (Scheme.FiniteEtale.fiber t)`, the automorphism group of weil-conjectures's finite étale
  fibre functor. weil-conjectures uses the same group in `Scheme.FiniteEtale.pullbackPathHom`
  and `ProEtale.LisseMonodromy.rep`.
- **Quotients.** For a property `P` of finite étale covers, `coverKernel t P` is the common
  kernel of the actions of `π₁` on the fibres at `t` of the covers with `P`: the automorphisms
  acting trivially on all of them. When the covers with `P` form a full Galois subcategory of
  the finite étale covers of a connected scheme, as the covers tame at given ends do, the
  quotient of `π₁` by this kernel classifies exactly the covers with `P`. A homomorphism out of
  that quotient is a homomorphism out of `π₁` trivial on the kernel. No quotient group is
  formed.

## Definitions

- `lineCoordinate k` is the coordinate `x` of `affineLine k`.
- `gmOpen k` is the basic open `x ≠ 0` of `affineLine k`: the punctured line
  `𝔾_m = Spec k[x, x⁻¹]`. `gmStructure k` is its structure map to `Spec k`. `gmCoordinate k` is
  the restriction of `x`, a unit (`gmCoordinate_isUnit`), and `gmConstantHom k` gives the
  constants. The instances `gmOpen_isAffine`, `gmStructure_smooth`,
  `gmOpen_isLocallyNoetherian`, `gmOpen_isRegular`, `gmOpen_nonempty` and `gmOpen_isIntegral`
  record that `𝔾_m` is affine, smooth over `k`, Noetherian, regular, nonempty and integral. They
  are the hypotheses of weil-conjectures's `ProEtale.universalLisseMonodromy`, used for lisse
  sheaves on `𝔾_m` in `Langlands.Correspondence.Laumon.CanonicalExtension`.
- `gmKummerCover k n hn`, for `n ≥ 1` with `p ∤ n`, is the finite étale power-map cover
  `u ^ n = x` of `𝔾_m`. It is weil-conjectures's `Scheme.kummerFiniteEtale` of `n`-th roots of
  `gmCoordinate k`, and `n` is a unit on `𝔾_m` by `gmNatCast_isUnit`. Remarque (1.1.3.7), p. 140,
  takes only the exponents `n` such that `k` contains a primitive `n`-th root of unity. For these
  `n` the cover is the underlying cover of Laumon's Kummer extension of `𝔾_m` by `μ_n(k)`. Over
  the algebraically closed field of the geometric statement below, every `n` prime to `p` has
  this property.
- `puncturedEndToGm k e : η_e → 𝔾_m` is the lift of `puncturedEndToLine k e` through the open
  immersion `𝔾_m → 𝔸¹`. The lift exists because the coordinate pulls back to the unit `t ^ ε`
  (`range_puncturedEndToLine_subset`). At `0` (and `0'`) this is Laumon's `ξ → 𝔾_m`, `x ↦ t`;
  at `∞` (and `∞'`) it is `x ↦ t⁻¹`.
- `FourierEnd.opposite` exchanges `0 ↔ ∞` and `0' ↔ ∞'`.
- `gmEndPoint k e` is the geometric point of `𝔾_m` at the end `e`: the geometric generic point
  `fieldGeometricPoint (endField k) Ω` of `η_e` (from
  `Langlands.Correspondence.Laumon.FieldMonodromy`) followed by `puncturedEndToGm k e`.
- `gmLocalMonodromy k e : Gal(Ω/endField k) → π₁(𝔾_m, gmEndPoint k e)` composes
  `fieldGaloisToAut`, the identification of the Galois group with `π₁(η_e)` of the bridge
  (b1), with `pullbackPathHom (puncturedEndToGm k e)`, the map `π₁(η_e) → π₁(𝔾_m)` induced by
  base change of covers. This is Laumon's `π₁(ξ, ξ̄) → π₁(𝔾_m, ξ̄)`.
- `gmGeometricSubgroup k t` is the kernel of `π₁(𝔾_m, t) → π₁(Spec k)` induced by
  `gmStructure k`. By the exact sequence (1.1.4.1) of Katz, which cites SGA 1, IX 6.1, it is the image of
  `π₁(𝔾_m ⊗ k^sep)`, the geometric fundamental group.
- `endTameField k` is the subfield of `Ω` generated over `endField k` by the constants
  `endConstants k` and the `N`-th roots of the uniformizer `t`, for all `N ≥ 1` prime to `p`.
  For a perfect field `k`, in particular a finite or an algebraically closed one, this is the
  maximal tamely ramified extension of the henselian end field.
  `endWildInertia k` is its fixing subgroup, the wild inertia `P` of Laumon (2.1.1).
- `IsTameCoverAt k e E` says that `endWildInertia k` acts trivially, through
  `gmLocalMonodromy k e`, on the fibre of the finite étale cover `E` of `𝔾_m` at
  `gmEndPoint k e`. Equivalently, the restriction of `E` to `η_e` splits over the tame closure:
  `E` is tamely ramified at the end.
- `IsTameLisseAt k ℓ e F` says that `endWildInertia k` acts trivially on the field monodromy
  (`fieldMonodromy`) of the pullback of the lisse sheaf `F` to `η_e`.
- `coverKernel t P` is the kernel described under Conventions, a subgroup of
  `Aut (fiber t)` for any scheme.

**Tameness and the completion.** Tameness is defined on the henselian end trait. For a finite
field `k`, clause 4 of `HenselianCompletionRamificationStatement` in
`Langlands.Correspondence.Laumon.Completion` characterizes the image of the Library's
`Langlands.Ramification.Local.localWildInertia` of `LaurentSeries k` under
`completionRestriction k`. It consists of the automorphisms fixing `endUnramifiedField k` and
every `N`-th root of `t`, `p ∤ N`. These are exactly the elements of `endWildInertia k`, as an
automorphism fixes a generated subfield if and only if it fixes the generators. So `endWildInertia
k` is the Library's wild inertia carried over by the bridge (b2). The field-theoretic
description also makes sense when `LaurentSeries k` is not a local field, for instance over an
algebraically closed field, where the geometric statement below is formulated.

## `GeometricTameKummerCofinalityStatement`

For every algebraically closed field `κ`:

1. for every `n ≥ 1` with `ringChar κ ∤ n`, the Kummer cover `gmKummerCover κ n hn` is a connected
   object of the Galois category of finite étale covers (`PreGaloisCategory.IsConnected`) and is
   tame at `0` and at `∞`;
2. every connected finite étale cover of `𝔾_m` tame at `0` and at `∞` is isomorphic to
   `gmKummerCover κ n hn` for some such `n`.

So the Kummer covers are cofinal among the connected geometric covers tame at both ends. This is
the identification `π₁(𝔾_m ⊗ k̄)^{mod} ≅ Ẑ'(1)(k̄)` that Laumon uses in the proof of (2.2.2.1),
through the Kummer covers of (1.1.3.7). The statement asserts it as a classification of covers;
Laumon states the identification with a reference to (2.1.1) and (1.1.3.7). The proof route uses the tame Riemann–Hurwitz formula
`CurveRiemannHurwitzDifferentStatement` of `Langlands.Correspondence.Laumon.CurveRiemannHurwitz`.
For a connected cover of degree `n`, let `D` be the normalization of `ℙ¹` in it. Tame
Riemann–Hurwitz with boundary terms `e_y − 1` gives `2g(D) − 2 = −r₀ − r_∞`, for the numbers
`r₀, r_∞` of points over `0, ∞`. Hence `g(D) = 0` and there is a single point over each end. A
degree-one function `u` with divisor `[0_D] − [∞_D]`, from genus-zero Riemann–Roch, then
satisfies `u ^ n = c x`. Rescaling gives `u ^ n = x`, and tameness gives `p ∤ n`.

## `TamePuncturedLineEquivalenceStatement`

For a finite field `k` and every end `e`, write `ρ = gmLocalMonodromy k e` and let `N` be
`coverKernel (gmEndPoint k e)` of the covers tame at `0` and at `∞`, the kernel of
`π₁(𝔾_m) → π₁(𝔾_m)^{mod}`. Then:

1. `ρ(σ) ∈ N` if and only if `σ ∈ endWildInertia k`;
2. every `g ∈ π₁(𝔾_m)` satisfies `g⁻¹ ρ(σ) ∈ N` for some `σ`;
3. `ρ` maps the inertia group, the automorphisms fixing `endUnramifiedField k`, into the
   geometric fundamental group `gmGeometricSubgroup k (gmEndPoint k e)`;
4. every element `g` of the geometric fundamental group satisfies `g⁻¹ ρ(σ) ∈ N` for some
   inertia element `σ`.

Clauses 1 and 2 say that `ρ` induces a bijective homomorphism from the tame quotient
`Gal(Ω/endField k)/P` onto `π₁(𝔾_m)/N`. As a continuous bijective homomorphism of compact
Hausdorff groups, it is an isomorphism of topological groups: Laumon's `ξ^{mod}`. Clauses 3 and 4
give the same for the inertia group `I` and the geometric fundamental group, and the
inertia-geometric bijection `I/P → π₁(𝔾_m ⊗ k̄)/N` is Laumon's geometric map. Here
`N ⊆ gmGeometricSubgroup` because constant covers are tame. The two bijections fit into a map
of short exact sequences
`1 → I/P → Gal(Ω/endField k)/P → Gal(k̄/k) → 1` and
`1 → π₁(𝔾_m ⊗ k̄)/N → π₁(𝔾_m)/N → Gal(k̄/k) → 1`,
where `π₁(𝔾_m ⊗ k̄)` is `gmGeometricSubgroup k (gmEndPoint k e)`. The restriction maps lie
over the identity of the constant Galois group `Gal(k̄/k)`. The global row is the two-ended
analogue of Katz's sequence (1.1.5.1), p. 73. Katz's sequence uses the covers tame at `0` only,
and its quotient is strictly larger in characteristic `p`. For example, the Artin–Schreier cover
`yᵖ − y = x` is étale across `0` but wildly ramified at `∞`. The same holds at both ends. At `∞` the uniformizer is `t = x⁻¹`, and the roots of `x`
generate the same tame closure as the roots of `t`.

## The prime `p` and the field

`TamePuncturedLineEquivalenceStatement` is the case of a finite field `k` of Laumon's Lemme
(2.2.2.1), p. 157, at either end. Laumon works over a perfect field of characteristic `p`
((0.1), p. 134, recalled in (2.1.1), p. 151). The restriction to finite fields is the setting of
the canonical extension and its applications here.
`GeometricTameKummerCofinalityStatement` is stated for every algebraically closed field. In
characteristic `0`, `ringChar κ = 0` and the condition `p ∤ n` is `n ≠ 0`. All covers are then
tame and the statement is the classical description of the connected covers of `𝔾_m`.

## Declarations used

The module imports `Langlands.Correspondence.Laumon.FieldMonodromy`,
`Langlands.Correspondence.Laumon.Completion` (for the instance that `endGenericClosure k` is a
separable closure of `endField k`) and three modules of weil-conjectures. From the Library it
uses `FourierEnd`, `endField`, `endRing`, `endUniformizer`, `endGenericClosure`,
`endConstants`, `endUnramifiedField`, `puncturedEnd` and `puncturedEndToLine` of
`Langlands.Correspondence.Laumon.Traits`, and `fieldGeometricPoint`, `fieldGaloisToAut` and
`fieldMonodromy` of `Langlands.Correspondence.Laumon.FieldMonodromy`. From weil-conjectures it
uses `AlgebraicGeometry.affineLine`, `AlgebraicGeometry.affineLine.isoSpecPolynomial`,
`AlgebraicGeometry.affineLine.isoSpecPolynomial_inv_mem_basicOpen_iff`,
`AlgebraicGeometry.Scheme.isUnit_of_basicOpen_eq_top`,
`AlgebraicGeometry.Scheme.kummerFiniteEtale`, `AlgebraicGeometry.Scheme.FiniteEtale`,
`AlgebraicGeometry.Scheme.FiniteEtale.fiber`,
`AlgebraicGeometry.Scheme.FiniteEtale.pullbackPathHom`, `AlgebraicGeometry.IsRegular`,
`AlgebraicGeometry.IsRegular.of_smooth`, `AlgebraicGeometry.ProEtale.LisseSheaf` and
`AlgebraicGeometry.ProEtale.LisseSheaf.upperStar`. Under `#print axioms` each of them depends only
on `propext`, `Classical.choice` and `Quot.sound`, and so does every declaration of this module
(`FourierEnd.opposite` depends on no axiom).
