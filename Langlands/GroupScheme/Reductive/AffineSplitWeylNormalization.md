# Weyl normalization of opposite root pairs over an arbitrary commutative ring

Module `Langlands.GroupScheme.Reductive.AffineSplitWeylNormalization`. The statement and its
proof are in namespace `Langlands.GroupScheme`; the lemmas are in namespace
`Langlands.GroupScheme.AffineSplitWeylNormalization`.

## Statement

`AffineSplitSimpleRootGroupStatement : Prop` (universe `u`) says the following. Let `R` be
any commutative ring and `G` a reductive group scheme over `Spec R` with affine structure map.
Let `i : 𝔾_m^I → G` be a closed coordinate split torus, maximal on every residue-field fibre
(`IsFibrewiseMaximalTorus`). Let `P` be a root datum on the coordinate lattices that is the root
datum of the torus on every field-valued fibre (`IsFibrewiseRootDatumOf`). Assume every root space
`splitTorus.exponentWeightSpace I G i (P.root α)` is free of rank one over `R`. Then for every base
`b` of `P` there is a family `u : J → (Ga R ⟶ G)` with two properties. First, for every simple
root `a`, `u a` is a root parametrization for `a` and `u (P.reflectionPerm a a)` is one for `-a`.
Second, the Weyl point `weylPoint (u a) (u (-a))`, which is `u_{-a}(-1) u_a(1) u_{-a}(-1)`, acts on
the torus through the simple reflection `P.reflection a` (`IsWeylPoint`).

The conclusion is word for word that of `LocalSplitSimpleRootGroupLocalStatement` (module
`LocalSplitIsomorphismAssembly`). That statement assumes a local base ring; here the base is
arbitrary and the root spaces are assumed free. Freeness is also a hypothesis of the target
`AffineSplitIsomorphismTheoremStatement`.

`affineSplitSimpleRootGroup : AffineSplitSimpleRootGroupStatement.{u}` proves it. It is
`exists_simpleRootFamily_of_free` below, with the statement's binders.

## Main results

```
theorem exists_unit_weylNormalization_global (hG : IsReductive G)
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G) (hi : IsClosedSubgroup i)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    {J : Type u} {P : RootDatum J (I → ℤ) (I → ℤ)} (hP : IsFibrewiseRootDatumOf I G i P)
    (b : P.Base) (fam : J → (Ga R ⟶ G))
    (hfam : ∀ α, IsRootParametrization i (P.root α) (fam α)) {a : J} (hpos : b.IsPos a) :
    ∃ d : Rˣ, IsWeylPoint i (weylPoint (fam a) (scaleHom (d : R) ≫ fam (P.reflectionPerm a a)))
      (P.reflection a)

theorem exists_simpleRootFamily_of_free (hG : IsReductive G)
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G) (hi : IsClosedSubgroup i)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    {J : Type u} {P : RootDatum J (I → ℤ) (I → ℤ)} (hP : IsFibrewiseRootDatumOf I G i P)
    (hfree : ∀ α : J, Nonempty
      (splitTorus.exponentWeightSpace I G i (P.root α) ≃ₗ[CommRingCat.of R] CommRingCat.of R))
    (b : P.Base) :
    ∃ u : J → (Ga R ⟶ G),
      (∀ a ∈ b.support, IsRootParametrization i (P.root a) (u a) ∧
        IsRootParametrization i (P.root (P.reflectionPerm a a)) (u (P.reflectionPerm a a))) ∧
      ∀ a ∈ b.support,
        IsWeylPoint i (weylPoint (u a) (u (P.reflectionPerm a a))) (P.reflection a)
```

Throughout, `R` is an arbitrary commutative ring in universe `u` (no localness, reducedness or
field hypothesis), `G` is a reductive group scheme over `Spec R` with affine structure map,
`i` is a closed coordinate split torus `𝔾_m^I → G`, maximal on every residue-field fibre, and
`P` is a root datum on the coordinate lattices that is the root datum of the torus on every
field-valued fibre (`IsFibrewiseRootDatumOf`).

`exists_unit_weylNormalization_global` says: given root parametrizations `fam α` of all roots
and a root `a` that is positive for the base `b`, the parametrization of `-a`
(`P.reflectionPerm a a`) can be rescaled by a unit `d` of `R` so that the Weyl point
`v(-1) u(1) v(-1)` (`weylPoint`) of `u = fam a` and `v = fam (-a)(d ·)` acts on the torus
through the reflection `s_a` (`IsWeylPoint`).

`exists_simpleRootFamily_of_free` says: if every root space
`splitTorus.exponentWeightSpace I G i (P.root α)` is free of rank one over `R` (the hypothesis
of the target `AffineSplitIsomorphismTheoremStatement`), then for every base `b` there are root
parametrizations of the simple roots and their negatives whose Weyl points act by the simple
reflections. Its conclusion is word for word the conclusion of
`LocalSplitSimpleRootGroupLocalStatement` (module `LocalSplitIsomorphismAssembly`), which is
stated over local rings; here the base is arbitrary.

## Provenance

These are internal lemmas for the proof of `AffineSplitIsomorphismTheoremStatement`
(Conrad, *Reductive group schemes* (2014), Theorem 6.1.17). The literature counterpart of the
Weyl normalization is Conrad, Cor. 5.1.9(1): `w_a(X) = exp_a(X) exp_{-a}(-X⁻¹) exp_a(X)`
normalizes the torus and induces `s_a`, with `X⁻¹` the dual section from the Lie algebra
pairing. The route below (a dual-number coefficient in the big cell, checked at local-ring
points) is internal to this project and is not taken from the literature. It extends the
reduced-local argument of `LocalWeylNormalizationProof` to arbitrary rings, using the
published local results `LocalSplitCell.exists_unit_weylNormalization` and
`localSplitRootPairLaws` in place of the field case.

## The proof of `exists_unit_weylNormalization_global`

1. **The big cell.** `a` is positive and `-a` is not, since its height is `-height a`.
   Enumerate the negative and positive roots with `Finite.equivFin`. By
   `LocalSplitBigCell.isOpenImmersion_cellMap` (any commutative ring) the big-cell map
   `cellMap i fam neg pos` is an open immersion. Let `kn`, `kp` be the indices of `-a` and `a`.
2. **The dual-number coefficient.** `LocalWeylNormalization.exists_dualCellLift` writes the
   point `u(1) v(ε)` over `R[ε]` as `y ≫ cellMap`. Let `c := -snd X`, where `X ∈ R[ε]` is the
   `u`-coordinate `posCoord y kp` read through `Γ(Spec R[ε]) ≅ R[ε]`.
3. **Local algebras (`key`).** Let `A` be a local commutative `R`-algebra. The base changes of
   `G`, `i`, `P` and the root maps to `A` keep all hypotheses (`hG.baseChange`,
   `IsClosedSubgroup.baseChange`, `splitTorus.isFibrewiseMaximalTorus_baseChangeHom`,
   `IsFibrewiseRootDatumOf.baseChange_implicit`, `isRootParametrization_baseChangeRoot`).
   The root `P.root (-a)` is `-P.root a`. So the local theorem
   `LocalSplitCell.exists_unit_weylNormalization` gives `δ ∈ Aˣ` such that the Weyl point of
   `u_A` and `v_A(δ ·)` acts by `s_a`. Then `localSplitRootPairLaws` gives the four rank-one
   laws for this pair (`RankOneLaws`). `algebraMap_snd_posCoord_of_rankOneLaws` (below) turns
   the fourth law into `algebraMap R A c = δ⁻¹`.
4. **`c` is a unit.** Otherwise `c` lies in a maximal ideal `M`
   (`exists_max_ideal_of_mem_nonunits`). Step 3 for `A = R_M` makes the image of `c` a unit,
   contradicting `IsLocalization.AtPrime.isUnit_to_map_iff`.
5. **The answer** is `d := c⁻¹`. For every local `R`-algebra `A`, with `δ` as in step 3, the
   image of `c⁻¹` in `A` is `δ`. So the base change of `v(c⁻¹ ·)` to `A` is `v_A(δ ·)`
   (`LocalSplitRootBaseChange.baseChangeRoot_scaleHom`), and the Weyl-point property holds
   over `A`. `isWeylPoint_of_localBaseChange` (below) gives it over `R`.

## The proof of `exists_simpleRootFamily_of_free`

It copies the proof of the published `localSplitSimpleRootGroupLocal`, with two
substitutions. Root parametrizations `u α` of all roots come from
`LocalRootGroup.exists_rootParametrization_of_free_weight` (using `hfree`). For each simple root
`a` the unit `d a` comes from `exists_unit_weylNormalization_global`, applied to the family
`u`. The family `u'` agrees with `u` away from the negatives of simple roots. At `-a`, for `a`
simple, it is `u(-a)(d a ·)`, which is a root parametrization by `IsRootParametrization.scale`.
This is well defined because a negative simple root is not simple and `a ↦ -a` is injective.

## Auxiliary results

### Weyl points from local-ring points (`section WeylLocal`)

- `isWeylPoint_apply_of_baseChange`: let `A` be a commutative `R`-algebra. If the Weyl point
  of the base-changed root maps `baseChangeRoot A u`, `baseChangeRoot A v` acts through `f`
  on the base-changed torus, then the Weyl point of `u, v` satisfies `n t n⁻¹ = f(t)` on every
  test scheme over `Spec A`, regarded over `Spec R`. This is the computation of
  `LocalWeylNormalization.isWeylPoint_apply_of_baseChange` for an arbitrary algebra instead
  of a field, using `baseChangePointsEquiv` and `splitTorus.exponentIso_baseChange`.
- `isWeylPoint_of_localBaseChange`: if `G` has affine structure map and this holds after base
  change to every local commutative `R`-algebra, then `IsWeylPoint i (weylPoint u v) f`.
  The identity is an equality of two morphisms from a test scheme `Z` into the affine scheme
  `G`. By `CellGluing.hom_ext_of_localRingPoints` it suffices to compare them on points
  `x : Spec A ⟶ Z.left` with `A` local. Make `A` an `R`-algebra through `x ≫ Z.hom`
  (`Spec.preimage`), regard `x` as a morphism over `Spec R` from `Spec A`, and apply the
  previous lemma.

### The dual-number computation over an algebra (`section RingCoord`)

- `ringDualMap`: the `R`-algebra map `R[ε] → k[ε]`, `r + sε ↦ r + sε`, for an `R`-algebra `k`;
  `ringDualMap_eps` and `snd_ringDualMap` compute it.
- `ringDualUnit c`: the unit `1 + cε` of `k[ε]`, with inverse `1 - cε`.
- `testOverHom_appTop`, `testOverHom_rootPoint`, `testOverHom_torus`, `baseScalar_testOver`,
  `ringDualMap_appTop_epsSec`: the algebra versions of the corresponding field lemmas of
  `LocalWeylNormalizationProof`. They move root values, torus values, base scalars and the
  section `ε` between the test scheme `Spec D` over `Spec k` and over `Spec R`.
- `algebraMap_snd_posCoord_of_rankOneLaws`: suppose `u(1) v(ε) = y ≫ cellMap` over `R[ε]`,
  and over an `R`-algebra `k` the base changes `u_k` and `v_k(d ·)`, for a unit `d` of `k`,
  satisfy `RankOneLaws`. Then the `ε`-coefficient of the `u`-coordinate of `y` maps to
  `-d⁻¹` in `k`. Proof: over `k[ε]` the fourth (Bruhat) law, applied to `u_k` and
  `v_k(d ·)` with `x = 1`, `y = d⁻¹ε` and the unit `U = 1 + d⁻¹ε` (so `U⁻¹ = 1 - d⁻¹ε`), gives
  `u_k(1) v_k(ε) = v_k(d U⁻¹ d⁻¹ε) · ν(U) · u_k(U⁻¹)`, with `ν` the cocharacter of the laws.
  Read over `Spec R` this is a big-cell point with `u`-coordinate `U⁻¹`. The pullback of `y` along `R[ε] → k[ε]` is another
  cell lift of the same point. Since the cell map is a monomorphism,
  `LocalWeylNormalization.posCoord_eq_of_cellPoint_eq` identifies the two `u`-coordinates.
  So the image of the coordinate is `1 - d⁻¹ε`, whose `ε`-coefficient is `-d⁻¹`.
