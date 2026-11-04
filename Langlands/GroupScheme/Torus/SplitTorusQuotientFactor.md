# Homomorphisms into split tori factor through split-torus fppf quotients

Author: Worker 1386.

This module proves that a homomorphism from a smooth connected affine group over a field
into a split torus factors as an fppf quotient onto a split torus followed by a closed
subgroup embedding.

## Main theorem

`Langlands.GroupScheme.IsSplitTorus.exists_fppfQuotient_factor`. Let `k` be a field
(`[Field k]`, of any characteristic and not necessarily algebraically closed). Let
`H T : GroupScheme (Spec (CommRingCat.of k))` and assume:

- `H` is smooth (`[Smooth H.X.hom]`), affine (`[IsAffineHom H.X.hom]`) and connected
  (`[ConnectedSpace H.X.left]`);
- `T` is a split torus (`hT : IsSplitTorus T`).

Then every homomorphism `f : H ⟶ T` comes with a group scheme
`D : GroupScheme (Spec (CommRingCat.of k))` and homomorphisms `q : H ⟶ D` and `m : D ⟶ T`
such that

- `IsSplitTorus D`;
- `IsClosedSubgroup m`, which means that the underlying morphism of schemes of `m` is a
  closed immersion;
- `q ≫ m = f`;
- `RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (kernelι f)) q`. This means that the
  underlying morphism of schemes of `q` is flat, surjective and locally of finite
  presentation, and that the subgroup functor cut out by the kernel of `q` equals the one
  cut out by the kernel of `f`, on every test scheme.

## Provenance

This is a derived auxiliary result. It is not stated in this form in the literature. It is
the step "the image of `H` in a split torus is a split torus, and `H` maps onto it with the
same kernel" needed for the split-torus quotient of a smooth connected solvable group
(`SolvableTorusQuotientStatement`, task 9a45b06d, after Milne 2017, Theorem 16.33). The
construction is the usual one: the image of a homomorphism into a diagonalizable group
corresponds to the group of characters it pulls back. In particular, a surjection of
character groups `ℤ^I ↠ L` gives the closed embedding `D(L) ⟶ D(ℤ^I)` (Milne 2017,
Theorem 12.9(b), printed p. 233). The proof below is self-contained. It uses the Library's
diagonalizable groups and rational characters and does not rely on a general
image-of-a-homomorphism theorem.

## Construction

All auxiliary declarations are in the namespace
`Langlands.GroupScheme.SplitTorusQuotientFactor`.

- `latticeHom c : (I → ℤ) →+ rationalCharacters H` sends `n` to `∑ i, n i • c i`, for a
  finite family `c : I → rationalCharacters H`. `latticeHom_single` gives its value on the
  basis vectors.
- `charPoint L T x : Multiplicative L →* Γ(T.left, ⊤)ˣ` evaluates the characters in an
  additive subgroup `L` of `rationalCharacters H` at a point `x : T ⟶ H.X`, using the
  Library's `characterEval`. `charPointHom L T` packages it as a homomorphism from the point
  group of `H`.
- `quotientPoints L T` composes `charPointHom L T` with the inverse of the points
  equivalence `Corepresented.pointsEquiv` of the diagonalizable group
  `D(L) = Diagonalizable.groupScheme R L`, where `R = CommRingCat.of k`. Naturality in `T`
  (`quotientPoints_naturality`) follows from `Corepresented.pointsEquiv_naturality` and
  `characterEval_naturality`. `quotientHom L : H ⟶ D(L)` is the homomorphism obtained from
  these points by `homOfPoints`. `pointsEquiv_quotientHom` states that its value at a point
  `x`, read through the points equivalence, is `charPoint L T x`.
- `inclusionHom c : D(L) ⟶ D(I → ℤ)`, with `L` the range of `latticeHom c`, is the
  homomorphism `Corepresented.groupSchemeMap` given by `Diagonalizable.restrict` along
  the surjection `(latticeHom c).rangeRestrict : (I → ℤ) → L`. On schemes it is `Spec` of
  the group-algebra map `Diagonalizable.incl` (`inclusionHom_hom_left`, through
  `Corepresented.groupSchemeMap_hom_left` and `Diagonalizable.homEquiv_symm_restrict`).
  This algebra map is surjective (`Diagonalizable.incl_surjective`), so `inclusionHom c` is a
  closed immersion (`isClosedImmersion_inclusionHom`).

## The factorization

Write `T ≅ splitTorus (Spec R) I` by `e`, with `I` finite. `coordChar e f i` is the
restriction along `f ≫ e.hom` (`characterRestrict`) of the `i`-th coordinate character of
the split torus. By `characterEval_coordChar`, its value at a point is the `i`-th unit
coordinate of the image point, as given by `splitTorus.pointsEquiv`.

`quotientHom_inclusionHom_splitIso` proves
`quotientHom L ≫ inclusionHom c ≫ (Diagonalizable.splitIso R (AddEquiv.refl _)).hom = f ≫ e.hom`
for `c = coordChar e f` and `L` the range of `latticeHom c`. The proof checks this on
points (`hom_ext_points`) and in unit coordinates. It uses
`splitTorus.diagonalizable_splitIso_points`, `Corepresented.groupSchemeMap_points`,
`Diagonalizable.restrict_app_apply`, `pointsEquiv_quotientHom` and `latticeHom_single`. The
main theorem sets `D = D(L)`, `q = quotientHom L` and
`m = inclusionHom c ≫ (Diagonalizable.splitIso R (AddEquiv.refl _)).hom ≫ e.inv`. Then `m`
is a closed immersion followed by two isomorphisms, and `q ≫ m = f`.

## Kernel

`range_kernelι_comp` works over any base scheme. For homomorphisms `q : H ⟶ D` and
`m : D ⟶ G` such that the underlying morphism of schemes of `m` is a monomorphism, the
kernels of `q ≫ m` and `q` define the same subgroup functor. The proof is pointwise, through
`mem_range_kernelι_iff`. A closed immersion is a monomorphism, so the kernel of `q` is the
kernel of `f`.

## Geometry of the quotient map

From here on `H` is affine.

- `unitChar L : Multiplicative L →* (CharacterUnits.Coord H)ˣ` sends a character to its
  unit in the coordinate algebra, `CharacterUnits.unit`. `coordMap L = Diagonalizable.lift R L
  (unitChar L)` is the algebra map `k[L] → O(H)` sending the monomial of `l` to that unit.
  By `coordMap_apply` it is the `Finsupp.linearCombination` of these units.
- `coordMap_injective`: `coordMap L` is injective because distinct characters give linearly
  independent units (`CharacterUnits.linearIndependent_unit`).
- `coordinateIso_comp_quotientHom`: precomposed with the coordinate presentation
  `(Lie.coordinateIso H).hom`, the scheme map of `quotientHom L` is `Spec` of `coordMap L`
  (as `(algSpec R).map (coordMap L).op`). The proof evaluates at the universal point
  (`functor_map_charPoint`, using `Corepresented.affineSectionsIso_hom_ringHom` and
  `CharacterUnits.universalPoint_eq`). Then it compares classifying maps through
  `Corepresented.map_affineSectionsIso_pointsEquiv` and the corepresentation of `D(L)`.
- `isDominant_spec_map_of_injective`: `Spec` of an injective ring map is dominant, since its
  kernel lies in the nilradical (`PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical`).
  Hence `isDominant_quotientHom`, through `IsDominant.of_comp`.
- `isDomain_algebra` and `isIntegral_quotient`: when `H` is also smooth and connected, its
  coordinate algebra is a domain (`CharacterLatticeProof.isDomain_coord`). So the group
  algebra `k[L]` is a domain, being a subring through `coordMap L`, and `D(L)` is integral.
- `free_finite`: `L` is a free `ℤ`-module of finite rank. The proof applies
  `CharacterLattice.free_and_finite` to the images of the units in the fraction field of
  `O(H)`, as in the Library's proof of `rationalCharacterLattice`. It uses that `O(H)` is
  finitely generated (`Lie.coordinateAlgebraFiniteType`). A basis of `L` then makes `D(L)` a
  split torus (`Diagonalizable.isSplitTorus`).
- `quotientHom_fppf`: the scheme map of `quotientHom L` is flat, surjective and locally of
  finite presentation. `D(L)` is a split torus, hence smooth and locally noetherian. It is
  integral, hence reduced and irreducible. The map is of finite type and quasi-compact,
  because `H` is of finite type and affine over `k`. It is dominant. So it is flat by
  `DominantHomFlat.flat_of_isDominant` and surjective by `DominantHomFlat.surjective_of_flat`.
  It is locally of finite presentation because it is of finite type over a locally
  noetherian target.

The main theorem combines these facts. The split-torus clause comes from `free_finite` and
`Diagonalizable.isSplitTorus`, and the kernel clause from `range_kernelι_comp` applied to
`q ≫ m = f`.
