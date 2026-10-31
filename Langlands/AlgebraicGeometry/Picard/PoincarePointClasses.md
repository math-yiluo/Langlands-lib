# Classes of Poincaré pullbacks at points

Module `Langlands.AlgebraicGeometry.Picard.PoincarePointClasses`.

All declarations are in `Langlands.AbelianScheme`, for an abelian scheme `A` over `S` and
`preservation : pullbackTensorComparisonIsIsoStatement.{u}`. Classes live in the group
`LineBundle.IsoClasses` of the module `LineBundleIsoClassGroup`.

## Point classes of a family

For a rigidified family `L : RigidifiedFamily A T` (a line bundle on `T ×_S A`, parameter
first), a scheme `Z` over `S` and points `z : Z ⟶ T`, `x : Z ⟶ A.X`,

- `familyPointClass preservation A L z x` is the class of `(z, x)^* L` on `Z`, where
  `(z, x) = (pairOver A z x).left : Z ⟶ T ×_S A`; informally `[L(z, x)]`.

Its properties:

- `familyPointClass_comp`: for `h : Z' ⟶ Z`, `[L(h z, h x)] = h^* [L(z, x)]`.
- `familyPointClass_relativePullback`: for `h : T ⟶ U` and a family `L` over `U`, the class
  of the relative pullback `(h × 1)^* L` at `(z, x)` is `[L(z h, x)]`.
- `familyPointClass_tensor`: point classes are multiplicative in the family.
- `familyPointClass_congr`, `familyPointClass_eq_of_iso`: invariance under equal points and
  isomorphic families.
- `isoClass_forget_eq_familyPointClass`: the class of `L` itself is its point class at the
  tautological point `(pr₁, pr₂)` of `T ×_S A`.

Supporting lemmas: `pairOver_left_relativeSpace_map`, `comp_pairOver_left`,
`pairOver_relativeFst_relativeSnd_left` (the tautological pair is the identity),
`comp_relativeDiagonal` (`x` followed by the diagonal `A ⟶ A ×_S A` is `(x, x)`),
`pairOver_comp_mumfordFirst`, `pairOver_comp_mumfordSecond`,
`pairOver_left_mumfordAddition` (`(u, v)` followed by the addition is `u * v`), and the class
identities `isoClass_pullback_eq`, `isoClass_pullback_tensor`, `isoClass_pullback_pullback`
(pullback along a composite).

## Mumford maps have symmetric Poincaré slices

Fix a line bundle `L` on `A` with the unit-section normalization data of the Library's
`mumfordSchemeMapOfLineBundle` (a bundle `B` on `S` with `evaluationB`, and an inverse `M`
of the normalized bundle with `evaluation`), `square : MumfordBundlePicardZeroStatement.{u}`
and `hA : HasDualScheme A`. Write `Λ(L)` for `mumfordSchemeMapOfLineBundle … square hA`.

- `familyPointClass_mumfordFamily`: the class of the Mumford family of `L` at `(u, v)` is
  `[(u v)^* (L ⊗ π^* B)] · [u^* M] · [v^* M]`. This unfolds the Library's
  `mumfordFamilyOfLineBundle_forget` (the family is `m^*(L ⊗ π^*B) ⊗ p₁^*M ⊗ p₂^*M`) and
  uses `pairOver_left_mumfordAddition`.
- `familyPointClass_mumfordSchemeMap_comm`: `[P(u Λ(L), v)] = [P(v Λ(L), u)]`. Both sides are
  rewritten with `familyPointClass_relativePullback` and the Library's isomorphism
  `mumfordSchemeMapOfLineBundlePullbackIso` (the Poincaré family pulled back along `Λ(L)` is
  the Mumford family) into the expression above, which is symmetric in `u` and `v` because
  `u * v = v * u` (`A` is commutative) and the class group is commutative.
- `poincareSliceSymmetric_mumfordSchemeMap`: for every point `t : T ⟶ A.X`,
  `PoincareSliceSymmetric A hA Λ(L) t` holds. This is the previous lemma at
  `u = pr₁ ≫ t`, `v = pr₂` on `T ×_S A`, read back through `isoClass_eq_iff`.

## Provenance and purpose

Internal infrastructure for the proof of
`Langlands.AbelianScheme.PolarizationDiagonalMumfordStatement` (Mumford, Fogarty, Kirwan,
*Geometric Invariant Theory*, 3rd ed., Prop. 6.10). The symmetry of the Mumford bundle in its
two factors is the standard reason why `Λ(L)` is symmetric; here it is recorded pointwise in
terms of isomorphism classes.
