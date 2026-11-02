# Zariski locality and gluing of relative homomorphisms

Authors: Worker 1042.

This module proves that relative homomorphisms of commutative group schemes
form a Zariski sheaf on the test scheme: they are determined by their
restrictions to an open cover, and compatible families on an open cover
glue. It works over an arbitrary base scheme `S : Scheme.{u}`, for actual
`G H : Langlands.GroupScheme.Cartier.CommGroupScheme S` and a test object
`T : Over S`. It uses the published relative-Hom interface of
`Langlands.GroupScheme.Cartier.Restriction`. In that interface,
`RelativeHom G H T` is the set of homomorphisms `G_T ⟶ H_T` of group objects
over `T.left`, `baseChangeProj G a : G_W ⟶ G_T` is the canonical projection
for `a : W ⟶ T`, and `restrict G H a` is restriction along `a`. The
point-level helpers `basePoint`, `basePoint_left`, `homEquiv_left_fst`,
`mapPullbackAdj_homEquiv_mul`, `mul_left_fst` and `isMonHom_of_mul_comp`
come from the published module
`Langlands.AbelianScheme.GroupSchemeSubalgebraDescentProof`. All
declarations live in namespace `Langlands.GroupScheme.Cartier`. The module
adds no axioms. It is a project-internal helper for the proof of
`Langlands.AbelianScheme.RelativeEndomorphismRepresentabilityStatement`. Its
content is the standard fact that homomorphisms of group schemes form a
Zariski sheaf.

## Canonical projections along open immersions

- `isPullback_baseChangeProj G a`: for `a : W ⟶ T` over `S`, the square with
  top `baseChangeProj G a`, sides the second pullback projections
  `G_W ⟶ W.left` and `G_T ⟶ T.left`, and bottom `a.left` is a pullback
  square. Proof: pasting of pullback squares (`IsPullback.of_right`), using
  `baseChangeProj_fst`, `baseChangeProj_snd` and `Over.w a`.
- Instance: if `a.left` is an open immersion, so is `baseChangeProj G a`.
  Proof: open immersions are stable under base change.
- `range_baseChangeProj G a`: the range of `baseChangeProj G a` is the
  preimage of `Set.range a.left` under `G_T ⟶ T.left`. Proof: comparison
  with `Scheme.Pullback.range_fst` through the isomorphism with the chosen
  pullback.

## Locality

- `relativeHom_eq_of_locally χ χ'`: two `χ χ' : RelativeHom G H T` are equal
  if every point `x` of `T.left` lies in the range of some `a : W ⟶ T` with
  `a.left` an open immersion and `restrict G H a χ = restrict G H a χ'`.
  Proof: by `relativeHom_ext` it is enough to compare the composites with the
  first projection `H_T ⟶ H.X.left`. Apply `Scheme.hom_ext_of_forall` on
  `G_T`. A point `y` lies in the open range of `baseChangeProj G a` for the
  `a` chosen at the image of `y` in `T.left`. On that range the two
  morphisms agree by `restrict_fst` and the hypothesis.
- `relativeHom_eq_of_forall_isAffine χ χ'`: the same conclusion if the
  restrictions agree along every open immersion from an affine scheme over
  `S`. Proof: use the members of `T.left.affineCover`.

## Relative homomorphisms through their first projections

For `m : G_T ⟶ H.X.left` with `hm : m ≫ H.X.hom = (G_T ⟶ T.left) ≫ T.hom`:

- `ptLift x₀ P` is the point `Z ⟶ G_T` built from `x₀ : Z ⟶ T.left` and a
  point `P` of `G` over `Z`. `ptMap m hm x₀ P` is the point `ptLift x₀ P ≫ m`
  of `H` over `Z`, with `ptMap_left` as its defining equation.
- `IsPtMul m hm` (a `Prop`) says that `ptMap m hm x₀` is multiplicative for
  every `x₀ : Z ⟶ T.left`, with the group structures of points of `G.X` and
  `H.X` over `S`.
- `comp_ptMap`: `ptMap` is compatible with a map of test objects
  `b : T' ⟶ T`, a morphism `e` of points over it, and `m'` with
  `baseChangeProj G b ≫ m = m'`. Proof: `pullback.hom_ext`.
- `fstMap χ` is `CommGroupScheme.hom χ ≫ (H_T ⟶ H.X.left)`. `fstMap_hom`
  gives its compatibility with the structure morphisms, and
  `fstMap_restrict` says that `fstMap (restrict G H a χ)` is
  `baseChangeProj G a ≫ fstMap χ` (the published `restrict_fst`).
- `basePoint_mul`: the published `basePoint` (points of a base change, as
  points of the original group object) is multiplicative. Proof: through the
  adjunction `Over.mapPullbackAdj` and `mapPullbackAdj_homEquiv_mul`.
- `homEquiv_left` and `ptMap_fstMap` identify `ptMap (fstMap χ)` with
  `basePoint` of the adjoint point composed with the group homomorphism `χ`.
  Then `isPtMul_fstMap χ` follows from `mapPullbackAdj_homEquiv_mul`,
  `MonObj.mul_comp` and `basePoint_mul`.
- Conversely, `liftMap m hm : G_T ⟶ H_T` over `T` is the pullback lift with
  first component `m`. `basePoint_comp_liftMap` relates its points to
  `ptMap`, and `isMonHom_liftMap` proves that it is a monoid morphism if
  `IsPtMul m hm` holds. That proof uses `isMonHom_of_mul_comp` and
  `pullback.hom_ext`. The first component comes from
  `basePoint_comp_liftMap` and `basePoint_mul`. The second is the
  structure-morphism identity. `ofFstMap m hm hmul : RelativeHom G H T` is
  the resulting homomorphism, and `fstMap_ofFstMap` says that its first
  projection is `m`.

## Gluing

Let `a i : W i ⟶ T` (`i : J`) be morphisms over `S` with every `(a i).left`
an open immersion.

- `fstMap_overlap`: suppose `χ i : RelativeHom G H (W i)` satisfy
  `restrict G H p (χ i) = restrict G H q (χ j)` whenever
  `p ≫ a i = q ≫ a j`. Then their first projections agree on the pullback of
  `baseChangeProj G (a i)` and `baseChangeProj G (a j)`. Proof: that
  pullback maps to `G_Z` for `Z` the pullback of `(a i).left` and
  `(a j).left`, and the hypothesis applies to the two projections out of
  `Z`.
- `relativeHom_exists_glue`: if moreover the ranges of the `(a i).left`
  cover `T.left`, there is `χ' : RelativeHom G H T` with
  `restrict G H (a i) χ' = χ i` for every `i`. Proof: the
  `baseChangeProj G (a i)` form an open cover of `G_T` (by
  `range_baseChangeProj`), built with `Scheme.Cover.mkOfCovers`. The
  first projections glue by `glueMorphisms` and `fstMap_overlap` to some
  `m`. Its compatibility with the structure morphisms is checked on the
  cover. Multiplicativity `IsPtMul m` is checked on the open cover of each
  point's source `Z` by the pullbacks of the `(a i).left`, using
  `comp_ptMap` and `isPtMul_fstMap (χ i)`. Then `χ' = ofFstMap m`, and the
  restriction identities follow from `relativeHom_ext`, `fstMap_restrict`
  and `fstMap_ofFstMap`.
