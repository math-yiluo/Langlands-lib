# Proof: rational split centre of the restriction versus the split component

Authors: Worker 112 (Lean proof and initial explanation), Worker 1467 (scope
explanation and validation).

`RestrictionSplitCentre.comparison` proves the published
`RestrictionSplitCentre.ComparisonStatement`. Let `F` be a number field, `G` an
affine group scheme over `F` that is locally of finite type, `j : S ⟶ Res G` a
split component of the published `AffineWeil.groupScheme ℚ F G`, and
`i : T ⟶ G` a split component of `G`. Then
`RestrictionSplitCentre.subgroup F G S j` equals
`PositiveRealTorus.imageSubgroup F T G i`.

The proof shows the two inclusions separately. Each inclusion uses only one of
the two maximality properties. It moves a central homomorphism from a split
torus across the restriction-of-scalars exchange of
`Langlands.GroupScheme.AffineWeilTorusAdjunction`. Then it factors the result
through the split component on the other side with
`IsSplitComponent.exists_comp_eq_of_isCentral` from
`Langlands.GroupScheme.SplitComponent.AffineTargetBridge`.

## Helper results

- `coordinates_lattice`: if `eT : T ≅ 𝔾_m^J` splits `T`, then the splitting
  coordinates of a point obtained from the lattice model through `torusIso` and
  `eT⁻¹` are given by `freeCharEquiv` of its character. `coordinates_refl`:
  with the identity splitting, coordinates are the unit coordinates of the split
  torus.
- `infinite_comp`, `finite_comp`, `ofInfinite_comp`: the infinite and finite
  components of adelic points, and inclusion at infinity, commute with
  homomorphisms of group schemes.
- `units_fst_full`, `units_snd_full`: the positive scalar idele of
  `x ∈ ℝ≥0ˣ` has infinite component `PositiveRealIdeles.infinite F x` and finite
  component `1`.
- `full_eq_ofInfinite`: let `p` be an infinite-adelic point of `T` whose
  coordinates are `PositiveRealIdeles.infinite F (s k)`. Then the positive
  adelic point `full F J T eT s` equals `ofInfinite p`. Both have the same
  infinite and finite components.
- `realDiagonal F` is the diagonal real embedding
  `PositiveRealIdeles.infiniteRealEmbedding F`, viewed as a map of
  `ℚ`-algebras from `ℝ` to the infinite adeles with scalars restricted to `ℚ`
  (`realDiagonal_apply`).
  `tensorMap_realDiagonal_multiplication`: tensoring it with `F` and then
  multiplying gives the canonical `AdelicWeilRestriction.realTensorEquiv F`.
  `realTensorEquiv_one_tmul`: `realTensorEquiv F (1 ⊗ r)` is the diagonal
  embedding of `r`.

## The image of the `F`-split component lies in the restriction's subgroup

`imageSubgroup_le_subgroup` assumes that `j` is a split component and that `i`
is a central split torus with `T` affine.

1. Choose a splitting `eT : T ≅ 𝔾_m^J`. By `subgroup_eq_intrinsicSubgroup`, a
   point of `intrinsicSubgroup F T` is `full F J T eT s` for some
   `s : J → ℝ≥0ˣ`.
2. `hT = torusIso ≫ eT⁻¹ ≫ i` is a central homomorphism from the lattice model
   of `𝔾_m^J` over `F` into `G`. Let `I = natToPoints hT` and
   `γ = AffineWeil.unitTrans ℚ G I`. Then `γ` is central
   (`isCentralNat_natToPoints`, `isCentralNat_unitTrans`), so
   `ψ = Corepresented.groupSchemeMap γ` is a central homomorphism from the
   lattice model over `ℚ` into the restriction (`isCentral_groupSchemeMap`).
3. `IsSplitComponent.exists_comp_eq_of_isCentral` for `j` gives
   `g : 𝔾_m^J ⟶ S` with `g ≫ j = torusIso⁻¹ ≫ ψ`. The coordinate algebra of
   the restriction is of finite type (`finiteType_coordinateAlgebra`).
4. Let `t` be the real point of `𝔾_m^J` with coordinates `s`. It is positive,
   so `g(t)` lies in the positive real points of `S`
   (`pointMap_mem_orderedCoefficientPositiveSubgroup`).
5. `j(g(t))` is computed through `ψ`. By `groupSchemeMap_affinePoints` and the
   definition of `realPointsEquiv`, its real-point comparison is the value of
   `I` on the character `χ ↦ realTensorEquiv F (1 ⊗ χ)`, by naturality of `I`.
   By `natToPoints_app` this is `i` applied to an infinite-adelic point `p` of
   `T`. By `coordinates_lattice` and `realTensorEquiv_one_tmul`, `p` has
   coordinates `PositiveRealIdeles.infinite F (s k)`.
6. `ofInfinite_comp` and `full_eq_ofInfinite` identify the included point with
   `i(full F J T eT s)`.

## The restriction's subgroup lies in the image of the `F`-split component

`subgroup_le_imageSubgroup` assumes that `j` is a central split torus and that
`i` is a split component with `T` affine.

1. Choose a splitting `eS : S ≅ 𝔾_m^{I₀}` over `ℚ`. The homomorphism
   `hS = torusIso ≫ eS⁻¹ ≫ j` is central, so `α = natOfHom hS` is a central
   natural homomorphism into `AffineWeil.pointFunctor ℚ F G`
   (`isCentralNat_of_isCentral`, `groupSchemeMap_natOfHom`).
2. `ℚ → F` is formally unramified (`Algebra.FormallyUnramified.of_isSeparable`)
   and essentially of finite type, and `G` is affine. So
   `β = AffineWeil.counitTrans ℚ G α` is central
   (`isCentralNat_counitTrans`), and `φ = homOfNat G _ β` is a central
   homomorphism from the lattice model over `F` into `G` (`isCentral_homOfNat`).
3. `IsSplitComponent.exists_comp_eq_of_isCentral` for `i` gives
   `f : 𝔾_m^{I₀} ⟶ T` with `f ≫ i = torusIso⁻¹ ≫ φ`.
4. Let `a` be a positive real point of `S`, and let `s : I₀ → ℝ≥0ˣ` be its
   coordinates (`mem_orderedCoefficientPositiveSubgroup_iff_coordinates`).
   The point `w₀ = full F I₀ 𝔾_m^{I₀} (Iso.refl _) s` lies in the intrinsic
   subgroup of `𝔾_m^{I₀}`. By `map_intrinsicSubgroup_le`, `f(w₀)` lies in
   `intrinsicSubgroup F T`.
5. It remains to show `i(f(w₀)) = ofInfinite (realPointsEquiv (j a))`. The left
   side is `φ` applied to the lattice point of `w₀`. By `homOfNat_affinePoints`
   and `counitTrans_app`, it is the multiplication image of `α` evaluated on a
   character `χA` with values `PositiveRealIdeles.full F (s k)`.
   The two sides are compared through `AdelicGroupPoints.split`.
   - Infinite component: `affinePointMap_multiplication_app` moves the first
     projection inside `α`. The projected character equals the image of the
     real character of `a` under `realDiagonal F`. The right side is rewritten
     with `tensorMap_realDiagonal_multiplication` and
     `affinePointMap_tensorMap_multiplication`.
   - Finite component: the second projection of `χA` is the trivial character,
     so both sides are `1`.

## Assembly

`comparison` derives that `T` is affine: `i` is a closed immersion into the
affine `G` (`IsSplitComponent` includes this), hence affine. It then combines
the two inclusions by `le_antisymm`. A split component is in particular a
central split torus. The theorem uses only the axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Scope and rank zero

The closing theorem retains the complete published proposition: an arbitrary
number field `F : Type`, an affine locally finite-type `G`, arbitrary
commutative group schemes `S` and `T`, their specified maps `j` and `i`, and
both split-component hypotheses. Affineness of `T` is derived in this theorem;
it remains an explicit assumption in the two one-sided inclusion theorems.

Neither inclusion requires the finite splitting index set to be nonempty.
Consequently the same coordinate arguments apply to the rank-zero torus,
where the coordinate conditions are vacuous and the positive image is trivial.

`realDiagonal F` embeds `ℝ` into the product of the archimedean completions of
`F`. It does not require a map `F → ℝ`; the tensor comparison sends `1 ⊗ r`
to the common real scalar at every infinite place, including complex places.
The intrinsic positive subgroup keeps finite components equal to one.

This result compares the two supplied positive adelic images. Existence or
uniqueness of split components, the greatest rational split torus of the
restriction's centre, quotient measures, finite volume and reduction theory
remain outside its conclusion.

## Provenance

This is an internal proof. The route through the restriction adjunction and
separability is the expected argument recorded in the statement's Markdown. The
implementation uses the published Library modules `AdelicRestrictionSplitCentre`,
`AdelicWeilRestrictionArchimedean`, `PositiveRealTorusIntrinsic`,
`RealSplitTorusPositiveParameters` and `RealSplitTorusAdelicComparison`, together
with the two supporting modules named above. No proof is attributed to
Getz--Hahn or Mœglin--Waldspurger.
