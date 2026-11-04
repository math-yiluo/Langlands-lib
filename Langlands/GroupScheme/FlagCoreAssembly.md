# Assembly of the covering core of the flag step

This module proves `Langlands.GroupScheme.FlagCoreDualLineStatement` (module
`Langlands.GroupScheme.FlagCoreDualLine`) from five upstream statements. These statements
are hypotheses of the final theorem and are **not** proved here. The proof applies the
linear-algebra theorem `FlagCore.exists_semiInvariant_form` (module
`Langlands.GroupScheme.FlagCoreLinear`) to the rational points of `G`. The geometric
inputs come from the modules `FlagCoreQuotient`, `FlagCoreOrbits`, `FlagCoreFixedLine` and
`FlagCoreTorus`. The only new input is the Weyl step `exists_weyl_of_isTorusFixed`.

Notation. `pt` is the base test `Over.mk (𝟙 (Spec k))`. A morphism `pt ⟶ G.X` is a rational
point of `G`. Rational points form a group: `g * h` is the product and `g⁻¹` the inverse.
`G.innerIso g` is conjugation `y ↦ g y g⁻¹` by the rational point `g`. For a matrix
representation `ρ`, `ρ.rationalMatrix` is the homomorphism from rational points to `GL m k`,
and `e_j` is the coordinate vector `Pi.single j 1`. From `FlagCoreLinear`:

- `orbitVec ρ' e g = ρ'(g) e`;
- `IsTorusFixed ρ' τ u` says that every `ρ'(τ s)` maps `u` to a scalar multiple of `u`.

`StabilizesLine σ v b` (from `FlagCoreOrbits`) says that on every test `Z`, every `Z`-point
of `G` in the range of `b` maps the image of `v` to a unit multiple of that image.

The condition `hstab` below is the hypothesis of `FlagCoreDualLineStatement`: on every test
`Z`, a point `x : Z ⟶ G.X` lies in the range of `b` if and only if `ρ.pointMatrix Z x` maps
`e_j` to a unit multiple of `e_j`. So `B` is the stabilizer of the coordinate line `j`.

All declarations are in the namespace `Langlands.GroupScheme.FlagCore`.

## Definition

- `rationalImage i` (definition): for `i : U ⟶ G`, the set of rational points of `G` of the
  form `x ≫ i.hom.hom` with `x` a rational point of `U`. It is the subset `U` of the abstract
  group passed to `exists_semiInvariant_form`.

## Lines on rational points

Here `k` is any field.

- `StabilizesLine.rational hs hx`: if `b` stabilizes the line of `v` under `σ` and the
  rational point `x` lies in the range of `b` at the base test, then
  `σ.rationalMatrix x *ᵥ v = c • v` for some `c : k`. Proof: specialize `hs` to the base
  test and apply `Scheme.ΓSpecIso` to the unit-eigenvalue equation; by
  `ΓSpecIso_hom_scalarMap` the image of `v` becomes `v` again.
- `stabilizesLine_single ρ j hstab`: under `hstab`, `StabilizesLine ρ e_j b`. Only the
  forward direction of `hstab` is used; `scalarMap` sends `e_j` over `k` to `e_j` over
  `Γ(Z.left, ⊤)`.

## The Weyl step

From here on `k` is algebraically closed. The data are as follows:

- `t : T ⟶ G` is a maximal torus (`ht : IsMaximalTorus t`);
- `b : B ⟶ G` is a Borel subgroup (`hb : IsBorelSubgroup b`);
- `ρ : MatrixRepresentation G m` and `j : m` satisfy `hstab`;
- `τ : (I → kˣ) → (pt ⟶ G.X)` has range equal to the set of rational points `z ≫ t.hom.hom`
  of the image of `t` (`hτ`).

The declarations are:

- `range_conj_le_of_isTorusFixed ht hb ρ j hstab τ hτ g hg`: if the line of `ρ(g) e_j` is
  torus-fixed (`hg : IsTorusFixed ρ.rationalMatrix τ (orbitVec ρ.rationalMatrix e_j g)`), then
  `SubgroupFunctor.range (t ≫ (G.innerIso g⁻¹).hom) ≤ SubgroupFunctor.range b`. In words,
  `g⁻¹ T g ⊆ B` on all tests. The proof is the same as steps 1 and 2 of
  `stable_of_isTorusFixed` in `FlagCoreTorus`:
  1. By `hstab` and `exists_unit_pointMatrix_iff`, a rational point `y` lies in `B` if and
     only if `ρ(y) e_j ∈ k e_j`. So if `ρ(y)` maps `ρ(g) e_j` to a multiple of itself, then
     `g⁻¹ y g` lies in `B`.
  2. `T` is smooth (`IsTorus.smooth`), hence reduced. `b` is a closed immersion. Then
     `SubgroupFunctor.range_le_of_algClosed_points` reduces the inclusion to rational points.
     A rational point of the torus is `τ s` by `hτ`, and step 1 applies to it by `hg s`.
- `exists_weyl_of_isTorusFixed htorus ht hb ρ j hstab τ hτ g₁ g₂ hg₁ hg₂`: assume also
  `[IsAffineHom G.X.hom]` and `htorus : MaximalTorusConjugacyStatement`. The statement
  `htorus` is a hypothesis and is not proved here. If the lines of `ρ(g₁) e_j` and `ρ(g₂) e_j`
  are both torus-fixed, then there is a rational point `n` with two properties:
  - for every `s` there is `s'` with `n⁻¹ * τ s * n = τ s'`;
  - `orbitVec ρ.rationalMatrix e_j (n * g₂) = c • orbitVec ρ.rationalMatrix e_j g₁` for some
    `c : k`.

  This is the hypothesis `hweyl` of `exists_semiInvariant_form`. Proof:
  1. By `range_conj_le_of_isTorusFixed`, `t ≫ (G.innerIso gₐ⁻¹).hom` factors through `b` as
     `fₐ : T ⟶ B` for `a = 1, 2` (`SubgroupFunctor.factorOfRangeLE`). The monomorphism
     facts it needs hold because `t` and `b` are closed immersions and `G.innerIso` is an
     isomorphism.
  2. `f₁` and `f₂` are maximal tori of `B`. A conjugate of a maximal torus is a maximal torus
     (`IsMaximalTorus.comp_iso`), and `IsMaximalTorus.of_comp` descends maximality along the
     closed subgroup `b`.
  3. `B` is smooth and connected (fields of `IsBorelSubgroup`), and affine over `k` because
     `b` is a closed immersion into the affine `G`. So `htorus` applies to `B`, `f₁` and `f₂`.
     It gives a rational point `β` of `B` and an isomorphism `φ : T ≅ T` with
     `f₁ ≫ (B.innerIso β).hom = groupHom φ.hom ≫ f₂`.
  4. Put `n₀ = g₂ * (β ≫ b.hom.hom) * g₁⁻¹`. A computation with `innerIso_mul_hom`,
     `comp_innerIso_hom_comp` and the factorizations of step 1 gives
     `t ≫ (G.innerIso n₀).hom = groupHom φ.hom ≫ t`. Take `n = n₀⁻¹`. Given `s`, write
     `τ s = z ≫ t.hom.hom` by `hτ`. Then `n⁻¹ * τ s * n = n₀ (τ s) n₀⁻¹` is the image under
     `t` of the rational point `z ≫ φ` of `T`, which is some `τ s'` by `hτ`.
  5. `n * g₂ = g₁ * (β ≫ b.hom.hom)⁻¹` in the group of rational points. The point
     `(β ≫ b.hom.hom)⁻¹` lies in `B`, so by `hstab` and `exists_unit_pointMatrix_iff` it maps
     `e_j` to `c • e_j`. Hence `ρ(n g₂) e_j = ρ(g₁) (c • e_j) = c • ρ(g₁) e_j`.

## The covering core

- `flagCoreDualLine_of_prerequisites hproper hconj htorus hsplit hfix :
  FlagCoreDualLineStatement.{u}`. The hypotheses are the following statements, all at
  universe `u`:
  - `hproper : SomeBorelQuotientProperStatement`;
  - `hconj : BorelConjugacyStatement`;
  - `htorus : MaximalTorusConjugacyStatement`;
  - `hsplit : TorusFiniteGaloisSplittingStatement`;
  - `hfix : SolvableProperFixedPointStatement`.

  None of them is proved in this module, so `FlagCoreDualLineStatement` holds only
  conditionally on them.

  Proof. Introduce the data of `FlagCoreDualLineStatement`:
  - the field `k`, the group `G`, and the maximal torus `t`;
  - `i : U ⟶ G` with `hthrough`: the range of `i` lies in every Borel subgroup whose range
    contains the range of `t`;
  - the Borel subgroup `b`, the representation `ρ` on `Fin (n + 1) → k`, and `j` with
    `hstab`;
  - the spanning hypothesis `hspan` and the rational point `g`.

  Apply `exists_semiInvariant_form` with:
  - the group of rational points of `G` and `ρ.rationalMatrix`;
  - `e = e_j` and `U = rationalImage i`.

  Its hypotheses are supplied as follows.
  - `e_j ≠ 0`.
  - `exists_stabilizesLine_dual hfix hb ρ` (`FlagCoreFixedLine`) gives `w₀ ≠ 0` with
    `StabilizesLine ρ.dual w₀ b`.
  - The span hypothesis is `hspan`.
  - Suppose `ρ(h) e_j = c • e_j`. Then `h` lies in `B` by `hstab` and
    `exists_unit_pointMatrix_iff`, so `h⁻¹` lies in `B`. `StabilizesLine.rational` for the
    dual representation gives `ρ.dual(h⁻¹) *ᵥ w₀ = c' • w₀`. By `rationalMatrix_dual`,
    `ρ.dual(h⁻¹)` is the transpose of `ρ(h)`, and `mulVec_transpose` turns the equation into
    `w₀ ᵥ* ρ(h) = c' • w₀`.
  - Closed orbits. `exists_proper_quotient hproper hconj hb` (`FlagCoreQuotient`) gives a
    proper `Q` and a smooth, surjective, quasi-compact `q : G.X ⟶ Q` whose fibers lie in
    left cosets of `B`. The line of `e_j` (`stabilizesLine_single`), the dual line of `w₀`,
    and the line of `e_j ⊗ w₀` under `ρ.tensor ρ.dual` (`StabilizesLine.tensor`) are
    stabilized by `B`. So `fibersStabilizeLine_of_fibersInCosets` applies to each of them.
    Then `isClosedOrbit_orbitVec`, `isClosedOrbit_dualOrbitVec` and
    `isClosedOrbit_tensorOrbitVec` (`FlagCoreOrbits`) give the three closed orbits.
  - `exists_torusDiagonal hsplit ht ρ` (`FlagCoreTorus`) gives `P`, `wt` and `τ` with
    `ρ(τ s) = P · diagonal (charValue wt s) · P⁻¹`, and the range of `τ` is the set of
    rational points of the image of `t`.
  - `hU` is `stable_of_isTorusFixed ht hb hthrough ρ j hstab τ` (`FlagCoreTorus`), applied
    to each rational point `x` of `U`.
  - `hweyl` is `exists_weyl_of_isTorusFixed htorus`.

  The result is a row vector `w` with `w ⬝ᵥ ρ(g) e_j ≠ 0`. For every element of
  `rationalImage i`, in particular every `x ≫ i.hom.hom`, there is a unit `c` with
  `w ᵥ* ρ(x ≫ i.hom.hom) = c • w`. This is the conclusion of `FlagCoreDualLineStatement`.

## Provenance

These are internal helper results for the proof of task 877d0194. They assemble a
linear-algebra replacement for part of the proof of Milne, *Algebraic Groups* (2017),
source ID `milne-2017-algebraic-groups`, Theorem 17.65 (printed pp. 374-375). The
differences from Milne's route are explained in `FlagCoreLinear.md`.

- The Weyl step `exists_weyl_of_isTorusFixed` corresponds to Milne's sentence "There exists
  an `n ∈ N_G(T)` such that `n(x_λ) = x` (see 17.53)". Milne relates two `T`-fixed points of
  `G/B` by an element of the normalizer of `T`. Here the two `T`-fixed points are the
  torus-fixed orbit lines of `ρ(g₁) e_j` and `ρ(g₂) e_j`. The normalizer element comes from
  conjugacy of maximal tori inside `B`, which is the input `MaximalTorusConjugacyStatement`
  applied to `B`. The conclusion is stated only on rational points, and `n` normalizes the
  image of `τ` rather than `T` as a subgroup scheme.
- `flagCoreDualLine_of_prerequisites` combines the inputs of `exists_semiInvariant_form`. The
  five upstream statements are standard results on Borel subgroups and tori, and this route
  needs them as inputs. They are: some Borel subgroup has proper quotients; Borel subgroups
  are conjugate (Milne 17.9(b)); maximal tori are conjugate; tori split over a finite Galois
  extension (Milne 12.18, 12.19); and smooth connected solvable groups have fixed points on
  proper schemes (the Borel fixed-point theorem, Milne 17.3). They are hypotheses here, and
  this module does not prove them.
- `rationalImage`, `StabilizesLine.rational` and `stabilizesLine_single` are internal
  infrastructure; they do not come from a source.
