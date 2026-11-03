# Proof of the properness transfer to quotients by open subgroups of stabilizers

Authors: Worker 716 (the Lean proof and this description), adapting in
`exists_factor` a draft lemma of Worker 898. Worker 1400 rechecked the module
against the current Library and added the section on the use of the hypotheses.

The module proves

```
theorem Langlands.GroupScheme.finiteIndexQuotientProperTransfer :
    FiniteIndexQuotientProperTransferStatement.{u}
```

for the published proposition of
`Langlands.GroupScheme.Absolute.FiniteIndexQuotientProperStatement`, at arbitrary
universe `u`. Fix an algebraically closed field `k`, a smooth affine `G`, closed
subgroups `iS : S ⟶ G` and `iH : H ⟶ G` with `f : H ⟶ S`, `f ≫ iS = iH` and open image of
`f`. Fix a proper `O` with a flat, surjective, quasi-compact `π : G ⟶ O` with all-test fibers
the cosets `gS`, and a supplied model `q : G ⟶ Q` by `H`. The proof shows
`UniversallyClosed Q.hom`. Separatedness and local finite type of `Q.hom` are hypotheses, so
`IsProper Q.hom` follows.

## Scheme lemmas (namespace `Langlands.GroupScheme.FiniteIndexTransfer`)

- `exists_lift_of_range_subset`: a morphism `g : Y ⟶ Z` from a reduced scheme whose image
  lies in the image of a closed immersion `i : X ⟶ Z` factors through `i`. The projection
  `pullback i g ⟶ Y` is a closed immersion. It is surjective by
  `Scheme.Pullback.exists_preimage_pullback`, hence an isomorphism by Mathlib's
  `isIso_of_isClosedImmersion_of_surjective` (target reduced). The lift is its inverse
  followed by the other projection.
- `exists_isFinite_cover`: for finitely many sections `σ i` of `p : Y ⟶ Z` (indices in a
  nonempty finset), there is `e : X ⟶ Y` with `e ≫ p` finite and every `range (σ i)` inside
  `range e`. Induction on the finset: `X = Z, e = σ a` for a singleton. Otherwise
  `X ⨿ Z` with `coprod.desc e (σ a)`, which is finite over `Z` by Mathlib's instance for
  `coprod.desc` of finite morphisms.
- `universallyClosed_of_sections`: if these sections cover `Y`, then `e` is surjective, `e ≫ p` is
  finite and hence universally closed, and `UniversallyClosed.of_comp_surjective` gives
  `UniversallyClosed p`.

## Translations and covering by rational translates

- `leftMul A s`, `rightMul A s`: left and right multiplication by a section
  `s : 𝟙_ ⟶ A.X` of a group scheme, as morphisms `A.X ⟶ A.X` over the base, with
  `comp_leftMul : c ≫ leftMul A s = (toUnit T ≫ s) * c` and
  `comp_rightMul : c ≫ rightMul A s = c * (toUnit T ≫ s)` on points `c : T ⟶ A.X`.
- `exists_finset_leftMul_cover`: let `S` be locally of finite type with compact underlying
  space over an algebraically closed `k`, and let `f : H ⟶ S` have open image `V`. Then a
  finite set `t` of rational points `s` has the following property: every point `x` of `S`
  satisfies `(leftMul S s⁻¹) x ∈ V` for some `s ∈ t`. The sets `U s = (leftMul S s⁻¹)⁻¹' V` are
  open. Each rational point lies in its own `U s`, because `s⁻¹ * s = 1` and the unit of `S` is
  the image of the unit of `H`. If the `U s` missed some point, their closed complement would
  contain a closed point (`IsClosed.exists_closed_singleton`). That point is rational by
  `pointOfClosedPoint` (Mathlib, algebraically closed base), a contradiction. Compactness
  then gives the finite subcover.

## The comparison map and the main lemma

- `exists_factor`: let `q` be flat, surjective and quasi-compact with
  `g ≫ q = h ≫ q → g⁻¹h ∈ H`, and let `π` satisfy `g⁻¹h ∈ H → g ≫ π = h ≫ π`. Then
  `π = q ≫ ρ` for some `ρ : Q ⟶ O` over `k`. Two scheme maps `a, b : Z ⟶ G` with
  `a ≫ q = b ≫ q` are made test points over `Z` by `Over.homMk`. Then `q.left` is an
  effective epimorphism (Mathlib, fpqc), and `EffectiveEpi.desc` gives `ρ.left`.
- `universallyClosed_of_isOpen_range` (the main lemma). Steps in the Lean proof:
  1. `f.left` is a closed immersion by `IsClosedImmersion.of_comp`, since `iS` is separated
     and `f ≫ iS = iH`. `S` is locally of finite type and quasi-compact over `k` through `iS`,
     so its space is compact.
  2. Points of `H` are points of `S`, so `ρ` exists by `exists_factor`.
  3. By fpqc descent of universal closedness along `π` (Mathlib
     `descendsAlong_universallyClosed_surjective_inf_flat_inf_quasicompact` through
     `MorphismProperty.of_pullback_fst_of_descendsAlong`), it suffices that the projection
     `G ×_O Q ⟶ G` is universally closed. Then `Q.hom = ρ.left ≫ O.hom` is universally
     closed.
  4. Take the finite set `t` of `exists_finset_leftMul_cover`. For `s ∈ t`, right
     multiplication by `s ≫ iS` preserves `π` (all-test fiber condition for `π` with
     `T = G`). Hence `σ s = pullback.lift (𝟙 G) (rightMul G (s ≫ iS) ≫ q)` is a section of
     `G ×_O Q ⟶ G`.
  5. `G ×_O G ⟶ G ×_O Q` (the map `pullback.map` with `q` on the second factor) is
     surjective. It is the base change of `q`, shown by `IsPullback.of_bot` from the two
     pullback squares over `π`.
  6. Covering. A point of `G ×_O Q` comes from a point `w` of `G ×_O G`. Its residue-field
     point gives `a, b : Spec κ(w) ⟶ G` with `a ≫ π = b ≫ π`, hence `a⁻¹b = c ≫ iS` for a
     point `c` of `S`. Choose `s ∈ t` with `(leftMul S s⁻¹)(c(pt)) ∈ V`. Then
     `c' = s⁻¹·c` has image in `V`, and `Spec κ(w)` is reduced, so `c'` lifts through `f` by
     `exists_lift_of_range_subset`. Since group homomorphisms preserve products and inverses
     (`MonObj.mul_comp`, `GrpObj.zpow_comp`, `GrpObj.comp_inv`), `(a·(s ≫ iS))⁻¹ b` is a
     point of `H`. So `(a·(s ≫ iS)) ≫ q = b ≫ q`, and the residue-field point of `w`
     composed into `G ×_O Q` equals `a ≫ σ s`. Applying both to the point of `Spec κ(w)`
     puts the given point in the range of `σ s`.
  7. `universallyClosed_of_sections` concludes.
- `finiteIndexQuotientProperTransfer`: unpacks the proposition, uses
  `IsProper.toUniversallyClosed` for `O`, applies the main lemma (smooth implies flat for `q`,
  and smooth affine `G` is locally of finite type and quasi-compact), and assembles
  `IsProper Q.hom` from the hypotheses `IsSeparated Q.hom` and `LocallyOfFiniteType Q.hom`.

## Use of the hypotheses

In the order of the proposition:

- `IsAlgClosed k`: only in `exists_finset_leftMul_cover`, where `pointOfClosedPoint`
  makes closed points of `S` rational.
- `Smooth G.X.hom` gives `LocallyOfFiniteType G.X.hom`, and `IsAffineHom G.X.hom` gives
  `QuasiCompact G.X.hom`. Both are passed to `S` through `iS` (step 1) for the finite
  cover by translates.
- `IsClosedSubgroup iS`: `iS` is a closed immersion. It is used for `IsClosedImmersion.of_comp`
  (a closed immersion is separated) and to transfer finite type and quasi-compactness to `S`.
- `IsClosedSubgroup iH` and `f ≫ iS = iH`: `f ≫ iS` is a closed immersion, so `f` is one
  (step 1). The equation also turns points of `H` into points of `S` (step 2) and identifies
  `d ≫ f ≫ iS` with a point of `H` in `G` (step 6).
- Openness of the image of `f`: the open sets `U s` of `exists_finset_leftMul_cover`.
- `IsProper O.hom`: only through `IsProper.toUniversallyClosed`. In step 3,
  `Q.hom = ρ.left ≫ O.hom` is then a composite of universally closed morphisms.
- `Flat`, `Surjective`, `QuasiCompact` for `π.left`: descent of universal closedness along
  `π` (step 3).
- Fiber condition for `π`, direction "`g⁻¹h ∈ S` implies `g ≫ π = h ≫ π`": in
  `exists_factor` (step 2) and for `rightMul G (s ≫ iS) ≫ π = π` (step 4). Direction
  "`g ≫ π = h ≫ π` implies `g⁻¹h ∈ S`": the point `c` of `S` in step 6.
- `IsSeparated Q.hom` and `LocallyOfFiniteType Q.hom`: assembled with the proved
  `UniversallyClosed Q.hom` into `IsProper Q.hom`.
- `QuasiCompact Q.hom`: not used.
- `Smooth q.left`: only through the implied `Flat q.left`. With `Surjective q.left` and
  `QuasiCompact q.left` it makes `q.left` an effective epimorphism in `exists_factor`.
  `Surjective q.left` is also used for the surjectivity of `G ×_O G ⟶ G ×_O Q` (step 5).
- Fiber condition for `q`, direction "`g ≫ q = h ≫ q` implies `g⁻¹h ∈ H`": in
  `exists_factor`. Direction "`g⁻¹h ∈ H` implies `g ≫ q = h ≫ q`": the equation
  `(a·(s ≫ iS)) ≫ q = b ≫ q` in step 6.

Axioms: `propext`, `Classical.choice`, `Quot.sound`.

## Dependencies

Library: `Langlands.GroupScheme.Absolute.FiniteIndexQuotientProperStatement` (the target)
and, through it, `Langlands.GroupScheme.HomogeneousQuotientStatement` (`SubgroupFunctor.range`,
`IsClosedSubgroup`, `GroupScheme`). Mathlib: `AlgebraicGeometry.AlgClosed.Basic`
(`pointOfClosedPoint`), `AlgebraicGeometry.Sites.Fpqc` (effective epimorphisms),
`AlgebraicGeometry.Morphisms.FlatDescent` (descent of universal closedness),
`AlgebraicGeometry.Morphisms.Integral` and `Finite` (finite morphisms and `coprod.desc`),
`ClosedImmersion` and `Separated`.

The route is the classical finite-map argument behind Milne, *Algebraic Groups* (2017),
5.21–5.25 and A.75–A.76 (source `milne-2017-algebraic-groups`). The implementation replaces
the finite scheme `S/H` by finitely many rational translates and sections, so it constructs
neither `S/H` nor a `G`-action on `Q`.
