# Proof that the dynamic cell of a smooth connected solvable group is the whole group

`Langlands.GroupScheme.solvableDynamicCell` proves the unchanged published
proposition `Langlands.GroupScheme.SolvableDynamicCellStatement.{u}` (from
[`Dynamic.SolvableCellStatement`](SolvableCellStatement.md)) for every
universe `u`, with no additional hypotheses.

For every field `k : Type u`, every group scheme `G` over `S = Spec k` with
`Smooth G.X.hom`, `IsAffineHom G.X.hom`, `ConnectedSpace G.X.left` and
`IsSolvableGroupScheme G`, every cocharacter `χ : 𝔾_m ⟶ G`, and all
homomorphisms `iU : U ⟶ G`, `iP : P ⟶ G` that represent `Dynamic.unipotent (-χ)`
and `Dynamic.parabolic χ`, the ordered multiplication
`SubgroupFunctor.cellMultiplication iU iP : U × P ⟶ G`, `(u, p) ↦ iU(u) iP(p)`,
is an isomorphism of schemes over `S`. Here `-χ` is
`CommGroupScheme.groupHom (Gm.powerHom S (-1)) ≫ χ`.

## Route

The proof does not use Milne's induction on `dim G`. It uses three published
results instead: the open-cell theorem over a field, the decomposition
`G = G_u ⋊ T` of a smooth connected solvable group over an algebraically closed
field, and the published criterion that an open cell whose two factors are
smooth and unipotent covers a connected affine group. Base change to `k̄`
reduces the general case to the algebraically closed case.

## Auxiliary lemmas (namespace `Langlands.GroupScheme.SolvableDynamicCell`)

- `preimage_isPullback`: for group-scheme homomorphisms `n : N ⟶ G` and
  `iP : P ⟶ G`, the group-scheme pullback `pullback n iP` (the preimage of `P`
  in `N`) gives a pullback square of the underlying objects over `S`. The
  forgetful functor `Grp (Over S) ⥤ Over S` preserves this limit.
- `comp_cellMultiplication`: precomposing the cell multiplication with a point
  `m` of `U × P` gives the product of the two coordinates of `m`, each pushed
  into `G`.
- `cell_isPullback`: suppose `a : U ⟶ N` satisfies `a ≫ n = iU`. Then the square
  with top `cellMultiplication a (pullback.fst n iP) : U × P' ⟶ N`, left side
  `U ◁ (pullback.snd n iP) : U × P' ⟶ U × P`, bottom
  `cellMultiplication iU iP` and right side `n` is a pullback square over `S`.
  Here `P' = pullback n iP`. The lift of a pair `(x ∈ N, (u, p) ∈ U × P)` with
  `n(x) = iU(u) iP(p)` is `(u, (a(u)⁻¹ x, p))`. The point `a(u)⁻¹ x` lies over `p`
  in the preimage square because `n(a(u)⁻¹ x) = iU(u)⁻¹ iU(u) iP(p) = iP(p)`.
  Uniqueness follows from the joint monicity of the projections.
- `smooth_of_isOpenImmersion_cellMultiplication`: let `U` be smooth and
  quasi-compact over `S`, let `N` be smooth, and let `P` be locally of finite
  presentation over `S`. If the cell multiplication `U × P ⟶ N` of `a : U ⟶ N`
  and `p : P ⟶ N` is an open immersion, then `P` is smooth over `S`. The proof
  writes `U × P → S` as `cell ≫ (N → S)`, an open immersion followed by a
  smooth morphism. The projection `U × P → P` is smooth, quasi-compact and
  surjective, since it has the section `x ↦ (1, x)`. Smoothness then descends by
  `AlgebraicGeometry.Smooth.of_comp_of_smooth_of_surjective_of_locallyOfFinitePresentation`.
- `range_le_parabolic_of_factor`: if a cocharacter has the form `c ≫ s`, where
  `s : T ⟶ G` is a homomorphism from a commutative group scheme, then the range
  of `s` lies in `Dynamic.parabolic (c ≫ s)`. Commutativity of `T` shows that
  every point of `T` is fixed by conjugation by `c`. So the range of `s` lies in
  the centralizer, which `Dynamic.centralizer_le_parabolic` places inside the
  parabolic.

## The algebraically closed case: `isIso_cellMultiplication_of_isAlgClosed`

Let `k` be algebraically closed and keep the hypotheses of the target.

1. **Open immersion.** `dynamicFieldOppositeCell` shows that
   `cellMultiplication iU iP` is an open immersion on underlying schemes.
2. **A maximal torus through `χ`.** `IsSplitTorus.exists_factor_isSplitSubtorus`
   applied to the split torus `𝔾_m` (`isSplitTorus_gm`) factors `χ = π ≫ i`
   through a closed split subtorus `i : D ⟶ G`.
   `EnvelopeInfiniteReduction.exists_isMaximalTorus_factor` factors `i = f ≫ s`
   through a maximal torus `s : T ⟶ G`. So `χ = (π ≫ f) ≫ s`.
3. **The unipotent part.** `solvableMaximalTorusSemidirect` gives a closed,
   smooth, connected, unipotent subgroup `n : N ⟶ G` that contains every
   closed unipotent subgroup of `G`, such that the multiplication
   `subgroupMultiplication n s : N × T ⟶ G` is an isomorphism.
4. **The first factor lies in `N`.** `iU` is a closed subgroup
   (`Dynamic.Affine.isClosedSubgroup_of_isRepresentedBy_unipotent`). It is
   smooth (`dynamicSmooth`) and unipotent (`dynamicUnipotentUnipotence`). By the
   maximality of `N`, the range of `iU` lies in the range of `n`, and
   `IsRepresentedBy.factorHom` gives `a : U ⟶ N` with `a ≫ n = iU`.
5. **The cell inside `N`.** Let `P' = pullback n iP`. Then
   `pullback.fst n iP : P' ⟶ N` is a closed immersion, the base change of the
   closed immersion `iP`
   (`Dynamic.Affine.isClosedSubgroup_of_isRepresentedBy_parabolic`). So `P'` is
   a closed subgroup of the unipotent group `N`, and `unipotentClosedSubgroup`
   shows that `P'` is unipotent. `cell_isPullback` shows that the cell
   `cellMultiplication a (pullback.fst n iP) : U × P' ⟶ N` is a base change of
   the open immersion of step 1, so it is an open immersion. By
   `smooth_of_isOpenImmersion_cellMultiplication`, `P'` is smooth.
   `SubgroupFunctor.isIso_cellMultiplication_of_unipotent` (connected affine
   `N`, smooth affine unipotent factors, open cell) shows that this cell is an
   isomorphism.
6. **`T` lies in the parabolic.** `range_le_parabolic_of_factor` and step 2 show
   that the range of `s` lies in `Dynamic.parabolic χ`. So
   `IsRepresentedBy.factorHom` gives `τ : T ⟶ P` with `τ ≫ iP = s`.
7. **A section.** Let `w = (subgroupMultiplication n s)⁻¹ : G ⟶ N × T` and
   `e = w ≫ fst ≫ (cellMultiplication a (pullback.fst n iP))⁻¹ : G ⟶ U × P'`.
   Put `σ = (e₁, iP-coordinate of e₂ · τ(w₂)) : G ⟶ U × P`, where `e₂` is mapped
   to `P` by `pullback.snd n iP`. A computation with the commutativity of the
   preimage square and `a ≫ n = iU` gives
   `σ ≫ cellMultiplication iU iP = w ≫ subgroupMultiplication n s = 𝟙`.
   The cell multiplication is therefore a split epimorphism. It is also a
   monomorphism, since its underlying morphism is an open immersion. Hence it
   is an isomorphism.

## Reduction to the algebraic closure: `solvableDynamicCell`

Let `K = AlgebraicClosure k` and `b : Spec K ⟶ Spec k`. Write `B` for base change
of group schemes along `b`.

- The cell over `k` is an open immersion (`dynamicFieldOppositeCell`).
- `B G` is smooth, affine and connected (`connectedSpace_baseChange_of_connected`).
  It is solvable by `solvableFieldExtensionStatement`.
- `B iU` and `B iP` represent the unipotent and parabolic subgroups of the
  base-changed cocharacter. This uses `IsRepresentedBy.baseChange`,
  `Dynamic.unipotent_baseChange`, `Dynamic.parabolic_baseChange` and
  `Dynamic.baseChangeCocharacter_powerHom`.
- By the algebraically closed case,
  `cellMultiplication (B iU) (B iP)` is an isomorphism.
  `DynamicBaseOppositeCell.baseChange_cellMultiplication` identifies the base
  change of the original cell with this isomorphism, composed with the product
  comparison isomorphism. So the base-changed cell is surjective.
- Surjectivity descends along the surjective morphism `b`
  (`fieldExtension_fpqc`, `surjective_overHom_of_baseChange`). A surjective open
  immersion is an isomorphism (`isIso_iff_isOpenImmersion_and_surjective`), and
  `Over.forget` reflects isomorphisms, so the original cell is an isomorphism.

Only the standard axioms `propext`, `Classical.choice` and `Quot.sound` are
used.

## Provenance

The proved assertion is J. S. Milne, *Algebraic Groups* (Cambridge University
Press, 2017), Proposition 16.35, printed p.337 (source ID
`milne-2017-algebraic-groups`). The statement Markdown records how the source
corresponds to the Lean encoding. Milne proves the proposition by reducing to
`k` algebraically closed and inducting on `dim G` with a central `𝔾_a` in
`G_u`. The proof here keeps the reduction to `k̄` but replaces the induction with
the published semidirect decomposition `G = G_u ⋊ T` (Milne, Theorem 16.33) and the
published closed-orbit criterion for open cells with unipotent factors. The
auxiliary lemmas in `SolvableDynamicCell` are internal steps of this proof.
