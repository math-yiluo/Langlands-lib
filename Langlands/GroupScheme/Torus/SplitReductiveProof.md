# Split tori are reductive: proof

Author: Worker 207.

This module proves `Langlands.GroupScheme.IsSplitTorus.ReductiveStatement` from
`Langlands.GroupScheme.Torus.SplitReductiveStatement`. That statement has two parts. First, a
split torus over a field is a connected reductive group (`IsConnectedReductive`). Second, a split
torus over any scheme is a reductive group scheme (`IsReductive`). The final theorem is
`IsSplitTorus.reductiveStatement`. It uses only the axioms `propext`, `Classical.choice` and
`Quot.sound`.

All declarations are in the namespace `Langlands.GroupScheme`.

## Transport along isomorphisms

- `isAffineHom_of_over_iso`: if `X ≅ Y` in `Over S` and `Y → S` is affine, then `X → S` is
  affine. The structure map of `X` is the isomorphism `X ≅ Y` followed by the structure map of
  `Y`, and isomorphisms are affine.
- `connectedSpace_of_over_iso`: connectedness of the total space moves along an isomorphism over
  `S`, via the homeomorphism `Scheme.homeoOfIso`.

## The Laurent polynomial model (namespace `splitTorus`)

Fix a type `I` and a commutative ring `R`.

- `LaurentAlgebra I R` is the group algebra `AddMonoidAlgebra R (I →₀ ℤ)`. It is the Laurent
  polynomial ring `R[t_i^{±1} : i ∈ I]`.
- `coordUnit I R i` is the unit `t_i`, with inverse `t_i^{-1}`. It records the coordinates; the
  proofs below do not use it.
- `unitsFunctor I R` is the functor `A ↦ (I → Aˣ)` from commutative `R`-algebras to groups.
- `algHomEquiv I R A` is the bijection between `R`-algebra maps `LaurentAlgebra I R → A` and
  families `I → Aˣ`. It composes the universal property of `AddMonoidAlgebra.lift`, the
  correspondence between monoid maps into `A` and into `Aˣ` from a group, the universal property
  of `I →₀ ℤ` (`Finsupp.liftAddHom`), and `zmultiplesHom`. By `algHomEquiv_apply_val`, the `i`-th
  unit is the image of `t_i`.
- `corepresentableBy I R` says that `LaurentAlgebra I R` corepresents the functor of units.
- `laurentGroupScheme I R` is the group scheme over `Spec R` that the published construction
  `Corepresented.groupScheme` builds from this data. Its underlying scheme is
  `Spec (LaurentAlgebra I R)`.
- `laurentPointsEquiv I R T` identifies its points over `T` with `I → Γ(T, 𝒪_T)ˣ`, naturally in `T`
  (`laurentPointsEquiv_naturality`).
- `laurentIso I R`, for finite `I`, is an isomorphism of group schemes
  `splitTorus (Spec R) I ≅ laurentGroupScheme I R`. It is `isoOfPointModels` from
  `Langlands.GroupScheme.Torus.Split`. Both group schemes have points `I → Γ(T, 𝒪_T)ˣ`,
  naturally in `T`, compatibly with the group structure.
- `isAffineHom_laurentGroupScheme`: the structure map is `Spec` of a ring map, so it is affine.
- `connectedSpace_laurentGroupScheme`: over a field `k`, the Laurent algebra is an integral
  domain, so its spectrum is irreducible and in particular connected.

## Affineness and connectedness of split tori

- `isAffineHom_splitTorus_spec`: over `Spec R`, by `laurentIso` and
  `isAffineHom_of_over_iso`.
- `isAffineHom_splitTorus`: over any scheme `S`. The published `splitTorus.baseChangeIso`
  identifies `splitTorus S I` with the base change of `splitTorus (Spec ℤ) I` along
  `Gm.toSpecZ S : S → Spec ℤ`. In Lean, `Spec ℤ` is `Spec (ULift ℤ)` in universe `u`. The structure map of that base change is the second projection of
  a pullback. Affine morphisms are stable under base change
  (`isAffineHom_isStableUnderBaseChange.of_isPullback`), and the case `Spec ℤ` is the previous
  lemma.
- `IsSplitTorus.isAffineHom`: every split torus is affine over its base, by transport along the
  isomorphism `G ≅ splitTorus S I`.
- `IsSplitTorus.connectedSpace`: over a field, by transport along
  `G ≅ splitTorus (Spec k) I ≅ laurentGroupScheme I k`.

## The unipotent radical

Fix a homomorphism `f : H ⟶ splitTorus (Spec R) I` with `I` finite.

- `splitTorus.coordinateRepresentation f j` is the one-dimensional matrix representation of `H`
  obtained from the `j`-th coordinate of `f`. It is `f`, then the projection to the `j`-th factor
  `Gm`, then the published one-dimensional cocharacter
  `GeneralLinear.diagonalCocharacter Unit R (fun _ => 1)` of `GL_1`.
- `splitTorus.pointMatrix_coordinateRepresentation`: on a point `y` of `H`, this representation
  is the `1 × 1` diagonal matrix whose entry is the `j`-th coordinate unit of `f(y)`.

`IsSplitTorus.hasTrivialUnipotentRadical` says that a split torus `G` over a field `k` has trivial
unipotent radical. Let `i : H ⟶ G` be a homomorphism from a unipotent group scheme `H`, and fix
an isomorphism `e : G ≅ splitTorus (Spec k) I`. The proof does not use the other hypotheses
(closed immersion, smoothness, connectedness, normal image). For each `j`, apply unipotence to
`coordinateRepresentation (i ≫ e.hom) j`. This gives a nonzero fixed vector `v ∈ k¹`. For every
point `y` of `H` over a test scheme `T`, the fixed-vector equation reads `t_j · c = c`. Here
`t_j` is the `j`-th coordinate of `e(i(y))` and `c` is the image of `v` in `Γ(T, 𝒪_T)`. Since
`v ≠ 0` in the field `k`, `c` is a unit, so `t_j = 1`. All coordinates of `e(i(y))` are `1`, so
`i(y) = 1`, because `isoPointsEquiv e` and `splitTorus.pointsEquiv` are injective and
multiplicative. Hence `SubgroupFunctor.range i = ⊥`.

## Reductivity

- `IsSplitTorus.isPseudoReductive`: over a field, from the published `IsSplitTorus.smooth`
  and from `IsSplitTorus.isAffineHom`, `IsSplitTorus.connectedSpace` and
  `IsSplitTorus.hasTrivialUnipotentRadical` above.
- `IsSplitTorus.isConnectedReductive`: over a field `k`, the same fields. The geometric condition
  applies `hasTrivialUnipotentRadical` to the base change along `toAlgebraicClosure k`. That base
  change is a split torus by the published `IsSplitTorus.baseChange`.
- `IsSplitTorus.isReductive`: over a scheme `S`, smoothness and affineness as above. For each
  point `s`, the geometric fibre `geometricFiber G s` is a split torus over a field by
  `IsSplitTorus.baseChange`, hence pseudo-reductive.
- `IsSplitTorus.reductiveStatement` combines the last two.

## Relation to the literature

The statement's Markdown cites Milne, *Algebraic groups* (2017), Corollary 19.18, which derives
reductivity from a faithful semisimple representation. This proof does not go through
semisimplicity. It checks the definition used in `Langlands.GroupScheme.Reductive.Basic`
directly: a unipotent subgroup of a split torus has trivial image under every coordinate
character, because a one-dimensional representation of a unipotent group is trivial (Milne 6.45:
every nonzero representation has a nonzero fixed vector). The Laurent polynomial ring
`R[t_i^{±1}]` is the usual coordinate ring of `Gm^I`. Here it is built from the published
corepresentability API (`Corepresented.groupScheme`) and compared with `splitTorus` through
points.

## Authorship

Worker 207 authored the proof and this explanation, first shared as revision 1
of this task's public draft. Worker 1173 rechecked the pair in the pinned
environment and submitted it. Worker 1173 left the Lean unchanged and changed
the Markdown only by noting that `coordUnit` is unused, that `Spec ℤ` is
`Spec (ULift ℤ)` in Lean, and by adding this paragraph. Development compilation
does not establish independent review.
