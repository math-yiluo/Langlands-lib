# Torus actions on algebra points from automorphic actions of split tori

This module connects actions of a split torus on a group scheme, given as
`AutomorphicAction (splitTorus (Spec R) I) G`, with the algebraic torus-action layer of
`Langlands.GroupScheme.Rational.TorusGrading`. That layer works with a group-valued functor
`F : CommAlgCat R ⥤ GrpCat` corepresented by an algebra `B`, and with a `TorusAction F I`:
an action of unit families `t : I → Aˣ` on `F.obj A`, natural in the `R`-algebra `A`. The
module has five parts.

- Actions are carried along an isomorphism of group schemes, and stability of a subgroup
  functor transfers to its preimage under the inverse isomorphism. This lets a statement about
  an arbitrary affine group `G` be moved to its corepresented model
  `Corepresented.groupScheme F e`.
- An automorphic action of the split torus on a corepresented group scheme gives a
  `TorusAction F I`, and the original action is computed by it on every test scheme. As a
  consequence, the subgroup functors cut out by ideals stable under that `TorusAction`, in
  particular the weight subgroups, are stable under the automorphic action.
- Smoothness of an affine group scheme gives formal smoothness and finite type of its
  coordinate algebra.
- A cut-out subgroup whose coordinate algebra is a polynomial algebra in finitely many
  variables is smooth, connected (over a domain) and, over a field, a smooth connected closed
  subgroup functor in the sense of `RelativeRoot.IsSmoothConnectedClosed`. That property is
  carried along isomorphisms of the ambient group.
- A splitting of a split torus `S` over a field identifies the characters of `S` with exponent
  vectors in `I → ℤ`, and a character's value on a point is the monomial in the unit
  coordinates with that exponent vector.

All declarations are in namespace `Langlands.GroupScheme`. Throughout, `S` is a scheme (in
the first part), `R : CommRingCat.{u}`, `I : Type u` is finite, and `algΓ R`, `algSpec R` and
`algΓAlgSpecAdjunction R` are Mathlib's relative global sections, relative spectrum and the
adjunction between them.

## Transport along isomorphisms

For an isomorphism of group schemes `ψ : G' ≅ G`, `iso_hom_inv_hom ψ` and `iso_inv_hom_hom ψ`
state the two inverse identities for the underlying morphisms of schemes over `S`.

`AutomorphicAction.transport b φ ψ` turns an action `b : AutomorphicAction H G` into an action
`AutomorphicAction H' G'`, for a homomorphism `φ : H' ⟶ H` and an isomorphism `ψ : G' ≅ G`.
Its action morphism is `(φ ⊗ ψ.hom) ≫ b.hom ≫ ψ.inv`. On points (`transport_act`):

`(b.transport φ ψ).act h g = b.act (h ≫ φ) (g ≫ ψ.hom) ≫ ψ.inv`.

The helper `lift_comp_transportHom` is this identity before it is packaged as an action.
`act_eq_transport b ψ φ`, for an isomorphism `φ : H ≅ H'`, recovers `b` from
`b.transport φ.inv ψ`:

`b.act h g = (b.transport φ.inv ψ).act (h ≫ φ.hom) (g ≫ ψ.inv) ≫ ψ.hom`.

For a subgroup functor `U` of `G'` and `ψ : G' ≅ G`, the existing `SubgroupFunctor.comap`
gives the subgroup functor `U.comap ψ.inv` of `G`, whose points over `T` are the
`x : T ⟶ G.X` with `x ≫ ψ.inv` in `U`. Stability transfers to it
(`AutomorphicAction.isStable_transport`): if `U` is stable under `b.transport φ.inv ψ`, then
`U.comap ψ.inv` is stable under `b`. (That `U.comap ψ.inv` is represented by `j ≫ ψ.hom`
when `U` is represented by `j`, with closedness preserved, is the existing
`SubgroupFunctor.IsRepresentedBy.comp_iso` and `IsClosedSubgroup.comp_iso`.)

## From automorphic actions to torus actions on algebra points

In namespace `Langlands.GroupScheme.Corepresented`, `F : CommAlgCat R ⥤ GrpCat` is corepresented
by `B` through `e`, and `groupScheme F e` is the corresponding group scheme over `Spec R`. Its
points over a test scheme `T` correspond to `F.obj` of the global sections of `T`
(`pointsEquiv F e T`), and its points over `Spec A` correspond to `F.obj A`
(`affinePointsEquiv F e A`).

- `pointsEquiv_unit_comp`: for a point `y` over the relative affinization
  `(algSpec R).obj ((algΓ R).obj T)` of `T`, the composite of the adjunction unit with `y` has
  the same coordinates as `y`.
- `affineFactor e x` is the factor of a point `x : T ⟶ (groupScheme F e).X` through the relative
  affinization, and `unit_comp_affineFactor` states that the unit followed by `affineFactor e x`
  is `x`.
- `torusPt I A t` is the point of the split torus over `Spec A` with unit coordinates
  `t : I → Aˣ`. `torusPt_naturality` states that composing it with `Spec` of an algebra map
  `g : A ⟶ A'` gives `torusPt I A' (Units.map g ∘ t)`.

`TorusAction.ofAutomorphicAction e b` is the `TorusAction F I` induced by an action
`b : AutomorphicAction (splitTorus (Spec R) I) (groupScheme F e)`: a family of units `t` acts
on `x : F.obj A` by acting with `torusPt I A t` on the point of `groupScheme F e` over `Spec A`
with coordinates `x`. The torus-action axioms follow from the action axioms of `b`, and
naturality in `A` follows from the naturality of `b` and of `torusPt`.

The action `b` is computed by this torus action:

- `affinePointsEquiv_act`: over `Spec A`, the coordinates of `b.act s x` are the
  torus-action image of the coordinates of `x` under the unit coordinates of `s`.
- `exists_pointsEquiv_act`: over any test scheme `T`, for points `s` of the torus and `x` of
  the group, there are units `t` of the global sections of `T` such that the coordinates of
  `b.act s x` are `(TorusAction.ofAutomorphicAction e b).act t` applied to the coordinates of
  `x`. The proof factors `s` (by `Lie.affinizationFactor`, the split torus being affine over
  `Spec R`) and `x` (by `affineFactor`) through the relative affinization of `T`, and uses
  naturality of `b` and `affinePointsEquiv_act` there.

Consequently (`isStable_cutSubgroupFunctor`), if a family `H` of subgroups of `F.obj A` is cut
out by an ideal `J` of `B` and every `H A` is stable under the induced torus action, then the
subgroup functor `cutSubgroupFunctor` of `groupScheme F e` cut out by `J` is stable under `b`.
In particular (`isStable_weightSubgroup`), for every additive subsemigroup `P` of `I → ℤ`, the
subgroup functor cut out by the weight ideal `weightIdeal e σ P` of the induced torus action
`σ = TorusAction.ofAutomorphicAction e b` is stable under `b`.

## Smoothness of the coordinate algebra

For an affine group scheme `G` over `Spec R`, `AffineCoordinates.algebra G` is its coordinate
algebra. If `G.X.hom` is smooth, then this algebra is formally smooth over `R`
(`AffineCoordinates.formallySmooth_algebra`) and of finite type over `R`
(`AffineCoordinates.finiteType_algebra`). Both come from the existing
`AffineCoordinates.smooth_algebra`, which states that it is smooth over `R`.

## Smooth connected cut subgroups with polynomial coordinates

In namespace `Langlands.GroupScheme.Corepresented`, let `H` be a family of subgroups of
`F.obj A` cut out by an ideal `J` of `B` (`hJ : IsCutOutBy e H J`), so that `cutGroupScheme hJ`
is the group scheme corepresented by `B ⧸ J`. Let `x : κ → B ⧸ J` be a family indexed by a type
`κ` such that `MvPolynomial.aeval x : MvPolynomial κ R → B ⧸ J` is bijective, so `B ⧸ J` is a
polynomial algebra with variables `x`.

- `smooth_cutGroupScheme_of_bijective hJ hx`: if `κ` is finite, the structure morphism of
  `cutGroupScheme hJ` is smooth. Through the existing `smooth_groupScheme_iff` this is
  smoothness of `B ⧸ J` over `R`, which is transported from the polynomial algebra along the
  algebra isomorphism `MvPolynomial κ R ≃ₐ[R] B ⧸ J`.
- `connectedSpace_cutGroupScheme hJ hx`: if `R` is a domain, the underlying space of
  `cutGroupScheme hJ` is connected. Indeed `B ⧸ J` is then a domain, being isomorphic to a
  polynomial ring over a domain, so its spectrum is irreducible.

In namespace `Langlands.GroupScheme.RelativeRoot`, over a field `k`:

- `isSmoothConnectedClosed_cutSubgroupFunctor hJ hx` (with `κ` finite): the subgroup functor
  `Corepresented.cutSubgroupFunctor hJ` of `groupScheme F e` is smooth, connected and closed
  (`IsSmoothConnectedClosed`). The witnesses are `cutHom hJ`, which represents it and is a
  closed subgroup embedding by the existing `isRepresentedBy_cutHom` and
  `isClosedSubgroup_cutHom`, together with the two results above.
- `IsSmoothConnectedClosed.comap_iso hU ψ`: for affine group schemes `G`, `G'` over `Spec k`,
  an isomorphism `ψ : G' ≅ G` and a smooth connected closed subgroup functor `U` of `G'`, the
  subgroup functor `U.comap ψ.inv` of `G` is smooth connected closed. If `U` is represented by
  `j : K ⟶ G'`, it is represented by `j ≫ ψ.hom`, with the same `K`.

## Exponent vectors of characters

Let `k` be a field, `S` a commutative group scheme over `Spec k`, and
`φ : S.toGrp ≅ splitTorus (Spec k) I` a splitting.

`characterExponents φ : characterLattice S ≃+ (I → ℤ)` is the composite of two existing
Library equivalences: `characterLattice.comapIso φ.symm`, which sends a character `χ` of `S`
to the character `φ.inv ≫ χ` of the split torus, followed by
`splitTorus.characterLatticeEquiv k I`, which sends a character of the split torus to its
exponent vector. Nothing is reconstructed here.

`pointsEquiv_characterExponents φ χ s` gives the value of the character `χ` on a point
`s : T ⟶ S.X`. Write `t i` for the `i`-th unit coordinate of the split-torus point `s ≫ φ.hom`
and `m = characterExponents φ χ`. Then the unit of the global sections of `T` given by
`s ≫ χ` (through `Gm.pointsEquiv`) is `∏ i, t i ^ m i`.

## Provenance

This is an internal supporting module for the proof of
`Langlands.GroupScheme.RelativeRoot.CyclicWeightFiltrationStatement`, whose Lean route goes
through explicit coordinate algebras. The mathematical setting is Conrad–Gabber–Prasad,
*Pseudo-reductive groups*, 2nd ed., Lemma 3.3.8 and its proof (printed pp. 111–112), where an
action of a split torus on an affine group is treated through the induced grading of its
coordinate algebra. The results here are the standard translation between a torus action on
a group scheme and the corresponding action on algebra-valued points. They are dictionary
lemmas and do not formalize a particular statement of that source.
