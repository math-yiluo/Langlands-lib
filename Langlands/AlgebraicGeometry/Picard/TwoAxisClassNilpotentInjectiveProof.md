# Nilpotent injectivity (strong F5) for the two-axis class presheaf

Worker 386 wrote this module for Task 6296. It proves the published proposition
`Langlands.AlgebraicGeometry.Picard.NoetherianTwoAxisClassNilpotentInjectiveStatement`
as the theorem
`Langlands.AlgebraicGeometry.Picard.noetherianTwoAxisClassNilpotentInjective`,
in every universe `u`.

The target says: for every noetherian ring `R` and every Library abelian scheme
`A` over `Spec R`, the two-axis class presheaf `classPresheaf A` satisfies
Murre's condition `NilpotentInjective`. That is, for every local artinian ring
`B`, every nilpotent ideal `I` of `B` and every `f : Spec B ⟶ Spec R`, the class
restriction along `algebraOverBase f (B ⧸ I)` is injective.

The module proves something stronger: injectivity holds for every local ring `B`
(not necessarily artinian or noetherian), every proper ideal `I`, and every
morphism `Spec B ⟶ S` to an arbitrary base scheme `S`. The main input is the
published theorem `localTwoAxisTriviality`.

## Notation

`cl` is `LineBundle.isoClass` and `pb f` is the group homomorphism
`LineBundle.pullbackHom f` on isomorphism classes of line bundles. Both are
taken with the published `pullbackTensorComparisonIsIso`.

## Private helpers (namespace `TwoAxisRigidifiedLineBundle`)

- `pb_isoClass_eq_one_iff`: `pb f (cl L) = 1` exactly when the module pullback
  of `L` along `f` is isomorphic to the structure sheaf.
- `pb_injective_of_isIso`: `pb f` is injective when `f` is an isomorphism of
  schemes. Proof: apply `pb (inv f)` and use the composition and identity laws
  for `pullbackHom`.
- `exists_isoClass_eq`: every isomorphism class has a representative.
- `carrierClass L`: the class of the underlying line bundle (carrier) of a
  two-axis-rigidified line bundle `L`. By `pb_isoClass_eq_one_iff`, the first
  and second rigidifications of `L` give `pb i (carrierClass L) = 1` and
  `pb j (carrierClass L) = 1` (`pb_first_carrierClass`,
  `pb_second_carrierClass`).
- `compProductInv_comp_hom`: `compProductInv A b ≫ compProductHom A b = 𝟙`.
  The published `compProductHom_inv` proves the composite in the other order.
  The proof uses pullback extensionality and the projection lemmas
  `cartesianSelfProductMap_fst` and `cartesianSelfProductMap_snd`.
- `exists_factor_productMap`: let `T : Over S` and `b : W ⟶ T.left`. A morphism
  `k` into the self-product of `abelian A T` whose structure map equals `w ≫ b`
  factors through `productMap A (compTestHom b)`. The factor is
  `pullback.lift k w _`, followed by the inverse of
  `mumfordProductBaseChangeIso (abelian A T) b` and then `compProductInv A b`.
  The proof uses the published `compProductHom_baseChangeMap` and
  `mumfordProductBaseChangeIso_hom_fst`.
- `firstAxis_comp` and `secondAxis_comp`: for an abelian scheme `G` over `B`,
  `π₀ := Over.prodLeftIsoPullback G.X G.X` identifies the categorical
  self-product `(G.X ⨯ G.X).left` with the explicit fibre product. Composed with
  `π₀.hom`, the two axes in the form used by `localTwoAxisTriviality`,
  `prod.lift (𝟙 G.X) (!G.X ≫ 1)` and `prod.lift (!G.X ≫ 1) (𝟙 G.X)`, become
  `mumfordSection G` and `twoAxisSecond G`. The proof checks both pullback
  projections.

## Injectivity over local rings

`classesPullback_injective_local` (public) takes a local ring `B`, a proper ideal
`I`, and `g : Spec B ⟶ S`. Let `b := Spec.map (algebraMap B (B ⧸ I))`. The
theorem says that `classesPullback A` along `compTestHom b` from `Over.mk g` is
injective. Proof:

1. Take classes of rigidified bundles `L` and `M` with equal images.
   `Quotient.exact` gives an isomorphism of their relative pullbacks. Its image
   under the inclusion of the full subcategory and
   `TwoAxisRigidifiedModule.forget` is an isomorphism of the pullbacks of the
   carriers along `productMap A (compTestHom b)`. So `carrierClass L` and
   `carrierClass M` have equal images under `pb (productMap A (compTestHom b))`.
2. Let `G := abelian A (Over.mk g)` and
   `c := pb π₀.hom (carrierClass L / carrierClass M)`, a class on
   `(G.X ⨯ G.X).left`.
3. Axes: by `firstAxis_comp` and `secondAxis_comp`, the pullbacks of `c` along
   the two axes are `pb` of `carrierClass L / carrierClass M` along
   `mumfordSection G` and `twoAxisSecond G`. These are the rigidification axes
   of `L` and `M`, so both pullbacks equal `1 / 1 = 1`.
4. Closed fibre: let `s` be the closed point of `Spec B`. Since `I` is proper,
   `I` lies in the maximal ideal, so `algebraMap B κ(s)` factors through
   `ψ : B ⧸ I →+* κ(s)` (`Ideal.Quotient.lift`). With Mathlib's
   `Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField`, the map
   `Spec κ(s) ⟶ Spec B` equals
   `Spec.map (residueFieldIso _ s).inv ≫ Spec.map ψ ≫ b`. With
   `Scheme.Hom.fiber_fac`, the structure map of
   `fiberι s ≫ π₀.hom` therefore factors through `b`. By
   `exists_factor_productMap`, `fiberι s ≫ π₀.hom = l ≫ productMap A
   (compTestHom b)` for some `l`. So the pullback of `c` to the fibre is
   `pb l` of the quotient of two equal classes (step 1), which is `1`.
5. Choose a line bundle `Λ` with `cl Λ = c`. By `pb_isoClass_eq_one_iff`,
   steps 3 and 4 say that `Λ` is trivial on both axes and on the fibre at `s`.
   The structure map of `G.X` is smooth, proper and geometrically connected
   (instances of the Library abelian scheme), and the sections are the units
   `1`. The published `localTwoAxisTriviality` gives an open `U ∋ s` over which
   `Λ` is trivial. In a local ring every open set containing the closed point
   is everything (`IsLocalRing.closedPoint_mem_iff`), so `U = ⊤`. Then
   `pullback.fst (G.X ⨯ G.X).hom U.ι` is an isomorphism, because `U.ι` is
   (`Scheme.topIso`). By `pb_injective_of_isIso`, `c = 1`.
6. `pb π₀.hom` is injective (`π₀.hom` is an isomorphism), so
   `carrierClass L = carrierClass M`. `LineBundle.isoClass_eq_iff` gives an
   isomorphism of carriers. The published `nonempty_iso_of_carrierIso`
   upgrades it to an isomorphism of rigidified bundles, and `Quotient.sound`
   gives equality of classes.

## The target

`noetherianTwoAxisClassNilpotentInjective` introduces `R`, `A`, `B`, `I`, the
nilpotency hypothesis and `f`. If `I = ⊤`, then nilpotency gives
`⊤ = ⊤ ^ n = ⊥` (`Ideal.top_pow`), which is impossible because a local ring is
nontrivial. So `I ≠ ⊤`. The presheaf map along `algebraOverBase f (B ⧸ I)` is
definitionally `classesPullback A` along
`compTestHom (Spec.map (algebraMap B (B ⧸ I)))` from `Over.mk f`, so the target
is `classesPullback_injective_local A B I _ f`. The noetherian hypothesis on
`R`, the artinian hypothesis on `B` and the full strength of nilpotency are not
used; only `I ≠ ⊤` is.

## Provenance

The provenance is internal: the module composes published Library results. In
Murre's criterion, (F5) is injectivity of the functor along infinitesimal
thickenings of local artinian rings. Classically, for the rigidified Picard
functor of an abelian scheme it follows from the seesaw-type statement that a
line bundle on a product, trivial on two axes and on one fibre, is trivial near
that fibre. This is the published `localTwoAxisTriviality`, applied here to the
class `[L] / [M]` on `A ×_B A`.
