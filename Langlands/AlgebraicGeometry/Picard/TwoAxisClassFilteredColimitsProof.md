# Proof: Murre's condition (F2) for the two-axis class presheaf

Author: Worker 385.

This module proves the published proposition
`Langlands.AlgebraicGeometry.Picard.NoetherianTwoAxisClassFilteredColimitsStatement`:

```lean
theorem Langlands.AlgebraicGeometry.Picard.noetherianTwoAxisClassFilteredColimits :
    NoetherianTwoAxisClassFilteredColimitsStatement.{u}
```

The proof is unconditional. Its only axioms are `propext`, `Classical.choice` and `Quot.sound`.

## The statement

Let `R` be a noetherian ring and `A` an abelian scheme over `S = Spec R`. Let `R'` be a ring and
`f : Spec R' ⟶ S` an open immersion. `UnramifiedFunctor.FilteredColimits` asks that the functor
`G = algebraFunctor f ⋙ classPresheaf A` preserve colimits of filtered diagrams in `Type u`. Here
`algebraFunctor f` sends an `R'`-algebra `B` to `Spec B`, viewed over `S` through `f`. A class
over a test scheme `T` is an isomorphism class of line bundles on the self-product
`P_T = A_T ×_T A_T`, with compatible trivializations along the two unit axes.

The proof never uses that `R` is noetherian or that `f` is an open immersion. It works for every
morphism `f : Spec R' ⟶ S`.

Throughout, the proof uses the same two facts as the (F3) proof `TwoAxisClassAdicLimitsProof`,
both from the helper module `TwoAxisClassProductBaseChange`:

- a class is determined by the isomorphism class of its underlying line bundle
  (`mk_eq_mk_of_carrierIso`, `nonempty_carrierIso_of_mk_eq_mk`);
- restricting a class along a test map `h` pulls back its carrier along `productMap A h`, and
  `productMap A h` is a base change of `h` (`productMap_isPullback`).

## Directed colimits of algebras are direct limits of rings (section `DirectLimit`)

Let `α` be a nonempty directed partial order and `K : α ⥤ CommAlgCat R'` a diagram with colimit
cocone `c`.

- `transition K a b h` is the ring map `K a →+* K b` given by `K.map (homOfLE h)`. The instance
  `directedSystem` shows that these maps form a `DirectedSystem`.
- `coconeMap K c a` is the ring map `K a →+* c.pt` of the cocone.
- `isColimit_forget_mapCocone` shows that the forgetful functor to types sends `c` to a colimit
  cocone. It writes this functor as `commAlgCatEquivUnder`, followed by `Under.forget` (which
  preserves connected colimits, and `α` is connected because it is filtered), followed by the
  forgetful functor of `CommRingCat` (which preserves filtered colimits).
- `isDirectLimit` gives the ported FLT predicate
  `IsDirectLimit (transition K) (coconeMap K c)`. Its surjectivity and injectivity are Mathlib's
  `Types.jointly_surjective_of_isColimit` and `Types.FilteredColimit.isColimit_eq_iff`, and its
  compatibility is the cocone condition.

## Classes over a directed colimit (section `Classes`)

Keep `K` and `c` as above. For an index `j`, write `T_j = Spec (K j)` and `T = Spec c.pt` as
objects over `S`, and `h_j = algHomOver f (c.ι.app j).hom : T ⟶ T_j`. The map of `G` at
`c.ι.app j` is `classesPullback A h_j` (`mapCocone_ι_app_apply`), and the map of `K ⋙ G` at
`g : i ⟶ j` is `classesPullback A (algHomOver f (K.map g).hom)` (`comp_map_apply`). Both hold
by `rfl`. `algHomOver_comp_algebraOverBase` says that an algebra map followed by a structure map
over `Spec R'` is the structure map.

### Surjectivity: `exists_classesPullback_eq`

Let `⟦L⟧` be a class over `T`. Write `P_0` for the self-product over `U = Spec R'` (with
`U = Over.mk f`) and `f₀ : P_0 ⟶ Spec R'` for its structure map. `f₀` is proper, hence
quasi-compact and quasi-separated.

1. By `productMap_isPullback`, the self-product `P_T` is the base change of `P_0` along
   `Spec c.pt ⟶ Spec R'`. The published
   `NoetherianApproximation.exists_lineBundle_descent_of_isDirectLimit`, applied to the direct
   limit `isDirectLimit K hc`, gives an index `j` and a line bundle `M₀` on the chosen pullback
   `pullback f₀ (Spec K_j ⟶ Spec R')`. The pullback of `M₀` along any map to that pullback
   compatible with both projections is isomorphic to the carrier of `L`.
2. `κ` is the map from the self-product `P_{T_j}` to that chosen pullback, built with
   `pullback.lift` from `productMap A (T_j ⟶ U)` and the structure map. Then
   `productMap A h_j ≫ κ` is compatible with both projections: the first because
   `productMap_comp` and `algHomOver_comp_algebraOverBase` identify it with
   `productMap A (T ⟶ U)`, and the second by the cartesian square of `h_j`. So
   `E = pullback κ M₀` is a line bundle on `P_{T_j}`, and
   `pullbackComp` gives an isomorphism `e` from the pullback of `E` along `productMap A h_j` to
   the carrier of `L`.
3. `E` need not be trivial along the unit axes. As in the (F3) proof, replace it by the
   Library's normalized bundle `twoAxisNormalizedBundle pullbackTensorComparisonIsIso A_{T_j} E`,
   with its canonical rigidification `twoAxisNormalizedBundleRigidification`. The class `y` of
   this normalized bundle is the required preimage. The published
   `twoAxisNormalizedBundleRestrictionIso` turns `e` into an isomorphism between the pullback of
   the normalized bundle along `productMap A h_j` and the carrier of `L`. Its inputs are
   `productMap_fst`, `productMap_snd`, `first_naturality`, `second_naturality` and the inverses of
   the two rigidification isomorphisms of `L`. Then `mk_eq_mk_of_carrierIso` gives
   `classesPullback A h_j y = ⟦L⟧`.

### Injectivity: `exists_classesPullback_eq_of_eq`

Let `⟦L⟧`, `⟦M⟧` be classes over `T_i` with equal restrictions to `T`.

1. `nonempty_carrierIso_of_mk_eq_mk` gives an isomorphism of the pullbacks of the carriers
   along `productMap A h_i`.
2. Let `fX` be the structure map of the self-product `P_{T_i}`. The cartesian square of `h_i`
   gives a map `θ` from `pullback fX (Spec c.pt ⟶ Spec K_i)` to `P_T` over `P_{T_i}`. The
   published `NoetherianApproximation.nonempty_iso_pullback_of_fac` moves the isomorphism to the
   pullbacks along `pullback.fst fX _`.
3. The ported FLT theorem
   `Scheme.Modules.exists_nonempty_iso_pullback_of_nonempty_iso_pullback_of_isDirectLimit`
   (its invertibility hypotheses come from `isInvertible_of_isLocallyFreeRankOne`) gives
   `j ≥ i` and an isomorphism of the pullbacks along `pullback.fst fX (Spec K_j ⟶ Spec K_i)`.
4. With `k = algHomOver f (K.map (homOfLE hij)).hom`, the map `κ` from `P_{T_j}` into that
   pullback, built from `productMap A k` and the structure map, has first projection
   `productMap A k`. `nonempty_iso_pullback_of_fac` moves the isomorphism to the pullbacks along
   `productMap A k`, and `mk_eq_mk_of_carrierIso` gives equal restrictions to `T_j`.

### Directed colimits: `isColimitMapCocone`

Mathlib's `Types.FilteredColimit.isColimitOf'` combines the two halves. It shows that
`G.mapCocone c` is a colimit cocone for every directed diagram `K`.

## Filtered diagrams: `noetherianTwoAxisClassFilteredColimits`

Let `J` be a small filtered category, `K : J ⥤ CommAlgCat R'` and `c` a colimit cocone.
Mathlib's `IsFiltered.exists_directed` gives a nonempty directed partial order `α` and a final
functor `Φ : α ⥤ J`. By `Functor.Final.isColimitWhiskerEquiv`, the whiskered cocone `c.whisker Φ`
is a colimit cocone of `Φ ⋙ K`. So `isColimitMapCocone` makes `G.mapCocone (c.whisker Φ)` a
colimit. That cocone is isomorphic to `(G.mapCocone c).whisker Φ` (`Functor.mapCoconeWhisker`).
A second application of `Functor.Final.isColimitWhiskerEquiv` shows that `G.mapCocone c` is a
colimit. This is the `PreservesColimit` instance required for every such `K`.

## Provenance

Condition (F2) is from Murre's representability criterion, as encoded in
`UnramifiedFunctor.FilteredColimits`. The mathematical route is the standard limit argument for
finitely presented quasi-coherent sheaves on quasi-compact, quasi-separated schemes (EGA IV₃,
§8.5). Line bundles and their isomorphisms descend along direct limits of rings, through the
published `exists_lineBundle_descent_of_isDirectLimit` and the ported FLT theorem on isomorphisms.
The rigidifications are recovered by the same renormalization along the unit axes as in the
(F3) proof. The Lean proof and its helper declarations are original to this project.
