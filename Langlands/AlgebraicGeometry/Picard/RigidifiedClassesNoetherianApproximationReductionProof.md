# Proof of the reduction of noetherian approximation of agreement to noetherian models

`Langlands.AbelianScheme.rigidifiedClassesNoetherianApproximationReduction` proves
`Langlands.AbelianScheme.RigidifiedClassesNoetherianApproximationReductionStatement.{u}`:
the noetherian model statement `AbelianSchemeNoetherianModelStatement.{u}` implies
`RigidifiedClassesNoetherianApproximationStatement.{u}`. See
`RigidifiedClassesNoetherianApproximationReductionStatement.md` for the two propositions. The
proof is a conditional implication. It does not prove the hypothesis.

The local helpers live in the namespace
`Langlands.AbelianScheme.RigidifiedClassesNoetherianApproximationReduction`. They use only
published results: the rigidified pullback functor `RigidifiedLineBundle.pullback` with its
comparison isomorphisms `pullbackComp`, `pullbackCongr` and `pullbackId` (with the proved
coherence `RigidifiedModule.pullbackCoherence`), and the lemma
`RigidifiedLineBundle.nonempty_iso_of_forget_iso` (with the proved preservation input
`Langlands.Scheme.Modules.pullbackTensorComparisonIsIso`). Throughout, `cp[A]` abbreviates
`RigidifiedLineBundle.classesPullback A.X.hom (unitSection A) (unitSection_comp A)`, which is
`Quotient.map` of the relative rigidified pullback `relativePullback … h`, itself
`RigidifiedLineBundle.pullback ((relativeSpace A.X.hom).map h) h.left _`.

## General rigidified pullback lemmas

1. **`pullbackPullbackIso`.** Given composable squares `(f, g)` and `(f', g')` for rigidified
   pullback and morphisms `F`, `G` with `f' ≫ f = F` and `g' ≫ g = G`, the iterated pullback
   of `L` along `(f, g)` then `(f', g')` is isomorphic to the pullback of `L` along `(F, G)`.
   It is `pullbackComp` followed by `pullbackCongr`.
2. **`nonempty_iso_of_pullback`.** If `f` and `g` are isomorphisms and the pullbacks of `L`
   and `M` along `(f, g)` are isomorphic, then `L ≅ M`. Pull the isomorphism back along
   `(inv f, inv g)` and use step 1 with `pullbackId` to identify both sides with `L` and `M`.
3. **Projection lemmas.** `relativeSpace_map_fst`, `relativeSpace_map_snd` and
   `relativeSection_fst` compute the two projections of `(relativeSpace f).map h` and of the
   induced section on the chosen fibre products; each is `pullback.lift_fst` or
   `pullback.lift_snd`.

## Total space and the family over the identity

For an abelian scheme `A` over `S`, the member of the relative family over the identity object
`Over.mk (𝟙 S)` is the chosen fibre product `S ×_S A.X.left`.

- `totalSpaceLift A : A.X.left ⟶ S ×_S A.X.left` is `pullback.lift A.X.hom (𝟙 _)`, with
  projections `A.X.hom` and the identity (`totalSpaceLift_fst`, `totalSpaceLift_snd`).
  `totalSpaceLift_comm` says it carries `unitSection A` to the induced section over the
  identity.
- `toTotal A F` restricts a family `F` over the identity to a rigidified line bundle on
  `A.X.left`: the rigidified pullback of `F` along `(totalSpaceLift A, 𝟙 S)`.
- `ofTotal A M` spreads a rigidified line bundle `M` on `A.X.left` to a family over the
  identity: the rigidified pullback of `M` along the second projection
  `S ×_S A.X.left ⟶ A.X.left` and `𝟙 S` (the square is `snd_comm`, the published
  `relativeSection_snd`).

## Comparing the two families over a test object

Fix a model as in the hypothesis: `b : S ⟶ S₀`, `a : A.X.left ⟶ A₀.X.left` with
`hpb : IsPullback a A.X.hom A₀.X.hom b` and `hunit : unitSection A ≫ a = b ≫ unitSection A₀`.

- **`isPullback_paste`, `spaceIso`.** For `T' : Over S`, pasting the chosen fibre-product
  square of `T'.hom` and `A.X.hom` with `hpb` shows that `T' ×_S A.X.left` with projections
  `pullback.fst` and `pullback.snd ≫ a` is a pullback of `T'.hom ≫ b` and `A₀.X.hom`. Its
  comparison with the chosen fibre product is the isomorphism
  `spaceIso hpb T' : T' ×_S A.X.left ≅ T' ×_{S₀} A₀.X.left` (`IsPullback.isoPullback`), with
  projections computed by `spaceIso_hom_fst` and `spaceIso_hom_snd`.
- **`spaceIso_comm`.** `spaceIso` carries the section induced by `unitSection A` to the
  section induced by `unitSection A₀`, over the identity of `T'.left`. Checked on both
  projections, using `hunit` for the second.
- **`nonempty_iso_model`.** Let `h : T' ⟶ Over.mk (𝟙 S)`, `F` a family over the identity for
  `A`, and `M₀` a rigidified line bundle on `A₀.X.left` with an isomorphism `e` from the
  pullback along `a` of the line bundle underlying `M₀` to the line bundle underlying
  `toTotal A F`. Then the relative pullback of `F` along `h` is isomorphic to the pullback
  along `(spaceIso hpb T').hom, 𝟙 T'.left` of the relative pullback of `ofTotal A₀ M₀` along
  `Over.homMk (T'.hom ≫ b)`. Proof:
  1. `nonempty_iso_of_forget_iso` upgrades `e` to an isomorphism `e'` of rigidified line
     bundles between the rigidified pullback of `M₀` along `(a, b)` (square `hunit`) and
     `toTotal A F`.
  2. The relative pullback of `F` along `h` is the pullback along the second projection
     `T' ×_S A.X.left ⟶ A.X.left` (and `T'.hom`) of `toTotal A F`, by step 1 of the general
     lemmas, because `pullback.snd ≫ totalSpaceLift A = (relativeSpace A.X.hom).map h`
     (checked on projections; the first uses `h.left = T'.hom` and `pullback.condition`).
  3. Replace `toTotal A F` by the pullback of `M₀` along `(a, b)` using `e'`, and compose the
     two pullbacks (general step 1): the result is the pullback of `M₀` along
     `(pullback.snd ≫ a, T'.hom ≫ b)`.
  4. On the other side, the relative pullback of `ofTotal A₀ M₀` along
     `Over.homMk (T'.hom ≫ b)` is the pullback of `M₀` along the second projection of
     `T' ×_{S₀} A₀.X.left` (and `T'.hom ≫ b`), by general step 1 and
     `relativeSpace_map_snd`. Pulling this back along `(spaceIso hpb T').hom` and composing
     again (general step 1 with `spaceIso_hom_snd`) gives the pullback of `M₀` along
     `(pullback.snd ≫ a, T'.hom ≫ b)` as well.

## Main theorem

Let `R`, `A` and `q r : RigidifiedClasses A (Over.mk (𝟙 (Spec R)))` be given. Choose
representatives `F` and `G` of `q` and `r` (`Quotient.inductionOn`). Apply the hypothesis to
`R`, `A`, `M₁ = toTotal A F` and `M₂ = toTotal A G`; it returns `R₀`, its noetherianity,
`φ`, `A₀`, `a`, `M₁₀`, `M₂₀`, the pullback square `hpb` over `b = Spec.map φ`, the unit
compatibility `hunit` and isomorphisms `e₁`, `e₂` of underlying line bundles. Take
`q₀ = ⟦ofTotal A₀ M₁₀⟧` and `r₀ = ⟦ofTotal A₀ M₂₀⟧`.

For `T'` and `h : T' ⟶ Over.mk (𝟙 (Spec R))`, `nonempty_iso_model` gives isomorphisms `i₁`
and `i₂` identifying the relative pullbacks of `F` and `G` along `h` with the pullbacks along
`((spaceIso hpb T').hom, 𝟙 T'.left)` of the relative pullbacks of `ofTotal A₀ M₁₀` and
`ofTotal A₀ M₂₀` along `Over.homMk (T'.hom ≫ Spec.map φ)`. Unfolding `classesPullback` to
`Quotient.map`, both sides of the required equivalence become `Nonempty` isomorphisms:

- if the pullbacks of `F` and `G` along `h` are isomorphic, then so are the two pulled-back
  model families after pullback along the isomorphism `spaceIso`, and
  `nonempty_iso_of_pullback` removes that pullback;
- conversely, an isomorphism of the model families is pulled back along `spaceIso` and
  conjugated by `i₁` and `i₂`.
