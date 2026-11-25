# Statement: isotriviality of étale local systems spreads out from local rings

`Langlands.AlgebraicGeometry.EtaleLocalSystemIsotrivialSpreadingStatement.{u}` states that
an étale local system that becomes constant over a finite étale cover of `Spec 𝒪_{S,s}`
already becomes constant over a finite étale cover of some open neighbourhood of `s`. The
module states the proposition and supplies no proof.

## The formula

```lean
def EtaleLocalSystemIsotrivialSpreadingStatement : Prop :=
  ∀ (S : Scheme.{u}) (F : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u}),
    IsFinitelyGeneratedLocallyConstant.{u, u} F → ∀ s : S,
      (∃ (L : Scheme.{u}) (p : L ⟶ Spec (S.presheaf.stalk s)), IsFinite p ∧ Etale p ∧
        Surjective p ∧ ∃ M : AddCommGrpCat.{u}, AddGroup.FG M ∧
          Nonempty (restrict (p ≫ S.fromSpecStalk s) F ≅ constant L M)) →
      ∃ U : S.Opens, s ∈ U ∧
        ∃ (U' : Scheme.{u}) (p : U' ⟶ U.toScheme), IsFinite p ∧ Etale p ∧ Surjective p ∧
          ∃ M : AddCommGrpCat.{u}, AddGroup.FG M ∧
            Nonempty (restrict (p ≫ U.ι) F ≅ constant U' M)
```

`restrict`, `constant` and `IsFinitelyGeneratedLocallyConstant` are the published
definitions of `Langlands.AlgebraicGeometry.EtaleLocalSystem`, used unchanged.

- `S` is an arbitrary scheme in universe `u`. No normality, noetherian or
  quasi-compactness hypothesis is imposed.
- `F` is an abelian presheaf on `Over S`, the category of all `S`-schemes, with
  `IsFinitelyGeneratedLocallyConstant.{u, u} F`. So `F` is a sheaf for the big étale
  topology, and on each member of some étale cover of `S` it is isomorphic to the constant
  sheaf of a finitely generated abelian group.
- `s` is a point of `S`. `S.fromSpecStalk s : Spec (S.presheaf.stalk s) ⟶ S` is Mathlib's
  canonical morphism from the spectrum of the local ring `𝒪_{S,s}`.
- **Hypothesis: isotrivial over `Spec 𝒪_{S,s}`.** There is a morphism
  `p : L ⟶ Spec (S.presheaf.stalk s)` that is finite, étale and surjective, and a finitely
  generated abelian group `M`, such that `restrict (p ≫ S.fromSpecStalk s) F` is
  isomorphic to `constant L M`. The presheaf `restrict (p ≫ S.fromSpecStalk s) F` is `F`
  evaluated on schemes over `L`, viewed as `S`-schemes through `p ≫ S.fromSpecStalk s`.
- **Conclusion: isotrivial over a neighbourhood.** There is an open subset `U` of `S`
  containing `s`, with open subscheme `U.toScheme` and inclusion `U.ι`. Over it there are
  a finite, étale, surjective `p : U' ⟶ U.toScheme` and a finitely generated abelian group
  `M` with `restrict (p ≫ U.ι) F ≅ constant U' M`. This conclusion has the same form as
  part 1 of `EtaleLocalSystemNormalIsotrivialStatement`.

## Source and provenance

Brian Conrad, *Reductive group schemes* (2014), `conrad-2014-reductive-group-schemes`,
proof of Corollary B.3.6, p.293 (one-based PDF page = printed page):

> Each `Spec 𝒪_{S,s}` is normal and irreducible, and any finite étale cover of
> `Spec 𝒪_{S,s}` spreads out to a finite étale cover of an open neighborhood of `s` in `S`.
> Thus, by the local constancy and finite type hypotheses on `F`, the isotriviality
> Zariski-locally on `S` is reduced to the isotriviality for each `F|Spec 𝒪_{S,s}`.

The statement is this reduction step. Conrad states it for the normal schemes of
Corollary B.3.6, but the spreading out uses only the local constancy and finite type of
`F`. So no normality hypothesis is included. The Lean statement uses the big étale site
and the published local-system definitions, as `EtaleLocalSystemNormalIsotrivialStatement`
does. "Isotrivial" means "constant over a finite étale surjective cover", as in that
statement.

It is a prerequisite for part 1 of `EtaleLocalSystemNormalIsotrivialStatement`: the
theorem `etaleLocalSystemNormalIsotrivial_of` of `EtaleLocalSystemLevelStructure` takes it
as its hypothesis `hSpread`. Part 1 then follows from part 2 applied to the irreducible
normal scheme `Spec 𝒪_{S,s}`, together with this statement.
