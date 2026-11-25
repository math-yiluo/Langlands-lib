# Statement: étale local systems over normal schemes are locally isotrivial

`Langlands.AlgebraicGeometry.EtaleLocalSystemNormalIsotrivialStatement.{u}` is the sheaf
theorem to which Conrad reduces Corollary B.3.6 ("groups of multiplicative type over
normal bases are locally isotrivial"). The module states the proposition and supplies
no proof.

## Source

Brian Conrad, *Reductive group schemes* (2014), `conrad-2014-reductive-group-schemes`.
The page numbers below are one-based PDF pages, which agree with the printed pages. The
proof of Corollary B.3.6 begins on p.293:

> We call an étale sheaf on a scheme isotrivial if it becomes constant over a finite
> étale cover. By Proposition B.3.4, our task is to prove that if `F` is a finite type
> locally constant abelian étale sheaf on a normal scheme `S` then: `F` is isotrivial if
> `S` is irreducible, and in general `F` is isotrivial Zariski-locally on `S`.

The proposition below is exactly this claim.

## The formula

```lean
def EtaleLocalSystemNormalIsotrivialStatement : Prop :=
  ∀ (S : Scheme.{u}),
    (∀ x : S, IsDomain (S.presheaf.stalk x) ∧ IsIntegrallyClosed (S.presheaf.stalk x)) →
    ∀ F : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u}, IsFinitelyGeneratedLocallyConstant.{u, u} F →
      (∀ s : S, ∃ U : S.Opens, s ∈ U ∧
        ∃ (U' : Scheme.{u}) (p : U' ⟶ U.toScheme), IsFinite p ∧ Etale p ∧ Surjective p ∧
          ∃ M : AddCommGrpCat.{u}, AddGroup.FG M ∧
            Nonempty (restrict (p ≫ U.ι) F ≅ constant U' M)) ∧
      (IrreducibleSpace S →
        ∃ (S' : Scheme.{u}) (p : S' ⟶ S), IsFinite p ∧ Etale p ∧ Surjective p ∧
          ∃ M : AddCommGrpCat.{u}, AddGroup.FG M ∧ Nonempty (restrict p F ≅ constant S' M))
```

`restrict`, `constant` and `IsFinitelyGeneratedLocallyConstant` are the published
definitions of `Langlands.AlgebraicGeometry.EtaleLocalSystem`, used unchanged.

## Correspondence with the source

- **Normal scheme.** This is the hypothesis of the multiplicative-type statement
  `Langlands.GroupScheme.MultiplicativeTypeNormalIsotrivialStatement`, word for word:
  every stalk `S.presheaf.stalk x` is an integrally closed domain. No noetherian
  hypothesis is imposed, as in Conrad, who notes that irreducibility can fail for
  connected normal non-noetherian schemes.
- **Finite type locally constant abelian étale sheaf.** This is
  `IsFinitelyGeneratedLocallyConstant.{u, u} F` for an abelian presheaf
  `F : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u}` on all `S`-schemes. Concretely, `F` is a sheaf for
  the big étale topology (`EtaleLocalSystem.topology S`, Mathlib's
  `Scheme.etaleTopology.over S`). Moreover, there is an étale cover `𝒰` of `S` such
  that, on each member `𝒰.X i`, the restriction `restrict (𝒰.f i) F` is isomorphic to
  `constant (𝒰.X i) M` for some finitely generated abelian group `M` in universe `u`.
  The group `M` may depend on `i`. Conrad's étale sheaves live on the étale site of
  `S`. The big site is used here because the published local-system definitions, and the
  character sheaves of groups of multiplicative type that they model, are defined on it.
- **Constant sheaf.** `constant T M` assigns to an object `V` of `Over T` the
  continuous, that is locally constant, maps from `V.left` to `M` with the discrete
  topology. Its sections are `LocallyConstant V.left M`
  (`EtaleLocalSystem.constantSections`). This is Conrad's constant sheaf `M_T`.
- **Isotrivial.** Conrad: "becomes constant over a finite étale cover". The cover is a
  morphism `p : S' ⟶ S` that is finite (`IsFinite`), étale (`Etale`) and surjective
  (`Surjective`). Surjectivity is what makes it a cover. "Constant over `S'`" means an
  isomorphism of abelian presheaves on `Over S'` between the restriction `restrict p F`
  (composition with `Over.map p`) and `constant S' M`. Here `M` is a finitely generated
  abelian group (`AddGroup.FG M`).
- **Part 1, Zariski-locally isotrivial.** For every point `s` there is an open `U ∋ s`
  of `S`, with open subscheme `U.toScheme` and inclusion `U.ι`, such that `F` restricted
  to `U` is isotrivial. In other words, there is a finite étale surjective
  `p : U' ⟶ U.toScheme` with `restrict (p ≫ U.ι) F ≅ constant U' M`. This uses the same
  open-neighbourhood quantifiers as part 1 of `MultiplicativeTypeNormalIsotrivialStatement`.
- **Part 2, irreducible base.** If `S` is an irreducible space, then `F` is isotrivial
  over `S` itself. This uses the same quantifiers as part 2 of `MultiplicativeTypeNormalIsotrivialStatement`.

## Provenance and use

This is a source statement, Conrad's reformulation of Corollary B.3.6 in terms of
sheaves. In the proof of `MultiplicativeTypeNormalIsotrivialStatement`
(`multiplicativeTypeNormalIsotrivial` in `Langlands.GroupScheme.Torus.MultiplicativeTypeNormalIsotrivialProof`) it is combined with:
- a comparison between characters of a group of multiplicative type and local systems
  (`RelativeCharacterConstancyStatement` and `RelativeCharacterLocalConstancyStatement`, with
  their proofs, assembled in `MultiplicativeTypeNormalIsotrivialAssembly`);
- Proposition B.3.4(1), étale-local diagonalizability.

The Lean encoding of "finite type locally constant" follows the published definition
`IsFinitelyGeneratedLocallyConstant` rather than a stalkwise definition. This is
Conrad's meaning in Proposition B.3.4: étale-locally isomorphic to a constant sheaf
with finitely generated value group.
