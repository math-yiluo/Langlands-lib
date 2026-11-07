# Adjunctions from a counit on smooth contragredients

Module `Langlands.Representation.Category.DualCounitAdjunction`, namespace
`Langlands.SmoothRep`.

This module carries out the formal step of Renard 2026, VI.9.6 (printed pp.201–202, PDF
pp.207–208). There, second adjointness (VI.9.6.1) for representations of the form `π~` is
extended to every smooth `π`. Renard compares the left-exact `Hom` sequences of
`0 → π → π~~ → π₁~~` in a commutative diagram. In Lean, a counit given on smooth
contragredients is extended along that kernel diagram instead, using
`Langlands.adjunctionOfCopresentedCounit`. The two arguments are equivalent.

Nothing here proves (VI.9.6.1) or (VI.9.6.2). Here the functors `L` and `R` are arbitrary.
The analytic input is the hypotheses `ε'`, `hfac` and `hbij` below. For second
adjointness they are to come from the Casselman pairing (VI.9.6.4).

## General coefficients

- `contragredientHom_comp`: `(f ≫ g)~ = g~ ≫ f~`. This is the Library's
  `contragredientMap_comp`.
- `bidualHom_comp_contragredientHom`: every `h : A ⟶ V~` equals
  `bidualHom A ≫ (bidualHom V ≫ h~)~`. In other words, morphisms into a smooth
  contragredient extend along bidual evaluation. The proof combines naturality of
  bidual evaluation along `h` with the triangle identity `bidualHom_contragredient_comp`.

## Smooth complex representations

Let `G` be a topological group with `hG : CompactOpenCofinal G`, and let `M` be a
topological group.

- `bidualFunctor`: the abbreviation `D.rightOp ⋙ D`, that is `A ↦ A~~`.
- `IsContragredient`: the object property `∃ V, V~ = X`.
- `bidualKernelCopresentation hG A : KernelCopresentation IsContragredient A`. It is the
  bidual copresentation `A ⟶ A~~ ⟶ (A~~/A)~~` from `ContragredientAdjunction`. The
  extension property for a target `V~` is `bidualHom_comp_contragredientHom`.
- `contragredientCounit hG L R ε' hfac`. The data are:
  - `ε' : R ⋙ L ⟶ bidualFunctor`;
  - `hfac`: for every `V`, `ε'_{V~}` factors as `e ≫ bidualHom V~`.

  The result is the counit on contragredients made of these factorisations. It is
  `Langlands.liftOfMonoFactorisation` with `ι = bidualTransformation`, which is mono by
  `mono_bidualHom hG`.
- `contragredientCounit_app_comp`: its defining equation.
- `adjunctionOfBidualCounit hG L R hR ε' hfac hbij : L ⊣ R`. The hypotheses are:
  - `[L.PreservesZeroMorphisms]`;
  - `hR : PreservesShortExact R`;
  - `hbij`: for every `V`, every `τ`, and every factorisation `e` of `ε'_{V~}`, the map
    `g ↦ L g ≫ e` on `τ ⟶ R V~` is bijective.

  The construction applies `adjunctionOfCopresentedCounit` to `contragredientCounit`
  and the bidual copresentations. `R` preserves their kernel diagrams by
  `PreservesShortExact.isLimitMapCokernelπComp`, because both bidual evaluations are
  injective.
- `adjunctionOfBidualCounit_counit_app_comp`: the counit of this adjunction at `V~`,
  followed by `bidualHom V~`, is `ε'_{V~}`.
- `nonempty_adjunction_of_bidualCounit hG L R hL hR ε' hfac hbij : Nonempty (L ⊣ R)`:
  the same result when both `L` and `R` preserve short exact sequences. This is the form
  used for second adjointness, where `L` is normalized parabolic induction and `R` is the
  opposite Jacquet functor. Zero morphisms for `L` come from
  `PreservesShortExact.preservesZeroMorphisms`.
