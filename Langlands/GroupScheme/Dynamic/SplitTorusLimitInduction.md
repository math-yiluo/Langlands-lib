# Limit induction for split torus actions on proper schemes

Module `Langlands.GroupScheme.Dynamic.SplitTorusLimitInduction`, namespace
`Langlands.GroupScheme.SplitTorusLimitInduction`. This is an internal supporting module for
the proof of `RankOneCentralCoverStatement` (`Reductive.RankOneCentralCoverProof`). It packages the Białynicki-Birula style descent used to reach torus-fixed points:
limits along cocharacters exist on a proper scheme, they are fixed by the cocharacter, and
they stay fixed by commuting cocharacters. It uses only Library results about orbit
extensions (`Dynamic/SchemeActionLimit`, `Dynamic/ProperAffineExtension`). It needs no
literature source.

Notation. `a : SchemeAction T.toGrp X` is an action of a commutative group scheme `T` on
`X`. For a cocharacter `ν : cocharacterLattice T`, `a.restrict (CommGroupScheme.groupHom ν)`
is the induced `𝔾ₘ`-action. An orbit extension `e` of a point `w` along `ν`
(`IsGmOrbitExtension w e`) extends `t ↦ ν(t) · w` over `𝔸¹`. Its value at `0` is
`Dynamic.evalZero e`, the limit of `w` along `ν`.

## Statements

Over an arbitrary base scheme `S`:

- `isFixed_evalZero_of_isFixed [IsSeparated X.hom]
  (he : (a.restrict (groupHom ν)).IsGmOrbitExtension w e)
  (hw : (a.restrict (groupHom ν')).IsFixed w) :
  (a.restrict (groupHom ν')).IsFixed (Dynamic.evalZero e)`.
  The limit along `ν` of a point fixed along `ν'` is again fixed along `ν'`.
- `isFixed_of_forall (eC : T ≅ splitTorus.commGroupScheme S I) [Fintype I]
  (hx : ∀ j, (a.restrict (groupHom (splitTorus.single S I j ≫ eC.inv))).IsFixed x) :
  a.IsFixed x`. A point fixed along every coordinate cocharacter of a split torus is fixed
  by `T`.

- `isFixed_evalZero_of_normalizes [IsSeparated X.hom] (ψ : (Gm S).toGrp ⟶ G) (j : U ⟶ G)
  (hnorm) (he : (a.restrict ψ).IsGmOrbitExtension w e) (hw : (a.restrict j).IsFixed w) :
  (a.restrict j).IsFixed (Dynamic.evalZero e)`. Here `a : SchemeAction G X` for an arbitrary
  group scheme `G`. The hypothesis `hnorm` says that `ψ` normalizes `j`: for every test
  scheme `Q`, `s : Q ⟶ (Gm S).X` and `v : Q ⟶ U.X` there is `v' : Q ⟶ U.X` with
  `v' ≫ j.hom.hom = (s ≫ ψ.hom.hom)⁻¹ * (v ≫ j.hom.hom) * (s ≫ ψ.hom.hom)`. The limit along
  `ψ` of a point fixed by `U` is again fixed by `U`. The previous lemma is the case of
  commuting cocharacters.

Over a field `k`, for `X : Over (Spec (CommRingCat.of k))` with `[IsProper X.hom]`, and
rational points `w : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X`:

- `exists_isGmOrbitExtension a ν w : ∃ e, (a.restrict (groupHom ν)).IsGmOrbitExtension w e`.
  Every rational point has a limit along every cocharacter.
- `limit_induction (hT : IsSplitTorus T.toGrp) (P R : rational points → Prop)` with three
  hypotheses:
  - `hP`: for every `ν`, `w`, `e` with `IsGmOrbitExtension w e` along `ν`, `P w` implies
    `P (evalZero e)`;
  - `hR`: for the same data, `P w` and `R (evalZero e)` imply `R w`;
  - `hfix`: `a.IsFixed w` and `P w` imply `R w`.

  Conclusion: `P w → R w` for every rational point `w`. The field need not be
  algebraically closed.

## The implemented proofs

- `isFixed_evalZero_of_isFixed`. Use the universal criterion `isFixed_iff_universal`, over
  `Z × 𝔾ₘ`. There, `e₁ = fst ▷ 𝔸¹ ≫ e` is an orbit extension of `fst ≫ w` along `ν`
  (`IsGmOrbitExtension.whiskerRight`). Acting on `e₁` by the `𝔾ₘ`-coordinate along `ν'`
  gives a second extension `e₂` of the same orbit. Points of `T` commute (`mul_comm`), so
  the actions along `ν` and `ν'` commute (`act_mul`). Since `w` is fixed along `ν'`, `e₂`
  extends the orbit of `fst ≫ w` along `ν`. Extensions into a separated scheme are unique
  (`IsGmOrbitExtension.unique`), so `e₂ = e₁`. Evaluating at `0`
  (`Dynamic.evalZero_whiskerRight`, `naturality`) gives the universal fixedness equation
  for the limit.
- `isFixed_evalZero_of_normalizes`. The argument is the same as for the previous lemma,
  over `Z × U`. Acting on `e₁ = fst ▷ 𝔸¹ ≫ e` by the `U`-coordinate `v` gives a second
  extension of the `ψ`-orbit of `fst ≫ w`. This uses `v · ψ(s) = ψ(s) · v'` with `v'` from
  `hnorm` (verified by `group`) and the fixedness of `w` under `v'`. Uniqueness of
  extensions and evaluation at `0` finish.
- `isFixed_of_forall`. `∑ⱼ (eC.hom ≫ proj j) ≫ (single j ≫ eC.inv) = 𝟙 T`, by
  `splitTorus.sum_proj_comp_single`. So every point `h` of `T` is the product over `j` of
  its components along the coordinate cocharacters (`comp_groupHom_sum`,
  `comp_groupHom_comp`). Each component fixes the point (`restrict_act`), and `act_mul`
  together with Finset induction gives fixedness by the product.
- `exists_isGmOrbitExtension` is `AffineLine.exists_extension_of_isProper` applied to the
  orbit map.
- `limit_induction`. Write `T ≅ 𝔾ₘ^I` and let `νⱼ = single j ≫ eC.inv`. By Finset induction
  on `F ⊆ I`, prove: every `w` with `P w` that is fixed along `νᵢ` for all `i ∉ F` satisfies
  `R`.
  - For `F = ∅`, `w` is fixed by `T` (`isFixed_of_forall`), and `hfix` applies.
  - For `F = insert j F'`, take the limit `w' = evalZero e` of `w` along `νⱼ`. Then `P w'`
    holds by `hP`. Also `w'` is fixed along `νⱼ` (`IsGmOrbitExtension.isFixed_evalZero`) and
    along every `νᵢ` with `i ∉ insert j F'` (`isFixed_evalZero_of_isFixed`). So the
    induction hypothesis gives `R w'`, and `hR` gives `R w`.

  The case `F = univ` is the theorem.
