# Base-change invariance of geometric connected-component counts

Worker 189. This helper module supplies the base-change step used in the proof of
`SchemeGeometricComponentCountConstructibleStatement` (the scheme case of Conrad,
*Weil and Grothendieck approaches to adelic points*, 2011, Lemma 5.1, which refers
to EGA IV₃ 9.7.7). Its results are derived internal lemmas: the source treats these
facts as standard and gives no separate statements for them. Every count below is
`ENat.card` of the actual topological `ConnectedComponents`, so it may be `⊤`.

## Topological counting

- `componentCount_congr` and `componentCount_congr_iso`: homeomorphic spaces, and
  hence isomorphic schemes, have equal component counts. The proof builds an
  explicit equivalence of component types from the maps induced by the
  homeomorphism and its inverse.
- `componentCount_eq_intersectionQuot`: if a space is covered by finitely many
  closed connected sets `s i`, its component count is the cardinality of the
  quotient of the index type by the relation `intersectionRelation s` ("`s i` and
  `s j` meet"). The proof applies the published
  `Langlands.Topology.componentCount_eq_closedCoverIncidence` to the identity map
  and identifies its fibre relation with `intersectionRelation s`.

## Schemes over a field

Throughout, `f : X ⟶ Spec K` for a field `K`, and the `g i : Z i ⟶ X` are finitely
many closed immersions whose ranges cover `X`.

- `componentCount_eq_of_closedCover`: if each `g i ≫ f` is geometrically connected,
  each `Z i` is connected, so the count of `X` is the number of incidence classes
  of the ranges of the `g i`.
- `fieldBaseChange_componentCount_eq`: under the same hypotheses, for any field `L`
  and any morphism `e : Spec L ⟶ Spec K`, the count of `pullback f e` is the
  number of incidence classes of the *original* ranges. The base-changed pieces
  form a closed cover of the pullback (`baseChangeSubschemeRanges_cover`), each is
  connected (`isConnected_fieldBaseChangeSubschemeRanges`), and their incidence
  agrees with the original incidence (`fieldBaseChangeSubschemeRanges_incidence_iff`).
- `algClosed_fieldBaseChange_componentCount_eq`: if `K` is algebraically closed and
  `f` is locally of finite type and quasi-compact, then for every `e` the count of
  `pullback f e` equals the count of `X`. Here `X` is Noetherian, so it has finitely
  many irreducible components. They are covered by the vanishing-ideal closed
  subschemes on these components. Each such subscheme is irreducible, hence
  connected, so it is geometrically connected over the algebraically closed field
  (`Langlands.AlgebraicGeometry.algClosedConnected`). The previous two lemmas then
  give both counts as the same incidence count.
- `algClosedPoint_componentCount_eq`: for `f` locally of finite type and
  quasi-compact, and any algebraically closed field `Ω` with `e : Spec Ω ⟶ Spec K`,
  the count of `pullback f e` equals the count of the pullback along
  `Spec K̄ ⟶ Spec K` for `K̄ = AlgebraicClosure K`. Write `e = Spec.map φ`. Then
  `IsAlgClosed.lift` gives a `K`-embedding `K̄ → Ω`, so `e` factors through
  `Spec K̄`. Pullback pasting (`pullbackLeftPullbackSndIso`) and the previous lemma,
  applied over `K̄`, finish the proof.

## Geometric fibres of an arbitrary morphism

- `geometricFiberComponentCount_eq_fiber`: `geometricFiberComponentCount f y` is
  the count of the base change of the residue-field fibre
  `f.fiberToSpecResidueField y` along `Spec κ(y)‾ ⟶ Spec κ(y)`. This follows from
  pullback pasting.
- `componentCount_algClosedPoint_eq`: for `f` locally of finite type and
  quasi-compact, every geometric point `Spec Ω ⟶ Spec κ(y) ⟶ Y` with `Ω`
  algebraically closed computes `geometricFiberComponentCount f y`. The residue-field
  fibre inherits both hypotheses by base change.
- `geometricFiberComponentCount_baseChange`: for an actual cartesian square
  `IsPullback a b f g` with `f` locally of finite type and quasi-compact,
  `geometricFiberComponentCount b y = geometricFiberComponentCount f (g y)` for every
  `y`. Pasting the defining pullback of `b` with the square identifies its
  geometric fibre with the pullback of `f` along `componentCountGeometricPoint y ≫ g`.
  By `Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField`, this point factors as
  `Spec κ(y)‾ ⟶ Spec κ(g y) ⟶ Y`, and the previous lemma applies.
- `geometricFiberComponentCount_eq_incidence`: let the `g i` be finitely many closed
  immersions into `X` whose fibres over `y` cover the residue-field fibre
  (`closedSubschemeFiberCover`), with each fibre piece geometrically connected over
  `κ(y)`. Then the geometric count at `y` is the number of classes of
  `closedSubschemeFiberIncidence f g y`. This is `fieldBaseChange_componentCount_eq`
  applied to the residue-field fibre, combined with
  `range_baseChange_eq_fiberSubschemeSets`.

No Noetherian hypothesis is imposed on any base scheme. The finite-type and
quasi-compactness hypotheses are used only to make the relevant fibres Noetherian.
