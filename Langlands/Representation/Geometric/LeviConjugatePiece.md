# Full pieces of the geometric lemma for a parabolic with the same Levi

Module `Langlands.Representation.Geometric.LeviConjugatePiece`. Written for the proof of
Renard VII.1.3 (`MaximalLeviSupercuspidalUnitarizableConstituentStatement`), where the
graded pieces of the geometric lemma (Renard VI.5.1,
`GeometricLemmaIntersectionDatum.pieceFunctor`) of `i^G_P(ρ)` are analysed along a second
represented parabolic `Q` whose Levi factor is the same subgroup `M` of `G`.

## Provenance

Internal. It generalizes the published module
`Langlands.Representation.Geometric.SelfIntersectionPiece` (the case `Q = P`) to a parabolic
`Q` whose Levi factor has the same source group scheme `M`. In Renard's proof of VII.1.3
(printed pp.224-226) the pieces of `r_Q ∘ i_P (ρ)` attached to a double coset `P z Q` with
`M ∩ zQz⁻¹ = M` are the conjugates of the supercuspidal `ρ`; this module formalizes that
identification for the represented graded piece `i^M_{Q'} ∘ ι ∘ r^M_{P'}` of
`RepresentedGeometricLemmaStatement`, together with the action of a split component on it.
Ingredients, all published:

- `isIso_l'_of_isIso_p'` (module `Langlands.Representation.Geometric.SelfIntersectionLevi`) and
  `isIso_lQ'_comp_q'_of_isIso_p'_of_iso`, `isIso_q'_of_isIso_p'_of_iso`,
  `isIso_lQ'_of_isIso_p'_of_iso`, `pieceFunctor_isIrreducible_of_isIso_source_of_iso` (module
  `Langlands.Representation.Geometric.FullIntersectionIrreducible`), applied with `E = Iso.refl M`;
- `fullLeviJacquetEquiv` and `subsingleton_pieceFunctor_obj` (module
  `Langlands.Representation.Geometric.DegenerateJacquetPieces`);
- `isoParabolicInductionEquiv` (module `Langlands.Representation.Exponents.IsoParabolicInduction`);
- `IsSplitComponent.exists_factor` (module `Langlands.GroupScheme.Rational.SplitTorusFactorization`)
  and `IsSplitComponent.comp_iso` (module
  `Langlands.Representation.Exponents.GeometricLemmaExponentTransfer`).

## Split components (namespace `Langlands.GroupScheme`)

- `IsSplitComponent.exists_iso_comp`: for split components `a : A ⟶ M` and `a' : A' ⟶ M'`
  over a field, `M'` affine over the base, and an isomorphism `τ : M ≅ M'`, there is an
  isomorphism `e : A ≅ A'` of commutative group schemes with
  `CommGroupScheme.groupHom e.hom ≫ a' = a ≫ τ.hom`. Proof: `a ≫ τ.hom` is a split component
  of `M'` (`comp_iso`), so it factors as `f ≫ a'` (`exists_factor`), and maximality of
  `a ≫ τ.hom` makes `f` an isomorphism.

## Setting for the pieces

Namespace `Langlands.Aubert.General.RepresentedParabolic.GeometricLemmaIntersectionDatum`. Fix
a nonarchimedean ambient `G(F)` (topology `RationalPointFamily.pointTopology`, locally compact
and nonarchimedean), a represented parabolic `p : P ⟶ G` with Levi `l : M ⟶ P` and radical
`r : N ⟶ P`, a second represented parabolic `q : Q ⟶ G` with Levi `lQ : M ⟶ Q` (the **same**
source `M`) and radical `rQ : U ⟶ Q`, a point `z ∈ G(F)`, and an intersection datum
`D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ z` for the
double coset `P z Q`. The first five results assume `[IsIso D.p']`: the parabolic
`P' = M ∩ zQz⁻¹` of `M` is all of `M`. The representation `ρ` is a smooth representation of
`M(F)` with its Levi topology `leviPointTopology l hl`.

## Results

- `leviConjugation` (definition): the automorphism of `M` given as the composite
  `M ≅ L' ≅ M' ≅ M` of the inverse of `lQ' ≫ q' : L' ⟶ M`, the datum's intersection
  isomorphism `φ : L' ≅ M'`, and `l' ≫ p' : M' ⟶ M`.
- `leviConjugation_hom`: the unfolding
  `leviConjugation.hom = inv (lQ' ≫ q') ≫ φ.hom ≫ l' ≫ p'`.
- `leviConjugation_comp`: if `lQ ≫ q = l ≫ p` (the Levi factors of `Q` and `P` have the same
  composite into `G`), then
  `leviConjugation.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso z).hom`, i.e. the automorphism is
  conjugation by `z` inside `G`. Proof: the datum's identity `φ_comp`
  (`φ.hom ≫ l' ≫ p' ≫ l ≫ p = lQ' ≫ q' ≫ lQ ≫ q ≫ Int(z)`), rewritten with `hcomp`.
- `leviConjugation_map_rationalPoints`: for `b ∈ L'(F)`, `leviConjugation` sends
  `(lQ' ≫ q')(b)` to `(l' ≫ p')(φ(b))`.
- `leviPieceEquiv` (definition): the linear equivalence `D.pieceFunctor.obj ρ ≃ₗ[ℂ] ρ`, the
  composite of `isoParabolicInductionEquiv` for the full parabolic `Q'` (evaluation at `1` on
  the induction along `Q'` of the pullback along `D.e` of the Jacquet module along `P'`) with
  `fullLeviJacquetEquiv` for the full parabolic `P'`.
- `leviPieceEquiv_representation`: for `m ∈ M(F)` and `x` in the piece,
  `leviPieceEquiv ρ (m · x) = ρ(leviConjugation(m)) (leviPieceEquiv ρ x)`, where `m · x` is
  the action of `D.pieceFunctor.obj ρ` and `leviConjugation(m)` is
  `rationalPoints.map D.leviConjugation.hom m`. Proof: as for `selfPieceEquiv_representation`;
  write `m = (lQ' ≫ q')(b)`, then `leviConjugation_map_rationalPoints`, `D.e_apply`,
  `isoParabolicInductionEquiv_map` and `fullLeviJacquetEquiv_representation`.
- `subsingleton_or_isIrreducible_scalar` (no `[IsIso D.p']` assumption). Hypotheses:
  `hcomp : lQ ≫ q = l ≫ p`; `ρ` irreducible; the supercuspidality hypothesis `hsuper` in the
  form used by `MaximalLeviSupercuspidalInductionEndomorphismStatement` (for every represented
  parabolic `p' : P' ⟶ M` that is not an isomorphism, the normalized Jacquet module
  `(jacquetFunctor p' l' r' hp' hr' hl' hmul').obj ρ` is a subsingleton); a split component
  `a : A ⟶ M` and a group homomorphism `ωA : A(F) →* ℂˣ` with
  `ρ(a(t)) y = ωA(t) • y` for all `t ∈ A(F)` and `y ∈ ρ`. Conclusion: either the piece
  `D.pieceFunctor.obj ρ` is a subsingleton, or `D.p'` is an isomorphism, the piece is
  irreducible, and there are `ψ : M ≅ M` with `ψ.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso z).hom` and
  `e : A ≅ A` with `CommGroupScheme.groupHom e.hom ≫ a = a ≫ ψ.hom`, such that every
  `a(t)` acts on the piece by the scalar `ωA(e(t))` (where `e(t)` is
  `rationalPoints.map (CommGroupScheme.groupHom e.hom) t`). Proof: case split on `IsIso D.p'`.
  If it holds, take `ψ = leviConjugation` (`leviConjugation_comp`), `e` from
  `IsSplitComponent.exists_iso_comp ha ha ψ`, irreducibility from
  `pieceFunctor_isIrreducible_of_isIso_source_of_iso`, and the scalar action by transporting
  through the injective `leviPieceEquiv ρ`:
  `ρ(ψ(a(t))) = ρ(a(e(t))) = ωA(e(t))`. Otherwise `hsuper` applied to the datum's `P'` gives a
  vanishing Jacquet module, and `subsingleton_pieceFunctor_obj` a vanishing piece.

The equivalence is an intertwining linear equivalence rather than an isomorphism in `Rep`,
since the piece lives in `Rep.{max u v}` and `ρ` in universe `v`. Neither maximality nor
properness of `P` or `Q` is used, and no admissibility of `ρ` is assumed.
