# The identity piece of the geometric lemma for a full self-intersection

Module `Langlands.Representation.Geometric.SelfIntersectionPiece`. Used in the proof of
Renard VI.5.3 (`MaximalLeviSupercuspidalInductionEndomorphismStatement`), where the graded
pieces of the geometric lemma (Renard VI.5.1,
`GeometricLemmaIntersectionDatum.pieceFunctor`) are analysed for a single represented
parabolic `P = MN` and `Q = P`.

## Provenance

Internal. In Renard VI.5.3 the graded piece attached to a double coset `P z P` with
`M ∩ zPz⁻¹ = M` is read off as the conjugate `ρ^z` of `ρ`; this module formalizes that
identification for the represented graded piece `i^M_{Q'} ∘ ι ∘ r^M_{P'}` of
`RepresentedGeometricLemmaStatement`. It combines three ingredients:

- `selfConjugation` and its lemmas (module `Langlands.Representation.Geometric.SelfIntersectionLevi`):
  when `P' = M ∩ zPz⁻¹` is all of `M`, the maps `l'`, `q'`, `lQ'` are isomorphisms and
  conjugation by `z` is an automorphism of `M`;
- `fullLeviJacquetEquiv` (module `Langlands.Representation.Geometric.DegenerateJacquetPieces`):
  the Jacquet module along a parabolic equal to its Levi is the representation itself;
- `isoParabolicInductionEquiv` (module `Langlands.Representation.Exponents.IsoParabolicInduction`):
  normalized induction along an isomorphic parabolic and Levi is the representation itself.

## Setting

Namespace `Langlands.Aubert.General.RepresentedParabolic.GeometricLemmaIntersectionDatum`. Fix
a nonarchimedean ambient `G(F)` (topology `RationalPointFamily.pointTopology`, locally compact
and nonarchimedean), one represented parabolic `p : P ⟶ G` with Levi `l : M ⟶ P` and radical
`r : N ⟶ P`, a point `z ∈ G(F)`, and an intersection datum
`D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul p l r hp hr hl hmul z` for the double
coset `P z P`. The first three results assume `[IsIso D.p']`: the parabolic `P' = M ∩ zPz⁻¹`
of `M` is all of `M`; `subsingleton_or_exists_selfPieceEquiv` does not, and splits on it.
The representation `ρ` is a smooth representation of `M(F)` with its Levi topology
`leviPointTopology l hl`.

## Results

- `selfPieceEquiv` (definition): the linear equivalence
  `D.pieceFunctor.obj ρ ≃ₗ[ℂ] ρ`. It is the composite of
  `isoParabolicInductionEquiv` for `Q' = L'` (evaluation at `1` on the induction along `Q'`,
  applied to the pullback along `D.e` of the Jacquet module of `ρ` along `P'`) with
  `fullLeviJacquetEquiv` for `P' = M'`.
- `selfPieceEquiv_representation`: for `m ∈ M(F)` and `x` in the piece,
  `selfPieceEquiv ρ (m · x) = ρ(selfConjugation(m)) (selfPieceEquiv ρ x)`, where `m · x` is
  the action of the representation `D.pieceFunctor.obj ρ` and `selfConjugation(m)` is
  `rationalPoints.map D.selfConjugation.hom m`.
- `exists_selfPieceEquiv`: the packaged form used downstream. There are an automorphism
  `ψ : M ≅ M` with `ψ.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso z).hom` (conjugation by `z` inside
  `G`) and a linear equivalence `T : D.pieceFunctor.obj ρ ≃ₗ[ℂ] ρ` with
  `T (m · x) = ρ(ψ(m)) (T x)` for all `m ∈ M(F)` and `x`. Proof: `ψ = selfConjugation`
  (with `selfConjugation_comp`) and `T = selfPieceEquiv ρ`.
- `subsingleton_or_exists_selfPieceEquiv`: the dichotomy for a supercuspidal `ρ`. The
  hypothesis `hρ` is the supercuspidality hypothesis in the form used by
  `MaximalLeviSupercuspidalInductionEndomorphismStatement`: for every represented parabolic
  `p' : P' ⟶ M` (with Levi `l'`, radical `r'`, multiplication isomorphism `hmul'`) that is not
  an isomorphism, the normalized Jacquet module `(jacquetFunctor p' l' r' hp' hr' hl' hmul').obj ρ`
  is a subsingleton. Conclusion: either the piece `D.pieceFunctor.obj ρ` is a subsingleton,
  or `D.p'` is an isomorphism and the conclusion of `exists_selfPieceEquiv` holds. Proof: case
  split on `IsIso D.p'`; if it holds, `exists_selfPieceEquiv`; otherwise `hρ` applied to the
  datum's `P' = M ∩ zPz⁻¹` gives a vanishing Jacquet module, and `subsingleton_pieceFunctor_obj`
  (module `Langlands.Representation.Geometric.DegenerateJacquetPieces`) gives a vanishing piece.

The equivalence is stated as an intertwining linear equivalence rather than an isomorphism in
`Rep`, since the piece lives in `Rep.{max u v}` and `ρ` in universe `v`.

## Proof of `selfPieceEquiv_representation`

Since `lQ' ≫ q' : L' ⟶ M` is an isomorphism (`isIso_lQ'_comp_q'_of_isIso_p'`), every
`m ∈ M(F)` is `(lQ' ≫ q')(a)` with `a = (lQ' ≫ q')⁻¹(m) ∈ L'(F)`. By
`selfConjugation_map_rationalPoints` and `D.e_apply`, the right-hand side becomes
`ρ((l' ≫ p')(e a))`. On the left, `isoParabolicInductionEquiv_map` turns the action of
`(lQ' ≫ q')(a)` on the induced representation into the action of `a` on the pullback along
`e`, which is the Jacquet action of `e a`; then `fullLeviJacquetEquiv_representation` turns
that into `ρ((l' ≫ p')(e a))`.

Neither maximality of `P` nor properness of `P` is used.
