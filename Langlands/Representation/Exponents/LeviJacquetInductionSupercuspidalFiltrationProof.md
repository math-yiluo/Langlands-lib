# Renard VI.5.3 (iii) for represented parabolics: proof

Author: Worker 5106. Module
`Langlands.Representation.Exponents.LeviJacquetInductionSupercuspidalFiltrationProof`,
namespace `Langlands.Aubert.General.RepresentedParabolic`.

The main theorem is

```lean
theorem leviJacquetInductionSupercuspidalFiltration :
    LeviJacquetInductionSupercuspidalFiltrationStatement.{u, v}
```

It proves the published `LeviJacquetInductionSupercuspidalFiltrationStatement`
(Renard 2026, VI.5.3, Proposition, assertion (iii), printed p.173 / PDF p.179; registered
source `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`). It has the
statement's universes `u` (field) and `v` (coefficients) as independent parameters and
adds no hypothesis.

The proof has two parts:

- `leviJacquetInductionSupercuspidalFiltration_of_geometricLemma` deduces the target from
  the published `RepresentedGeometricLemmaStatement.{u, v}` (Renard VI.5.1 for
  represented parabolics, in filtration form). It is described in the section "The
  deduction" below.
- The main theorem applies that deduction to the published proof
  `representedGeometricLemma` of the geometric lemma, from
  `Langlands.Representation.Geometric.RepresentedGeometricLemmaProof`.

Renard derives (iii) from the geometric lemma VI.5.1 and Lemma V.4.6 (iii). The Lean
route uses the geometric lemma in the same way. Instead of Weyl-group combinatorics it
compares index sets through a dynamic-limit argument that is already in the Library.

## Helper constructions

All four are in namespace `GeometricLemmaIntersectionDatum`. They concern one datum
`D : GeometricLemmaIntersectionDatum … z` of the represented geometric lemma, an
isomorphism `E : M ≅ L` of the outer Levis and a proof `h : IsIso D.p'` that the source
intersection `M ∩ zQz⁻¹` is all of `M`. Under these hypotheses the target intersection is
full too, by the published `isIso_q'_of_isIso_p'_of_iso`. So the published constructions
of `Exponents/ActualGeometricFullPiece` apply.

- `fullTargetConjugacy E h : {ψ : L ≅ M // ψ.hom ≫ l ≫ p = lQ ≫ q ≫ (G.innerIso z).hom}`
  is the inverse of the published `fullLeviConjugacy`. That isomorphism `ε : M ≅ L`
  satisfies `ε.hom ≫ lQ ≫ q = l ≫ p ≫ inner(z⁻¹)`. The equation for `ε⁻¹` comes from
  composing with `ε.inv` on the left and `inner(z)` on the right, as in the published
  `isIso_p'_iff`. So `z L z⁻¹ = M` for the representative `z` itself.
- `fullTargetPointsEquiv E h : L(F) ≃ₜ* M(F)` is the inverse of the published
  `fullLeviPointsEquiv`, with the canonical Levi topologies `leviPointTopology`.
- `fullTargetPointsEquiv_apply` says that it is the point map of
  `(fullTargetConjugacy E h).val`. Apply `fullLeviPointsEquiv` to both sides. The
  published `fullLeviPointsEquiv_apply` identifies `fullLeviPointsEquiv` with the point
  map of `ε.hom`, and the point map of `ε.inv ≫ ε.hom = 𝟙` is the identity.
- `fullTargetPieceEquiv E h σ` is the published `fullPieceEquiv σ`. It is a
  `Representation.Equiv` between the geometric piece `D.pieceFunctor.obj σ` and
  `σ ∘ fullLeviPointsEquiv⁻¹`, which is by definition
  `(SmoothRep.pullback (fullTargetPointsEquiv E h) σ).representation`.

## The deduction

`leviJacquetInductionSupercuspidalFiltration_of_geometricLemma` introduces the field, the
group, the two represented parabolics and the conjugacy hypothesis. It keeps only the
isomorphism `E : M ≅ L` from that hypothesis. It installs the affine and topological
instances of the statement, and then introduces `ρ` and its supercuspidality `hρ`.

1. **Geometric lemma.** Applying the hypothesis to `(P, M, N)` and `(Q, L, U)` gives an
   enumeration `c₀ : Fin m₀ ≃ P(F)\G(F)/Q(F)`, representatives `z₀ i` of `c₀ i`, data
   `D i` and the gluing `IsGluedFrom (leviJacquetInductionFunctor …) (D · ).pieceFunctor`.
2. **Vanishing pieces.** If `(D i).p'` is not an isomorphism, `hρ` applied to the
   represented parabolic `((D i).p', (D i).l', (D i).r')` of `M` kills its Jacquet module.
   The published `subsingleton_pieceFunctor_obj` then makes the piece at `ρ` zero.
3. **Deleting the zero pieces.** The published `IsGluedFrom.exists_selected_filtration`,
   with the predicate `IsIso (D i).p'`, evaluates the glued filtration at `ρ` and
   deletes the excluded pieces. It gives `m`, a bijection
   `e : Fin m ≃ {i // IsIso (D i).p'}` and an `ObjectRepFiltration` `s` of
   `(leviJacquetInductionFunctor …).obj ρ`, which is by definition
   `SmoothRep.toRep.obj τ`. Its `j`th graded representation is equivalent to the piece of
   `D (e j)` at `ρ`.
4. **Index set.** The published `fullIndexEquiv`, applied to the published proof
   `parabolicDynamic` of `ParabolicDynamicStatement`, to `hG` and to `E`, restricts `c₀`
   to a bijection from `{i // IsIso (D i).p'}` onto the subtype of double cosets that
   contain some `w` with `ψ : L ≅ M` and `ψ.hom ≫ l ≫ p = lQ ≫ q ≫ inner(w)`. This
   subtype is the index type of the statement. The enumeration is
   `c = e.trans (fullIndexEquiv …)`. Since `(fullIndexEquiv … i).1 = c₀ i` by definition,
   `DoubleCoset.mk (z j) = (c j).1` holds by `hz₀`, with `z j = z₀ (e j)`.
5. **Witnesses.** For each `j` the statement's `φ j` is
   `(fullTargetConjugacy E (e j).2).val`, and its conjugacy equation is the property of
   that subtype. `e j` is `fullTargetPointsEquiv E (e j).2`, and the equation
   `e j x = rationalPoints.map (φ j).hom x` is `fullTargetPointsEquiv_apply`. The `j`th
   graded representation of `s` is equivalent to the piece by step 3. The piece is
   equivalent to `(SmoothRep.pullback (e j) ρ).representation` by `fullTargetPieceEquiv`.
   The composite `Representation.Equiv` is the required witness.
6. **Supercuspidality of `τ`.** Each `SmoothRep.pullback (e j) ρ` is supercuspidal, in
   the sense of the published `IsSupercuspidal`, by the published
   `isSupercuspidal_pullback_of_iso` for `φ j : L ≅ M`. A proper parabolic `p'` of `L`
   becomes the proper parabolic `p' ≫ φ j` of `M`, where `hρ` applies. The published
   `isSupercuspidal_of_filtration`, applied to `s` and the equivalences of step 5, gives
   `IsSupercuspidal τ`. That is the second conjunct of the statement. That theorem uses only
   right exactness of coinvariants along the filtration; no exactness of the Jacquet
   functor is assumed.

The deduction uses no hypothesis beyond the geometric-lemma statement. In particular
there is no standardness, admissibility, irreducibility, finite-length or Weyl-group
premise.

## The main theorem

`leviJacquetInductionSupercuspidalFiltration` is
`leviJacquetInductionSupercuspidalFiltration_of_geometricLemma representedGeometricLemma`.
So the target holds unconditionally. The axioms reported for it are `propext`,
`Classical.choice` and `Quot.sound`.
