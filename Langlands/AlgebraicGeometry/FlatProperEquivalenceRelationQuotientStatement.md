# Effective quotients by flat proper equivalence relations on quasi-projective schemes

Author: Worker 22, for task `07219dde-fd87-48cf-83be-db16cbb3707c` (Task 5705).
The interface was agreed with Worker 5705, who uses the statement in the
Picard construction of that task.

## Statement

`Langlands.AlgebraicGeometry.FlatProperEquivalenceRelationQuotientStatement.{u}`
is a proposition with no proof asserted here. It quantifies over

- a noetherian commutative ring `A : Type u`, with `S = Spec (CommRingCat.of A)`;
- schemes `Z` and `R` in universe `u`, a morphism `p : Z ⟶ S`, and two
  morphisms `s t : R ⟶ Z` with `h : s ≫ p = t ≫ p`.

Its hypotheses are:

1. `IsHQuasiProjective p`: `Z` has a quasi-compact immersion into some
   `ProjectiveSpace A n` over `S` (see `Langlands.AlgebraicGeometry.HQuasiProjective`).
2. `Mono (pullback.lift s t h)`: the induced morphism `R ⟶ Z ×_S Z` is a
   monomorphism of schemes. Equivalently, for every scheme `T` the map from
   `T`-points of `R` to pairs of `T`-points of `Z` is injective.
3. For every scheme `T : Scheme.{u}`, the relation on morphisms `T ⟶ Z` given by
   `x ~ y ↔ ∃ φ : T ⟶ R, φ ≫ s = x ∧ φ ≫ t = y` is an equivalence relation
   (`Equivalence`).
4. `Flat s` and `IsProper s` (Mathlib's flatness and properness).

The conclusion is that there are a scheme `Q`, a morphism `q : Q ⟶ S` and a
morphism `π : Z ⟶ Q` such that

- `IsHQuasiProjective q`;
- `π ≫ q = p`, so `π` is a morphism over `S`;
- `π` is flat, surjective, proper and locally of finite presentation;
- `IsPullback s t π π`: the square formed by `s`, `t` and two copies of `π` is
  a pullback square. In particular `s ≫ π = t ≫ π`, and the induced morphism
  `R ⟶ Z ×_Q Z` is an isomorphism, so the equivalence relation is effective.

Hypotheses 2 and 3 together say that `R`, with `(s, t)`, is a schematic
equivalence relation on `Z` over `S` in Nitsure's sense: the functor of points
of `R` is the graph of an equivalence relation on the functor of points of `Z`.
Hypothesis 3 is required for all schemes `T`, not only for `S`-schemes. Since
`s ≫ p = t ≫ p`, related points always have the same image in `S`, so the
relation is the same on `S`-points.

## Sources

The statement is the scheme-theoretic quotient theorem of Altman and Kleiman.
Kleiman uses it in the proof of Lemma 4.9 of *The Picard scheme*
(`kleiman-2005-picard-scheme-arxiv-math0504020v1`, pp.30–31). There, from a
flat proper `R ⟶ Z` with `R ⊆ Z ×_S Z` the graph of an equivalence relation on
`T`-points and `Z` quasi-projective over `S`, he concludes "there exist a
quasi-projective `S`-scheme `Q` and a faithfully flat and projective map
`Z → Q` such that `R = Z ×_Q Z` (in other words, a flat and proper equivalence
relation on a quasi-projective scheme is effective)". He cites [AK80,
Thm. (2.9), p. 70], which is not among the retained sources.

The retained source with a complete noetherian proof is N. Nitsure,
*Construction of Hilbert and Quot schemes*
(`nitsure-2005-hilbert-quot-arxiv-math0504590v1`). Theorem 6.8 (p.33) reads:
let `S` be a noetherian scheme and `X → S` quasi-projective, and let
`f : R → X ×_S X` be a schematic equivalence relation whose projections
`f₁, f₂` are proper and flat. Then a schematic quotient `X → Q` exists over
`S`, `Q` is quasi-projective over `S`, the morphism `X → Q` is faithfully flat
and projective, and `R → X ×_Q X` is an isomorphism. The schematic equivalence
relation is defined on pp.31–32. Theorem 6.9 (p.36) gives the same conclusion
under strong quasi-projectivity, with `X → Q` strongly projective and `Q`
strongly quasi-projective.

## Relation between the Lean statement and the sources

- **Base.** The base is the affine noetherian scheme `Spec A`, a special case of
  Nitsure's noetherian base.
- **Quasi-projectivity.** "Quasi-projective" is replaced by `IsHQuasiProjective`
  for both `Z` and `Q`. Over an affine base the two notions agree: Stacks Lemma
  29.44.16 in the retained snapshot
  `stacks-projective-space-twists-morphisms-2026-10-26` shows that
  quasi-projective implies H-quasi-projective, and Lemma 29.44.11 with Lemma
  29.44.3 gives the converse.
- **Flatness and properness of `t`.** Only `s` is assumed flat and proper.
  Nitsure assumes both projections are. Symmetry of the relation (hypotheses 2
  and 3, applied to `T = R`) gives an automorphism of `R` exchanging `s` and
  `t`, so `t` is flat and proper as well.
- **Conclusions on `π`.** "Faithfully flat" is stated as `Flat π ∧ Surjective π`.
  "Projective" is weakened to `IsProper π`, because the Library has no
  projectivity predicate for morphisms with a non-affine target. A projective
  morphism is proper (Stacks Lemma 29.44.5 in the same snapshot).
  `LocallyOfFinitePresentation π` is also derived: `Z` is of finite type over
  the noetherian ring `A`, so `π` is locally of finite type, and the target `Q`
  is locally noetherian.
- **Effectiveness.** `R = Z ×_Q Z` is stated as `IsPullback s t π π`. Nitsure's
  coequaliser property of `π` is not part of the statement.

These are explanations of the derivation, not Lean proofs.

## Use

In Kleiman's proof of the main Theorem 4.8, the quotient is applied with `Z` an
open subscheme of the scheme of relative effective divisors and with `R` the
linear-system equivalence relation. The resulting `Q` represents a piece of
the Picard sheaf. Task 5705 uses the statement for this step.
