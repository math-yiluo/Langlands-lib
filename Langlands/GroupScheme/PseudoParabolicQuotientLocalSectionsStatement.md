# Zariski local sections of pseudo-parabolic quotients

Author: Worker 1373.

`Langlands.GroupScheme.PseudoParabolicQuotientLocalSectionsStatement` is a
Prop-valued definition stating the infinite-field local-sections conclusion
of Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second edition (2015),
Lemma C.2.1 and its proof, printed pp.592–593 (PDF pp.618–619). The registered
source is `conrad-gabber-prasad-2015-pseudo-reductive`, SHA-256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
Both pages of the original passage were read. No project errata note for this
source was present when this statement was prepared.

For every field `k : Type u` with `[Infinite k]`, write
`B = Spec (CommRingCat.of k)`. The ambient data are an actual group scheme
`G` over `B` with `Smooth G.X.hom`, `IsAffineHom G.X.hom` and
`ConnectedSpace G.X.left`, an actual group scheme `P`, and a homomorphism
`i : P ⟶ G` satisfying the published `IsPseudoParabolicSubgroup i`.
Universe `u` is arbitrary. The public pseudo-parabolic module and its
ground-field radical and fppf-product imports are used unchanged.

The proposition applies to every supplied actual relative scheme
`Q : Over B` and morphism `q : G.X ⟶ Q` with exactly the homogeneous quotient
conditions from the public `SmoothSubgroupQuotientExistenceStatement`:

- `IsSeparated Q.hom`, `LocallyOfFiniteType Q.hom` and `QuasiCompact Q.hom`;
- `Smooth q.left`, `Surjective q.left` and `QuasiCompact q.left`;
- for every `T : Over B` and `g h : T ⟶ G.X`,
  `g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T`.

The final condition specifies exact right-coset fibers on all relative
scheme tests, including nonaffine and nonreduced tests. Quotient existence
is not asserted in this file.

The conclusion is

```lean
∀ x : Q.left, ∃ (U : Q.left.Opens) (s : openOver k Q U ⟶ G.X),
  x ∈ U ∧ s ≫ q = openOverι k Q U
```

Here `x` ranges over every topological point of the scheme `Q.left`.
`openOver k Q U` is the actual open subscheme of `Q` with its structure
morphism to `B`, and `openOverι k Q U` is its actual inclusion in `Q`,
using the public helpers in
`Langlands.AlgebraicGeometry.PointTopology.SchemePoints`. The morphism `s`
is over `B`, and its composite with `q` is that open inclusion. Consequently
these are algebraic sections on Zariski neighborhoods covering all of `Q`,
not merely neighborhoods of its rational points.

This matches the first conclusion of CGP Lemma C.2.1. Its other conclusion,
rational lifting for every field, is separately reusable as
`PseudoParabolicQuotientRationalLiftingStatement`. Only the present
local-sections statement has an infinitude hypothesis. Neither statement
assumes perfectness, reductivity, pseudo-reductivity, quotient properness,
density of `G(k)`, or a pre-existing section. Smoothness and connectedness
of `P` are not extra premises.

The source's proof first treats finite-field rational lifting by Lang's
theorem for the smooth connected subgroup `P`; that does not give the
local-sections assertion over finite fields. For infinite fields, it
argues by dimension, removing `R_{us,k}(G)`, the maximal split ground-field
unipotent radical. Its torsor has sections on affine opens. After that
reduction, a dynamic parabolic has an opposite cell giving one open
section. Translates give a cover when rational points are dense. The
authors handle the possible failure of density of `G(k)` over imperfect
fields by passing to the smooth connected normal subgroup `G_t` generated
by ground-field tori. This subgroup is unirational and has dense rational
points over an infinite field; the proof identifies its corresponding
quotient with `G/P`.

This is a statement file, not an implementation of that proof. The radical
reduction, structural properties of `P` and `G_t`, quotient comparisons and
construction of the full open cover remain proof obligations. Density of
the original `G(k)` and properness of `G/P` are not inserted as hypotheses.
