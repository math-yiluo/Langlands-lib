# Rational conjugation of split subtori into pseudo-parabolic subgroups

`Langlands.GroupScheme.SplitTorusIntoPseudoParabolicStatement.{u}` is an
unproved proposition target. For every field `k : Type u`, actual group
schemes `G,P` over `Spec (CommRingCat.of k)`, actual homomorphism
`i : P ⟶ G`, commutative group scheme `S` over the same base and actual
homomorphism `j : S.toGrp ⟶ G`, it asserts

```text
Smooth G.X.hom → IsAffineHom G.X.hom → ConnectedSpace G.X.left →
  IsPseudoParabolicSubgroup i → IsSplitSubtorus j →
    ∃ (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
      (f : S.toGrp ⟶ P), f ≫ i = j ≫ (G.innerIso g).hom.
```

The three ambient hypotheses are typeclass binders in Lean. Smoothness and
affineness refer to the structure morphism; connectedness is ordinary
connectedness of the underlying scheme. The field and universe are arbitrary,
so the statement covers finite and imperfect fields. It requires neither
reductivity nor pseudo-reductivity of `G`.

## Hypotheses

The module imports the published `Langlands.GroupScheme.PseudoParabolic`,
`Langlands.GroupScheme.InnerAutomorphism` and
`Langlands.GroupScheme.Rational.SplitTorus` unchanged.

`IsPseudoParabolicSubgroup i` already includes the three ambient properties
of `G` and a product presentation of `i` from a ground-field unipotent radical
and the dynamic parabolic of an actual cocharacter. The ambient properties
are repeated as explicit binders to expose the geometric setting, as in the
companion target `PseudoParabolicSubgroupStructureStatement`. The supplied
`i` is the subgroup inclusion; `IsPseudoParabolicSubgroup.isClosedSubgroup`
extracts `IsClosedSubgroup i`. The statement uses no smoothness or
connectedness of `P`, and no quotient `G/P`.

`IsSplitSubtorus j` is `IsSplitTorus S.toGrp ∧ IsClosedSubgroup j`: the
group scheme `S` is isomorphic to `splitTorus` on some finite index type, and
`j` is a closed immersion. The statement applies to every split subtorus,
not only to maximal split subtori, and includes the trivial split torus.

## Conclusion

The rational point `g` is a section of `G.X` over the base, that is, an
element of `G(k)`. By `comp_innerIso_hom`, `(G.innerIso g).hom` acts on the
points over every test scheme `T` by `x ↦ g_T x g_T⁻¹`, where `g_T` is the
pullback `constantPoint G g T`. The equation says that the conjugate
homomorphism `j ≫ (G.innerIso g).hom` factors through the inclusion `i` by a
group-scheme homomorphism `f`. This is the actual factorization form of the
containment `g S g⁻¹ ⊆ P`.

For fixed `G`, `P` and `i`, the conclusion over all `S` and `j` has the same
form as the body of the published
`Langlands.GroupScheme.SplitToriConjugateInto i` in
`Langlands.GroupScheme.Rational.MaximalSplitTorusDescentStatement`. That
module is not imported here.

## Source and derived provenance

The source is Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second edition
(2015), registered as `conrad-gabber-prasad-2015-pseudo-reductive`, SHA256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
Printed page `p` is PDF page `p + 26`.

Lemma C.2.2, on printed p.593 (PDF p.619), states: for a smooth connected
affine group `G` over a field `k`, a `k`-split solvable smooth connected
`k`-subgroup `H`, and any pseudo-parabolic `k`-subgroup `P ⊆ G`, there exists
`g ∈ G(k)` with `g⁻¹ H g ⊆ P`. CGP's rational point is therefore inverted
when the conclusion is written with `innerIso`, which conjugates by
`x ↦ g x g⁻¹`. Existence is unchanged by this inversion.

This target is a derived specialization of Lemma C.2.2 to `H` the image of a
split subtorus. The specialization uses the fact that a split torus is a
`k`-split solvable smooth connected affine `k`-group (the notion reviewed at
the beginning of CGP §B.1). That bridge is a proof obligation and is not
proved or assumed here. Theorem C.2.3 (Borel–Tits), on printed pp.593–594
(PDF pp.619–620), applies Lemma C.2.2 in this way to a maximal `k`-split
torus.

CGP's proof of Lemma C.2.2 uses the left translation action of `H` on the
coset space `G/P` and three further results, all of which remain proof
obligations:

- Proposition C.1.6, printed p.586 (PDF p.612): `G/P` is pseudo-complete over
  `k` in the sense of Definition C.1.1, printed p.581 (PDF p.607), a variant
  of the valuative criterion for properness;
- Proposition C.1.5, printed p.585 (PDF p.611): a `k`-split solvable smooth
  connected affine group acting on a pseudo-complete `k`-scheme with a
  rational point has a rational fixed point;
- Lemma C.2.1, printed p.592 (PDF p.618): `G(k) → (G/P)(k)` is surjective;
  for finite `k` the source proves this from Lang's theorem.

The proof must also construct the quotient `G/P` and its action. Rational
surjectivity is not a consequence of an fppf quotient projection alone and
must be proved as in Lemma C.2.1.

This module defines a `Prop` and supplies no proof or new instance. It does
not assume a conjugacy theorem, properness of `G/P`, or perfectness or
infinitude of `k`.
