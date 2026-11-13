# Conjugating maximal split tori inside the centralizer of a split torus

Author: Worker 149 (Task 5622). This is a helper module for the proof of
`Langlands.GroupScheme.TitsIndexIndependenceStatement` in
`Langlands.GroupScheme.Reductive.TitsIndexIndependenceProof`.

## Statement

`Langlands.GroupScheme.exists_centralizing_conj_of_isMaximalSplitTorus`. The
universe is `u`. Fix:

- a field `K : Type u` and a group scheme `H` over `Spec K` with
  `IsConnectedReductive H`;
- a commutative group scheme `A` over `Spec K` that is a split torus
  (`IsSplitTorus A.toGrp`), and a homomorphism `a : A.toGrp ⟶ H`;
- two homomorphisms `t₁ : T₁.toGrp ⟶ H` and `t₂ : T₂.toGrp ⟶ H`, both maximal split
  tori (`IsMaximalSplitTorus`);
- homomorphisms `f₁ : A ⟶ T₁` and `f₂ : A ⟶ T₂` with `f₁ ≫ t₁ = a` and
  `f₂ ≫ t₂ = a` (after `CommGroupScheme.groupHom`). So both tori contain the image
  of `a`.

Conclusion: there are a `K`-point `z` of `H`, given as
`Over.mk (𝟙 (Spec K)) ⟶ H.X`, and an isomorphism `φ : T₁ ≅ T₂` with two
properties:

1. conjugation by `z` carries `t₁` onto `t₂` through `φ`:
   `t₁ ≫ (H.innerIso z).hom = groupHom φ.hom ≫ t₂`;
2. `z` centralizes `a`: `a ≫ (H.innerIso z).hom = a`.

Mathematically: two maximal split tori of a connected reductive group that both
contain a split torus `A` are conjugate by a rational point of the centralizer of
`A`. There is no hypothesis that `a` is a monomorphism.

## Provenance

This is an internal helper lemma. No literature source is claimed for this Lean
statement. It is the standard reduction of conjugacy of maximal split tori to the
centralizer `Z_H(A)`: that centralizer is connected reductive, it contains both
tori as maximal split tori, and conjugacy of maximal split tori in it gives a
conjugating point that centralizes `A`. Every step is a published Library theorem.

## Proof

1. `IsSplitTorus.exists_cocharacter_centralizer_eq`
   (`Langlands.GroupScheme.Rational.SplitTorusCentralizerReduction`) gives a
   cocharacter `ν` of `A`. The dynamic centralizer of `χ = ν ≫ a` equals
   `torusCentralizer a`.
2. `j = Dynamic.Affine.centralizerHom χ`
   (`Langlands.GroupScheme.Dynamic.AffineRepresentability`) is a closed subgroup
   (`Dynamic.Affine.isClosedSubgroup_centralizerHom`). It represents the dynamic
   centralizer (`Dynamic.Affine.isRepresentedBy_centralizerHom`), and so represents
   `torusCentralizer a` by step 1.
3. `splitTorusCentralizerReductive`
   (`Langlands.GroupScheme.Rational.SplitTorusCentralizerReductiveProof`) shows that
   the centralizer scheme `Dynamic.Affine.centralizerScheme χ` is connected
   reductive.
4. Each `tᵢ` factors through `a`, so its range lies in the centralizer
   (`range_le_torusCentralizer_of_factor`,
   `Langlands.GroupScheme.Rational.MaximalSplitTorusCentralizer`).
   `IsMaximalSplitTorus.lift`
   (`Langlands.GroupScheme.Rational.MaximalSplitTorusSubgroup`) then lifts `tᵢ` to a
   maximal split torus `qᵢ` of the centralizer, with `qᵢ ≫ j = tᵢ`.
5. `smoothMaximalSplitTorusConjugacy`
   (`Langlands.GroupScheme.Rational.SmoothMaximalSplitTorusConjugacyProof`), applied
   in the centralizer, gives a point `p` and a group isomorphism `e` with
   `q₁ ≫ inn(p) = e ≫ q₂`. Set `z = p ≫ j` and
   `φ = CommGroupScheme.isoOfGroupIso e`
   (`Langlands.GroupScheme.Torus.SplitLatticeBaseChange`).
6. Property 1 follows from `comp_innerIso_hom_comp`
   (`Langlands.GroupScheme.Rational.ParabolicCocharacterConjugacy`): conjugation by
   `p` in the subgroup is compatible with conjugation by its image `z`. For
   property 2, `z` is a `K`-point of the subgroup that represents
   `torusCentralizer a`. So `mem_torusCentralizer_base_iff`
   (`Langlands.GroupScheme.Rational.TorusCentralizer`) gives `a ≫ inn(z) = a`.

The axioms used are only `propext`, `Classical.choice` and `Quot.sound`. The
module's imports are all in `Langlands.GroupScheme.Rational` and
`Langlands.GroupScheme.Dynamic`. Their transitive closure contains no
local-rank-one classification or Kneser–Tits module.
