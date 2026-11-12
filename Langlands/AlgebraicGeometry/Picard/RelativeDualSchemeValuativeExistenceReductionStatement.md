# Reduction from dominating-ring Picard-zero extension to dual valuative existence

`Langlands.AbelianScheme.RelativeDualSchemeValuativeExistenceReductionStatement`
is a proposition definition. Its body is the implication

```lean
PicardZeroValuativeExtensionStatement.{u} →
  RelativeDualSchemeValuativeExistenceStatement.{u}
```

between two existing Library propositions in the namespace
`Langlands.AbelianScheme`. They are imported unchanged from
`Langlands.AlgebraicGeometry.Picard.PicardZeroValuativeExtensionStatement`
and
`Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeValuativeExistenceStatement`.
Their paired Markdown files give their complete quantifiers. This unit only
defines the implication. It does not prove the implication or either
constituent proposition, and it introduces no axiom.

## The two constituents

Both propositions are instantiated at the same universe `u`, and the
declaration is universe-polymorphic in `u`. The implication adds no
hypothesis to either side and redefines no predicate that they use.

The antecedent, `PicardZeroValuativeExtensionStatement.{u}`, quantifies over
a scheme `S : Scheme.{u}` with `[QuasiSeparatedSpace S]`, an abelian scheme
`A : AbelianScheme S`, a valuation domain `R : Type u` of arbitrary rank,
its fraction field `K : Type u`, a morphism `i₂ : Spec R ⟶ S`, and an actual
rigidified Picard-zero class `q : PicardZeroClasses A TK` over the test
scheme `TK = Over.mk (Spec.map (algebraMap R K) ≫ i₂)`. It asserts that
there exist:

- a valuation domain `R' : Type u` with fraction field `K' : Type u`;
- a local ring homomorphism `φ : R →+* R'` and a field homomorphism
  `ψ : K →+* K'` with `(algebraMap R' K').comp φ = ψ.comp (algebraMap R K)`;
- a class `q' : PicardZeroClasses A (Over.mk (Spec.map φ ≫ i₂))` over
  `Spec R'`;

such that the actual pullbacks
`RigidifiedLineBundle.classesPullback` of `q'` and of `q` to `Spec K'`
agree. It requires no dual scheme and has no `HasDualScheme` hypothesis.

The consequent, `RelativeDualSchemeValuativeExistenceStatement.{u}`,
quantifies over a scheme `S : Scheme.{u}` with `[QuasiSeparatedSpace S]`,
an abelian scheme `A : AbelianScheme S` and a proof
`hA : HasDualScheme A`. It asserts
`ValuativeCriterion.Existence (dualScheme A hA).hom`. Here
`dualScheme A hA` is the Library's actual chosen parameter scheme of a
universal rigidified Picard-zero family, from
`Langlands.AlgebraicGeometry.Picard.DualScheme`. Mathlib's
`ValuativeCriterion.Existence` requires every `ValuativeCommSq` to have a
lift. Such a square consists of a valuation domain `R : Type u` of arbitrary
rank, its fraction field `K : Type u`, and morphisms
`i₁ : Spec K ⟶ (dualScheme A hA).left` and `i₂ : Spec R ⟶ S` with
`i₁ ≫ (dualScheme A hA).hom = Spec.map (algebraMap R K) ≫ i₂`. The lift is
a morphism `l : Spec R ⟶ (dualScheme A hA).left` with
`Spec.map (algebraMap R K) ≫ l = i₁` and `l ≫ (dualScheme A hA).hom = i₂`.

The only base hypothesis on either side is `QuasiSeparatedSpace S`. The
consequent keeps its existing `HasDualScheme` hypothesis. No properness,
quasi-compactness, separatedness, finite-type, quasi-separatedness or other
geometric condition on the chosen dual or its structural morphism is
imposed.

## Extension after domination versus the original-ring conclusion

The two sides differ in which valuation ring they allow.

- The antecedent extends a class only after an alteration. The field `K`
  may be replaced by an extension `K'`, which need not be finite or
  algebraic. The ring `R` may be replaced by a valuation ring `R'` of `K'`
  that dominates the image of `R`: the local map `φ` and the ring-level
  square with `ψ` say this. The extended class is only asserted to agree
  with `q` after pullback to `Spec K'`.
- The consequent asks for a lift over the original `R` and `K` of the given
  square. It allows no field extension, no change of valuation ring and no
  base alteration. The lift must satisfy both triangle equations of the
  original square.

So the implication has two parts. First, the classes that the antecedent
supplies must be turned into morphisms to the chosen dual. Second, the
resulting lift over `R'` must be turned into a lift over `R`.

## Internal provenance

This is a derived, internal proposition and not a translation of an
original-literature assertion. Worker 2093 formulated it as a focused
prerequisite for the exact-target proof task
`54d4a7cc-7607-4c5a-82e7-25bafba9e3e9`, whose target is
`RelativeDualSchemeValuativeExistenceStatement`. That proposition's paired
Markdown gives the source background (Lan's thesis, Theorem 1.3.2.3) and
says why a direct internal route avoids a comparison with a source Picard
functor. The antecedent's paired Markdown describes the same route.

The intended proof works with the Library's actual rigidified classes,
actual pullbacks and geometric-fibre Picard-zero predicate. It is described
here as a plan, not as proof evidence:

1. Pull the class of the chosen Poincaré family `poincareFamily A hA` back
   along the top map `i₁` of a valuative square, viewed as a morphism
   `TK ⟶ dualScheme A hA` in `Over S`. This gives a class `q` over `Spec K`.
2. Apply the antecedent to `q`, obtaining `R'`, `K'`, `φ`, `ψ` and an
   extended class `q'` over `Spec R'`. Classifying `q'` with
   `dualClassify` gives a morphism `Spec R' ⟶ (dualScheme A hA).left` over
   `Spec.map φ ≫ i₂`. Compatibility of classification with actual pullback
   is the Library lemma `dualClassify_pullback`. Its coherence and stability
   inputs are the published theorems
   `Langlands.SchemeModule.RigidifiedModule.pullbackCoherence` and
   `Langlands.AbelianScheme.picardZeroPullback`. With
   `dualClassify_poincare`, it shows that this morphism restricts on
   `Spec K'` to `Spec.map ψ ≫ i₁`.
3. Descend to the original ring by the stalk argument of Mathlib's
   `ValuativeCriterion.Existence.of_specializingMap`. In the fibre product
   of `i₂` and the structural morphism of the dual, consider the point of
   `Spec K` mapped in by `Spec.map (algebraMap R K)` and `i₁`. The image of
   the closed point of `Spec R'`, under the map induced by `Spec.map φ` and
   the lift over `R'`, specializes that point and lies over the closed
   point of `Spec R`. Mathlib's
   `bijective_rangeRestrict_comp_of_valuationRing` then gives a ring map
   from the stalk at that image to `R`. This gives the lift over `R`.

Step 3 is where the change of valuation ring is undone. It needs only that
`φ` is local and that the ring-level square with `ψ` commutes. It does not
use any geometric property of the dual. Worker 2093 reports an unreviewed
compiled Lean draft of this route, shared as a public draft of task
`54d4a7cc-7607-4c5a-82e7-25bafba9e3e9`. That draft is not part of this unit
and is not evidence for it.

## Authorship

Worker 2093 specified the exact Lean statement in the objective of task
`4c2d89fa-73d6-4f69-a6eb-439a293038d1` and wrote the first draft of this
module and Markdown. Worker 3612 checked the draft against the two imported
statement pairs and the Library's `DualScheme` module, and expanded this
Markdown.
