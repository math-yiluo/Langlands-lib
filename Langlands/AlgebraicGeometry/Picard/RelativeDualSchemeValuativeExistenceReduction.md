# Original-ring valuative existence from dominating-ring Picard-zero extension

Authors: Worker 2093 wrote the Lean proof and the first version of this
Markdown (shared as revision 3 of the public draft of task
`54d4a7cc-7607-4c5a-82e7-25bafba9e3e9`). Worker 198 rechecked it unchanged
against the published statement and revised this Markdown for submission
under task `85f8f1aa-3b75-418f-97f6-1261f6b7d291`.

The theorem
`Langlands.AbelianScheme.relativeDualSchemeValuativeExistenceReduction`
proves the exact internal proposition
`Langlands.AbelianScheme.RelativeDualSchemeValuativeExistenceReductionStatement.{u}`:

```lean
PicardZeroValuativeExtensionStatement.{u} →
  RelativeDualSchemeValuativeExistenceStatement.{u}
```

The first proposition remains an explicit premise; the module does not
import its published proof
`Langlands.AlgebraicGeometry.Picard.PicardZeroValuativeExtensionProof`.
This result alone does not prove either constituent proposition. It proves
the derived statement of task `4c2d89fa-73d6-4f69-a6eb-439a293038d1`, a
prerequisite of task `54d4a7cc-7607-4c5a-82e7-25bafba9e3e9`, using the
existing Library definitions and published compatibility proofs. It is not
a translation of an original-literature assertion.

## Descent over the original ring

The `ValuativeDescent` helpers apply to an arbitrary morphism of schemes.
`hasLift_of_specialization` extracts the stalk argument of Mathlib's
`ValuativeCriterion.Existence.of_specializingMap` (Apache 2.0; authors
Andrew Yang, Qi Ge, Christian Merten; attribution in the Lean file header).
Let `x` be a point of the fibre product `pullback sq.i₂ f` that is a
specialization of the image of the point of `Spec K` under the map induced by
`Spec.map (algebraMap R K)` and `i₁`, and whose first projection is the
closed point of `Spec R`. Then the square has a lift over the original
ring. The local map from `R` to the stalk at `x`, followed by the map from
that stalk to `K` given by the specialization, has composite
`algebraMap R K`.
`bijective_rangeRestrict_comp_of_valuationRing` identifies the image in `K`
with `R`, constructing the required stalk-to-`R` map. Applying `Spec` and
the canonical map from a stalk spectrum to the scheme constructs the lift
and proves both triangle equations.

`hasLift_of_dominatingLift` maps the closed point of a dominating valuation
ring into that fibre product. The equality over the extension fraction
field proves the required specialization of the original generic image.
The local ring map proves that this point lies over the original closed
point. It then applies the preceding helper, so the final lift is over the
original `R` and `K`, even though the supplied preliminary lift used `R'`
and `K'`.

Neither helper assumes quasi-compactness, separatedness, finite type,
properness, or quasi-separatedness of the morphism `f` or of its source. The first helper follows
the corresponding portion of Mathlib's
`ValuativeCriterion.Existence.of_specializingMap`; it takes the required
specialization directly rather than assuming a universal specializing-map
property. Its construction works for valuation rings of arbitrary rank,
including fields.

## Classification of the extended family

`relativeDualSchemeValuativeExistence_of_picardZeroValuativeExtension`
implements the implication. Let `sq` be an arbitrary valuative square for
`(dualScheme A hA).hom`, with rings `R` and `K`. Its top map is a morphism
`g : TK ⟶ dualScheme A hA` in `Over S`, where
`TK = Over.mk (Spec.map (algebraMap R K) ≫ sq.i₂)`.

1. Let `q₀` be the class of `poincareFamily A hA`. It is Picard zero by
   `poincareFamily_universal`. Pulling it back along `g` gives
   `q : PicardZeroClasses A TK`. The published theorems
   `RigidifiedModule.pullbackCoherence` and `picardZeroPullback` supply the
   compatibility inputs to `dualClassify_pullback` and
   `dualClassify_poincare`. These imply `dualClassify A hA TK q = g`.
2. Apply the explicit premise `hExt` to `q`. It produces `R'`, `K'`,
   `φ : R →+* R'`, `ψ : K →+* K'`, the local-map proof and the
   fraction-field square, together with an actual extended Picard-zero
   class `q'` over `TR' = Over.mk (Spec.map φ ≫ sq.i₂)`.
3. On the common test scheme `TK'`, the extension equation is equality
   between the actual pullbacks along
   `h : TK' ⟶ TR'` and `k : TK' ⟶ TK`. Applying `Subtype.ext` gives
   equality of the Picard-zero classes themselves.
   `dualClassify_pullback` converts this into
   `h ≫ dualClassify A hA TR' q' = k ≫ g`.
4. The underlying scheme morphism of `dualClassify A hA TR' q'` is the
   preliminary lift over `R'`. The equation just obtained is its generic
   compatibility; its second triangle is `Over.w`. The helper
   `ValuativeDescent.hasLift_of_dominatingLift` gives the requested lift
   over the original `R`, satisfying both original triangle equations.

The final theorem `relativeDualSchemeValuativeExistenceReduction` is the
same implication packaged with the named proposition as its exact type.
The entire argument is universe-polymorphic in `u`; all rings, fields,
schemes and stalks used here stay in the universes of the statement.
The base hypothesis is exactly `QuasiSeparatedSpace S`. No source
Picard-functor comparison or dual existence construction is used, and no
geometric property of the chosen dual is assumed.

The transparency options `backward.isDefEq.respectTransparency` and
`backward.isDefEq.respectTransparency.types`, set to `false`, match existing
Picard compatibility modules. They affect elaboration only and add no
mathematical assumptions; the final theorem depends only on the axioms
`propext`, `Classical.choice` and `Quot.sound`.
