# Joint normalized determinant and numerical action presheaves

Author: Worker 57.

This internal construction combines the normalized Harris–Taylor determinant condition and prescribed geometric dimension on one actual rational algebra action. It constructs their image in actual equivariant rational-isomorphism classes, proves arbitrary-base-change stability, and forms a subpresheaf on schemes over the actual CM spectrum. The exact named `LieBaseChangeNaturalityStatement` remains an explicit hypothesis.

The parameters are a totally real number field `E`, a totally complex quadratic extension `F/E` with CM structure, a central simple unitary datum `D` of degree `n`, the compatible rational, `E` and `F` algebra structures and scalar towers on `A`, an imaginary quadratic CM field `L`, an `L`-algebra structure on `F`, an embedding `τ₀ : L →+* ℂ`, and actual signature charts `C` for `harrisCMSection E (algebraMap L F) τ₀`. These types and schemes have universe zero. A base object is an actual map `p : S → Spec F`; an action is an actual abelian scheme `B/S` with `i : A →ₐ[ℚ] End0 B`.

The normalized determinant is the existing `HarrisTaylorCMRationalLieDeterminantCondition`. Its prescribed polynomial coefficients use the explicitly conjugated scalar map `harrisTaylorReflexToCM` and the constructed map `harrisTaylorReflexStructure C p`. The original unconjugated reflex map and its separate condition retain their existing meanings.

For an arbitrary scheme morphism `f : T → S`, `harrisTaylorCMRationalLieDeterminantCondition_baseChange_of_naturality` assumes `LieBaseChangeNaturalityStatement S`. It converts the normalized determinant to the existing reflex determinant condition at `harrisTaylorReflexStructure C p`, applies the proved reflex determinant pullback theorem, and uses `harrisTaylorReflexStructure_comp` to identify the resulting base map. Thus its conclusion concerns the actual pulled-back abelian scheme and the action obtained by composing `i` with `rationalBaseChangeEnd f B`. The generic theorem already handles every finite Lie chart and smaller open by actual local Lie pullback, chart comparison and coefficientwise sheaf separation. No flatness, affineness or reducedness restriction is added here.

`harrisTaylorCMDeterminantDimensionCondition_baseChange_of_naturality` combines this result with the existing arbitrary-base-change theorem for

```text
B.HasRelativeDimension ([E : ℚ] * n²).
```

Both conditions therefore hold on the same pulled-back representative.

`HarrisTaylorCMDeterminantClassCondition` is the existing well-defined reflex determinant class predicate evaluated at the normalized reflex structure. Its representative formula identifies it with the normalized determinant on that representative. Its pullback theorem follows the same normalized structure-map comparison.

The joint predicate `HarrisTaylorCMActionClassCondition` is explicitly

```text
∃ X : RationalAlgebraAction S A,
  classOf X = q ∧
  HarrisTaylorCMDeterminantDimensionCondition C p
    X.abelianScheme X.action.
```

There is one witness for the two conditions. In `harrisTaylorCMActionClassCondition_iff`, this image is proved equal to the conjunction of the normalized determinant class predicate and the existing `HarrisTaylor.NumericalActionClassCondition`. For the forward implication, the all-scalar central trace consequence converts the witness's determinant and dimension into its numerical condition. For the reverse implication, select the existing numerical image witness; the well-defined determinant class predicate gives the determinant on that same witness. Its geometric dimension then supplies the other conjunct. This argument needs no invariance of geometric dimension under arbitrary rational isomorphism.

The `_determinant` and `_centralTrace` theorems consequently give the normalized determinant and full central trace on every actual representative of a joint class. The latter quantifies over every CM scalar and the existing all-chart local section tests. Geometric dimension remains a condition on a satisfying witness.

`HarrisTaylorCMActionClass` is the subtype of ambient rational action classes with this joint predicate. `harrisTaylorCMActionClassOf` sends an actual jointly satisfying action to its class. Equality of two such classes is equivalent to an actual isomorphism between the rationalizations of their abelian schemes, with a two-sided inverse and the equation intertwining every element of `A`. This is the existing actual action-class relation, retained by subtype extensionality. Surjectivity of `harrisTaylorCMActionClassOf` extracts a satisfying representative from an already existing joint class; it asserts no existence of a joint class.

Joint class pullback is proved directly: pull back its satisfying representative, use the same-representative determinant-and-dimension theorem, and identify its class with the constructed `RationalAlgebraAction.pullbackClass`.

For an explicit family

```text
allNaturality : ∀ X : Scheme.{0}, LieBaseChangeNaturalityStatement X,
```

`harrisTaylorCMDeterminantSubfunctor` and `harrisTaylorCMActionSubfunctor` restrict the existing `RationalAlgebraAction.isoClassOverPresheaf (Spec F) A`. On a morphism of schemes over `Spec F`, the actual underlying scheme pullback and the over-category triangle give closure. The theorem `harrisTaylorCMActionSubfunctor_eq_inf` identifies the joint subfunctor with the intersection of the determinant subfunctor and the existing numerical subfunctor, using the same-representative equivalence above.

`harrisTaylorCMDeterminantPresheaf` and `harrisTaylorCMActionPresheaf` are the corresponding subtype functors

```text
(Over (Spec F))ᵒᵖ ⥤ Type 1.
```

Their identity and composition laws come from `Subfunctor.toFunctor` and the actual ambient class presheaf, whose maps use actual abelian-scheme pullback. The object, map-value and representative-value formulas expose those constructions. The joint presheaf has natural projections to determinant and numerical classes, and an objectwise injective natural inclusion into ambient rational action classes. The two proved forgetful-square equations identify the composites through either projection with that same ambient inclusion.

The provenance is internal: the module specializes proved normalized reflex pullback, combines it with actual geometric dimension pullback, and uses the existing rational action quotient, determinant invariance, all-scalar trace consequence and numerical representative image. It supplies no proof of the named integral Lie naturality statement. The inherited arithmetic trace formula and geometric dimension retain the provenance documented in `HarrisTaylorCMCentralTrace` and `HarrisTaylorLieCondition`; no new source theorem is asserted here.

This is the determinant-and-dimension action part of a varying-base moduli problem. Full source Lie-plus equivalence, polarizations, compatible Weil level structures, representability, scheme levels and coefficient descent remain additional constructions of the Harris PEL problem.
