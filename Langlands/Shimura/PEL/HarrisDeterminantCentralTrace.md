# The central coefficient of the actual normalized Harris determinant

This module constructs the normalized binary central determinant over the source CM field and proves that its extracted linear coefficient is exactly the existing Harris–Taylor arithmetic value. The comparison passes through the actual regular Kottwitz Hodge module, its actual left algebra action and the existing coefficientwise reflex descent. It also proves the equality on actual structure-sheaf sections.

The general parameters are the existing totally real number field `E`, its totally complex quadratic extension `K`, the central simple unitary datum `D` of degree `n`, its Harris signature charts `C`, and a CM-section proof. The displayed rational, `E` and `K` scalar towers on the algebra `A` are retained. The Harris–Taylor part additionally assumes `IsCMField K`, an imaginary quadratic CM field `L` with an `L`-algebra structure on `K`, and charts using exactly `harrisCMSection E (algebraMap L K) τ₀`. The types and schemes have universe zero, as in the reflex determinant and normalization prerequisites.

`traceCoefficient_kottwitzHodgeDeterminant` applies to every `a : A`, before specialization to the centre. It proves that extracting the linear coefficient after evaluating the binary Hodge polynomial for `(1, a)` at `(1, X)` gives the intrinsic trace of the actual endomorphism
`kottwitzHodgeAction C (1 ⊗ (1 ⊗ a))` on `kottwitzHodgeModule C`. Its proof installs the finite-dimensional instances from the actual datum, unfolds the determinant to the existing finite basis of that module, and identifies the first endomorphism with the identity using the tensor algebra unit and the unital algebra action. It then applies `HodgeDeterminant.traceCoefficient_polynomial`. Thus the proof computes the actual determinant's coefficient; it does not postulate a module with prescribed multiplicities.

`coe_traceCoefficient_kottwitzReflexDeterminant` identifies the complex inclusion of the corresponding reflex-field coefficient with the same intrinsic trace. This follows from coefficient-extraction naturality and the existing theorem that the descended reflex polynomial includes into the actual Hodge determinant.

For a central `a : K`, `harrisTaylorReflexToCM_traceCoefficient` combines this result with `trace_kottwitzHodgeAction_center_harrisTaylor`. That actual-module theorem identifies the complex trace with

```text
distinguishedEmbedding
  (cmConjugation E K (HarrisTaylor.lieTraceValue L K n a)).
```

The explicitly conjugated scalar map `harrisTaylorReflexToCM` therefore sends the reflex coefficient to `lieTraceValue L K n a`. This uses its previously proved complex-value characterization and injectivity of the distinguished embedding. The earlier unconjugated `harrisReflexToCM` and its scheme structure are preserved with their existing meanings.

`harrisTaylorCentralDeterminant C a` is the actual polynomial

```text
map (harrisTaylorReflexToCM C)
  (kottwitzReflexDeterminant C hΦ ![1, algebraMap K A a]).
```

`traceCoefficient_harrisTaylorCentralDeterminant` proves that its extracted coefficient is precisely

```text
algebraMap L K (complexConj L (trace L K (n²*a)))
  + n*a - complexConj K (n*a).
```

This is the existing `HarrisTaylor.lieTraceValue` convention. Its original source is Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura Varieties* (2001), III.1, Lemma III.1.2(3), printed p.90 / PDF p.98, registered source `harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256 `5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`. The present module is an internal derivation from that existing definition and the actual trace and normalization prerequisites; it does not assume a new literature theorem.

For an actual scheme map `p : S ⟶ Spec K`, `traceCoefficient_harrisTaylorCentralDeterminant_section` proves that mapping the constructed polynomial through `secHom p U` and extracting its coefficient gives the actual section `HarrisTaylor.lieTraceSection L p n a U`. `traceCoefficient_reflexDeterminant_harrisTaylor_section` proves the same result for the reflex polynomial mapped directly through the actual normalized structure `harrisTaylorReflexStructure C p`. The proofs use polynomial-map composition and extraction naturality. The base and the open are arbitrary; there is no reducedness, nonemptiness, flatness or faithfulness assumption on their section rings.

Finally, `traceCoefficient_harrisTaylorCentralDeterminant_rank_three` checks the normalization in the imaginary-quadratic case `L = K`, `n = 3`. For every `a` with `complexConj K a = -a`, the actual normalized determinant coefficient is `-3*a`. The proof specializes the general coefficient theorem, uses the trace of the identity field extension, and simplifies the conjugation and ring arithmetic. In particular the central element corresponding to `i` in the rank-three example has coefficient `-3i`, the sign required by the Harris–Taylor formula.

These results resolve the central coefficient normalization needed before adjoining the determinant and numerical conditions. They do not construct a satisfying abelian scheme, prove equivalence with the full Lie-plus condition, replace the CM tower, or establish varying-base representability. Those are separate obligations of the Harris geometry construction.
