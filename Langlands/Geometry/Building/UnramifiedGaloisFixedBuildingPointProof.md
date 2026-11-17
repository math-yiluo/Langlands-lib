# Rational translates of fixed apartment points cover the fixed building

`Langlands.Geometry.Building.unramifiedGaloisFixedBuildingPoint.{u}` proves
exactly the published proposition
`Langlands.Geometry.Building.UnramifiedGaloisFixedBuildingPointStatement.{u}`.
The theorem has no additional hypotheses. It holds for every universe `u`
and in both equal and mixed characteristic.

For the original nonarchimedean local field \(F\), put
\(K=\operatorname{inertiaFixedField}(F)\). Retain the connected reductive
group \(G\), maximal \(F\)-split torus \(S\), containing torus \(T\) with
maximal \(K\)-split base change, and the supplied Galois-stable apartment
datum \(D\) with its actual centralizer and full V6 compatibility. Every
coefficient-fixed point \(y\) of the reduced building has the form
\[
  y=g_K\cdot D.\operatorname{apartmentMap}(x)
\]
for \(g\in G(F)\) and an apartment point \(x\) whose underlying
root-function family is fixed by every coefficient automorphism of \(K/F\).
Here \(g_K\) is `rationalExtend F K G g`. The Lean conclusion writes the
displayed equality with \(y\) on the right.

The implemented proof applies the published theorem
`Langlands.Geometry.Building.unramifiedTorusUnitCoveringReduction` from
`Langlands.Geometry.Building.UnramifiedTorusUnitCoveringReduction` to these
two unconditional published proofs at the same universe:

1. `Langlands.Geometry.Building.unramifiedFixedPointSplitTorus`, from
   `Langlands.Geometry.Building.UnramifiedFixedPointSplitTorusProof`.
   It supplies a maximal \(F\)-split torus \(S'\) whose entire
   \(K\)-character-valuation kernel fixes the prescribed point \(y\).
2. `Langlands.Geometry.Building.unramifiedTorusUnitFixedApartment`, from
   `Langlands.Geometry.Building.UnramifiedTorusUnitFixedApartmentProof`.
   It puts a coefficient-fixed point fixed by that kernel for the chosen
   torus \(S\) in the image of a coefficient-fixed point of the supplied
   \(T_K\)-apartment.

The reduction uses `Langlands.GroupScheme.smoothMaximalSplitTorusConjugacy`
to choose \(g\in G(F)\) conjugating \(S\) to \(S'\). The inverse translate
\(z=g_K^{-1}\cdot y\) is fixed by the units of \(S_K\), by
`IsFixedByScalarTorusUnits.conjugate`. It is still coefficient-fixed:
`KPApartmentData.galoisQuotientAction_smul` gives semilinearity, and
`rationalConjugate_rationalExtend` fixes the extended rational element.
The second input supplies a coefficient-fixed apartment point \(x\) with
\(D.\operatorname{apartmentMap}(x)=z\). Applying \(g_K\) gives the required
equality. Thus the fixed apartment preimage and all original quantified
data are retained.

This module is an internal derived composition of these Library results.
Their paired explanations give the geometric constructions and source
provenance behind the two inputs. The proof uses none of
`UnramifiedBuildingDescentStatement`,
`UnramifiedBuildingDescentReductionStatement`,
`UnramifiedBuildingDescentRemainingReductionStatement`, or results
consuming them as mathematical inputs. The module declaring the target
also declares a separate full-descent reduction; that reduction is not
used here. The target statement and every Lean/Markdown pair it imports remain
unchanged. A companion compatibility repair gives the eight local arithmetic
instances in `UnramifiedFixedPointSplitTorusProof` explicit names so that the
two independently published proofs can be imported together. Their types and
values and the mathematical statements remain unchanged.
