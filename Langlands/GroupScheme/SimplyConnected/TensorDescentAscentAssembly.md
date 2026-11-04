# Ascent assembly using the proved finite-Galois tensor decomposition

Author: Worker 416.

This internal assembly supplies the published theorem
`Langlands.FieldTheory.finiteGaloisTensorDecomposition.{u}` to the
conditional algebraic-closure ascent construction in
`ClosureAscentReduction`. The tensor decomposition is consequently no
longer an assumption of the new deductions. All other structural inputs
remain explicit. This module does not prove the unconditional
`IsSimplyConnectedFieldExtensionStatement`.

`isSimplyConnectedAlgebraicClosureAscent_of_fullCoverDescent` is a
proof-valued definition with nine arguments:

1. Full cover descent, `SimplyConnectedCoverTensorDescentStatement.{u,u}`.
2. Split simply connected cover existence.
3. The separate simply connected central-cover universal property.
4. Semisimplicity under arbitrary field extension.
5. Maximal-torus preservation under field extension.
6. Root-datum existence for the actual split maximal torus.
7. The integral coroot-span necessity criterion.
8. The integral coroot-span sufficiency criterion.
9. Finite Galois splitting of tori.

It applies
`isSimplyConnectedAlgebraicClosureAscent_of_tensorDescent` to those nine
arguments and the actual theorem
`Langlands.FieldTheory.finiteGaloisTensorDecomposition`. Unfolding that
theorem's published proposition gives precisely the literal tensor input
of the older construction: for finite Galois `L/k`, an `L`-algebra
equivalence
`L ⊗[k] L ≃ₐ[L] (Gal(L/k) → L)` with
`e (a ⊗ b) σ = a * σ b`. The algebra structure is through the first
factor. No conversion of the equivalence or its formula is required.

The imported closure construction descends a supplied full cover over an
auxiliary finite Galois splitting field, recovers its actual arrow, uses
simple connectedness of the original group, and then passes to the
algebraic closure through an actual algebra embedding and
`baseChangeCompIso`. This module reuses that construction in full; it
does not reconstruct the descent or prove its retained hypotheses. The
local `linter.defProp` option follows the proof-valued-definition convention
of that construction.

`isSimplyConnectedFieldExtension_of_fullCoverDescent_and_corootCriterion`
adds central-isogeny preservation under base change as a tenth argument.
It applies the existing geometric and coroot reduction to those arguments
and the preceding closure-ascent construction. Its conditional conclusion
is exactly `IsSimplyConnectedFieldExtensionStatement.{u}`.

The universe `u` is arbitrary throughout. The descent input is specialized
to index universe `u` because its eventual index is `Gal(L/k)`. The final
field extension is unrestricted: imperfect fields, positive
characteristic, transcendental extensions and inseparable extensions remain
within its scope. The auxiliary tensor theorem requires a finite Galois
extension only at the internal splitting step.

The definitions of simple connectedness, central isogeny and full cover
remain the published ones. All group extensions use the actual
`GroupScheme.baseChange` functor. Central kernels retain their
scheme-theoretic meaning on all test schemes. No arbitrary group or
isogeny over a field extension is assumed to descend.

The provenance is internal composition of the two imported public
modules. The finite-Galois tensor theorem is reused by its Lean name.
No private draft is imported. This pair neither changes the older
conditional interfaces nor discharges any of its nine remaining
structural premises; independent proofs of those premises are still
required for the unconditional host theorem.
