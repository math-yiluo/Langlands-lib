# Unramified descent of smooth integral group models

The theorem
`Langlands.GroupScheme.IntegralModel.unramifiedSmoothModelDescent` proves
exactly `UnramifiedSmoothModelDescentStatement.{u}` at arbitrary universe
`u`. For a nonarchimedean local field `F`, a group scheme `G` over `F`,
and a smooth integral model `P` of `G` over the integers of the inertia
fixed field, stability of `P.integralPoints` under every `F`-automorphism
of that field gives a smooth integral model `M` over the given valuation
ring `𝒪[F]`. The conclusion includes an actual compatible model
isomorphism `M.baseChangeUnramified.Iso P (Iso.refl _)`.

The source of the target is Kaletha–Prasad, *Bruhat–Tits Theory: A New
Approach* (2023), Fact 2.10.16 and Remark 2.10.19, printed pp. 126–127 /
PDF pp. 157–158. The statement module
`IntegralModel.UnramifiedSmoothDescent` gives the precise comparison
between its group-scheme and nonarchimedean-local-field scope and the
source's affine-variety and Henselian-DVR scope.

The implemented proof is the direct application of
`unramifiedSmoothModelDescent_of_extension_of_finiteRecovery` to the two
proved inputs `smoothHomExtension` and `finiteUnramifiedRecovery`.
There is no extra premise on the final theorem. All results are imported
by their Lean names.

`smoothHomExtension`, in `IntegralModel.SmoothHomExtensionProof`, proves
the extension criterion for homomorphisms from a smooth model over a
strictly Henselian discrete valuation ring. The integral-point condition
places generic pullbacks of target coordinates in the source coordinate
ring; an affine-spectrum construction then extends the given group
homomorphism with its exact generic compatibility. Its paired Markdown
describes the divisibility and denominator arguments implementing KP
Lemma 2.10.9 and Corollary 2.10.10.

`finiteUnramifiedRecovery`, in `IntegralModel.FiniteRecoveryExistence`,
recovers each specified smooth model over the maximal-unramified
integers from an actual model over the integers of a finite Galois
unramified intermediate field. It descends both the integral group
scheme and the specified generic identification, enlarging the finite
field when necessary. Its compatible recovery isomorphism uses the
canonical field pullback comparison `finiteInertiaGenericIso`.

The assembly theorem in `IntegralModel.FiniteRecoveryInterface`
opens that finite recovery and applies `modelOfFiniteRecovery`.
The latter uses stable integral points and the extension criterion
to construct the finite descent datum, makes the datum effective,
and reflects smoothness from `P`. The resulting model is over the
given valuation integers and recovers `P` over the identity of the
generic group. The imported construction and comparison modules
prove these steps; the present proof supplies their two unconditional
inputs. The original statement's Lean/Markdown pair and all its
imports are unchanged.
