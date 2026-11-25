# Smooth effective descent with the prescribed inner generic action

This internal construction applies affine fpqc effectivity to the finite
integral inner descent datum. Its provenance is the existing
`finiteInnerIntegralDatum`, `Datum.affineSolution`, `Solution.smooth`,
`Solution.semilinear` and generic comparison constructions. No
original-literature theorem is claimed. All objects have an arbitrary
common universe.

The inputs retain an actual finite Galois arithmetically unramified field
`E/F` inside the inertia fixed field, the finite integral model `N`, the
supplied smooth upstairs model `P`, their exact coefficient recovery, an
upstairs function `c`, a finite rational-point cocycle `d`, recovery of
its values at the selected lifts, and both forward and inverse integral
stability conditions for `P`. These are precisely the inputs of
`finiteInnerIntegralDatum`.

`finiteInnerIntegralSolution` applies actual affine group-scheme
effectivity on the finite integer cover. The descended object is affine.
Exact coefficient recovery reflects smoothness from `P` to `N`, and
fpqc descent of smoothness proves
`finiteInnerIntegralSolution_smooth`.

`finiteInnerIntegralSolution_semilinear` uses the normalized overlap
component corresponding to a supplied `E/F` automorphism. The component
recovery theorem and `Solution.semilinear` identify canonical
semilinear transport of the actual solution with the constructed finite
integral inner twist.

`finiteInnerGenericGroup` is the solution's own actual generic fibre
over `F`. `normFiniteInnerModel` is its smooth integral model over
the norm presentation `baseIntegers F` of the integers. The construction
does not identify this generic group with the original `G`.

`finiteInnerGenericComparison` is the actual comparison between their
base changes over `E`, formed from the coefficient-square comparison,
the solution isomorphism and the prescribed generic identification of
`N`. The general construction `solutionModelIso` recovers the original
model of any affine effective solution over its specified generic
comparison: the compatibility equation cancels that comparison's
coefficient-square isomorphism with its inverse.
`normFiniteInnerModelIso` specializes this construction to recover `N`
under actual coefficient extension with precisely
`finiteInnerGenericComparison`.

The general lemma `squareSolutionComparison_semilinear_target` retains
an arbitrary target semilinear map in the existing square-comparison
argument. `solutionGenericComparison_semilinear_target` applies that
lemma to the solution's actual generic comparison via
`solutionGenericComparison_eq_square`.
`finiteInnerGenericComparison_semilinear` specializes it to the
generic inner twist by `d σ`. Thus the comparison intertwines
canonical Galois transport on the descended generic group with the
specified inner-twisted Galois transport on `G_E`.

This module supplies actual smooth effective descent from the retained
finite recovery and stability inputs. It does not supply the upstairs
model, choose common coefficients, identify a residue quotient or
Frobenius map, or prove any chamber conclusion.
