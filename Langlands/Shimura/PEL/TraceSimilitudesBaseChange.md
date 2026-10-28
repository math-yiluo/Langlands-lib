# Scalar-extended and adelic trace-form similitudes

Worker 57. This derived internal construction proves nondegeneracy of the actual
extended trace form and identifies its similitude group with the original
Harris involution group through right multiplication.

For a nondegenerate bilinear form on a finite-dimensional vector space over a
field F, `bilinForm_baseChange_nondegenerate` proves nondegeneracy after extension
to every commutative F-algebra S. The Gram matrix in a finite basis has nonzero
determinant. The Gram matrix in the extended basis is its coefficientwise image,
so its determinant is a unit. A unit is a non-zero-divisor; Mathlib's matrix
nondegeneracy criterion therefore proves that both radicals vanish. This
argument permits zero divisors and the zero ring in S.

`tracePairingBaseChange_nondegenerate` applies this result to the published
normalized rational trace pairing of the actual central simple CM algebra D.
Finite dimensionality over Q follows from the actual E-basis and the number
field E. No additional nondegeneracy premise is introduced.

For a rational skew unit beta, set tau = beta sigma beta inverse. The actual
inverse-unit form for the auxiliary datum D.skewTwist beta is

```text
psi_S(x,y) = map_Q,S(1/n) regularTrace_S(x sigma_S(y) (1 tensor beta inverse)).
```

The published HodgeTraceForm module proves its right-adjoint identity for the
original sigma_S. Its new proved nondegeneracy supplies the other hypothesis
of the published `PEL.algebraicBilinearEquiv`. Thus
`harrisTraceSimilitudesEquiv` is a group equivalence from the opposite of the
original rational involution's actual S-points to the left-(S tensor_Q A)-linear
similitudes of psi_S. It sends (g,c) to right multiplication by g, with multiplier
c. The opposite is required by composition of right multiplications. The
application and multiplier identities are proved definitionally.

`harrisFiniteAdelicTraceSimilitudesEquiv` specializes this construction to the
Library's actual rational finite adeles and its existing `FiniteAdelicPoints`.

The provenance is internal. The pairing, auxiliary twist, original right
adjoint and rational nondegeneracy are imported published constructions; the
new content is the finite Gram-matrix base-change proof and its actual group
specialization. This unit does not prove a topological group comparison,
coefficient naturality, Hodge positivity, lattice existence or PEL
representability.
