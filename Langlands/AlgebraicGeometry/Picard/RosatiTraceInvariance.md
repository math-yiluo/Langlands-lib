# Invariance of the actual geometric trace under Rosati conjugation

This internal helper development proves trace invariance for the fixed actual Rosati operation. It proves neither the nonnegative diagonal nor strict positivity of the Rosati trace form. It uses the actual prime Weil pairing, its published geometric nondegeneracy, and the actual rank-one Tate twist.

`PreservesGeometricTrace A f` is the Prop-valued predicate that the rational linear operation `f` on the actual rational endomorphisms preserves the fixed trace: for every `a`, `geometricEndomorphismTrace A (f a) = geometricEndomorphismTrace A a`. Its definition applies over any field and asserts no existence of a rational lift of the prime Tate trace. The final theorem proves this predicate for the actual Rosati operation under the stated geometric assumptions.

## Linear algebra and the twist

`trace_eq_of_nondegenerate_adjoint` states that two endomorphisms adjoint for a nondegenerate scalar-valued bilinear form have equal intrinsic traces over any field. No symmetry or finite-dimensionality assumption is required. If a finite basis exists, the proof computes the two traces in a basis and its bilinear-form dual basis. Adjointness identifies each diagonal coefficient. If no finite basis exists, Mathlib's intrinsic trace is the zero linear map, so the equality follows from its definition. The latter branch is a convention of this intrinsic trace, not an assertion about a geometric dimension.

`rationalTwist_scalar_equiv` constructs a linear equivalence from the actual rational Tate twist over the global sections of `Spec k` to `Q_p`, for an algebraically closed field `k` and a prime `p` with nonzero image in `k`. The proof transports global sections through `Scheme.ΓSpecIso`, chooses the existing integral rank-one equivalence, extends scalars from `Z_p` to `Q_p`, and applies the tensor right unitor. The result asserts existence; it specifies no canonical choice of generator.

## Actual trace invariance

`primeEndomorphismTrace_involution` takes exactly the existing construction prerequisites `P`, an actual abelian scheme over `Spec k` for an algebraically closed field `k : Type u`, dual datum `W`, its additivity witness `hadd`, an actual map `lam`, a witness `hpol : W.IsPolarization P lam`, and the existing `HasRationalInverse P W lam` instance. For every prime `p` nonzero in `k` and every actual rational endomorphism `a`, it proves
`primeEndomorphismTrace A p (involution P W hadd lam a) = primeEndomorphismTrace A p a`.

The proof uses the published `relativeFiniteWeilTransition` to fix the actual prime pairing along `lam`, and `primeRationalPolarizationWeilNondegeneracy` for both its radicals. It composes the twist-valued pairing with the scalar equivalence above, preserving nondegeneracy by injectivity. The actual adjunction identity `primeWeil_involution` then gives equal intrinsic traces. No Tate trace comparison or finite-dimensionality theorem is assumed.

`geometricEndomorphismTrace_involution` adds `CharZero k` and proves `PreservesGeometricTrace A (involution P W hadd lam)`, the same pointwise equality for the fixed rational `geometricEndomorphismTrace`. It splits the definition of that trace. When the rational lift of the actual 2-adic trace exists, injectivity of the rational embedding into `Q_2` reduces the result to `primeEndomorphismTrace_involution`. When no lift exists, the fixed construction is the zero map and the equality follows directly. Thus this helper establishes invariance without asserting existence of the rational lift; the separately stated comparison theorem retains that obligation.

All declarations have the full existing geometric universe parameter `u`. Their provenance is an internal derivation from the published actual pairing constructions, geometric nondegeneracy and twist rank-one theorem, together with the implemented elementary trace argument. No new axiom or positivity premise is introduced.
