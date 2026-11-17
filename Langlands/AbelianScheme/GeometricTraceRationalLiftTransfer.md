# Transfer of the fixed rational trace from a nonzero target trace

`Langlands.AbelianScheme.GeometricTraceCompatibleLinearMap A B F` states that the fixed rational geometric traces agree along a rational linear map `F` from the actual rational endomorphisms of `A` to those of `B`. The two abelian schemes may be over different arbitrary fields `k` and `K` in the same arbitrary universe `u`.

`geometricEndomorphismTrace_twoAdic_of_ne_zero` proves that one nonzero value of the fixed trace of `B` forces that entire trace to agree with the actual 2-adic trace after scalar extension. The proof splits the existing definition of `geometricEndomorphismTrace`. If a rational lift exists, its published uniqueness theorem identifies the fixed trace with that lift. Otherwise the fixed trace is the zero linear map, contradicting the supplied nonzero value.

`geometricTraceCompatibleLinearMap_of_target_ne_zero` assumes that `F` preserves the actual 2-adic traces and that the fixed rational trace of `B` has one nonzero value. By the preceding theorem, composing the target fixed trace with `F` constructs a rational lift of the source's actual 2-adic trace. The published rational-lift uniqueness theorem identifies this composite with the source fixed trace, giving the stated compatibility.

This is an internal derivation from the existing trace definition and its rational-lift uniqueness theorem. The linear map need not be multiplicative or surjective. No algebraic-closedness, characteristic-zero, finite-dimensionality or positivity assumption is made. A nonzero target trace value is an explicit premise; the result does not establish general trace rationality or comparison with every prime.
