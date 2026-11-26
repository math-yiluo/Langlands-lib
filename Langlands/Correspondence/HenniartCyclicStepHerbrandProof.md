# The relative Herbrand function of a cyclic prime-degree step

`Langlands.Henniart.cyclicPrimeStepHerbrandPsi` proves
`Langlands.Henniart.CyclicPrimeStepHerbrandPsiStatement.{u}` at an arbitrary
universe level. If a cyclic prime-degree step `S` has base \(L\) and top \(M\),
and \(M\) is \(L\)-isomorphic to a finite intermediate field \(E\) of
`AlgebraicClosure L.Carrier`, then `S.herbrandPsi` and `relativeHerbrandPsi E`
agree on all of \(\mathbb R\). [Statement](HenniartCyclicStepHerbrandStatement.md)

1. `Normal.of_algEquiv` transfers normality from \(M/L\) to \(E/L\).
   `IntermediateField.normalClosure_of_normal` identifies the intermediate
   field of `galoisClosure E` with \(E\).
2. The relative definition uses \(\phi_{N/E}(\psi_{N/L}(x))\), where `extendFiniteGalois`
   presents the normal closure \(N\) as an extension of \(E\). Each element of \(N\)
   has the same value in the ambient algebraic closure as an element of \(E\), by
   the equality of intermediate fields. Thus the algebra map \(E \to N\) is
   surjective. The auxiliary lemma `herbrandPhi_eq_self_of_surjective` shows that
   every automorphism over \(E\) fixes every element in its image. All lower
   groups consequently have order one, and the floor formula gives
   \(\phi_{N/E}(x)=\lfloor x\rfloor+(x-\lfloor x\rfloor)=x\) for \(x\geq 0\).
   `herbrandPhi_of_nonpos` gives the identity for \(x\leq 0\).
   [Relative index](../LocalFactor/Ramification/Herbrand/SubextensionProof.md)
   [Finite Herbrand functions](../LocalFactor/Ramification/Herbrand/Finite.md)
3. The proof composes the given isomorphism with `IntermediateField.equivOfEq`
   for the equality of intermediate fields and then with `extendFiniteGaloisEquiv`
   to obtain an \(L\)-algebra equivalence from \(M\) to the carrier used in the
   relative definition. `herbrandPsi_eq_of_algEquiv` identifies \(\psi_{N/L}(x)\)
   with \(\psi_{M/L}(x)\). Function extensionality finishes the comparison.
   [Transport of Herbrand functions](../LocalFactor/Ramification/Herbrand/TransportProof.md)

The comparison follows from the finite Galois formula for \(\phi\) and the
relative definition in Serre, *Local Fields*, Chapter IV §3, printed pp. 73–75,
including Remark 2 on p. 75. Inverting the relative formula there gives the
composition used here. The Library extends the functions to all real arguments
using the identity on the nonpositive ray. The registered source is
`serre-1979-local-fields`, SHA-256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
