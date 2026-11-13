# All-field port of `Langlands.Representation.Whittaker.MirabolicFunctionalMultiplicityProof`

`Langlands.AllField.Representation.Whittaker.MirabolicFunctionalMultiplicityProof` proves JPSS (1983), Section 1.5, Corollary 1, for the mirabolic group over every nonarchimedean local field. The p-adic module `Langlands.Representation.Whittaker.MirabolicFunctionalMultiplicityProof` works over `F : PadicField p` with bundled topological data `T : F.TopologicalData`. Here `F` is an arbitrary field with bundled data `T : LocalFieldData F`: a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure (see `Langlands.LocalFieldData`).

Source: Jacquet, Piatetski-Shapiro and Shalika, *Rankin-Selberg convolutions*, Amer. J. Math. 105 (1983), Section 1.5, Corollary 1. The original module also cites Bernstein and Zelevinsky (1976), Proposition 5.15(c), for compact minimality.

## Declarations

- `Langlands.AllField.Whittaker.mirabolicFunctionalMultiplicity_of_minimality` (theorem): assumes the all-field compact-minimality statement `MirabolicCompactMinimalityStatement` and proves `MirabolicFunctionalMultiplicityStatement F T n` for every field `F`, every `T : LocalFieldData F` and every `n`.
- `Langlands.AllField.Whittaker.mirabolicFunctionalMultiplicity` (theorem): the same statement, unconditionally. It combines the previous theorem with the ported `mirabolicCompactMinimality`.

## Proof

The algebraic part does not depend on the field. It is reused unchanged from the original module: the Frobenius coefficient map and the generic assembly `Langlands.Whittaker.mirabolicFunctionalMultiplicity_of_generic`, together with the compactly supported function `exists_mirabolicCompactEval_one_ne_zero` that is nonzero at the identity. The generic assembly needs four inputs. The first is compact minimality, from the hypothesis. The second is that compactly supported function. The third is that the representation is irreducible and smooth. The fourth is that the representation has countable dimension, which is `MirabolicRigidity.rank_le_aleph0`.

Only the instance setup is field-specific. With the topology `T.topology`, the following facts hold:

- The field is Hausdorff (`T.fieldT2`).
- `GL_{n+1}(F)` is a nonarchimedean group (`valuativeGeneralLinearNonarchimedean`).
- `GL_{n+1}(F)` is locally compact (`T.generalLinearLocallyCompactSpace`) and second countable (`T.generalLinearSecondCountableTopology`), and so is the mirabolic subgroup.

The original proof first handles the canonical topology of the p-adic field and then transports the result to an arbitrary `T`, using the equality of `T.topology` with the canonical topology. No transport is needed here, because every instance comes directly from `T`.

## Imports from the port

- `Langlands.AllField.Representation.Smooth.SmallRealizationProof`
- `Langlands.AllField.Representation.Whittaker.MirabolicMinimalityProof`
- `Langlands.AllField.Representation.Whittaker.MirabolicPairingStatement`
