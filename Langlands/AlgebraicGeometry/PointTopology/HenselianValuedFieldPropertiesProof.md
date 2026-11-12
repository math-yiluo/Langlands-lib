# The henselian valued field facts of Conrad's printed p.14

This module proves `Langlands.AlgebraicGeometry.PointTopology.HenselianValuedFieldPropertiesStatement`:

```lean
theorem henselianValuedFieldProperties : HenselianValuedFieldPropertiesStatement.{u}
```

The statement is the conjunction of the six assertions about henselian valued fields recalled on printed p.14 of Brian Conrad, *Weil and Grothendieck approaches to adelic points* (December 31, 2011). The proof is the tuple of the six component theorems:

| Component | Theorem | Module |
| --- | --- | --- |
| `HenselianIffSeparablyClosedStatement` | `henselianIffSeparablyClosed` | `HenselianIffSeparablyClosedProof` |
| `HenselianIffValuationRingHenselianStatement` | `henselianIffValuationRingHenselian` | `HenselianValuationRingProof` |
| `TensorCompletionProductStatement` | `tensorCompletionProduct` | `TensorCompletionProductProof` |
| `HenselianTensorCompletionFieldStatement` | `henselianTensorCompletionField` | `HenselianTensorCompletionFieldProof` |
| `ArchimedeanHenselianStatement` | `archimedeanHenselian` | `HenselianArchimedeanProof` |
| `HenselianFiniteEtaleEquivalenceStatement` | `henselianFiniteEtaleEquivalence` | `HenselianFiniteEtaleEquivalenceProof` |

Each module's Markdown describes its proof.
