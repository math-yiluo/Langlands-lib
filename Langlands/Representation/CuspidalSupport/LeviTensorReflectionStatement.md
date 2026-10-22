# Supercuspidality reflected by an actual Levi tensor

Author: Worker 158.

`Langlands.CuspidalSupport.PadicLeviTensorSupercuspidalReflectionStatement.{uF,uW}`
is a closed proposition definition. It states the reverse factorwise
cuspidality implication needed by
`PadicLeviCuspidalFactorizationStatement`. This pair provides the statement;
its proof is a separate obligation.

## Exact scope

For every prime `p`, actual p-adic field `F : PadicField.{uF} p`, supplied
`T : F.TopologicalData`, positive total rank `n`, and ordered block shape
`B : GeneralLinear.BlockShape n`, install exactly `T.topology`. Let

```text
A : ∀ i : Fin B.length,
  SmoothRep.{0,uF,uW} ℂ (GeneralLinear (B.size i) F.Carrier).
```

Assume every `A i` is irreducible and admissible and that
`IsLeviQuasicuspidal B (B.blockTensor (fun i => (A i).representation))`.
The conclusion is
`∀ i, GeneralLinear.IsSupercuspidal (A i).representation`.
The field universe `uF` and factor-carrier universe `uW` are independent.
There is no lower bound on the number of blocks beyond that implied by
positive total rank; in particular, the one-block case is included.

The factors are smooth representations of the actual block groups. Their
irreducibility predicate includes nonzeroness. `B.Levi F.Carrier` is the
actual product of these groups, and `B.blockTensor` is their external tensor
representation on `PiTensorProduct ℂ (fun i => (A i).obj.V)`, equivalently
the finite algebraic tensor of their underlying carriers. Each component
of a Levi element acts on its own tensor factor.

`IsLeviQuasicuspidal` tests vanishing, expressed as `Subsingleton`, of the
actual unipotent coinvariant quotient for every proper standard refinement.
It does not include admissibility. The conclusion `IsSupercuspidal` includes
the given factor's admissibility and coinvariant vanishing for every proper
standard block parabolic and every conjugate of its unipotent radical.
No factor supercuspidality, factor Jacquet vanishing, tensor admissibility,
or tensor-coinvariant equivalence is assumed.

## Original sources and provenance

The following retained originals were read directly on 2026-10-22.

- A. V. Zelevinsky, *Induced representations of reductive p-adic groups II.
  On irreducible representations of GL(n)*, Ann. Sci. ENS (4) 13 (1980),
  section 1.10, printed p.174, one-based PDF p.11. The first paragraph gives
  the equivalence between quasicuspidality of a nonzero external tensor
  product and quasicuspidality of every factor. This statement uses its
  reverse direction. Source ID: `zelevinsky-1980-induced-ii`; retained file:
  `/home/taskhub/central-library/Zelevinsky--Induced representations of reductive p-adic groups II, irreducible representations of GL(n)--1980.pdf`;
  SHA-256 `663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
- I. N. Bernstein and A. V. Zelevinsky, *Induced representations of reductive
  p-adic groups I*, Ann. Sci. ENS (4) 10 (1977), sections 2.2 and 2.4,
  printed pp.446–447, one-based PDF pp.7–8. Section 2.2 identifies standard
  Levis with products of block general linear groups and standard subgroups
  with refinements; section 2.4 defines quasicuspidality by proper Jacquet
  vanishing and cuspidality by adding admissibility. Source ID:
  `bernstein-zelevinsky-1977-induced-i`; retained file:
  `/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`;
  SHA-256 `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.

This is a derived interface specialization of those sources. The originals
use smooth representations and Jacquet functors; the Library expresses
vanishing with actual coinvariant carriers and tests all conjugate radicals
in `IsSupercuspidal`. Normalization changes the quotient action, not whether
its carrier is zero. Independent Lean universe levels record the scope of
the formalization and are not attributed to the papers.

## Route for the subsequent proof

Fix a block index `i` and a proper block parabolic of
`GeneralLinear (B.size i) F.Carrier`. Refine that block by the chosen
parabolic and leave every other block unrefined. Prove that the resulting
parabolic in the product Levi is proper and that its actual unipotent
radical has the chosen radical in component `i` and trivial components
elsewhere.

Identify the coinvariants of the actual external tensor for this radical
with the tensor whose `i`th factor is the chosen factor's coinvariant
quotient and whose other factors are unchanged. The assumed Levi
quasicuspidality makes that tensor zero. Irreducibility supplies nonzero
other factors; over the field `ℂ`, tensoring with finitely many such factors
detects vanishing, so the selected quotient is zero. With one block there
are no other factors, and the same argument uses the empty tensor as the
scalar field.

Combine this standard-radical vanishing with the given factor admissibility
using the published `GeneralLinear.isSupercuspidal_iff_standard`, available
through `CuspidalityComparisonProof`. That module also proves
`padicCuspidalityComparisonTheorems`, including the actual single-block
comparison. Its existing conjugation transport is reused.

The refinement identifications, tensor-coinvariant construction, and
vanishing detection described here belong to the subsequent proof or to
focused prerequisite definition tasks. None is an extra hypothesis or a
construction supplied by this statement pair. The target asserts no forward
tensor cuspidality, tensor association, factorization, or small realization.
The parent statement and its imports are unchanged.
