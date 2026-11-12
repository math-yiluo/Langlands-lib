# The local quotient-topology instance (M257.001)

`Langlands.NYLL.PortInternal.M257.d001` gives the already published norm
quotient `Langlands.NYLL.LocalFieldTheory.NormQuotient K L` its quotient topology
from `Kˣ`. The unit-group topology is Mathlib's topology on units of `K`,
and the quotient topology is Mathlib's `QuotientGroup.instTopologicalSpace`.
No topology on `L`, continuity, local-field or finiteness hypothesis is needed.

The full interface is

```lean
noncomputable local instance Langlands.NYLL.PortInternal.M257.d001
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [TopologicalSpace K] :
    TopologicalSpace (Langlands.NYLL.LocalFieldTheory.NormQuotient K L)
```

Both fields are in `Type 0`, exactly as in the source. This is concrete topology
data. It asserts no discreteness, compactness or reciprocity theorem.

The instance remains local. Importing this file makes the declaration available
without adding a global typeclass instance. A consuming module can restore its
source-local use with

```lean
attribute [local instance] Langlands.NYLL.PortInternal.M257.d001
```

## Source and modifications

This is Naganori Yamaguchi's
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/TopologicalReciprocity.lean`,
lines 36–41, at commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The module SHA-256 is
`28cfb0b56b885089511a7372bfe3bf5e80d444fb91d1e982ba0b5647d26d0108`.
The source registration is `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

| Original | Adapted |
| --- | --- |
| Local instance `LocalClassFieldTheory.normQuotientTopologicalSpace`, lines 36–41 (M257.001) | Local instance `Langlands.NYLL.PortInternal.M257.d001` |
| `LocalFieldTheory.NormQuotient` and `localNormSubgroup` | The published `Langlands.NYLL.LocalFieldTheory` declarations with the same construction |
| Full source imports | Published `NormQuotient.U002.Definitions`, `Mathlib.Topology.Algebra.Group.Quotient` and `Mathlib.Topology.Algebra.Group.Units` |

Worker 120 extracted this declaration, supplied the stable internal name from
the port inventory, and changed namespace and imports. The binder order,
Type-zero boundary, local attribute and instance body are unchanged. The opened
namespace resolves only the published norm quotient and norm subgroup. There is
no reused patch or external draft in this extraction.

The body unfolds the named norm quotient to `Kˣ ⧸ localNormSubgroup K L` and
infers its existing Mathlib quotient topology. This reuses the published algebraic
objects rather than reconstructing either the norm or its quotient. A private
focused check confirms definitional equality to
`QuotientGroup.instTopologicalSpace (localNormSubgroup K L)`, verifies the complete
source telescope, and verifies that the instance does not become global on
import. Native typeclass inference on the named `NormQuotient` fails without a
local bridge; this extraction provides that bridge, rather than an alternative
topology. The successful focused check also verifies that the omitted Artin,
class-formation, norm-continuity and topology-theorem imports are unnecessary for
this declaration.

## Attribution and license

The original copyright and author header is retained, including the source's
credit to OpenAI Codex. The source is Apache-2.0. Its unchanged `LICENSE` and
`NOTICE` are retained at `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
Their SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The source `NOTICE` contains no entry specific to `TopologicalReciprocity.lean`.
The extraction, naming and import modifications are recorded above and in the
Lean header.
