# NYLL abstract reciprocity: exactness of the upper Galois row

Worker 68, 13 November 2026.

## Source and correspondence

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Core.lean`. Registered source
`nyll-classfieldtheory-fbd320cd-supplement`, content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`. The original
copyright and author header is retained; see `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.

| Unit | Source theorem | Statement lines | Omitted proof |
| --- | --- | --- | --- |
| M075.012 | `ClassFormation.abstractReciprocity_galois_exact` | 581–592, up to `:= by` (docstring 579–580) | lines 593–617 |

The setting is a group `G` with a topology, closed subgroups `K`, `M`, `L` with
`hLM : L ≤ M` and `hMK : M ≤ K`, and the normality instances `hLnormal` of `L` and
`hMnormal` of `M`, both as subgroups of `K`.

`abstractReciprocity_galois_exactStatement K M L hLM hMK` first makes the normality of
`L` in `M` available as a local instance (`letI`). Its proof is the M068.003 theorem
`transferNormNaturality_intermediateExtension_normal K M L hLM hMK`, which derives it
from `hLnormal`. The statement then says that two subgroups of `K ⧸ L` are equal:

- the kernel of the restriction
  `abstractReciprocityRestriction K M L hLM hMK : K ⧸ L →* K ⧸ M` (M075.005, sibling module
  `Core/Restriction/Definitions`);
- the range of the inclusion
  `abstractReciprocityInclusion K M L hLM hMK : M ⧸ L →* K ⧸ L` (M075.010, sibling module
  `Core/Inclusion/Definitions`).

In the field picture this is exactness of `G(L/M) → G(L/K) → G(M/K)` at `G(L/K)`.

The hypotheses, including the instance arguments, are parameters of the `def`, in the
source order and with the source binder kinds. The value is exactly the source
conclusion, including its `letI`. The statement is not proved here.

## Name map

| Source | Adapted declaration |
| --- | --- |
| `ClassFormation.abstractReciprocity_galois_exact` | `Langlands.NYLL.ClassFormation.abstractReciprocity_galois_exactStatement` |
| `ClassFormation.abstractReciprocityRestriction` (used, M075.005) | `Langlands.NYLL.ClassFormation.abstractReciprocityRestriction` |
| `ClassFormation.abstractReciprocityInclusion` (used, M075.010) | `Langlands.NYLL.ClassFormation.abstractReciprocityInclusion` |
| `ClassFormation.transferNormNaturality_intermediateExtension_normal` (used, theorem M068.003) | `Langlands.NYLL.ClassFormation.transferNormNaturality_intermediateExtension_normal` (published proof, imported through `Core/Inclusion/Definitions`) |

## Modifications

- The source theorem becomes a Prop-valued `def` with the same name plus the suffix
  `Statement`, in the namespace `Langlands.NYLL.ClassFormation`. The complete source
  telescope is kept in order, including the universe-polymorphic `{G : Type*}` binder and
  the named instance arguments `hLnormal` and `hMnormal`. The proof is omitted. The
  docstring is rephrased as "Target of …".
- The source abbreviation M004.002 `CyclicCohomology.extensionSubgroup K L h`
  (`Nyll/GaloisCohomology/Cyclic/NormKernelVanishing.lean`, lines 51–54, defined as
  `L.toSubgroup.subgroupOf K.toSubgroup`) is not in the Library. As the task context
  directs, it is replaced by its defining Mathlib term:
  - `extensionSubgroup K L (hLM.trans hMK)` becomes `L.toSubgroup.subgroupOf K.toSubgroup`;
  - `extensionSubgroup K M hMK` becomes `M.toSubgroup.subgroupOf K.toSubgroup`;
  - `extensionSubgroup M L hLM` becomes `L.toSubgroup.subgroupOf M.toSubgroup`.

  The abbreviation ignores its proof argument, so the replacement is definitional.
- The `letI` binder cites the published Library theorem
  `transferNormNaturality_intermediateExtension_normal`, the proof of M068.003, with the
  source arguments `K M L hLM hMK`. Its declared type is
  `transferNormNaturality_intermediateExtension_normalStatement K M L hLM hMK`, which by
  definition is `(L.toSubgroup.subgroupOf M.toSubgroup).Normal`. No proof is inlined and
  no hypothesis is added.
- The unused section variables of `Core.lean` are omitted; the declaration binds its own
  `{G : Type*}`. The source imports are replaced by imports of the sibling modules
  `Core/Restriction/Definitions` and `Core/Inclusion/Definitions`.

## Validation

The module compiles in the project Lean service with no errors or warnings, and the
declaration inspection reports `statement_returns_prop = true`. A private check
reconstructs the source declarations verbatim (see the paired Markdown of
`Core/Inclusion/Definitions`), including the theorem
`transferNormNaturality_intermediateExtension_normal` with its source proof. It then proves
by `rfl` that the whole unapplied constant `abstractReciprocity_galois_exactStatement`
equals the adapted one. These checks establish compilation and source correspondence;
independent review is still required.
