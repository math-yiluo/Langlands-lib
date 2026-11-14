# Finite parameter subgroup membership target (M363.002)

`Langlands.NYLL.LubinTate.standardLubinTateUnitParameterClass_mem_subgroup_iffStatement`
is the exact Prop-valued target extracted from M363.002, source lines
42–48. Its explicit arguments are the shared LocalField package `F`,
natural numbers `n k`, the bound `hk : k ≤ n + 1`, and the valuation-ring
unit `u`, in that order. It asserts that `standardLubinTateUnitParameterClass F n u`
belongs to `standardLubinTateUnitParameterSubgroup F n k` exactly when
`u` belongs to `higherPrincipalUnitGroup F.toCompleteDVF k`.

The target retains `hk` as an explicit proof parameter even though the
proposition does not depend on its value. Modifications are extraction,
the namespace prefix, the `Statement` suffix, replacing the theorem by a
Prop-valued definition, and renaming the unused bound to `_hk`.
This file states the target and proves nothing.

The original source is Naganori Yamaguchi's NYLL,
`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/FiniteParameterFiltration.lean`,
pinned commit `fbd320cd8b1b06487c58227e92eb135794267709`.
Source file SHA-256: `0205d0dc5727b940c1ca25159ddc4ba008423ec44a19e8d7ae024a8a9f6e1aa1`.
Registered source `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The source universe context is `u v`, with `{K : Type u} [Field K]`.
All parameters, universes and hypotheses are retained. No instances are added.
The original copyright and author header and Apache-2.0 notice are retained;
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` carry the license and attribution.

The sole import is the shared finite-parameter subgroup definition,
whose direct subgroup-image body uses the canonical M225.001 and M358
data. The target requires no import of the abstract filtration conversion
M231.020 or the quotient-membership proof M120.082. Its definition and
proof remain separate reviewable units.
