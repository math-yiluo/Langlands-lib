# Finite unit-parameter subgroup (M363.001)

`Langlands.NYLL.LubinTate.standardLubinTateUnitParameterSubgroup`
is the image of the level-`k` higher principal units in the actual
level-`n+1` unit-parameter quotient. For `{K : Type u} [Field K]`, it
takes explicit `F : LocalField.{u,v} K` and `(n k : ℕ)` and returns
`Subgroup (standardLubinTateUnitParameter F n)` in `Type u`. Both
independent universes and the source binder order are retained.

The body is
`Subgroup.map (standardLubinTateUnitParameterClass F n)
(higherPrincipalUnitGroup F.toCompleteDVF k)`.
The imported shared M358 class map is the canonical quotient homomorphism
from valuation-ring units modulo
`higherPrincipalUnitGroup F.toCompleteDVF (n+1)`; the subgroup being
mapped is the concrete group of units whose difference from one belongs
to `F.maximalIdeal ^ k`. These are the published shared LocalField,
complete-DVF and principal-unit data used by the sibling tasks. No
uniformizer, primitive point, complete level-field package, finite-dimensional
or Galois hypothesis is required. No instance is added.

## Source and modifications

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/FiniteParameterFiltration.lean`,
M363.001, lines 33–38; universe/section context at lines 23–29.
The source file SHA-256 is
`0205d0dc5727b940c1ca25159ddc4ba008423ec44a19e8d7ae024a8a9f6e1aa1`.
Registered source `nyll-classfieldtheory-fbd320cd-supplement` has fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

Worker 299 extracted the single definition, added the `Langlands.NYLL`
namespace prefix, replaced the source module import by the published
`Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.FiniteParameters.Definitions`,
and added this documentation. The source body is reduced by unfolding its
filtration wrappers: M231.020 `higherPrincipalUnitGroup.toPrincipalUnitFiltration`
has subgroup component `higherPrincipalUnitGroup F.toCompleteDVF`, and
`AntitoneSubgroupFiltration.principalUnitSubgroup` reads that component;
`AntitoneSubgroupFiltration.principalUnitSubgroupClassInQuotient` is
`Subgroup.map (QuotientGroup.mk' _) _`. The latter two definitions are
published in the canonical `Units.Filtration` and `Units.Subquotient`
modules. Their source correspondence and the shared M358 class-map body
show that the submitted expression is definitionally equal to the source
body. A focused private check also verifies that equality by reflexivity
using the exact M231.020 draft.

Thus the definition needs no import or duplicate of M231.020, and no
separate antitone-law proof. This reduction changes no mathematical
content or signature. Membership and cardinality theorems are separate
units; this pair supplies only the subgroup definition. The original
copyright and author header remain. The existing `licenses/NYLL/LICENSE`
and `licenses/NYLL/NOTICE` retain the Apache-2.0 license and attribution.
