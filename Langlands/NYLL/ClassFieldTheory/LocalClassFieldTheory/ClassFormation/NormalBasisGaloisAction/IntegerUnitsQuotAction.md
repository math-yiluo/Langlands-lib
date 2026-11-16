# M145.010: chosenNormalBasisIntegerUnitsQuotMulDistribMulAction

Worker 197 adapts Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`
at pinned commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/NormalBasisGaloisAction.lean`,
lines 201–216 (declaration at 204; attribute at 203).
The source file SHA-256 is
`5d4eeb8f1dc2a8efeef90ee3c9d89bb43c048d5057e49f32701cefc8768a05c6`.
The readable original is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
Registered sources are `external-lean-reuse-snapshots-2026-10-21` (fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`) and
`nyll-classfieldtheory-fbd320cd-supplement` (fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
No applicable NYLL erratum was found in the current Library's `notes/errata/`.

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalClassFieldTheory.chosenNormalBasisIntegerUnitsQuotMulDistribMulAction` | `Langlands.NYLL.LocalClassFieldTheory.chosenNormalBasisIntegerUnitsQuotMulDistribMulAction` |

This is the actual multiplicative distributive action of `Gal(L / K)` on
`𝒪[L]ˣ ⧸ V`, where the carrier of `V` equals the chosen normal-basis
principal-unit set at level `n`. Scalar multiplication is the quotient of the
actual integral-closure Galois action on integer units: it sends the class of
`a` to the class of `sigma • a` under that ambient action.

The complete effective source telescope uses the single universe `u`, with
all binder kinds and order preserved:

```lean
(K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
  [IsIntegralClosure 𝒪[L] 𝒪[K] L]
  (n : Nat) (V : Subgroup 𝒪[L]ˣ)
  (hV : (V : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n)
```

The section context is original lines 92–94 and 120–122; `n`, `V` and `hV`
are explicit. No topology on `L` or positivity condition on `n` is added.
The unused source universes `uG` and `uA` do not occur in this declaration.

The source docstring, `@[implicit_reducible]` attribute and complete data body
are retained. A local instance installs
`galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L`.
The published `quotientMulDistribMulActionOfSubgroupStable` constructs the
quotient action. Its stability certificate rewrites source and target membership
using `hV` and applies the actual published theorem
`galoisGroup_smul_mem_chosenNormalBasisPrincipalUnitSet`; a Prop-valued target
is not substituted for that proof.
The canonical focused imports are
`NormalBasisGaloisAction.QuotientDistribAction.Definitions` and
`NormalBasisGaloisAction.U005.Proofs` under the full class-formation module path.
Both are already in the published Library. The nearby `StableQuotient`
compatibility module is unnecessary to this construction.

Modifications are extraction into this focused pair, the `Langlands.NYLL`
namespace prefix and replacement of the original umbrella imports with these
published focused imports. Unused openings, unused universe names and unrelated
source commands are omitted. The actual objects, attribute, parameter context,
constructor call and proof terms are unchanged. The construction is a definition;
it introduces no global instance.

The original copyright, author and Apache-2.0 header is retained;
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` apply.
This supporting construction establishes no class-formation or reciprocity
theorem. Compilation, independent semantic acceptance and publication are
separate checks.
