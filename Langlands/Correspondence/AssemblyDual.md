# Dual compatibility of the Henniart assembly

Author: Worker 1705.

This module proves the dual part of the published proposition
`Langlands.Correspondence.AssemblyOperationStatement` (module `AssemblyRelation`). Its
main theorem depends on two published propositions that are not yet proved. Both are
explicit hypotheses:

| Hypothesis | Library declaration (module) | Content |
| --- | --- | --- |
| `hwell` | `AssemblyWellDefinedStatement.{uF, uP, uA} F` (`Correspondence/AssemblyRelation`) | For every supercuspidal map `c0`, every parameter class `D` is assembled from `c0` (`IsAssembledFrom F c0 D π`) to exactly one automorphic class `π`. |
| `hcontra` | `Classification.MultisegmentConstituentContragredientCompatibility.{uF, uA} F F.canonicalTopologicalData` (`Representation/Classification/MultisegmentConstituentCompatibilityStatement`) | Let `Δ_1, …, Δ_r` be segments and let `B_i` represent the end of `Δ_i`. Then there are supercuspidal `Bv_i` equivalent to the smooth contragredients of the `B_i`, with this property. Let `Δv_i` be the segment with base `Bv_i` and the length of `Δ_i`. If `π` is a Langlands head (resp. Zelevinsky socle) of `∑ Δ_i`, then the smooth contragredient of `π` is a Langlands head (resp. Zelevinsky socle) of `∑ Δv_i`. |

The module does not prove either hypothesis. Both are separate proof targets in the
Library. Apart from them, the main theorem uses exactly these hypotheses of
`AssemblyOperationStatement`:

- the assembly relation `IsAssemblyOf F c0 c`,
- geometric normalization `IsGeometricReciprocity F e`,
- supercuspidal twist compatibility `SupercuspidalTwistCompatibility F e c0`,
- supercuspidal dual compatibility `SupercuspidalDualCompatibility F c0`.

Twist compatibility and geometric normalization enter because the contragredient of
the end `ν^m c0 σ` of a segment is the twist `|det|^(-m)` of `(c0 σ)^∨`. On the Weil
side this corresponds to the twist `ν^(-m)`. The field quasi-character used for this
twist is `dualTwistCharacter F e m`, the transport of `ω^(-m)` along `e`. The module
identifies it with `|·|^(-m)` only under geometric normalization.

## Main theorem

```lean
theorem dualCompatibility_of_assembly
    (hwell : AssemblyWellDefinedStatement.{uF, uP, uA} F)
    (hcontra : Classification.MultisegmentConstituentContragredientCompatibility.{uF, uA} F
      F.canonicalTopologicalData)
    (c0 : SupercuspidalMap.{uF, uP, uA} F) (c : FullMap.{uF, uP, uA} F)
    (e : ReciprocityCandidate F) (hc : IsAssemblyOf F c0 c) (he : IsGeometricReciprocity F e)
    (htwist : SupercuspidalTwistCompatibility F e c0)
    (hdual : SupercuspidalDualCompatibility F c0) : DualCompatibility F c
```

`DualCompatibility F c` says: for every parameter class `D` of rank `n`, some
parameter class `E` is the dual of `D` (`IsDualOf`: the underlying pair class of `E` is
`dualClass` of that of `D`), and `c n E` is the smooth contragredient of `c n D`
(`IsSmoothDual`). All declarations are in the namespace
`Langlands.Correspondence.AssemblyDual`. The axioms used are `propext`,
`Classical.choice` and `Quot.sound`.

## Literature context

Henniart 2002 (Bull. Soc. Math. France 130, pp.587–602) states the result that this
module proves under two extra hypotheses. In §2.9 (printed p.596, PDF p.10) the
assembled bijection `π` from Weil–Deligne classes to irreducible representations
satisfies `π(σ^∨) = π(σ)^∨` for every `σ`. Earlier in the same chapter Henniart states
these duality identities:

- `(σ_1 ⊕ σ_2)^∨ ≃ σ_1^∨ ⊕ σ_2^∨` (§2.1, printed p.593);
- `St_n^∨ ≃ ν^(1-n) ⊗ St_n` (§2.3, printed p.594);
- `π_2(σ^∨) = π_2(σ)^∨` for indecomposable `σ` (§2.7, printed p.595);
- `J^∨ ≃ J(π_r^∨, …, π_1^∨)` for the Langlands quotient `J = J(π_1, …, π_r)`, and
  `π^∨ = ∑_i π_i^∨` (§2.8, printed p.596).

For the classification of irreducible representations, Henniart refers to the
classifications of Langlands and Zelevinsky ([1], [11]) and to the introduction of [6]
(§2.5, printed p.594; §2.8 cites [1] and [6, Intr.]).

The Lean proof below is not a transcription of Henniart's text. It is an internal
derivation from the published Library interfaces. The Library defines the assembly
through segments and Langlands heads (`IsAssemblyOf`), not through Henniart's ordered
essentially square-integrable data. The proof uses two published but unproved
Library propositions as hypotheses: the contragredient compatibility of Langlands heads
(`hcontra`) and the well-definedness of the assembly (`hwell`). It combines them with
elementary computations that are proved here or published: the dual of a block sum
(the Lean counterpart of the identities of §§2.1 and 2.3 for blocks), and the
contragredient of the end of a segment.

## Proof

Fix `n` and `D`. Write `ν` for the norm character of the Weil group.

1. **The dual parameter class.** By `exists_isDualOf`, there is a parameter class `E`
   with `IsDualOf D E`. A representative of `E` is the dual `A^∨` of a representative
   `A` of `D`. It has open inertia kernel (`FiniteRepresentation.hasOpenInertiaKernel_dual`)
   and the same rank (`FiniteRepresentation.rank_dual`). Its Frobenius elements act
   semisimply: `A^∨(g)` is the transpose of `A(g⁻¹)`, and `g⁻¹` has nonzero degree
   when `g` has. The transpose of a semisimple endomorphism `f` of a finite-dimensional
   space is semisimple (`isSemisimple_dualMap`). The proof evaluates the squarefree
   minimal polynomial of `f` at the transpose (`aeval_dualMap`).
2. **Block sum of `E`.** `IsAssemblyOf` gives a block decomposition
   `φ : ⊕_i B_i ⊗ Sp(m_i + 1) ≅ A` and a Langlands-head class `c n D` of the
   multisegment `∑_i [c0 σ_i, ν^(m_i) c0 σ_i]`. By `isBlockSum_dual`, `E` is the block
   sum of the classes `σ'_i = ν^(-m_i) σ_i^∨` (`dualWeilClass`), with the same lengths
   `m_i + 1`. The equivalence
   `⊕_i (ν^(1-(m_i+1)) ⊗ B_i^∨) ⊗ Sp(m_i + 1) ≅ ⊕_i (B_i ⊗ Sp(m_i + 1))^∨ ≅ (⊕_i B_i ⊗ Sp(m_i + 1))^∨ ≅ A^∨`
   combines three equivalences. The first is the published
   `Blocks.blockDualEquiv` (module `WeilDeligne/BlockDualProof`) in each summand. The
   second is `dualDirectSumEquiv`. The third is the dual of `φ`. The definition of
   `σ'_i` twists by the pullback of `dualTwistCharacter F e m_i` along `rec`. For every
   reciprocity candidate `e` this Weil character is `ν^(1-(m_i+1))`
   (`weilCharacter_dualTwistCharacter`).
3. **Dual segments.** Choose supercuspidal representatives `B'_i` of the ends
   `ν^(m_i) c0 σ_i` of the segments. `hcontra` gives `Bv_i ≅ (B'_i)^∨`. By
   `isoClass_eq_dualWeilClass`, the class of `Bv_i` is `c0 σ'_i`. The steps are as
   follows. The end of the segment is the twist of `c0 σ_i` by `|det|^(m_i)`. Its
   contragredient is the twist of `(c0 σ_i)^∨` by `|det|^(-m_i)`
   (`GeneralLinear.SupercuspidalClass.contragredient_twist`). Supercuspidal dual
   compatibility identifies `(c0 σ_i)^∨` with `c0 σ_i^∨`. Supercuspidal twist
   compatibility for the quasi-character `dualTwistCharacter F e m_i` identifies the
   twist of `c0 σ_i^∨` by `dualTwistCharacter F e m_i ∘ det` with `c0 σ'_i`. Under
   geometric normalization, `dualTwistCharacter F e m ∘ det` is the inverse of
   `|det|^m` (`determinantQuasiCharacter_dualTwistCharacter`), so this twist is the
   twist by `|det|^(-m_i)` above. So the segments `Δv_i` of `hcontra` are the segments
   `[c0 σ'_i, ν^(m_i) c0 σ'_i]`.
4. **Dual head.** Let `J ≅ A0` be the Langlands head that represents `c n D`. By
   `hcontra` and step 3, the smooth contragredient of `J` is a Langlands head of the
   multisegment of the `σ'_i`. It is equivalent to the contragredient of `A0`
   (`smoothContragredientEquiv`). So the class `π'` of the contragredient of `A0` is a
   Langlands-head class of the `σ'_i`, and `IsSmoothDual F (c n D) π'` holds
   (`isMultisegmentHeadClass_dual`).
5. **Uniqueness.** Steps 2 and 4 show `IsAssembledFrom F c0 E π'`. `IsAssemblyOf` also
   gives `IsAssembledFrom F c0 E (c n E)`. By `hwell`, `π' = c n E`.

## Declarations

### Linear algebra

- `dualMap_pow`, `aeval_dualMap`: the transpose of `f^n`, or of a polynomial in `f`,
  is the corresponding power, or polynomial, of the transpose of `f`.
- `isSemisimple_dualMap`: the transpose of a semisimple endomorphism of a
  finite-dimensional space is semisimple.
- `dualDirectSumLinearEquiv` (definition): the linear equivalence between the dual of a
  finite direct sum `⨁_i M_i` and `⨁_i M_i^∨`. A functional `ℓ` goes to the family of
  its restrictions `ℓ ∘ lof i` (`dualDirectSumLinearEquiv_apply`).
- `dualDirectSumEquiv` (definition): the same map is an equivalence of Weil–Deligne
  representations `(⊕_i A_i)^∨ ≅ ⊕_i A_i^∨`. It intertwines the dual actions and the
  negative-transpose monodromies.

### Parameters, characters and the reduction

- `exists_isDualOf`: step 1.
- `dualTwistCharacter F e m` (definition): the inverse of the published
  `normPowerQuasiCharacter F e m`. It is the field quasi-character obtained by
  transporting the inverse Weil norm power `ω^(-m)` along the reciprocity candidate `e`.
  Under geometric normalization (`IsGeometricReciprocity F e`) it is the quasi-character
  `|·|^(-m)` of `Fˣ`. For an arbitrary candidate the module makes no such
  identification, and the main theorem assumes geometric normalization.
- `weilCharacter_dualTwistCharacter`: its pullback along `rec` is `ν^(1-(m+1))`, for
  any reciprocity candidate.
- `determinantQuasiCharacter_dualTwistCharacter`: under geometric normalization,
  `dualTwistCharacter F e m ∘ det` is the inverse of `|det|^m`.
- `dualWeilClass` (definition): the irreducible Weil class `ν^(-m) σ^∨`. It uses the
  published class bijections `continuousIrreducibleDualEquiv` and
  `continuousIrreducibleTwistEquiv`.
- `isBlockSum_dual`: step 2.
- `isoClass_eq_dualWeilClass`: step 3.
- `isMultisegmentHeadClass_dual`: step 4.
- `dualCompatibility_of_assembly`: the main theorem.

## Provenance

Derived. The module adds four definitions: `dualDirectSumLinearEquiv`,
`dualDirectSumEquiv`, `dualTwistCharacter` and `dualWeilClass`. They are elementary
constructions from published definitions: duality of finite direct sums, and the
inverse of a published quasi-character and its twist of a dual class. Every theorem
combines published definitions and published proofs with the two hypotheses `hwell` and
`hcontra`. Henniart 2002, §2.9, states the dual compatibility of the assembled
correspondence. This module derives a conditional Lean version from the Library
interfaces and does not transcribe Henniart's argument. In particular, the module does not assume the
classification, any correspondence, or any dual-existence statement for parameters; the
existence of the dual parameter class is proved in step 1.
