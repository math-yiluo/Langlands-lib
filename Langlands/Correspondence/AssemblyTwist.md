# Twist compatibility of the Henniart assembly

Authors: Worker 1705, Worker 1715.

This module proves the twist part of the published proposition
`Langlands.Correspondence.AssemblyOperationStatement` (module `AssemblyRelation`). Its
main theorem depends on two published propositions that are not yet proved. Both are
explicit hypotheses:

| Hypothesis | Library declaration (module) | Content |
| --- | --- | --- |
| `hwell` | `AssemblyWellDefinedStatement.{uF, uP, uA} F` (`Correspondence/AssemblyRelation`) | For every supercuspidal map `c0`, every parameter class `D` is assembled from `c0` (`IsAssembledFrom F c0 D π`) to exactly one automorphic class `π`. |
| `htw` | `Classification.MultisegmentConstituentCharacterTwistCompatibility.{uF, uA} F F.canonicalTopologicalData` (`Representation/Classification/MultisegmentConstituentCompatibilityStatement`) | For a character `χ` of `Fˣ` with open kernel, `J` is a Zelevinsky socle (resp. Langlands head) of a multisegment `a` if and only if `J ⊗ (χ ∘ det)` is a Zelevinsky socle (resp. Langlands head) of the multisegment `aχ`. Here `aχ` twists every cuspidal base by `χ ∘ det` and keeps every length. |

The module does not prove either hypothesis. Both are separate proof targets in the
Library. Apart from them, the main theorem uses exactly the hypotheses of
`AssemblyOperationStatement` that concern twists:

- the assembly relation `IsAssemblyOf F c0 c`,
- supercuspidal twist compatibility `SupercuspidalTwistCompatibility F e c0`.

Geometric normalization of `e` is not needed.

## Main theorem

```lean
theorem twistCompatibility_of_assembly
    (hwell : AssemblyWellDefinedStatement.{uF, uP, uA} F)
    (htw : Classification.MultisegmentConstituentCharacterTwistCompatibility.{uF, uA} F
      F.canonicalTopologicalData)
    (c0 : SupercuspidalMap.{uF, uP, uA} F) (c : FullMap.{uF, uP, uA} F)
    (e : ReciprocityCandidate F) (hc : IsAssemblyOf F c0 c)
    (htwist : SupercuspidalTwistCompatibility F e c0) : TwistCompatibility F e c
```

`TwistCompatibility F e c` says: for every parameter class `D` of rank `n` and every
quasi-character `χ` of `Fˣ`, some parameter class `E` is the twist of `D` by the Weil
character `χ ∘ rec` (`weilCharacter F e χ`, relation `IsTwistOf`), and
`c n E` is the twist of `c n D` by `χ ∘ det` (`IsCharacterTwist`). All declarations
are in the namespace `Langlands.Correspondence.AssemblyTwist`. The axioms used are
`propext`, `Classical.choice` and `Quot.sound`.

## Literature context

Henniart 2002, §§2.2–2.9 (printed pp.593–596, PDF pp.7–10), describes the objects
this module works with: the decomposition of a Weil–Deligne representation into
indecomposable blocks (§§2.2–2.3), the Langlands quotients of §2.8, and the assembled
bijection of §2.9. Henniart does not state twist compatibility of the assembly there,
and gives no argument for it. The argument below is an internal derived argument. It
combines the published twist compatibility of Langlands heads (hypothesis `htw`) and
well-definedness of the assembly (hypothesis `hwell`) with an elementary computation of
the twist of a block sum, which is proved here.

## Proof

Fix `n`, `D` and `χ`, and write `χ_W = χ ∘ rec` for the Weil character
`weilCharacter F e χ`.

1. **The twisted parameter class.** `exists_isTwistOf` gives a parameter class `E`
   with `IsTwistOf χ_W D E`. A representative of `E` is `χ_W ⊗ A` for a representative
   `A` of `D`. Its inertia kernel is open (`FiniteRepresentation.hasOpenInertiaKernel_twist`,
   since `χ_W` has open kernel on inertia by `isOpen_ker_weilCharacter_inertia`). Its
   Frobenius elements act semisimply, because `(χ_W ⊗ A)(g)` is the scalar multiple
   `χ_W(g) · A(g)` of a semisimple endomorphism.
2. **Block sum of `E`.** `IsAssemblyOf` gives a block decomposition
   `D = ⊕_i σ_i ⊗ Sp(m_i + 1)` and a Langlands-head class `c n D` of the multisegment
   `∑_i [c0 σ_i, ν^(m_i) c0 σ_i]`. By `isBlockSum_twist`, `E` is the block sum of the
   twisted irreducible classes `χ_W σ_i`, with the same lengths `m_i + 1`. The
   equivalence is built from `Blocks.blockTwistEquiv` (Library module
   `WeilDeligne/BlockTwistProof`: `χ ⊗ (σ ⊗ S_m) ≅ (χ ⊗ σ) ⊗ S_m`), from
   `twistDirectSumEquiv` (`χ ⊗ ⊕_i A_i ≅ ⊕_i (χ ⊗ A_i)`) and from the twist of the given
   equivalence.
3. **Twisted multisegment.** By `multisegmentOf_twist`, twisting every cuspidal base of
   `∑_i [c0 σ_i, ν^(m_i) c0 σ_i]` by `χ ∘ det` gives the multisegment
   `∑_i [c0 (χ_W σ_i), ν^(m_i) c0 (χ_W σ_i)]`. For each `i` this is
   `SupercuspidalTwistCompatibility`, turned into an equation of classes by
   `isSupercuspidalCharacterTwist_iff_eq_twist`.
4. **Twisted head.** Let `J ≅ A0` be the Langlands head that represents `c n D`. By
   `htw` and step 3, `J ⊗ (χ ∘ det)` is a Langlands head of the multisegment of the
   `χ_W σ_i`. So the class `π'` of `A0 ⊗ (χ ∘ det)` is a Langlands-head class of that
   multisegment, and `IsCharacterTwist F χ (c n D) π'` holds
   (`isMultisegmentHeadClass_twist`). The kernel of `χ` is open by
   `isOpen_ker_quasiCharacter`. So the kernel of `χ ∘ det` is open on every `GL_k(F)`.
5. **Uniqueness.** Steps 2 and 4 show `IsAssembledFrom F c0 E π'`. `IsAssemblyOf` also
   gives `IsAssembledFrom F c0 E (c n E)`. By `hwell`, `π' = c n E`.

## Declarations

- `twistDirectSumEquiv` (definition): for a finite family of Weil–Deligne
  representations, `χ ⊗ ⊕_i A_i` is equivalent to `⊕_i (χ ⊗ A_i)`. The carrier map is
  the identity.
- `isOpen_ker_quasiCharacter`: a quasi-character of `Fˣ` has open kernel. It is the
  preimage of the open kernel of the continuous character `χ ∘ det` of `GL_1(F)` under
  the continuous scalar embedding `Fˣ → GL_1(F)`.
- `isOpen_ker_weilCharacter_inertia`: `χ ∘ rec` has open kernel on inertia
  (`Weil.Local.localCharacterInertia`).
- `exists_isTwistOf`: step 1, for any Weil character with open kernel on inertia.
- `isBlockSum_twist`: step 2.
- `multisegmentOf_twist`: step 3.
- `isMultisegmentHeadClass_twist`: step 4.
- `twistCompatibility_of_assembly`: the main theorem.

## Provenance

Derived. The module adds one definition, `twistDirectSumEquiv`. It is an elementary
equivalence of Weil–Deligne representations with the identity carrier map. Every
theorem combines published definitions with the two hypotheses `hwell` and `htw`. No new
literature claim is made. Worker 1715 contributed the identity-carrier construction of
twist equivalences, which `twistDirectSumEquiv` follows and which their published
`Blocks.blockTwistEquiv` uses.
