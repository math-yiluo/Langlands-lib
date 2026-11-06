# Determinant compatibility of the Henniart assembly

Author: Worker 1705.

This module proves the determinant part of the published proposition
`Langlands.Correspondence.AssemblyOperationStatement` (module `AssemblyRelation`). Its
main theorem is conditional on one published but unproved proposition, which is an
explicit hypothesis:

| Hypothesis | Library declaration (module) | Content |
| --- | --- | --- |
| `hcc` | `Classification.MultisegmentConstituentCentralCharacter.{uF, uA} F F.canonicalTopologicalData` (`Representation/Classification/MultisegmentConstituentCompatibilityStatement`) | If each base of a multisegment `a = Δ_1 + … + Δ_r` has central character `ω_i`, then the Zelevinsky socle and the Langlands head of `a` have central character `∏_i ω_i^(m_i) · |det|^((m_i-1)/2)`, where `m_i` is the length of `Δ_i`. |

The module does not prove `hcc`. It is a separate proof target in the Library. Apart
from `hcc`, the main theorem uses exactly the hypotheses of
`AssemblyOperationStatement` that concern determinants:

- the assembly relation `IsAssemblyOf F c0 c`,
- geometric normalization `IsGeometricReciprocity F e`,
- supercuspidal determinant compatibility `SupercuspidalDeterminantCompatibility F e c0`.

It needs neither well-definedness of the assembly (`AssemblyWellDefinedStatement`) nor
any uniqueness or classification statement. The determinant is computed from the block
decomposition and the Langlands head that `IsAssemblyOf` supplies for the given class.

## Main theorem

```lean
theorem determinantCompatibility_of_assembly
    (hcc : Classification.MultisegmentConstituentCentralCharacter.{uF, uA} F
      F.canonicalTopologicalData)
    (c0 : SupercuspidalMap.{uF, uP, uA} F) (c : FullMap.{uF, uP, uA} F)
    (e : ReciprocityCandidate F) (hc : IsAssemblyOf F c0 c) (he : IsGeometricReciprocity F e)
    (hdet : SupercuspidalDeterminantCompatibility F e c0) : DeterminantCompatibility F e c
```

`DeterminantCompatibility F e c` says: for every parameter class `D` of rank `n` and
every `w` in the local Weil group, the scalar `rec(w) = reciprocityHom F e w` acts on
some representative of `c n D` by `det D (w)` (`parameterDeterminant`). All
declarations are in the namespace `Langlands.Correspondence.AssemblyDeterminant`. The
axioms used are `propext`, `Classical.choice` and `Quot.sound`.

## Literature context

Henniart 2002, §§2.2–2.9 (printed pp.593–596, PDF pp.7–10), describes the objects
this module works with: the decomposition of a Weil–Deligne representation into
indecomposable blocks `ρ ⊗ St_n` (§§2.2–2.3, where `St_n` restricted to the Weil group
is `1 ⊕ ν ⊕ … ⊕ ν^(n-1)`), the Langlands quotients of §2.8, and the assembled bijection
of §2.9. Henniart does not state determinant or central-character compatibility of the
assembly there, and gives no argument for it. The argument below is an internal derived
argument. It combines the published central-character formula for multisegments, kept as
the explicit hypothesis `hcc`, with elementary linear algebra for the determinant of a
block sum, which is proved here.

## Proof

Fix `n`, `D` and `w`. `IsAssemblyOf` gives:

- `r`, ranks `d_i + 1`, lengths `m_i + 1` and irreducible Weil classes `σ_i`;
- representatives `B_i` of `σ_i`, a representative `A` of `D`, and an equivalence
  `φ : ⊕_i block ν B_i (m_i + 1) ≃ A`;
- an automorphic object `A0` of class `c n D`, a Langlands head `J` of the multisegment
  `∑_i [c0 σ_i, ν^(m_i) c0 σ_i]`, and an equivalence `ψ : J ≃ A0`.

The proof has three steps.

1. **Central characters of the bases.** By `exists_centralCharacter`, each `det σ_i`
   factors through reciprocity: `det σ_i = ω_i ∘ rec` for a character `ω_i` of `Fˣ`.
   This uses only that `rec` is surjective and that `c0` is determinant-compatible. If
   `rec w = 1`, then `det σ_i (w)` acts as the identity on a nonzero vector of an
   irreducible representative of `c0 σ_i`, so `det σ_i (w) = 1`. Then
   `MonoidHom.liftOfSurjective` gives `ω_i`. By `hasScalarCharacter_of_isoClass`, every
   supercuspidal representative `R_i` of `c0 σ_i` has central character `ω_i`.
2. **Central character of the head.** By `hcc`, applied to the segments
   `segmentOf F c0 σ_i m_i` and to the `R_i`, the head `J` has central character
   `∏_i segmentCentralCharacter F (segmentOf F c0 σ_i m_i) ω_i`. By `smul_of_equiv`
   along `ψ`, this character also gives the action of `rec w` on `A0`.
3. **Comparison with the determinant.** `parameterDeterminant_eq` and `φ` reduce
   `det D (w)` to the determinant of `w` on the block sum. `det_directSum_block_apply`
   computes that determinant:
   `∏_i det(B_i(w))^(m_i+1) · (∏_(j<m_i+1) ν(w)^j)^(d_i+1)`.
   For each `i`, `segmentCentralCharacter_reciprocityHom` evaluates the `i`th factor
   of step 2 at `rec w`. It gives `ω_i(rec w)^(m_i+1) · (∏_(j<m_i+1) ν(w)^j)^(d_i+1)`.
   Finally `ω_i(rec w) = det σ_i (w) = det B_i (w)` (`irreducibleWeilDeterminant_eq`),
   and `B_i` has rank `d_i + 1` (`rank_eq_of_classOf_eq`).

The comparison of absolute values uses geometric normalization. By
`normalizedAbs_reciprocityHom`, the normalized absolute value of `rec w` equals the
norm character `ν(w) = q^(-deg w)`, because the order of `rec w` is the degree of `w`
(`IsGeometricReciprocity`, first component). Then `determinantPowerCharacter_reciprocityHom`
computes the power. The value of `|det|^(m/2)` on the scalar `rec w` in
`GL_((m+1)(d+1))` is
`ν(w)^((m+1)(d+1)m/2) = (∏_(j<m+1) ν(w)^j)^(d+1)`,
by the identity `2 · ∑_(j ≤ m) j = (m+1)m`.

## Declarations

### Linear algebra (any field `K`, any group `G`)

- `det_piMap_fin`: the determinant of a product of endomorphisms `∏_(i : Fin r) M_i`
  is the product of the determinants. The proof is by induction on `r`, using
  `Fin.consLinearEquiv` and `LinearMap.det_prodMap`. Mathlib's `LinearMap.det_pi`
  covers only a constant carrier.
- `det_directSum_lmap`: the same for `DirectSum.lmap` on `⨁_(i : Fin r) M_i`. It is
  transported along `DirectSum.linearEquivFunOnFintype`.
- `det_special_action`: the uncentered special block
  `WeilDeligneRepresentation.Special.action ν m g` is diagonal with entries
  `ν(g)^j`, `j < m`. Its determinant is their product.
- `det_block_apply`: the determinant of `block ν A m = A ⊗ S_m` at `g` is
  `det(A(g))^m · (∏_(j<m) ν(g)^j)^(rank A)`. This uses `Langlands.det_tensorProduct_map`.
- `det_directSum_block_apply`: the product of the previous formula over a direct sum of
  blocks.

### Representations and reciprocity

- `smul_of_equiv`: if `g` acts by a scalar `z` on one representation, it acts by `z`
  on every equivalent representation.
- `eq_one_of_smul_eq`, `exists_ne_zero_of_isIrreducible`: if a scalar fixes a nonzero
  vector, the scalar is `1`; an irreducible representation has a nonzero vector.
- `centralActsBy_apply`: `CentralActsBy` on a class holds on every representative of
  the class.
- `reciprocityHom_surjective`: `reciprocityHom F e` is surjective, because `e` is an
  equivalence from the abelianized Weil group.
- `normalizedAbs_reciprocityHom`: under geometric reciprocity, the normalized absolute
  value of `rec w` is the norm character at `w`.
- `determinantPowerCharacter_reciprocityHom`: the computation of `|det|^(m/2)` on
  `rec w` described above, for a segment of length `m + 1` with base of rank `d + 1`.
- `segmentCentralCharacter` (definition): the character
  `a ↦ ω(a)^(length Δ) · |det(a · 1)|^((length Δ - 1)/2)` of `Fˣ`, with `a · 1` in
  `GL_(deg Δ)`. It is literally the factor `ωΔ` in the statement of
  `Classification.MultisegmentConstituentCentralCharacter`. That proposition asserts
  that it is the central character of `Δ` when the base of `Δ` has central character `ω`.
- `segmentCentralCharacter_reciprocityHom`: its value at `rec w` for the segment
  `segmentOf F c0 σ m`.
- `parameterDeterminant_eq`, `irreducibleWeilDeterminant_eq`: the determinant of a
  parameter class, or of an irreducible Weil class, is the determinant character of
  any representative.
- `rank_eq_of_classOf_eq`: a representative of an irreducible Weil class of rank `n`
  has rank `n`.
- `exists_centralCharacter`, `hasScalarCharacter_of_isoClass`: step 1 of the proof.
- `determinantCompatibility_of_assembly`: the main theorem.

## Provenance

Derived. The module adds one definition, `segmentCentralCharacter`. It names the
character `ωΔ` that already occurs, in exactly this form, inside the published
statement `Classification.MultisegmentConstituentCentralCharacter`. Every theorem
combines published definitions with that one hypothesis. No new literature claim is
made. In particular, the module does not assume the classification, the
well-definedness of the assembly or any correspondence.
