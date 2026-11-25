# Proof: cuspidal realizations trivial on `A_GL` have unitary central characters

Module `Langlands.Global.Factors.CuspidalSplitCentreUnitaryProof` proves

```lean
theorem Langlands.Global.cuspidalSplitCentreUnitaryCentralCharacter :
    CuspidalSplitCentreUnitaryCentralCharacterStatement.{u}
```

The target is the published proposition
`Langlands.Global.CuspidalSplitCentreUnitaryCentralCharacterStatement` of module
`Langlands.Global.Factors.CuspidalSplitCentreUnitaryStatement`, unchanged, with
its universe parameter `u`. It says: for every number field `F : Type u` with
`[CompactSpace (AdeleQuotient F)]`, every `r : ℕ` and every actual cuspidal
realization `T : Automorphic.CuspidalOperatorRealization F r` of `GL_{r+1}`, if
`CuspidalPairPoles.IsTrivialOnSplitCentre T`, then
`Langlands.ClassFieldTheory.Global.RelativeWeilGroup.HasUnitaryCentralCharacter T`.

The module imports the statement module,
`Langlands.Global.HeckeCharacterPositiveRealUnitary` (helper ported with this
file, paired Markdown beside it) and `Langlands.Automorphic.IrreducibleCentralCharacterProof`.
It uses no axiom beyond `propext`, `Classical.choice` and `Quot.sound`.

## Declarations

### `CuspidalPairPoles.isPositiveArchimedeanScalar_positiveRealIdeles`

```lean
theorem Langlands.Global.CuspidalPairPoles.isPositiveArchimedeanScalar_positiveRealIdeles
    {F : Type u} [Field F] [NumberField F] (a : ℝ≥0ˣ) :
    IsPositiveArchimedeanScalar (PositiveRealIdeles.full F a)
```

The positive real ideles of the published module `Global.PositiveRealIdeles`
satisfy the predicate `CuspidalPairPoles.IsPositiveArchimedeanScalar` of the
statement. Its three clauses are proved as follows.

- The finite component of `PositiveRealIdeles.full F a` is `1`. This holds by
  definition (`rfl`): `full` is built from the inclusion of the infinite ideles
  with finite part `1`.
- The real number is `t = a`, which is positive because `a` is a unit of `ℝ≥0`.
- At every infinite place `v`, the chosen extended embedding sends the
  component to `(a : ℂ)`. This is the published lemma
  `PositiveRealIdeles.extensionEmbedding_full`.

### `cuspidalSplitCentreUnitaryCentralCharacter`

Fix `F`, `r`, `T` and the hypothesis `hT : IsTrivialOnSplitCentre T`.

1. **Central character.** `T.realization` is irreducible (`T.irreducible`), so
   it has a central character `χ : NumberField.IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ`
   with `T.realization.HasCentralCharacter χ`. This is the existence part of
   the published theorem `OperatorRealization.existsUnique_hasCentralCharacter`
   (module `Automorphic.IrreducibleCentralCharacterProof`).
2. **A nonvanishing value.** The published lemma
   `OperatorRealization.exists_evaluate_ne_zero` (same module) gives a function
   `f₀` of `T` and a point `x₀ ∈ GL_{r+1}(𝔸_F)` with `f₀(x₀) ≠ 0`.
3. **`χ` is trivial on `A_{G_m}`.** Let `a` be a positive real and
   `z = PositiveRealIdeles.full F a`. The published lemma
   `OperatorRealization.centralCharacter_evaluate` (module
   `Automorphic.OperatorRealization`) gives
   `f₀(z I_{r+1} · x₀) = χ̃(z) f₀(x₀)`, where `χ̃ = centralIdeleCharacter F χ` is
   `χ` pulled back to the ideles. The idele `z` satisfies
   `IsPositiveArchimedeanScalar` (the lemma above), so `hT` gives
   `f₀(z I_{r+1} · x₀) = f₀(x₀)`. Hence `χ̃(z) f₀(x₀) = 1 · f₀(x₀)`, and
   cancelling `f₀(x₀) ≠ 0` gives `χ̃(z) = 1`.
4. **Unitarity.** By step 3, `χ` is trivial on the class of every
   `PositiveRealIdeles.full F a`. The helper theorem
   `HeckeCharacter.isUnitary_of_positiveRealIdeles` (module
   `Global.HeckeCharacterPositiveRealUnitary`) then gives `‖χ(c)‖ = 1` for every
   idele class `c`. The types agree: `HeckeCharacter F` is an abbreviation of
   `IdeleClasses F →ₜ* ℂˣ`, and `IdeleClasses F` is an abbreviation of
   `NumberField.IdeleClassGroup (𝓞 F) F` (module `Global.Adelic`). The class
   map `ideleClassMap F` and the quotient map inside `centralIdeleCharacter`
   are both `QuotientGroup.mk'` of the principal ideles, so they agree
   definitionally and step 3 is the hypothesis of the helper theorem without
   any transport.
5. The pair `χ`, with the unitarity of step 4 and the central character of
   step 1, is `HasUnitaryCentralCharacter T`.

## Relation to the route of the statement Markdown

The statement Markdown (`CuspidalSplitCentreUnitaryStatement.md`, "Why the
statement is true") outlines four steps. Steps 1–3 above carry out its steps 1
and 2. Its steps 3 and 4 (decompose `z = a · y` with
`a ∈ A_{G_m}` and `|y| = 1`, using `t = |z|^{1/[F:ℚ]}`, then use the
compactness of `F^× \ (𝔸_F^×)^1`) are replaced by the helper theorem, whose
proof avoids `[F:ℚ]`-th roots. It uses `z ^ d = PositiveRealIdeles.full F |z| · y`
with `|y| = 1` and `d = [F:ℚ]`, the published lemma
`HeckeEulerProduct.norm_eq_one_of_ideleClass_eq_one` for `y`, and then
`‖χ(z)‖ ^ d = 1`. That published lemma carries out step 4 of the outline (a
compact group bounds `‖χ‖`, and `t ≠ 1` would give unbounded powers). A
comparison between `NormOneIdeleClasses F` and the idele class group is not
needed, because that lemma is stated on the idele class group directly.

## Sources and provenance

- J. R. Getz and H. Hahn, *An Introduction to Automorphic Representations*,
  Graduate Texts in Mathematics 300, Springer, 2024. Registered source
  `getz-hahn-2024-automorphic-representations`, PDF
  `/home/taskhub/central-library/Getz-Hahn--An introduction to automorphic representations (book)--2024.pdf`
  (SHA256
  `a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`). In
  Chapter 2 the PDF page is the printed page + 17, in Chapter 6 + 14, in
  Chapter 11 + 11.
  - Displays (2.19)–(2.20), printed page 68 (PDF page 85), continued on printed
    page 69: `A_{G_m}` is "the image of the diagonal embedding
    `ℝ_{>0} → F_∞^×`, regarded as a subgroup of `𝔸_F^×`", and
    `A_{GL_n} = {a I_n : a ∈ A_{G_m}}`.
  - Lemma 2.6.2, printed page 69 (PDF page 86): for a number field,
    `A_G G(𝔸_F)^1 = G(𝔸_F)` and `A_G ∩ G(𝔸_F)^1 = 1`. Its case `G = G_m` is the
    mathematical content of the helper theorem.
  - Display (6.20), printed page 168 (PDF page 182), and Theorem 6.5.3, printed
    page 169 (PDF page 183): cuspidal automorphic representations of
    `A_G \ G(𝔸_F)` are the `K`-finite parts of irreducible subrepresentations
    of `L²_cusp([G])`, so their central characters are unitary. This is the
    source of the statement. The Lean proof does not use `L²`: it derives
    unitarity from triviality on `A_{GL_{r+1}}` and the compactness of
    `F^× \ (𝔸_F^×)^1` alone.
  - Printed page 309 (PDF page 320), before Theorem 11.7.1: the normalization
    "we can assume that `π` (resp. `π'`) is trivial on `A_{GL_n}` (resp.
    `A_{GL_m}`)", which is the hypothesis `IsTrivialOnSplitCentre`.

The argument is the one in "Why the statement is true" of the statement
Markdown (`Langlands/Global/Factors/CuspidalSplitCentreUnitaryStatement.md`),
with steps 3 and 4 modified as described above. The identification of
`PositiveRealIdeles.full` with Getz–Hahn's `A_{G_m}` is the lemma
`isPositiveArchimedeanScalar_positiveRealIdeles` together with the published
Markdown of `CuspidalPairPoleStatement` (section on `A_GL`), which compares
`IsPositiveArchimedeanScalar` with display (2.20).

## Scope

- The theorem proves exactly the published statement. It does not prove a
  converse (a unitary central character need not be trivial on `A_{GL_n}`).
- Nothing is proved about twisting a cuspidal realization to make it trivial on
  `A_{GL_n}` (the "without loss of generality" of printed page 309), or about
  `L²` realizations.

## Lean checks

A `lake build` of this module and the helper module, in the Lean environment in
which they were written, compiled with no errors or warnings.
`cuspidalSplitCentreUnitaryCentralCharacter` is a
theorem with universe parameter `u`, and it depends only on the axioms
`propext`, `Classical.choice` and `Quot.sound`.
