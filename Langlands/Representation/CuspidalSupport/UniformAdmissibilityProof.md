# Uniform admissibility and uniform support (Renard VI.2.3–VI.2.4): proof

Module `Langlands.Representation.CuspidalSupport.UniformAdmissibilityProof`.
Namespace `Langlands.CuspidalSupport`. Universe parameters `u, v`.

`Langlands.CuspidalSupport.uniformAdmissibilityStatements` proves exactly
`UniformAdmissibilityStatements.{u, v}` (module
`Langlands.Representation.CuspidalSupport.UniformAdmissibilityStatements`,
[statement](UniformAdmissibilityStatements.md)). Here `u` is the universe of the
local field and `v` that of the representation carriers. The theorem has no
hypotheses. It proves all three conjuncts of the statement:

- `RationalPointsUniformAdmissibilityStatement.{u, v}`: Renard VI.2.3, Theorem.
  For every compact open subgroup `K` of `G(F)` there is `c : ℕ` with
  `rank V^K ≤ c` for every irreducible smooth complex representation `V` of
  `G(F)`.
- `RationalNormKernelUniformAdmissibilityStatement.{u, v}`: the Remark after
  VI.2.3. The same bound holds for the irreducible smooth representations of
  the common norm kernel `⁰G` and its compact open subgroups.
- `SupercuspidalUniformCoefficientSupportStatement.{u, v}`: Renard VI.2.4,
  Proposition. For every compact open subgroup `K` there is one open set,
  compact modulo the centre, that contains the support of every level-`K`
  coefficient of every irreducible supercuspidal representation.

The scope is the full scope of the statement. The theorem covers every
nonarchimedean local field in `Type u`, of either characteristic, and every
connected reductive group over it. Its axioms are `propext`,
`Classical.choice` and `Quot.sound`.

The module also proves `Langlands.CuspidalSupport.rationalPointsIrreducibleAdmissible`.
It proves `Aubert.General.RationalPointsIrreducibleAdmissibleStatement.{u, v}`
(Renard VI.2.2, Jacquet's theorem): every irreducible smooth complex
representation of `G(F)` is admissible. It holds for every carrier universe `v`.

## Proof

The proof is a composition of published Library theorems. Their source
arguments are in their own modules; this module adds no mathematical argument.

1. **Joint special-compact basis.**
   `BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence`
   (module `Langlands.BruhatTits.SpecialCompact.JointBasisProof`) proves
   `JointSpecialCompactBasisExistenceStatement.{u}`. This is the Chapter V
   structural input (Renard V.5.1–V.5.2). Take a maximal split torus with a
   generic cocharacter. At one special vertex, the theorem gives one special
   compact subgroup `K₀`. For `K₀` it gives the Iwasawa and Cartan
   decompositions, standard-Levi compatibility, and a basis of compact open
   subgroups. The subgroups of the basis are normal in `K₀` and adapted to
   every standard parabolic subgroup.
2. **VI.2.2.** `rationalPointsIrreducibleAdmissible` applies
   `Aubert.General.rationalPointsIrreducibleAdmissible_of_jacquetCartanDatum` to
   `Aubert.General.rationalPointsJacquetCartanDatum_of`. The latter builds a
   Jacquet–Cartan datum on every `G(F)` from step 1 and the proved theorems
   `GroupScheme.standardCocharacter` and `GroupScheme.standardParabolicOrder`.
   The former deduces admissibility of every irreducible smooth representation
   from that datum.
3. **VI.2.3 for `G(F)`.** `rationalPointsUniformAdmissibilityReduction`
   (module `RationalPointsUniformAdmissibilityReduction`) derives
   `RationalPointsUniformAdmissibilityStatement` from four inputs: step 1,
   `GroupScheme.standardCocharacter`, `GroupScheme.relativeRootSystem` and
   VI.2.2. Its proof passes to a smaller compact open level `K_L ≤ K`. There a
   Cartan-type decomposition gives finite sandwich data for the Hecke corner
   at level `K_L`: finitely many edge elements and finitely many commuting
   middle elements whose sandwich products span the corner. These data take
   the place of the printed decomposition `H(G, K) = ∑_j H₀ A D_j H₀` of V.5.3.
   Let `V` be an irreducible smooth representation. VI.2.2 makes `V^{K_L}`
   finite-dimensional. The bound `Hecke.FixedLevelSandwich.finrank_le` then
   has two cases. If `V^{K_L} = 0`, its dimension is zero and the bound holds
   trivially; this case does occur, for instance for a ramified character of a
   split torus. Otherwise `V^{K_L}` is a simple module of the corner by
   `CompactCoefficientClass.isSimpleModule_fixedVectors`. That theorem uses
   irreducibility and `V^{K_L} ≠ 0` (Renard III.1.5, Theorem (i): the fixed
   space is simple or zero). The dimension of a finite-dimensional simple
   module of the corner is bounded by a number that depends on the sandwich
   data alone. In both cases `V^K ⊆ V^{K_L}` gives the same bound for `V^K`.
   The reduction is applied here at carrier universe `max u v`, with VI.2.2
   from step 2 at the same universe.
4. **VI.2.4.** `supercuspidalUniformCoefficientSupportReduction` (module
   `SupercuspidalUniformSupportReduction`) derives
   `SupercuspidalUniformCoefficientSupportStatement.{u, v}` from four proved
   theorems: `GroupScheme.parabolicDynamic`, `GroupScheme.standardCocharacter`,
   `GroupScheme.relativeRootSystem` and step 1.
5. **Assembly.** `uniformAdmissibilityAssemblyReduction` (module
   `UniformAdmissibilityAssemblyReduction`) takes the `G(F)` theorem at carrier
   universe `max u v` from step 3 and VI.2.4 at `u, v` from step 4. It returns
   the full conjunction at `u, v`. It lowers the carrier universe of the `G(F)`
   theorem through `ULift`. It derives the `⁰G` theorem by the argument of the
   Remark after VI.2.3. Compact induction from `⁰G` to `G(F)` of an irreducible
   `σ` has an irreducible quotient `τ`. By Frobenius reciprocity `σ` embeds in
   the restriction of `τ` to `⁰G`, so the bound for `τ` bounds `σ^K`.

The Lean term of the main theorem is

```
uniformAdmissibilityAssemblyReduction.{u, v}
  (rationalPointsUniformAdmissibilityReduction.{u, max u v}
    jointSpecialCompactBasisExistence standardCocharacter relativeRootSystem
    rationalPointsIrreducibleAdmissible.{u, max u v})
  (supercuspidalUniformCoefficientSupportReduction.{u, v} parabolicDynamic
    standardCocharacter relativeRootSystem jointSpecialCompactBasisExistence)
```

## Provenance

The statements formalize David Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques` (SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`). The
sections are VI.2.2 Theorem, VI.2.3 Theorem and Remark, and VI.2.4 Proposition
(printed pp.140–142 / PDF pp.146–148). The statement Markdown gives the source
correspondence. This proof is an internal composition of the published Library
theorems named above. For VI.2.3 it uses sandwich data in place of the printed
form of V.5.3 (step 3), so its constant differs from Renard's
`(h² q)^{2^{d-1}}`. It does not use the identification
`C_∅^+/C_{A_G} ≅ ℕ^d` of V.3.24, which is false in general.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.Representation.CuspidalSupport.UniformAdmissibilityAssemblyReduction` | `uniformAdmissibilityAssemblyReduction` |
| `Langlands.Representation.CuspidalSupport.RationalPointsUniformAdmissibilityReduction` | `rationalPointsUniformAdmissibilityReduction` |
| `Langlands.Representation.CuspidalSupport.SupercuspidalUniformSupportReduction` | `supercuspidalUniformCoefficientSupportReduction` |
| `Langlands.Representation.Aubert.General.IrreducibleAdmissibleOfDatum` | `Aubert.General.rationalPointsIrreducibleAdmissible_of_jacquetCartanDatum` |
| `Langlands.Representation.Aubert.General.RationalJacquetCartanDatum` | `Aubert.General.rationalPointsJacquetCartanDatum_of` |
| `Langlands.GroupScheme.Absolute.ParabolicDynamicProof` | `GroupScheme.parabolicDynamic` |
| `Langlands.GroupScheme.Rational.StandardCocharacterProof` | `GroupScheme.standardCocharacter` |
| `Langlands.GroupScheme.Rational.RelativeRootSystemProof` | `GroupScheme.relativeRootSystem` |
| `Langlands.GroupScheme.Rational.StandardParabolicOrderProof` | `GroupScheme.standardParabolicOrder` |
| `Langlands.BruhatTits.SpecialCompact.JointBasisProof` | `BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence` |
