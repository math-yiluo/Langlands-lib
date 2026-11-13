# Existence of actual cuspidal contragredients without a unitary center

Author: Worker 5003.

`Langlands.Automorphic.CuspidalContragredientExistenceStatement.{uF}` is a Prop-valued
definition for a later proof. It states exactly:

```lean
∀ (F : Type uF) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  (r : ℕ) (T : CuspidalOperatorRealization F r),
  ∃ T' : CuspidalOperatorRealization F r, T'.realization.IsContragredientOf T.realization
```

`AdeleQuotient` is in `Langlands.Global`; the other declarations are in
`Langlands.Automorphic`. The number field `F` is arbitrary, with the Library's explicit
compactness instance for its additive adelic quotient. The group is `GL_(r+1)`, of
positive rank, including rank one.

## Meaning

The input `T` is an arbitrary [cuspidal operator realization](CuspidalOperatorRealization.md):
an actual irreducible space of automorphic functions under the finite adelic, standard
compact and real Lie algebra operators, with vanishing proper constant terms. Its central
character may be any Hecke character; in particular it need not be unitary.

The conclusion asks for another actual cuspidal operator realization `T'` of the same rank,
together with the published [contragredient relation](Contragredient.md)
`T'.realization.IsContragredientOf T.realization`: some bilinear pairing of `T` with `T'`
is invariant under the finite adelic group, the standard compact subgroup and the real Lie
algebra (acting by the negative transpose), and its partial map is a bijection from `T'`
onto the contragredient functionals of `T` (the algebraic functionals that are smooth for
the finite adelic group and finite for the standard compact subgroup). Nothing else is
asserted about `T'`: no presentation, no central character and no uniqueness.

## Relation to existing Library statements

- `CuspidalUnitaryContragredientExistenceStatement` in
  [CuspidalContragredientStatement](CuspidalContragredientStatement.md) has the extra
  premise `HasUnitaryCentralCharacter T` and the extra conclusion that `T'` has a unitary
  central character. It is proved (`cuspidalUnitaryContragredientExistence`) through the
  complex conjugate realization paired by a unitary form; that route uses unitarity.
  The present statement drops the premise and the extra conclusion.
- `CuspidalDualPresentationExistenceStatement`
  ([module](CuspidalDualPresentationExistenceStatement.md), proved) supplies spectral
  presentations of a *supplied* contragredient `T'` of a presented `T`, again without
  unitarity. It does not construct `T'`. With the present statement it gives presentations
  of the contragredient of every presented cuspidal realization.

The consumer is the proof of `AssociatedGammaStatement` (Henniart 2000, Théorème 2.3),
whose cuspidal inputs `T`, `T'` have arbitrary central characters. The completed
Rankin–Selberg functional equation `CuspidalPairGlobalFunctionalEquationStatement` takes
actual contragredients `Td`, `Td'` of the twisted pair as supplied inputs, so the global
argument needs them for nonunitary realizations as well.

## Derived provenance

This is a derived interface, not the verbatim statement of a single source theorem. The
original passages were read directly:

| Source | Passage | Role |
| --- | --- | --- |
| J. W. Cogdell, *Lectures on L-functions, converse theorems, and functoriality for GL_n* (Fields Institute lectures, 2003), registered as `cogdell-2003-fields-lectures-www` | Lecture 5, §1, Proposition 5.1(iii) and the paragraph after it, printed p.38 (0-based PDF page index 41) | For a cusp form `φ`, the function `φ̃(g) = φ(ᵗg⁻¹)` is again a cusp form; with `π̃(g) = π(ᵗg⁻¹)`, `π̃` is the contragredient of `π` and `φ̃ ∈ V_π̃`. |
| Same source | Lecture 5, opening paragraphs, printed p.37 (0-based PDF page index 40) | Cogdell takes `π` unitary there and remarks that the condition of unitarity is not restrictive but allows convenient normalizations. |
| G. Henniart, *Une preuve simple des conjectures de Langlands pour GL(n) sur un corps p-adique* (2000), `henniart-2000-simple-proof` | §2.2, printed p.444 (PDF p.6) | For an arbitrary automorphic representation `Π` (no unitarity) associated with `S`, `S^∨` and `Π^∨` are associated; Théorème 2.3 (§2.3) is stated for arbitrary automorphic `Π`, `Π'`. |

The standard fact behind the statement is that the contragredient of a cuspidal
automorphic representation of `GL_n(𝔸_F)` is again cuspidal automorphic, with no
condition on the central character. The sources do not construct the Library's actual
realization with its finite, compact and Lie algebra operators, nor its perfect invariant
pairing. A proof must supply these. Two routes are available, and the statement fixes
neither:

1. Realize `T'` on the transpose-inverse functions `φ(ᵗg⁻¹)` as in Cogdell. Identifying
   this realization with the contragredient needs the local result that `π_v ∘ ι` is the
   contragredient of `π_v` (Gelfand–Kazhdan) and a global comparison, or another argument.
2. Reduce to the proved unitary case by a twist. The Library already twists actual
   cuspidal realizations by `χ ∘ det` for an *arbitrary* Hecke character `χ`, with no
   finite-order premise: `CuspidalOperatorRealization.heckeDeterminantTwist` in
   [HeckeTwist.OperatorTwist](HeckeTwist/OperatorTwist.md). Its equivalence
   `heckeDeterminantTwistEquiv` sends `f` to `g ↦ χ(det g) f(g)`, picks up the scalar
   `χ(det ·)` at finite and compact translations, and intertwines a differential operator
   `D(a)` with `D(heckeEnvelopingShift n χ a)`. If `T` has central character `ω`, the
   positive character `μ = ‖ω‖^(−1/(r+1))` makes the twist `T ⊗ μ` have a unitary central
   character, so `cuspidalUnitaryContragredientExistence` gives a contragredient `T₀'` of
   `T ⊗ μ`, and `T₀' ⊗ μ` should be a contragredient of `T` through the pairing
   `B(μ·f', f) = B₀(f', μ·f)`. The obligations that remain are:
   - central-character analysis: that `T` has some central character `ω` at all (a
     Schur-lemma statement for the actual realization; the Library has no existence result
     of this kind for `CuspidalOperatorRealization`), and that `T ⊗ μ` has central character
     `ω μ^(r+1)`;
   - the norm-character specialization: `μ` as a continuous character of the idele class
     group (`HeckeCharacter F`) with `‖ω μ^(r+1)‖ = 1`;
   - the invariant pairing: invariance of the transported pairing, where the scalars
     `μ(det g)` of the two twists cancel at finite and compact elements and the two
     enveloping shifts cancel for the real Lie algebra;
   - perfectness: that the transported partial map is a bijection from `T₀' ⊗ μ` onto the
     contragredient functionals of `T`, which needs that composing with the twist
     equivalence preserves finite-adelic smoothness and compact finiteness of functionals.

These are proof obligations of the derived target, not hypotheses or results of this
module, which proves nothing.
