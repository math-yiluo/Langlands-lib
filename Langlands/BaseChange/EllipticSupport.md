# Test functions supported in the regular elliptic set

The module `Langlands.BaseChange.EllipticSupport` (namespace `Langlands.BaseChange`) defines
when a function on `GL_n(F)` is supported in the regular elliptic set and when a function on
`GL_n(E)` is supported in the σ-elliptic set, and proves their elementary properties. All
proofs are complete.

## Sources

- Henniart–Lemaire, *Changement de base et induction automorphe pour GL_n en
  caractéristique non nulle*, Mém. SMF 124 (2011), source ID
  `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`, file
  `/home/taskhub/central-library/Henniart-Lemaire--Changement de base et induction automorphe pour GLn en caracteristique non nulle--2011.pdf`
  (PDF page = printed page + 8). Cited as HL. II.1.2 (printed pp. 55–56): regular and
  elliptic elements, the sets `G(F)_e` of regular elliptic elements and `G(E)_{σ-e}` of
  σ-elliptic elements; I.2.2, Lemme (printed p. 12): for a cyclic algebra, the elements
  associated with a given `δ` exist and form one conjugacy class; II.6.3 (printed p. 120): the
  condition `c_{v₁}(f)` of the simple trace formula, whose first clause is
  "`f_{v₁}` s'annule en dehors des éléments (réguliers) elliptiques de `G(F_{v₁})`";
  II.6.4 (printed p. 121): the condition `c^σ_{v₁}(φ)` of its twisted form, whose first
  clause is "`φ_{v₁}` s'annule en dehors des éléments (σ-réguliers) σ-elliptiques de
  `G(E_{v₁})`"; II.6.6, continued at the top of printed p. 123 (before the heading II.6.7):
  the comparison of the two trace formulas for functions `f` and `φ` satisfying all the
  conditions of 6.3 and 6.4, "en particulier les conditions `c_{v₁}(f)` et `c^σ_{v₂}(φ)`"
  for places `v₁` and `v₂` that may differ.

The two predicates below formalize only the pointwise support clauses of `c_{v₁}(f)` and
`c^σ_{v₁}(φ)`; the further clause of these conditions (a linear combination of coefficients
of cuspidal representations) is not part of them.

## Setting

`GL_n(R)` is the Library's `GeneralLinear n R`. In items 1 and 3, `F : Type u` is a field and
`n : ℕ`; in items 2 and 4, `E : Type v` is moreover a commutative `F`-algebra,
`σ : E ≃ₐ[F] E` and `l : ℕ`. No topology and no hypothesis relating `σ` and `l` is needed.

## Definitions

1. `IsEllipticSupported f`, for `f : GL_n(F) → ℂ`: every `g` with `f g ≠ 0` satisfies the
   Library's `JacquetLanglands.IsRegularElliptic g` (characteristic polynomial separable and
   irreducible over `F`). This is HL's condition that `f` vanish off the set `G(F)_e` of
   regular elliptic elements (as in `c_{v₁}(f)`), with the Library's notion of regular
   elliptic element. HL II.1.2 call `γ` regular when its characteristic polynomial
   is a product of distinct irreducible polynomials, not necessarily separable, and elliptic
   when moreover `F[γ]` is a field; the Library asks for a separable characteristic
   polynomial, so the two notions agree when `F` is perfect, in particular in characteristic
   zero.
2. `IsSigmaEllipticSupported σ l φ`, for `φ : GL_n(E) → ℂ`: every `δ` with `φ δ ≠ 0`
   satisfies `IsSigmaElliptic σ l δ` (module `Langlands.BaseChange.Norm`; `δ` is associated with a regular elliptic
   element of `GL_n(F)`). This is HL's condition that `φ` vanish off the set `G(E)_{σ-e}` of
   σ-elliptic elements (as in `c^σ_{v₁}(φ)`), with the Library's notion of regular
   elliptic element. The two notions of σ-elliptic element differ in two ways:
   - *Quantifier.* HL II.1.2 ask that every element associated with `δ` be elliptic,
     `IsSigmaElliptic` that some associated element be regular elliptic. For a cyclic algebra, the
     elements associated with `δ` exist and form one conjugacy class of `GL_n(F)` (HL I.2.2;
     `CyclicNormLemmaStatement` of `Langlands.BaseChange.Norm`, proved as `cyclicNormLemma` in
     `Langlands.BaseChange.CyclicNormLemma`), so for a property invariant
     under conjugacy, "some associated element" and "every associated element" agree.
   - *Separability.* As in item 1, the Library's regular elliptic elements have a separable
     characteristic polynomial, whereas HL's elliptic elements need not. For a cyclic
     algebra, the σ-elliptic elements of `IsSigmaElliptic` are therefore exactly HL's σ-elliptic elements
     whose associated elements have a separable characteristic polynomial; this is a strict
     subset in general when `F` is not perfect (for instance `F = 𝔽₂((t))`, `E = F`,
     `σ = id`, `l = 1`, and `δ` the companion matrix of `X² - t`, which is HL-elliptic with
     inseparable characteristic polynomial). The two notions agree when `F` is perfect, in
     particular in characteristic zero, the setting of `EllipticTransferStatement`, which uses
     this predicate.

Both are pointwise conditions on arbitrary functions; they are applied to test functions by
the coercion of `SchwartzBruhat` to functions.

## Lemmas (all proved)

3. For `IsEllipticSupported`:
   - `IsEllipticSupported.isRegularSupported`: an elliptic-supported `f` satisfies
     `IsRegularSupported f` (module `Langlands.BaseChange.OrbitalIntegral`), by the Library's
     `IsRegularElliptic.isRegularSemisimple`;
   - `isEllipticSupported_zero`: the zero function is elliptic-supported;
   - `IsEllipticSupported.add`: if `f` and `f'` are, so is `f + f'` (where `(f + f') g ≠ 0`,
     one of `f g`, `f' g` is nonzero);
   - `IsEllipticSupported.const_mul`: if `f` is, so is `fun g => c * f g` for every `c : ℂ`
     (where `c * f g ≠ 0`, `f g ≠ 0`).
4. For `IsSigmaEllipticSupported`:
   - `IsSigmaEllipticSupported.isSigmaRegularSupported`: a σ-elliptic-supported `φ`
     satisfies `IsSigmaRegularSupported σ l φ`: a witness `γ` of
     `IsSigmaElliptic σ l δ` is regular elliptic, hence regular semisimple, and so witnesses
     `IsSigmaRegular σ l δ`;
   - `isSigmaEllipticSupported_zero`, `IsSigmaEllipticSupported.add` and
     `IsSigmaEllipticSupported.const_mul`, with the same proofs as in item 3.

## Dependencies and names

The module imports `Langlands.BaseChange.Norm` (`IsSigmaElliptic`,
`IsSigmaRegular`), `Langlands.BaseChange.OrbitalIntegral`
(`IsRegularSupported`, `IsSigmaRegularSupported`) and the Library's
`Langlands.JacquetLanglands.RegularElliptic` (`IsRegularElliptic`,
`IsRegularElliptic.isRegularSemisimple`). All names are used as published.
