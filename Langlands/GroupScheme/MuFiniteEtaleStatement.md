# Finite étaleness of the actual roots-of-unity group scheme

Author: Worker 306.

`Langlands.GroupScheme.MuFiniteEtaleStatement.{u}` is the proposition

```lean
∀ (S : Scheme.{u}) (n : ℕ),
  0 < n → IsUnit (n : Γ(S, ⊤)) →
    IsFinite (mu S n).X.hom ∧ Etale (mu S n).X.hom
```

Here `IsFinite` and `Etale` are Mathlib's properties of the structure morphism
of the existing group scheme. The module defines a proposition; it does not
prove it or install geometric instances.

## Existing construction and exact scope

The import `Langlands.GroupScheme.Multiplicative` supplies the actual
`Langlands.GroupScheme.Gm S` and `Langlands.GroupScheme.mu S n` unchanged.
The latter's underlying group scheme is definitionally

```lean
Langlands.GroupScheme.kernel
  (Langlands.GroupScheme.multiplication
    (Langlands.GroupScheme.Gm S).toGrp (n : ℤ))
```

This follows by unfolding `mu` and `torsion`; in particular the structure
morphisms agree definitionally. Thus a future proof of this proposition will
supply the finite and étale kernel hypotheses used by the existing Tate
monodromy constructions. No arbitrary replacement scheme or structure field
containing the desired conclusion occurs in this statement.

The quantifiers include every scheme in universe `u` and every positive natural
index. There is no assumption of connectedness, noetherianity, an algebraically
closed geometric point, or a chosen primitive root. `IsUnit` is a hypothesis
about the natural-number image in the base's global section ring.

## Checked original sources and derivation

Edixhoven, van der Geer and Moonen, *Abelian Varieties*, preliminary draft,
Chapter III, Examples 2–3, printed p. 32 (PDF p. 36), identifies the represented
units functor and its roots-of-unity subgroup. Example 3 uses positive `n` and
coordinate algebra `𝒪_S[x,x⁻¹]/(xⁿ−1)`. These examples justify the interpretation
of the imported construction, but do not assert finite étaleness.

The Stacks Project, [Example 39.5.2, Tag 040M](https://stacks.math.columbia.edu/tag/040M),
gives `Spec(ℤ[x]/(xⁿ−1))` and its base changes as the representing schemes.
For positive `n`, the polynomial coordinate is already invertible, so this
agrees with the Laurent-coordinate description. The imported natural
`mu.pointsEquiv` identifies the same represented functor; the comparison with
this affine model follows mathematically by Yoneda and remains part of the
future Lean proof.

The geometric claim is derived from the **proof**, rather than the sheaf-exactness
conclusion, of [Lemma 59.28.1, Tag 03PL](https://stacks.math.columbia.edu/tag/03PL).
Set its unit parameter to `1`. Over each affine open `Spec A`, the resulting
algebra is `A[t]/(tⁿ−1)`, free on `1,t,…,tⁿ⁻¹`. The restriction of the global unit
`n` stays invertible; `t` is invertible and the derivative `n tⁿ⁻¹` is a unit.
The source's standard-étale calculation therefore gives étaleness, and the
finite affine algebras give finiteness over `S`. This is a source derivation,
not an implemented proof in this module. The retained comments to Tag 03PL
explicitly clarify that its natural numbers are positive and that invertibility
is essential. No additional base hypothesis is used.

## Retained sources and reading record

- `edixhoven-vandergeer-moonen-abelian-varieties-draft`,
  `literature/Edixhoven, van der Geer, Moonen - Abelian Varieties (preliminary version of the first chapters).pdf`;
  SHA256 `81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
  PDF p. 36 was read and the fingerprint verified.
- `stacks-mu-finite-etale-2026-10-23`,
  `literature/Stacks Project - Roots of unity and the Kummer finite etale calculation (2026-10-23)/`;
  directory SHA256 `2de0f5be19b97254240ff5c7f1d41e9f81baa3280c9bba48263572c52bf29064`.
  Original `040M.html` and `03PL.html`, retrieved 23 October 2026, were read,
  including the comments. Their individual SHA256 values are
  `4dc450e8ae44698c605f1d8a8a3a637ccfcbb069d2599dc0385d123a2954fdbc`
  and `a71ef76e1123074b4e38b89a72307a4c7fd8f1ecf7e99fcf94040f5ed03b5773`,
  respectively.

No project errata note for either source was present when checked. This
statement does not assert a rank formula, a trivialization, or a monodromy
comparison. Its exact-target proof is a separate follow-up task.
