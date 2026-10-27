# Compatible monomial representatives are fixed by Weyl-conjugated transpose

Author: Worker 826.

`Langlands.Whittaker.CompatibleMonomialFixedStatement.{uF}` is an unproved
Prop-valued statement. It is the monomial specialization of property (1.5) of
Shalika (1974), printed p.174, to canonical p-adic fields and the standard
all-ones character. This module only defines the proposition; it proves nothing.

## The statement

For every prime `p` (with `Fact p.Prime`), every `F : PadicField.{uF} p`, every
`n : ℕ`, including `n = 0`, every bundled character
`ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier`, every permutation
`w : Equiv.Perm (Fin (n + 1))` and every diagonal parameter
`d : Fin (n + 1) → F.Carrierˣ`, put

```text
s := GeneralLinear.permutation (n + 1) F.Carrier w *
       GeneralLinear.Iwasawa.diagonalUnits d.
```

The statement asserts

```text
(∀ u v : GeneralLinear.upperUnipotent (n + 1) F.Carrier,
    s * u.val * s⁻¹ = v.val →
      standardCharacter ψ n u = standardCharacter ψ n v) →
  weylTransposeHomeomorph n F.Carrier s = s.
```

The conclusion is an equality of elements of the actual group
`GeneralLinear (n + 1) F.Carrier`. The statement installs `F.canonicalNormedField`
before quantifying over `n`. So the character, the topological ring structure
used by `weylTransposeHomeomorph` and every other topology come from the
canonical p-adic norm. The field universe `uF` is arbitrary.

Nothing else is assumed. In particular there is no premise on `w` (such as a
symmetry under reversal), no equality among the entries of `d`, no Bruhat-cell
stability, representation, distribution or genericity premise.

## Imported objects and conventions

The module imports `Langlands.Group.GL.UpperBruhatCells` and
`Langlands.Representation.Whittaker.Distribution` and uses only these existing
declarations, unchanged:

- `GeneralLinear.permutation (n + 1) F.Carrier w` is the permutation matrix
  sending `e j` to `e (w j)`. By the imported `permutation_entry`, its `(i, j)`
  entry is `1` if `w j = i` and `0` otherwise.
- `GeneralLinear.Iwasawa.diagonalUnits d` is the invertible diagonal matrix with
  entries `d i`. So the `(i, j)` entry of `s` is `d j` when `w j = i`, and `0`
  otherwise.
- `GeneralLinear.upperUnipotent (n + 1) F.Carrier` is the actual subgroup of
  upper triangular matrices with all diagonal entries `1`.
- `standardCharacter ψ n` is the character of that subgroup whose complex value
  at `u` is `ψ` applied to `∑ i : Fin n, u i.castSucc i.succ`, the sum of the
  first-superdiagonal entries (`standardCharacter_apply`).
- `weylTransposeHomeomorph n F.Carrier` is `g ↦ w₀ * gᵀ * w₀`. Here `w₀` is the
  published `weylLong`, the permutation matrix of `Fin.revPerm`, with ones on the
  anti-diagonal. It satisfies `w₀⁻¹ = w₀`. By `weylTransposeHomeomorph_entry`,
  the `(i, j)` entry of the image of `g` is `g j.rev i.rev`.

The bundle `UnitaryAdditiveCharacter` contains continuity, values in the unit
circle, and the field `nontrivial : ψ.toAddChar ≠ 1`. So the statement never
quantifies over a trivial additive character.

The rank is `n + 1`. In rank one (`n = 0`) the superdiagonal sum is empty and,
by the published `weylTransposeHomeomorph_rankOne`, the transpose map is the
identity. The implication is kept in that rank as well.

## Source

The source is J. A. Shalika, *The multiplicity one theorem for GLn*, Annals of
Mathematics (2) **100** (1974), 171–193. It is registered as
`shalika-1974-multiplicity-one`, SHA256
`788c5d124024c768aa47c4e8b179475fbcf5b0882a518ae60b19cdc88089f087`, at
`/home/taskhub/central-library/Shalika--The multiplicity one theorem for GLn--1974.pdf`.
Property (1.5) is on printed p.174 = one-based PDF page 5 = zero-based PDF
index 4. The conventions used there begin on printed p.173 (one-based PDF
page 4, zero-based index 3). Worker 826 read both pages visually. No
source-specific errata note was found in the published notes.

At the start of Section 1 (printed p.173), Shalika takes a field `k`,
`G = GL_n`, the diagonal subgroup `H`, its normalizer `N(H)` and the upper
triangular unipotent group `U`. His `w₀` is the matrix with ones on the
anti-diagonal and zeros elsewhere, the same matrix as the published `weylLong`,
and `Ū = w₀ U w₀⁻¹`. He fixes a nontrivial additive character `ψ` of `k`, and
writes a character of `U` as
`χ(u) = ψ(a₁ x₁₂ + ⋯ + a_{n−1} x_{n−1,n})`. Such a `χ` is nondegenerate exactly
when every `aᵢ` is nonzero. He sets `χ₀(u) = χ(w₀ ᵗu w₀⁻¹)` and fixes `h₀ ∈ H`
with `χ = χ₀^{h₀}`, where `χ^h(u) = χ(h⁻¹ u h)`. The anti-automorphism is
`θ(x) = w₀ h₀ ᵗx h₀⁻¹ w₀⁻¹`. Property (1.5) reads:

> Fix `s ∈ N(H)`. If `χ(u) = χ(s u s⁻¹)` for all `u ∈ U_s = U ∩ s⁻¹ U s`,
> then `θ(s) = s`.

### Monomial specialization

The matrix `s = permutation w * diagonalUnits d` is monomial, so it lies in
`N(H)`. The statement covers every such `s`, for every `w` and `d`. It is not
proved here that every element of `N(H)` has this form.

### The common unipotent domain

The premise quantifies over pairs `u, v` of actual upper-unipotent matrices
with `s * u.val * s⁻¹ = v.val`. For such a pair, `u` lies in `U ∩ s⁻¹ U s`,
which is Shalika's `U_s`, and `v = s u s⁻¹`. Conversely, every `u ∈ U_s` gives
such a pair with `v = s u s⁻¹`. So the premise says exactly that
`χ(u) = χ(s u s⁻¹)` on `U_s`, without constructing `U_s` as a second subgroup.
The character is evaluated only on elements of the actual subgroup `U`.

### The all-ones character and `h₀ = 1`

Shalika's rank `n` is the rank `n + 1` here, and his indices `1, …, n` are
`Fin (n + 1)` here. `standardCharacter ψ n` is Shalika's `χ` with every
`aᵢ = 1`. Since `ψ` is nontrivial, this `χ` is nondegenerate. The published
`standardCharacter_weylTranspose` shows that `χ(w₀ ᵗu w₀) = χ(u)` for every
`u ∈ U`, because reversing the superdiagonal entries keeps their sum. Since
`w₀⁻¹ = w₀`, this says `χ₀ = χ`. So `h₀ = 1` satisfies `χ = χ₀^{h₀}`, and with
this choice `θ(x) = w₀ ᵗx w₀⁻¹`, which is `weylTransposeHomeomorph n F.Carrier`.

### The canonical p-adic specialization

Property (1.5) is algebraic, and Shalika states it for his field `k` with a
nontrivial additive character. The statement here restricts `k` to the
Library's p-adic fields: finite extensions `F.Carrier` of `Padic p`, packaged as
`PadicField.{uF} p`, for every prime `p`. Each carries the topology of
`F.canonicalNormedField`, Mathlib's spectral norm extending the p-adic norm.
This is the field scope of `ShalikaDistributionInvarianceStatement`. The topology
appears only because the imported `UnitaryAdditiveCharacter` and
`weylTransposeHomeomorph` require one. The conclusion applies only the
underlying map of that homeomorphism, and neither the premise nor the
conclusion states a continuity or other topological property.

## Relation to existing declarations

Up to writing out namespaces, the premise is the defining body of the published
predicate `IsCharacterCompatibleRepresentative ψ n s` in
`Langlands.Representation.Whittaker.CompatibleTorus`. For this `s`, that predicate
is membership `d ∈ compatibleTorus ψ n w`, by `mem_compatibleTorus_iff`. This
module neither imports nor uses that predicate or the set `compatibleTorus`,
and defines no compatibility predicate or torus locus of its own.

## Scope

This module defines a proposition and proves nothing. It makes no claim of
invariance of any distribution under `weylTransposeHomeomorph`; that is the
separate `ShalikaDistributionInvarianceStatement`. It does not claim that any
Bruhat cell is stable, unconditionally or otherwise. It does not classify the
compatible permutations `w` or the compatible parameters `d`. Shalika's
combinatorial proof of (1.5) is not formalized here. A proof is left to a
separate task.
