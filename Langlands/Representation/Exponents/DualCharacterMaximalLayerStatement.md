# Maximal layers of a dual-detected character quotient

This module defines the proposition `Langlands.DualCharacterMaximalLayerStatement`
(universe parameters `uG uH uV`). It states the assertion but does not prove it.
The statement concerns the quotient and defect-image representations that are
already published in `Langlands.Representation.Exponents.DualCharacterQuotient`.
The module introduces no new data.

Worker 322 wrote the Lean formulation. Worker 728 audited it against the source
and the published API, reused it unchanged, and wrote this Markdown.

## Exact statement

Let `G : Type uG` be a group and `H : Type uH` a commutative group. Let
`V : Type uV` be a complex vector space, `ρ : Representation ℂ G V` any
representation, and `ι : H →* G` a homomorphism with
`hι : ∀ a, ι a ∈ Subgroup.center G`. Let `χ : H →* ℂˣ` be a character and `d`
a natural number with `0 < d`. Assume

```
commutativeCharacterNilpotenceIndex (commutativeTranspose (ρ.comp ι)) χ = (d : ℕ∞).
```

Then two things hold:

1. There exists `a : H` such that the carrier of
   `DualCharacterQuotient.defectRangeRepresentation ρ ι hι χ a (d - 1)` is
   `Nontrivial`.
2. For every `a : H`,
   `Classification.HasScalarCharacter
     (DualCharacterQuotient.defectRangeRepresentation ρ ι hι χ a (d - 1)).ρ ι χ`
   holds.

Since `0 < d`, the natural subtraction `d - 1` is the ordinary predecessor.

## Meaning of the objects used

All of the following are existing Library declarations, used unchanged.

- **Transpose.** `T := commutativeTranspose (ρ.comp ι)` is the action of `H` on
  the full algebraic dual `Module.Dual ℂ V`, given by `(T a φ) v = φ (ρ (ι a) v)`
  (`commutativeTranspose_apply`). It has the same order as `ρ`. There is no
  inversion of `a` and no complex conjugation.
- **Generalized dual space.** `E := DualCharacterQuotient.dualSpace ρ ι χ` is
  defined as `generalizedCommutativeCharacterSpace T χ`. It consists of the
  functionals `φ` that admit some `k` with
  `(T a - (χ a : ℂ) • 1) ^ k φ = 0` for all `a : H`.
- **Nilpotence index.** `commutativeCharacterNilpotenceIndex T χ` is
  `centralCharacterNilpotenceIndex` applied to the center of `H`, which is all of
  `H`. It is the least `n` for which one power `n` kills `T a - χ a` on all of
  `E`, uniformly in `a`, and it is `⊤` when no such `n` exists. The zero space
  has index `0`.

  The hypothesis therefore says three things: `E` is nonzero, `E` has a finite
  uniform exponent, and that exponent is exactly `d`. By
  `commutativeCharacterNilpotenceIndex_le_iff`, minimality means that `E` is
  not contained in `commutativeCharacterSpace T χ (d - 1)`.
- **Quotient.** `C := DualCharacterQuotient.quotient ρ ι hι χ` is the quotient
  of `V` by `annihilator ρ ι hι χ`, the common kernel of all functionals in `E`.
  It is a `Rep.{uV} ℂ G` that keeps the full `G`-action and the original carrier
  universe. Functionals in `E` descend to `C` via `evaluation`, and together
  they separate the points of `C` (`eq_zero_iff`).
- **Defect.** `D_a := DualCharacterQuotient.defect ρ ι hι χ a` is the
  `G`-endomorphism `C.ρ (ι a) - (χ a : ℂ) • 1` of `C`.
- **Defect image.** `defectRangeRepresentation ρ ι hι χ a k` is the range of
  `D_a ^ k` (`defectRange`), with the `G`-representation that the range
  inherits. When `d = 1`, the exponent is `0`, so the image is the whole
  quotient `C` (`defectRange_zero`); no separate case is needed.
- **`Nontrivial`.** For the carrier, `Nontrivial` means that the image contains
  a nonzero vector.
- **Scalar character.** By definition,
  `Classification.HasScalarCharacter R.ρ ι χ` means
  `R.ρ (ι c) w = (χ c : ℂ) • w` for every `c : H` and every vector `w` of `R`.
  For the image of `D_a ^ (d - 1)`, this is equivalent to
  `D_c (D_a ^ (d - 1) q) = 0` for all `c : H` and all `q ∈ C`. In words, the
  image lies in the simultaneous `χ`-eigenspace of the central action on `C`.

A private development check confirmed the last three equivalences in this
environment. It also confirmed that the statement applies verbatim to the
specialization in `DualCharacterQuotient`: the image representation
`T.dualJacquetCharacterDefectRangeRepresentation B A χ a (d - 1)` of the
opposite Jacquet module, under the hypothesis
`T.dualJacquetExponentNilpotenceIndex B A χ = d`.

## Scope

- The coefficients are `ℂ`. The scalar-action conclusion fails in positive
  characteristic. For example, let `H = (ℤ/2)^2` act on the regular
  representation `𝔽₂[H] ≅ 𝔽₂[x, y]/(x², y²)` with trivial `χ`. The uniform
  exponent is `2`, but for the generators `a, b` the product of defects is
  `(b - 1)(a - 1) = xy ≠ 0`. This remark is informal and is not part of the
  Lean statement.
- The universes of `G`, `H` and `V` are independent of one another.
- There are no topological, smoothness, admissibility, irreducibility,
  finite-dimensionality, finite-length, decomposition, unitarity, criticality or
  analytic hypotheses.
- Both conclusions are claims about the actual published quotient and image
  representations. Neither is a field of some new structure.
- The statement says nothing about square-integrability, supports, irreducible
  quotients or supercuspidality.

## Provenance

This is a derived algebraic interface, not a verbatim theorem of the source.
The source is Silberger, *Introduction to harmonic analysis on reductive p-adic
groups* (1979), registered as `silberger-1979-harmonic-analysis` with SHA256
`b9432812bb48ce0bcd3975144baa6b3cca99bcaaf0d33d785ce68e94e02854fc`. The PDF
page number is the printed page number plus six.

- **Printed p.91 (PDF p.97).** For `χ` an exponent of `V/V(N̄)`, Silberger sets
  `V'_χ = {φ ∈ V' | ᵗπ(n̄)φ = φ, (ᵗπ(a) − δ^{1/2}(a)χ(a))^{n(φ)} φ = 0 (a ∈ A)}`.
  He calls `d(χ) = max n(φ)` over `φ ∈ V'_χ` the *multiplicity* of `χ`, and
  defines `V̄_χ` as "the quotient module whose dual is `V'_χ`". Our
  `commutativeCharacterNilpotenceIndex` is the least uniform exponent on the
  whole generalized dual component. For a commuting action this equals the
  maximum of the individual exponents. The transpose has the same order, as
  Silberger's `ᵗπ` does.
- **Printed p.92 (PDF p.98), proof of Corollary 2.4.2.** Silberger sets
  `V̄_{j,χ} = {v̄ ∈ V̄_χ | (π̄(a) − δ^{1/2}(a)χ(a))^j v̄ = 0 for all a ∈ A}`.
  He writes "By hypothesis, `V̄_χ ≠ V̄_{d-1,χ}`", then "Clearly, for every
  `a ∈ A`, `(π̄(a) − δ^{1/2}(a)χ(a))^{d-1}` induces an M-module morphism of
  `V̄_χ/V̄_{d-1,χ}` into `V̄_{1,χ}`", then "Choose `a ∈ A` such that the image
  `W` is not zero".

  Conclusion (1) is the choice of `a` with `W ≠ 0`. Conclusion (2) is the
  "Clearly" step: the image lands in `V̄_{1,χ}`, the common `χ`-eigenspace.
- **Printed pp.189–190 (PDF pp.195–196).** The proof of Corollary 4.5.11 reuses
  the same image construction for weakly critical exponents ("arguing as in
  Corollary 2.4.2").

The source text and the central library contain no erratum for these pages.

The generic setting is a project choice. Silberger's objects correspond to ours
as follows:

| Silberger | This statement |
| --- | --- |
| the Levi `M` | the acting group `G` |
| the split component `A` | the commutative group `H` |
| the inclusion of `A` into the center of `M` | the central homomorphism `ι` |
| `π̄` on `V/V(N̄)` | `ρ` |
| `δ^{1/2}χ` | `χ` |
| `V'_χ` | `E` |
| `V̄_χ` | `C` |
| `W` | the range representation |

Silberger's admissibility, finite generation, criticality and supercuspidality
are not used. The statement records only the algebraic step, for an arbitrary
complex representation, under the hypothesis that the uniform exponent is finite
and positive.

## Proof obligations

These are for the separate proof task; nothing here is assumed or proved.

- **Nonzero image (conclusion 1).** Minimality of `d`, through
  `commutativeCharacterNilpotenceIndex_le_iff`, gives `φ ∈ E` and `a : H` with
  `(T a - χ a)^(d-1) φ ≠ 0`. Then `evaluation_defect_pow_quotientMap` gives a
  `v` with `D_a^(d-1)(quotientMap v) ≠ 0`.
- **Scalar action (conclusion 2).** By `eq_zero_iff` and
  `evaluation_defect_pow_quotientMap`, it suffices to prove
  `N_b N_a^(d-1) = 0` on `E`, where `N_c = T c - χ c` and `N_c^d = 0` for every
  `c`. Commutation together with separate nilpotence does not imply this; see
  the counterexample in Scope.

  A characteristic-zero argument does work. Let `U_c = χ(c)⁻¹ T c` on `E`; each
  `U_c` is unipotent and the `U_c` commute. Set `X_c = log U_c`. Then `X_c` is
  additive in `c` and `X_c^d = 0`, so `(t X_a + X_b)^d = 0` for
  `t = 0, …, d`. A Vandermonde argument extracts the coefficient of `t^(d-1)`,
  which gives `d · X_a^(d-1) X_b = 0`. Finally, `X_a^(d-1) = (U_a - 1)^(d-1)`,
  and `X_b` is `U_b - 1` times a unit.
