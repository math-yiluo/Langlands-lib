# A generic σ-stable representation that is not σ-induced is tempered (statement)

Module `Langlands.BaseChange.GenericSigmaNoninducedTemperedStatement`, declaration
`Langlands.BaseChange.GenericSigmaNoninducedTemperedStatement` (level parameters `u v uW`). The
module states one proposition and does not prove it.

## Statement

Let `F` be a nonarchimedean local field of characteristic zero. Let `E` be a field that is a
cyclic `F`-algebra of degree `l` with generator `σ`, with its module topology over `F`. Let
`r : ℕ` and `n = r + 1`. Let `τ` be an admissible representation of `GL_n(E)` on a complex vector
space `W : Type uW`. Assume:

1. `τ` is generic for some unitary additive character `ψ` of `E`;
2. `τ` has a central character `χ` with `|χ(z)| = 1` for every central `z`;
3. `τ` is σ-stable: `τ ≅ τ^σ`;
4. for every block shape `B` of `n` with at least two blocks and every smooth representation `Ξ`
   of the Levi product `M_B(E) = ∏ᵢ GL_{nᵢ}(E)` on a space `X : Type uW` with `Ξ ≅ Ξ^σ`, `τ` is
   not isomorphic to the smooth induction of `Ξ`, inflated to the standard upper block
   parabolic `P_B(E)` through the Levi projection.

Then `τ` is tempered.

In Lean, the binders are, in this order: `F : Type u` with `[Field F] [ValuativeRel F]
[TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]`; `E : Type v` with
`[Field E] [Algebra F E] [TopologicalSpace E] [IsTopologicalRing E] [IsModuleTopology F E]`;
`σ : E ≃ₐ[F] E`; `l r : ℕ`; `hE : IsCyclicAlgebra σ l`; then, by `haveI`, `Module.Finite F E`
from `hE.1` and the instances `generalLinear_t2Space_of_finite`,
`generalLinear_locallyCompactSpace_of_finite` and
`generalLinear_totallyDisconnectedSpace_of_finite` on `GeneralLinear (r + 1) E`. The proposition
continues

`∀ {W : Type uW} [AddCommGroup W] [Module ℂ W]
(τ : Representation ℂ (GeneralLinear (r + 1) E) W), IsAdmissible τ →
∀ (ψ : UnitaryAdditiveCharacter E), Whittaker.IsGeneric ψ r τ →
∀ χ : Subgroup.center (GeneralLinear (r + 1) E) →* ℂˣ, HasCentralCharacterRep τ χ →
(∀ z, ‖(χ z : ℂ)‖ = 1) → IsSigmaStable σ (r + 1) τ →
(∀ B : BlockShape (r + 1), 2 ≤ B.length →
∀ (X : Type uW) [AddCommGroup X] [Module ℂ X] (Ξ : Representation ℂ (B.Levi E) X),
IsSmooth Ξ → IsLeviSigmaStable σ B Ξ →
IsEmpty (τ.Equiv (Induction.smoothInduced (B.parabolic E) (Ξ.comp (B.leviProjection E))))) →
IsTemperedRep τ`.

## Library notation

- `IsCyclicAlgebra σ l` (module `Langlands.BaseChange.Norm`): `E` is a finite reduced
  `F`-algebra of dimension `l`, `σ` has order `l`, and the elements fixed by `σ` are those of
  `F`. Here `E` is a field, so `E/F` is a cyclic extension of degree `l`.
- `Whittaker.IsGeneric ψ r τ` (module `Langlands.Representation.Whittaker.GeneralLinear`): `τ`
  is irreducible and admissible and has a nonzero Whittaker functional for the standard
  character of the upper unipotent subgroup of `GL_{r+1}(E)` defined by `ψ`.
- `HasCentralCharacterRep τ χ` (module `Langlands.BaseChange.PseudoCoefficient`): every central
  `z` acts on `W` by the scalar `χ z`.
- `IsSigmaStable σ n τ` (module `Langlands.BaseChange.TwistedCharacter`): there is an
  isomorphism of `τ` onto `τ^σ = τ ∘ entrywiseAut σ n` (`SigmaIntertwiner σ n τ`).
- `BlockShape n`, `B.parabolic E`, `B.Levi E`, `B.leviProjection E` (module
  `Langlands.Group.GL.Blocks`): positive block sizes summing to `n`, the standard upper block
  triangular subgroup, the product of the block groups and the projection onto the diagonal
  blocks.
- `Induction.smoothInduced` (module `Langlands.Representation.Induction.Definitions`):
  unnormalized smooth induction by right translation.
- `IsLeviSigmaStable σ B Ξ` (module `Langlands.BaseChange.PseudoCoefficient`): `Ξ ≅ Ξ^σ`, with
  `σ` acting entrywise on every block. The modulus character of `P_B(E)` is σ-invariant, so
  σ-stability of the unnormalized inducing representation `Ξ` and of the normalized one
  `Ξ ⊗ δ_P^{-1/2}` are the same.
- `IsTemperedRep τ` (module `Langlands.BaseChange.PseudoCoefficient`): for every Haar measure on
  `GL_n(E)/Z`, `τ` is admissible, has a unitary central character and has matrix coefficients in
  `L^{2+ε}` modulo the centre for every `ε > 0`.

## Remarks on the form

- **Hypothesis 4** is the non-induction clause of the Library's `IsSigmaDiscreteSeries` (module
  `Langlands.BaseChange.PseudoCoefficient`), with the same carrier universe for `Ξ`. A
  representation satisfying the hypotheses of the statement and its conclusion is a σ-discrete
  series in the sense of `IsSigmaDiscreteSeries`.
- **Unitary central character.** Without it the conclusion fails: twisting a σ-discrete series
  by `|det|^s`, `s` real and nonzero, keeps hypotheses 1, 3 and 4 (`|det|^s` is σ-invariant) and
  destroys temperedness.
- **Genericity.** It is used to write `τ` as a full induced representation, not only a
  Langlands quotient. For a non-generic `τ`, hypothesis 4 says nothing about its Langlands
  data.
- **Admissibility** is bound separately for uniformity with the Library's
  `GenericSigmaEllipticDiscreteStatement`; `Whittaker.IsGeneric` already contains it.

## Why it is true (sketch; not part of the Lean)

1. **Classification.** By Zelevinsky's theorem (Zelevinsky 1980, Theorem 9.7), a generic `τ` is
   isomorphic to the normalized parabolic induction `Δ₁ × ⋯ × Δ_k` of essentially
   square-integrable `Δᵢ` (special representations of pairwise unlinked segments), and this
   product is irreducible and independent of the order; the multiset `{Δᵢ}` is determined by
   `τ`. The Library proves this for `GL_{r+1}` over fields presented as `PadicField`
   (`Langlands.Classification.genericSegmentProductExhaustion`, module
   `Langlands.Representation.Classification.GenericSegmentProductExhaustionProof`, and
   `Langlands.Classification.genericSegmentProductUniqueness`, module
   `Langlands.Representation.Classification.GenericSegmentProductUniquenessProof`).
2. **σ permutes the factors.** `τ^σ ≅ Δ₁^σ × ⋯ × Δ_k^σ`, since `σ` preserves the standard
   parabolic subgroups and their Levi projections. By uniqueness and `τ ≅ τ^σ`, `σ` permutes the
   multiset `{Δᵢ}`. Write `|ω_{Δᵢ}(a)| = |a|_E^{nᵢ eᵢ}` with real exponent `eᵢ`; since
   `|σ(a)|_E = |a|_E`, `Δᵢ^σ` has the exponent of `Δᵢ`.
3. **Unequal exponents give a σ-stable proper induction.** If the `eᵢ` are not all equal, let
   `Ξ₁` be the product of the `Δᵢ` of maximal exponent and `Ξ₂` the product of the others. By
   step 2 the two sub-multisets are σ-stable, so `Ξ₁ ≅ Ξ₁^σ` and `Ξ₂ ≅ Ξ₂^σ`, and by induction in
   stages and independence of the order, `τ` is the normalized induction of `Ξ₁ ⊗ Ξ₂` from a
   standard Levi subgroup with two blocks. In unnormalized form this is the induction of the
   σ-stable smooth representation `(Ξ₁ ⊗ Ξ₂) ⊗ δ_P^{1/2}`, which (being of countable dimension)
   can be realized on a space in `Type uW`. This contradicts hypothesis 4.
4. **Equal exponents.** If all `eᵢ = e`, the central character of `τ` has absolute value
   `|a|_E^{n e}` at `a · 1`, so `e = 0` by hypothesis 2. Then every `Δᵢ` is square-integrable,
   and a normalized induction of square-integrable representations is tempered (the Library's
   `Langlands.Classification.squareIntegrableBlockInduction`, module
   `Langlands.Representation.Classification.SquareIntegrableBlockInductionProof`).

Henniart–Lemaire argue with the Langlands classification instead: `τ ≅ ι_{α'}(Ξ'_{ψ'})` for a
Langlands triple `(α', Ξ', ψ')` with `Ξ'` tempered and `ψ'` a positive unramified character; `Ξ'`
is σ-stable with `τ`; if `α' ≠ (n)` this is a σ-stable proper induction, so `α' = (n)`, `τ` is a
tempered representation twisted by `|det|^a`, and the unitary central character gives `a = 0`.

## Provenance

This is derived content, formulated for this Library. It isolates the classification step of
the proof of Henniart–Lemaire 2011, II.5.8, Lemme (printed p. 106): "Puisque Π est σ-stable, Ξ′
l'est aussi, et d'après 4.5, si α est différent de (n), alors la fonction caractère `Θ^A_Π` est
nulle sur `G(E)_{σ-e}`. Donc α = (n) et Π ≅ Ξ′_{ψ′}", together with the passage from
"essentiellement σ-discrète" to σ-discrete by a unitary central character (II.4.7, printed
p. 89: "Π est une série σ-discrète si et seulement si ω est unitaire"; II.5.15, Proposition 1,
printed p. 117), and of Arthur–Clozel 1989, Chapter 1, proof of Lemma 2.11 (printed pp. 18–19:
"Therefore M = G, and Π is essentially tempered … Again, the condition on the character implies
that Π is itself σ-discrete"). In the sources the alternative "`τ` is a σ-stable proper
induction" is excluded by the twisted character on the σ-elliptic set; here it is excluded by
hypothesis 4, so the statement contains no character theory. Its conclusion is temperedness
only: σ-stability and non-induction are hypotheses.

## Sources

- G. Henniart, B. Lemaire, *Changement de base et induction automorphe pour GL_n en
  caractéristique non nulle*, Mém. SMF 124 (2011): II.4.6–II.4.7 (printed pp. 88–89), II.5.8,
  Lemme and its proof (printed p. 106), II.5.15, Proposition 1 (printed p. 117). The PDF page is
  the printed page plus 8.
- J. Arthur, L. Clozel, *Simple algebras, base change, and the advanced theory of the trace
  formula*, Ann. of Math. Stud. 120 (1989): Chapter 1, Lemma 2.11 and its proof (printed
  pp. 18–19). The PDF page is the printed page plus 14.
- A. V. Zelevinsky, *Induced representations of reductive p-adic groups II. On irreducible
  representations of GL(n)*, Ann. Sci. ÉNS 13 (1980), Theorem 9.7, for step 1 of the sketch.
