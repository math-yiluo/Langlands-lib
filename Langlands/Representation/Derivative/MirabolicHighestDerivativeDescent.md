# Radical triviality and `Ψ⁻` descent of pairings

Authors: Worker 1024.

This module proves two lower inputs of the proof of Bernstein–Zelevinsky,
*Induced representations of reductive p-adic groups I* (BZ77), Proposition 3.8
(module `Langlands.Representation.Derivative.MirabolicHighestDerivativePairingProof`).
The third input, detection of zero representations by their derivatives, is in
`Langlands.Representation.Derivative.MirabolicDerivativeVanishing`, which this
module imports. Throughout, `F` is a p-adic
field with topological data `T`, `ψ` is a unitary additive character, and
`uF`, `uV`, `uW` are independent universes: the field, the first
representation space and the second representation space. `mirabolic n F` is
`P_(n+1)`, `radical n F` is its unipotent radical `V_(n+1) ≅ F^n`, and
`levi : GL_n → P_(n+1)` is `g ↦ diag(g, 1)`.

## Main declarations

```
Langlands.Derivative.Mirabolic.radical_acts_trivially_of_phiMinus T ψ m :
  ∀ X : SmoothRep ℂ (mirabolic (m + 1) F.Carrier),
    Subsingleton ((phiMinus T ψ m).obj X) →
    ∀ (u : radical (m + 1) F.Carrier) (v : X), X.representation u v = v

Langlands.Derivative.Mirabolic.psiMinus_nondegeneratePairing T n :
  ∀ (A : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier))
    (B : SmoothRep.{0, uF, uW} ℂ (mirabolic n F.Carrier)),
    (∀ (u : radical n F.Carrier) (v : A), A.representation u v = v) →
    ∀ β : InvariantBilinear.forms A.representation B.representation
        (fun g => |det g.val|),            -- via T.determinantNorm (n + 1)
      (∀ v, (∀ w, β.val v w = 0) → v = 0) →
      ∃ γ : InvariantBilinear.forms ((psiMinus T n).obj A).representation
          ((psiMinus T n).obj B).representation (fun _ => 1),
        ∀ v, (∀ w, γ.val v w = 0) → v = 0
```

The other declarations in the module are listed under "Auxiliary declarations".

## Provenance

* `radical_acts_trivially_of_phiMinus` is the case `Φ⁻ X = 0` of BZ77
  Proposition 3.2(e) (printed p. 451): `0 → Φ⁺Φ⁻X → X → Ψ⁺Ψ⁻X → 0` is exact,
  so `Φ⁻ X = 0` gives `X ≅ Ψ⁺Ψ⁻X`, and the radical acts trivially there. Here
  it is proved directly, without the exact sequence or the plus functors.
* `psiMinus_nondegeneratePairing` is the `Ψ` case of BZ77 Proposition 3.7(a)
  (printed p. 453), for representations on which `V` acts trivially. That is
  exactly the situation of the case `k = 1` in the proof of Proposition 3.8. The
  covariance translation follows the statement's Markdown: the source
  `Δ_P`-pairing is a form with Library covariance `g ↦ |det g|`, and the output is
  an invariant pairing (covariance one).

## Implemented proof

### Radical triviality (`eq_zero_of_forall_mem_relations`, `radical_acts_trivially_of_phiMinus`)

`eq_zero_of_forall_mem_relations` states: a vector `x` of a smooth
representation of `P_(m+2)` that lies in the relation span
`relations ρ V χ_a` of every coordinate character `χ_a(u(c)) = ψ(a ⬝ c)` is
zero. Its proof is, line for line, the final part of the published proof of
`subsingleton_of_psiMinus_phiMinus`. Smoothness gives a radical lattice box
fixing `x`. `eventually_characterAverage_eq_zero` (from
`Jacquet.CharacterAveraging`) makes each twisted average of `x` over growing
radical boxes vanish. `exists_forall_characterAverage_eq_zero` picks one level
that works for a whole dual box of characters. Then the finite Fourier
inversion `eq_zero_of_forall_characterAverage_eq_zero` gives `x = 0`. The
published theorem proves this vector-wise fact only inside its own proof, so
the module repeats it as a standalone lemma.

For `radical_acts_trivially_of_phiMinus`, let `Φ⁻ X = 0`, i.e. the
`θ_ψ`-relations are everything. Fix `u ∈ V` and `v`, and put `y = ρ(u) v - v`.

* For `a = 0` the character is trivial (`coordinateCharacter_zero`), and `y` is
  a generator of the trivial-character relations (`sub_mem_relations`).
* For `a ≠ 0`, `exists_lastRow_eq_of_ne_zero` gives `g ∈ GL_(m+1)` with last row
  `a`. `levi_inv_mem_relations` carries the `θ_ψ`-relation `ρ(levi g) y` to the
  `χ_a`-relation `ρ(levi g⁻¹) ρ(levi g) y = y`.

So `y` lies in every coordinate-character relation span, and `y = 0`.

### Descent through `Ψ⁻` (`psiMinusDescendedForm`, `psiMinus_nondegeneratePairing`)

Let the radical act trivially on `A`. Let `β` have covariance
`β(ρ_A(g) v, ρ_B(g) w) = |det g| β(v, w)`.

* Radical elements have determinant one (`determinantNorm_radical`: the radical
  sits inside the upper unipotent group, `RankinSelberg.unipotent_det`). Hence
  `β(ρ_A(u) v, ρ_B(u) w) = β(v, w)`, and since `ρ_A(u) v = v` we get
  `β(v, ρ_B(u) w) = β(v, w)`.
* `psiMinusDescendedForm` factors `β` twice through the actual coinvariant
  quotients by the trivial-character relations, using
  `Jacquet.Localization.lift`. First `β.flip` descends in the second variable.
  Then the flipped result descends in the first variable, using `ρ_A(u) v = v`.
  By construction `γ(q_A v, q_B w) = β(v, w)` (`psiMinusDescendedForm_mk`, by
  `rfl`).
* The normalized `Ψ⁻` action is `g · q(v) = |det g|^(-1/2) q(ρ(levi g) v)`
  (`psiMinus_action`). Hence
  `γ(g · q v, g · q w) = |det g|^(-1/2) |det g|^(-1/2) |det (levi g)| β(v, w)`.
  `determinantNorm_levi` gives `|det_(n+1)(levi g)| = |det_n g|`, by the
  block-diagonal determinant. `half_power_mul_half_power_mul_self` gives
  `r^(-1/2) r^(-1/2) r = 1` for `r > 0`. So `γ` is invariant.
* Left nondegeneracy: every class is `q_A v`. If `γ(q_A v, ·) = 0`, then
  `β(v, w) = γ(q_A v, q_B w) = 0` for all `w`, so `v = 0` and `q_A v = 0`.

## Normalization bridges proved here

* `determinantNorm_levi`: `T.determinantNorm (n + 1) (levi g) = T.determinantNorm n g`.
* `determinantNorm_radical`: `T.determinantNorm (n + 1) u = 1` for `u` in the radical.
* `half_power_mul_half_power_mul_self`: the two `|det|^(-1/2)` twists of the
  normalized `Ψ⁻` (`Mirabolic.psiMinus`, via `realPowerCharacter`) cancel the
  covariance `|det|`.

No Haar modulus, plus functor or unnormalized/normalized comparison is used.

## Auxiliary declarations

`eq_zero_of_forall_mem_relations`, `determinantNorm_levi`,
`determinantNorm_radical`, `half_power_mul_half_power_mul_self`,
`psiMinusDescendedForm`, `psiMinusDescendedForm_mk`; all are in namespace
`Langlands.Derivative.Mirabolic`.

## Imports and independence audit

Direct imports: `Langlands.Representation.Derivative.MirabolicDerivativeVanishing`
(the companion module of this candidate, which imports `MinusVanishing` and
`MirabolicDerivativeDetectionStatement`; its own audit is in its Markdown) and
`Langlands.Representation.Filtration.InvariantBilinear`. Besides these two
modules of the candidate, the transitive `Langlands` import closure has 76
public modules: the 73 of `MirabolicDerivativeVanishing` plus
`Filtration.InvariantBilinear`, `Filtration.Definitions` and
`Filtration.ObjectDefinitions`. They cover
groups, local fields and their normalization, harmonic-analysis conductors,
smooth representations and twists, localization and character averaging,
compact orbit means, matrix coefficients, Whittaker characters, and the
elementary Rankin–Selberg lattice and quotient-integral lemmas used by
`MinusVanishing`, plus `Category.Subquotients` and the three filtration
modules. Every imported public Lean/Markdown pair is byte-identical to the
Library at `6789e5106aba61566887427750f5444a494d5879`.

Mathematical proof dependencies: the definitions of the minus functors and
the coinvariant quotients; the invariant-form spaces of
`Filtration.InvariantBilinear`; character averaging and its eventual vanishing;
the published `MinusVanishing` lemmas (its coordinate-character, Levi-transport,
radical-box and Fourier-inversion lemmas); `RankinSelberg.unipotent_det`; the
elementary determinant facts above. Nothing from `MirabolicDerivativeVanishing`
is used in this module's proofs; it is imported so that the proof module sees
one linear chain of the candidate's modules. No minus-functor exactness (the published
`MinusExactnessStatement` is neither imported nor used), no plus functor, no
`Φ⁺Φ⁻`/`Ψ⁺Ψ⁻` exact sequence, no Haar modulus comparison, and no consumer
result is used.

The Independence exclusions of task `a925b519-9bb9-4927-873e-ad322d41328e` hold.
Neither this module nor its import closure uses: the nonadjacent product
consumer `3c9849a4-a6c0-43ac-9982-d15ed76bf1e9`; `TwoSupercuspidalProductStructure`
or parent task `ab61f565-1427-4746-ba77-46097563e962`; any of the excluded
special-head, segment-socle, segment-classification, square-integrability,
exhaustion, existence, coverage, conversion, tempered-uniqueness,
product-irreducibility, socle-commutation or segment Jacquet-formula tasks,
statements or conclusions listed there; Ze80's segment derivative formulas
(§3.5, §9.6), Ze80 4.2, 9.3 or 9.7; or any classification or exhaustion
theorem. A text scan of the 78 Lean files of the closure (including the two
candidate modules) finds none of the excluded
declaration names. The only hits are in two imported Markdown files
(`Iteration.md`, `MirabolicMinus.md`), whose independence paragraphs state that
those names are *not* used; this Markdown and the companion one name
`MinusExactnessStatement` and `TwoSupercuspidalProductStructure` only to say
they are not used. The only derivative results used are the published,
accepted `MinusVanishing` lemmas and the published definitions.
