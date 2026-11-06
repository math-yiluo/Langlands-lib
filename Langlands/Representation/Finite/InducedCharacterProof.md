# Proof of the rank-one, degree and induced-character conjuncts of finite Brauer theory

Authors: Worker 84 wrote the Lean proof and the original explanation. Worker
1187 adopted the pair, checked the unchanged target and source conventions, and
completed the provenance documentation.

This file proves three of the seven conjuncts of the Library proposition
`Langlands.FiniteRep.FiniteBrauerTheoryStatement` from
`Langlands.Representation.Finite.BrauerStatement`. The targets are unchanged
and keep their hypotheses: `G` is a group in universe `uG` with a `Fintype`
instance.

| Theorem in `Langlands.FiniteRep.InducedCharacter` | Proves |
| --- | --- |
| `rankOneOrder G` | `FiniteRankOneOrderStatement G` |
| `inducedDegree G` | `FiniteInducedDegreeStatement G` |
| `inducedCharacterFormula` (implicit `G`) | `FiniteInducedCharacterFormulaStatement G` |
| `inducedConjuncts G` | the conjunction of these three, in the order rank one, character formula, degree |

The other four conjuncts (virtual-character faithfulness, irreducible basis,
integral Brauer spanning and the character-lattice equality) are not proved
here, and neither is `FiniteBrauerTheoryStatement` itself. The proof adds no
hypotheses or axioms. The declaration check of `inducedConjuncts` reports
only `propext`, `Classical.choice` and `Quot.sound`. The file defines helper
objects for the proof (right-coset coordinates); they are described below and
are not used by any target statement.

## Imports

The file imports only the target module. Through it, the proof uses Worker
18's public module `Langlands.Representation.Finite.Induction`:

- `induceRep S V`, the actual induced `FDRep`, built from Mathlib's
  quotient induction `Representation.ind S.subtype V.ρ`;
- `induceRepEquiv S V`, the equivalence between that quotient induction and
  the action of `induceRep S V`;
- `indCoindEquiv S V`, Mathlib's equivalence `Rep.indCoindIso` between
  induction and coinduction for a finite-index subgroup;
- `coindEvaluation S V`, evaluation of a coinduced function at the chosen
  right-coset representatives.

Mathlib's coinduction `Representation.coind S.subtype V.ρ` acts on
`coindV S.subtype V.ρ`, the functions `f : G → V` with
`f (s * x) = ρ s (f x)` for `s ∈ S`. An element `g` sends `f` to
`x ↦ f (x * g)`.

## Rank one

`rankOneOrder` proves `FiniteRankOneOrderStatement G`. For a unit character
`χ : S →* ℂˣ` and `s ∈ S`, `χ s ^ Nat.card S = χ (s ^ Nat.card S) = χ 1 = 1`,
by `map_pow` and Mathlib's `pow_card_eq_one'`.

## Right-coset coordinates

The section `Coordinates` works over any field `k` and any group `G`.

- `RightCoset S` is the quotient of `G` by `QuotientGroup.rightRel S`, whose
  classes are the right cosets `S g`. `rightCoset S g` is the class of `g`.
  `rightCoset_eq_iff` says that `S a = S b` if and only if `b * a⁻¹ ∈ S`, and
  `rightCoset_mul` says that `S (s * g) = S g` for `s ∈ S`.
- For `g` in the coset `q`, `factor S g q hq` is the element `g * q.out⁻¹` of
  `S`, where `q.out` is the representative chosen by `Quotient.out`. By
  `factor_mul_out`, `factor S g q hq * q.out = g`.
- `extend S V F` turns a function `F` on right cosets into the coinduced
  vector `g ↦ ρ (g * (S g).out⁻¹) (F (S g))`. It satisfies the equivariance
  condition because `S (s * g) = S g` and the factor of `s * g` is `s` times
  the factor of `g`.
- `coordEquiv S V` is a linear equivalence from `coindV S.subtype V.ρ` to
  functions `RightCoset S → V`. Its forward map is the imported
  `coindEvaluation`, and its inverse is `extend`. Applying `extend` to the
  values of `f` at the representatives gives back `f`, by the equivariance of
  `f` and `factor_mul_out`. Evaluating `extend S V F` at `q.out` gives `F q`,
  because the factor of `q.out` is `1`.
- `natCard_rightCoset` says that the number of right cosets is `S.index`. It
  uses Mathlib's `QuotientGroup.quotientRightRelEquivQuotientLeftRel` and
  `Subgroup.index_eq_card`.

## Degree

`inducedDegree` proves `FiniteInducedDegreeStatement G`. Since `G` is finite,
so is `RightCoset S`, and a `Fintype` instance is chosen for it. The proof
chains the linear equivalences `induceRepEquiv`, `indCoindEquiv` and
`coordEquiv`. Hence `finrank ℂ (induceRep S V)` equals the rank of
`RightCoset S → V`. By `Module.finrank_pi_fintype` this is the number of right
cosets times `finrank ℂ V`. `natCard_rightCoset` replaces that number by
`S.index`.

## Trace of a block-monomial map

`trace_pi_monomial` works for a finite index type `ι`, a
finite-dimensional vector space `M` over a field `k`, a map `π : ι → ι` and endomorphisms `A i` of `M`. The
endomorphism `∑ i, single i ∘ A i ∘ proj (π i)` of `ι → M` has trace
`∑ i, if π i = i then trace (A i) else 0`. The proof uses linearity of the
trace and the cyclicity `LinearMap.trace_comp_comm'` to move `single i` to
the right. Then `proj (π i) ∘ single i` is the identity if `π i = i` and zero
otherwise (`LinearMap.proj_comp_single_same` and
`LinearMap.proj_comp_single_ne`).

## Character of coinduction

`coind_character` computes the character of
`Representation.coind S.subtype V.ρ` at `g` as

`∑ q, if q.out * g * q.out⁻¹ ∈ S then χ_V (q.out * g * q.out⁻¹) else 0`,

summed over all right cosets `q`. Let `T` be the action of `g` on coinduced
vectors. In the coordinates of `coordEquiv`, `T` becomes the map sending `F`
to `q ↦ ρ (factor (q.out * g)) (F (S (q.out * g)))`. This is the
block-monomial map with `π q = S (q.out * g)` and `A q = ρ (factor (q.out * g))`,
which is the identity `hT`. Conjugation by a linear equivalence preserves the
trace (`LinearMap.trace_conj'`), and `trace_pi_monomial` computes the result.
By `rightCoset_eq_iff`, the block `q` is fixed exactly when
`q.out * g * q.out⁻¹ ∈ S`. In that case the factor of `q.out * g` is
`q.out * g * q.out⁻¹`, so the block contributes the trace of `ρ` at that
element, which is `χ_V` there.

## Induced character formula

`inducedCharacterFormula` proves `FiniteInducedCharacterFormulaStatement G`.
Fix `S`, `V` and `g`, and put

`φ y = if y * g * y⁻¹ ∈ S then χ_V (y * g * y⁻¹) else 0`.

- `φ` is invariant under left multiplication by `S` (`hφ`). For `s ∈ S`,
  `y * g * y⁻¹ ∈ S` if and only if `(s * y) * g * (s * y)⁻¹ ∈ S`, and in that
  case the two values of `χ_V` agree because `χ_V` is a class function on `S`
  (`FDRep.char_conj`).
- The map `E : S × RightCoset S ≃ G`, `(s, q) ↦ s * q.out`, is a bijection,
  with inverse `y ↦ (factor y, S y)`. Summing over `G` through `E` and using
  the invariance gives `∑ y, φ y = |S| * ∑ q, φ q.out` (`hsum`).
- The target sums over `x` the value at `x⁻¹ * g * x`. Reindexing by
  `x ↦ x⁻¹` (`Fintype.sum_equiv (Equiv.inv G)`) turns this sum into
  `∑ y, φ y` (`hinv`).
- `Nat.card S` is nonzero in `ℂ`, because a subgroup is nonempty. So the
  right side of the target equals `∑ q, φ q.out`.
- On the left side, `Representation.char_iso` applied to `induceRepEquiv` and
  then `indCoindEquiv` replaces the character of `induceRep S V` by the
  character of coinduction. `coind_character` then gives the same sum
  `∑ q, φ q.out`.

The membership tests in `φ` and in `coind_character` are decided by the
classical instance, as in the target statement.

## Provenance

The mathematics is standard. The target statement's Markdown cites Jean-Pierre
Serre, *Linear Representations of Finite Groups*, GTM 42, Springer, 1977, §7.1
(Proposition 18, the coset basis giving the degree) and §7.2 (Proposition
20(ii), the induced character formula). It also cites Richard Brauer, *On
Artin's L-Series with General Group Characters*, Ann. of Math. 48 (1947),
formula (6) (literature IDs `serre-1977-linear-representations` and
`brauer-1947-artin-l-series`). Henniart uses these facts in the Brauer step
of *Une preuve simple des conjectures de Langlands pour GL(n) sur un corps
p-adique* (2000), §3.7. The Lean proof follows its own route. It does not use
the tensor-product description of induction. Instead it passes to Mathlib's
coinduction through the published equivalences and computes in right-coset
coordinates, as described above.


## Retained source correspondence

The cited originals were checked directly during adoption. The normalized sum
on Serre's printed p.55 uses `t⁻¹ s t`, with the character evaluated only when
that element belongs to the subgroup, and divides by the subgroup order.
Proposition 20(ii) on p.56 identifies this function with the trace of actual
induction. This agrees with the unchanged target for every finite-dimensional
complex representation, including dimension zero. Proposition 18 on p.54
uses a coset basis for the group algebra, giving the same degree as the
independent coordinate argument implemented here.

Brauer's formula (6) on printed p.505 is a sum over right-coset
representatives with conjugates `R g R⁻¹`; footnote 9 extends the character
by zero outside the subgroup. This is the coset sum computed by
`coind_character`. The proof's invariance and inversion reindexing explain its
conversion to the normalized all-element sum of the target. Henniart's §3.7,
printed p.451, uses integral induction from finite-order subgroup characters;
that application motivates this input but is not proved by this file.

The registered retained originals and exact content fingerprints are:

| Literature ID | SHA-256 | Locator |
| --- | --- | --- |
| `serre-1977-linear-representations` | `b6c0432dfc882618110c25a489c8fa0d93f1e64da4fba4950eb90c1b8348dcc2` | §7.1, Proposition 18, p.54; §7.2, pp.55–56, Proposition 20(ii) (PDF pages 62–64). |
| `brauer-1947-artin-l-series` | `7c9a789091fc6e09aeba312575b87fae1cab99ce53e842c4e378da980e21a1b5` | Formula (6) and footnote 9, p.505 (PDF page 5). |
| `henniart-2000-simple-proof` | `be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de` | §3.7, p.451 (PDF page 13). |

No source-specific errata note for these IDs was present in the checked
project and Library note locations. The proof uses the published construction
modules by Lean name, without modifying any target or imported statement pair.
