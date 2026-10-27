# Actual affine equivalences and additive Haar change of variables

Module `Langlands.Analysis.AffineChangeOfVariables`, namespace
`Langlands.AffineChangeOfVariables`, universe `u`.
Authors: Worker 452 (original draft) and Worker 378.

This unit constructs the actual affine map

`S(A,v)(x) = A.val.mulVec x + v`

on the column-vector space `Fin n → R`. It packages this map as an
equivalence, a homeomorphism and a measurable equivalence, and proves its
additive Haar pushforward laws. Vectors are columns: `A.val.mulVec x` is
the matrix-vector product `(A x)_i = ∑_j A_ij x_j` of Mathlib's
`Matrix.mulVec`. There is no transpose and no row-vector convention.
The matrix `A` is an element of the Library's
`Langlands.GeneralLinear n R`, the unit group of the matrix ring
`Matrix (Fin n) (Fin n) R`. `A.val` is the underlying matrix and `A⁻¹` is the
group inverse.

No hypothesis excludes rank `n = 0` or the zero ring, unless a section says so.

## Algebraic equivalence

Hypotheses: `R : Type u` is any commutative ring and `n : ℕ` is any rank.

- `equiv A v : (Fin n → R) ≃ (Fin n → R)` has forward map
  `x ↦ A.val.mulVec x + v` and inverse map `x ↦ (A⁻¹).val.mulVec (x - v)`.
  The two inverse laws are proved by cancelling `v`, then rewriting
  `B.mulVec (C.mulVec x) = (B*C).mulVec x` (`Matrix.mulVec_mulVec`).
  The products `A⁻¹ * A` and `A * A⁻¹` of units equal `1`, and
  `1.mulVec x = x`.
- `equiv_apply` and `equiv_symm_apply` (both `rfl`) give the forward and
  inverse formulas.
- `equiv_symm` is the inverse formula as an affine map:
  `(equiv A v).symm = equiv A⁻¹ (-((A⁻¹).val.mulVec v))`. Its proof expands
  `(A⁻¹).val.mulVec (x - v)` by `Matrix.mulVec_sub`.
- `equiv_one_zero` is the identity formula:
  `equiv 1 0 = Equiv.refl (Fin n → R)`. It is proved by `simp`.
- `equiv_trans` is the composition formula in Mathlib's `trans` order. The
  term `(equiv B w).trans (equiv A v)` applies `S(B,w)` first and `S(A,v)`
  second. The theorem states
  `(equiv B w).trans (equiv A v) = equiv (A * B) (v + A.val.mulVec w)`.
  Its proof expands `A.val.mulVec (B.val.mulVec x + w) + v` with
  `Matrix.mulVec_add` and `Matrix.mulVec_mulVec`. The result is rearranged
  by commutativity of addition.
- `equiv_comp` states the same law with function composition:
  `⇑(equiv A v) ∘ ⇑(equiv B w) = ⇑(equiv (A * B) (v + A.val.mulVec w))`,
  that is, `S(A,v) ∘ S(B,w) = S(AB, v + A.val.mulVec w)`. The later map `A`
  is the left matrix factor. Its proof applies the coercion to
  `equiv_trans`.

## Homeomorphism

Hypotheses: `R : Type u` is a commutative ring with a topology for which it is a
topological ring (`IsTopologicalRing R`). The space `Fin n → R` has the
inherited finite product topology (Mathlib's `Pi.topologicalSpace` instance).

- `homeomorph A v : (Fin n → R) ≃ₜ (Fin n → R)` has underlying equivalence
  `equiv A v`. The forward map is continuous because finite matrix-vector
  multiplication by a constant matrix is continuous
  (`Continuous.matrix_mulVec`), and so is addition of a constant. The inverse
  map is continuous for the same reason, with subtraction of a constant.
- `homeomorph_apply` and `homeomorph_symm_apply` (both `rfl`) give the forward
  and inverse formulas. `homeomorph_toEquiv` (`rfl`) states
  `(homeomorph A v).toEquiv = equiv A v`.
- `homeomorph_symm`, `homeomorph_one_zero` and `homeomorph_trans` are the
  inverse, identity and composition formulas of the algebraic section. The
  composition formula has the same order as `equiv_trans`. Each is proved
  pointwise (`Homeomorph.ext`) from the algebraic formula.

## Measurable equivalence

Hypotheses: those of the homeomorphism section, plus an arbitrary measurable
structure `[MeasurableSpace (Fin n → R)]` that is Borel for the product
topology (`[BorelSpace (Fin n → R)]`). This structure is a supplied instance.
The construction does not replace it by the product σ-algebra
`MeasurableSpace.pi`.

- `measurableEquiv A v : (Fin n → R) ≃ᵐ (Fin n → R)` is
  `(homeomorph A v).toMeasurableEquiv`. This is Mathlib's construction: a
  homeomorphism between Borel spaces is a measurable equivalence.
- `measurableEquiv_apply` and `measurableEquiv_symm_apply` (both `rfl`) give
  `measurableEquiv A v x = A.val.mulVec x + v` and
  `(measurableEquiv A v).symm x = (A⁻¹).val.mulVec (x - v)`.
  `measurableEquiv_toEquiv` (`rfl`) states
  `(measurableEquiv A v).toEquiv = equiv A v`.
- `measurableEquiv_symm` is the inverse formula:
  `(measurableEquiv A v).symm = measurableEquiv A⁻¹ (-((A⁻¹).val.mulVec v))`.
- `measurableEquiv_one_zero` is the identity formula:
  `measurableEquiv 1 0 = MeasurableEquiv.refl (Fin n → R)`.
- `measurableEquiv_trans` is the composition formula
  `(measurableEquiv B w).trans (measurableEquiv A v) =
  measurableEquiv (A * B) (v + A.val.mulVec w)`.
  `measurableEquiv_comp` is the same formula with function composition:
  `S(A,v) ∘ S(B,w) = S(AB, v + A.val.mulVec w)`.

The inverse, identity and composition formulas are proved by function
extensionality (`MeasurableEquiv.ext`) from the algebraic formulas. These are
equivalences of the vector space itself. They are not a group isomorphism
with a direct or semidirect product, and they are not an abstract action
certificate.

## Additive Haar change of variables over a field

Hypotheses: `K : Type u` is a field with a topology for which it is a
topological ring. It is locally compact and second countable, and it carries a
Borel measurable structure (`[MeasurableSpace K] [BorelSpace K]`). The vectors
`Fin n → K` carry an arbitrary Borel measurable structure for the product
topology, as above. The data are:

- an additive Haar measure `ν` on `K` (`IsAddHaarMeasure ν`);
- a map `χ : K →*₀ ℝ≥0` of monoids with zero;
- the explicitly supplied scalar law
  `hχ : ∀ a ≠ 0, ν.map (fun x => a * x) = (χ a)⁻¹ • ν`;
- an additive Haar measure `μ` on `Fin n → K` (`IsAddHaarMeasure μ`), for
  the supplied measurable structure;
- `A : GeneralLinear n K` and `v : Fin n → K`.

`map_haar` proves

`μ.map (measurableEquiv A v) = (χ A.val.det)⁻¹ • μ`

and `map_haar_symm` proves

`μ.map (measurableEquiv A v).symm = χ A.val.det • μ`.

Normalization: the theorems hold for every additive Haar measure `μ` on the
vectors and choose none. The factor depends only on `χ` and `det A`, not on
the normalization of `μ` or `ν`.

Implemented proof of `map_haar`. The linear part is the published
`Langlands.HarmonicAnalysis.haarMeasure_map_in_coordinates`, applied with
coordinates `ContinuousAddEquiv.refl (Fin n → K)` and the hypothesis
`det A.val ≠ 0`. That hypothesis holds because the determinant of `A` is a
unit (`(GeneralLinear.determinant A).ne_zero`). The application gives
`μ.map A.val.mulVec = (χ A.val.det)⁻¹ • μ`. Using the identity coordinates
keeps the supplied Borel measurable structure on the vector space. The
affine map is the composition of `A.val.mulVec` with the translation
`x ↦ x + v`, both continuous and hence measurable. The proof composes the
pushforwards (`Measure.map_map`). It commutes pushforward with the scalar
(`Measure.map_smul`), and it removes the translation by additive invariance
(`map_add_right_eq_self`). An additive Haar measure is right invariant under
addition.

Implemented proof of `map_haar_symm`. Rewrite the inverse as
`measurableEquiv A⁻¹ (-((A⁻¹).val.mulVec v))` (`measurableEquiv_symm`) and
apply `map_haar` to it. The factor becomes `(χ (A⁻¹).val.det)⁻¹`. The
determinant homomorphism gives `(A⁻¹).val.det = (A.val.det)⁻¹`, through
`map_inv` and `Units.val_inv_eq_inv_val`. Then `map_inv₀` for `χ` and
`inv_inv` give the factor `χ A.val.det`.

The measure laws come from determinant Haar scaling and translation
invariance. A coordinate homeomorphism alone supplies no measure law.

## The p-adic specialization

Hypotheses: `p` is a prime (`[Fact p.Prime]`), `F : PadicField.{u} p`, and
`T : F.TopologicalData` is the supplied local-field realization. The statements
install exactly `T.topology`, `T.valuativeRel` and `T.localField` as local
instances. They then quantify over every Borel measurable structure on
`Fin n → F.Carrier` for the product of `T.topology`, every additive Haar measure
`μ` on it, every `A : GeneralLinear n F.Carrier` and every
`v : Fin n → F.Carrier`. The rank `n` is arbitrary, including `0`.

- `padic_map_haar F T n` proves
  `μ.map (measurableEquiv A v) = ((T.determinantNorm n A : ℝ≥0)⁻¹) • μ`.
- `padic_map_haar_symm F T n` proves
  `μ.map (measurableEquiv A v).symm = (T.determinantNorm n A : ℝ≥0) • μ`.

Here `T.determinantNorm n A` is the Library's existing residue-normalized
character `|det A|_F`. It is `T.normalizedAbsUnits` applied to the unit
determinant of `A`, and it equals `q^(-ord(det A))`, where `q` is the
residue-field cardinality. These theorems add no scalar-scaling assumption.

Implemented proof of `padic_map_haar`. Inside the proof only, the scalar field
gets the Borel measurable structure `borel F.Carrier`. Second countability comes
from the published `T.secondCountableTopology`
(`Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof`). The Hausdorff
property comes from `T.fieldT2` (`Langlands.LocalField.Topology`). Local
compactness and the topological-ring structure are inferred from
`T.localField` and `T.valuativeRel`. The published
`Langlands.HarmonicAnalysis.padicScalarHaarScaling F T` is applied to Mathlib's
additive Haar measure `addHaar` on `F.Carrier` and the unit `Units.mk0 a ha`.
It gives the scalar law
`addHaar.map (fun x => a * x) = (T.normalizedAbsHom a)⁻¹ • addHaar` for every
nonzero `a`. Then `map_haar` with `ν = addHaar` and `χ = T.normalizedAbsHom`
gives the claim. The factor `T.normalizedAbsHom A.val.det` is definitionally
`(T.determinantNorm n A : ℝ≥0)`. The auxiliary scalar measure `addHaar` does
not occur in the statement.

Implemented proof of `padic_map_haar_symm`. Rewrite the inverse with
`measurableEquiv_symm` and apply `padic_map_haar` to `A⁻¹`. The factor
`(T.determinantNorm n A⁻¹)⁻¹` simplifies to `T.determinantNorm n A`, using
`map_inv` for the monoid homomorphism `T.determinantNorm n`,
`Units.val_inv_eq_inv_val` and `inv_inv`.

## Provenance and scope

This is an internal construction. It is derived from:

- `Langlands.GeneralLinear` and `Langlands.GeneralLinear.determinant` in
  `Langlands.Group.GL.Basic`;
- `Langlands.HarmonicAnalysis.haarMeasure_map_in_coordinates` (the published
  determinant Haar-scaling theorem) in
  `Langlands.HarmonicAnalysis.PadicRectangularHaarScalingProof`;
- `Langlands.HarmonicAnalysis.padicScalarHaarScaling` and
  `Langlands.PadicField.TopologicalData.secondCountableTopology` in
  `Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof`, and
  `Langlands.PadicField.TopologicalData.fieldT2` in
  `Langlands.LocalField.Topology` (all reached through the import of
  `Langlands.HarmonicAnalysis.PadicRectangularHaarScalingProof`);
- `Langlands.PadicField.TopologicalData.normalizedAbsHom` and `determinantNorm`
  in `Langlands.Group.GL.NormalizedCharacter`;
- Mathlib's `Matrix.mulVec` algebra, `Continuous.matrix_mulVec`,
  `Homeomorph.toMeasurableEquiv`, `Measure.map_map`, `Measure.map_smul` and
  `map_add_right_eq_self`.

No external literature transcription is claimed. The forward factor
`|det A|⁻¹` is the usual change-of-variables rule
`μ(S(A,v)⁻¹(E)) = |det A|⁻¹ μ(E)`.

This pair constructs no operator on an L2 space. It proves no continuity of a
group representation, no quotient-measure formula for parabolic subgroups, no
transport of null classes, no Fourier identity, no coefficient completion, no
general semidirect induction and no irreducibility result. Mirabolic matrix
coordinates, normalized L2 pullbacks, coefficient completions and general
semidirect induction remain separate units, and none of them is imported.
