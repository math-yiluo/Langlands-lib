# Reflex-field coefficients of the actual regular Hodge determinant: proof

Authors: Worker 217 wrote the Lean proof and this documentation and checked
them. Worker 277 also worked on the task. After this file's Galois conjugacy
lemma had been written, they independently proposed the same fix for it
(`open scoped CategoryTheory.MonObj`). No code from their drafts is used.

`Langlands.Shimura.CentralSimpleUnitaryData.kottwitzHodgeDeterminantReflexDescent`
proves the exact proposition `D.KottwitzHodgeDeterminantReflexDescent C` from
`Langlands.Shimura.PEL.HodgeDeterminantReflexStatement`. It keeps the whole
target telescope unchanged: the arithmetic types `E K A : Type`, the scalar
towers `IsScalarTower E K A`, `IsScalarTower ℚ E A` and `IsScalarTower ℚ K A`,
and the implicit `n` and `Φ`. The proof introduces the premise
`IsCMSection E K Φ` and does not use it. For every finite `ι : Type`, family
`a : ι → A` and exponent `d : ι →₀ ℕ`, the theorem proves that
`(D.kottwitzHodgeDeterminant C a).coeff d` lies in
`D.kottwitzCocharacterReflexField C`.

## Notation and route

Write `h₀ = (D.realPositiveKottwitzHom C).val`, the fixed conjugated Kottwitz
homomorphism. Its identity Hodge summand is
`V₁ = D.kottwitzHodgeModule C = RegularHodge.submodule h₀.hom` inside
`ℂ ⊗[ℝ] (ℝ ⊗[ℚ] A)`. An element `x` lies in `V₁` when right multiplication by
the complexified homomorphism at `z` sends `x` to `z • x`, for every `z`. The
polynomial `D.kottwitzHodgeDeterminant C a` is
`HodgeDeterminant.polynomial` of the left actions of
`1 ⊗ₜ (1 ⊗ₜ a i)` on `V₁`, computed in `Module.finBasis ℂ V₁`. Let
`Θ = AlgebraInvolution.baseChangeTowerEquiv ℚ ℝ ℂ A`. This is the published
`ℂ`-algebra isomorphism `ℂ ⊗[ℚ] A ≃ ℂ ⊗[ℝ] (ℝ ⊗[ℚ] A)`. For a rational
automorphism `s` of `ℂ`, `s̃ = ComplexMatrix.coefficientEquiv s` is the
published coefficient change `z ⊗ₜ a ↦ s z ⊗ₜ a` on `ℂ ⊗[ℚ] A`. It is
`s`-semilinear (`coefficientEquiv_smul`). The automorphism `s` need not fix
`ℝ`, so the proof applies it only to the rational tensor algebra `ℂ ⊗[ℚ] A`,
never to a real tensor factor.

The proof follows the route suggested in the task contract. It has three
steps.

1. The proof identifies `V₁` with the inverse-weight space of right
   multiplication by the actual cocharacter values. Both inclusions are
   proved.
2. Let `s` stabilize the actual cocharacter class. The proof builds the map
   `Ψ x = Θ(s̃(Θ⁻¹ x) · γ⁻¹)` with an explicit conjugating unit `γ`. It shows
   that `Ψ` maps all of `V₁` into `V₁`, is injective and `s`-semilinear, and
   commutes with left multiplication by every rational algebra element.
3. A general lemma turns such a map into invariance of the determinant
   polynomial under `s`. `mem_complexCocharacterFixedField` then gives the
   field membership.

No matrix-column ranks are used. The comparison concerns the whole regular
Hodge summand `V₁` and the left action of arbitrary elements of `A`.

## General determinant lemmas (`Langlands.Shimura.HodgeDeterminant`)

**`map_polynomial`.** Let `g : F →+* F` be a ring map. Let `b` and `b'` be
bases of `M` and `f : ι → Module.End F M`. Suppose every matrix entry of
`f i` in `b'` is `g` of the corresponding entry in `b`. Then
`MvPolynomial.map g (polynomial b f) = polynomial b' f`. The proof uses
`RingHom.map_det` and maps the linear entries `∑ i, C (m i j k) * X i` entry by
entry.

**`map_polynomial_eq_of_semilinear`.** Let `F` be an infinite field and
`g : F ≃+* F` a ring automorphism. Let `Ψ : M →+ M` be additive and
injective, with `Ψ (c • m) = g c • Ψ m`. Let `b` be a finite basis and suppose
`f i (Ψ m) = Ψ (f i m)` for all `i` and `m`. Then
`MvPolynomial.map g (polynomial b f) = polynomial b f`.

The family `Ψ ∘ b` is linearly independent. This is
`LinearIndependent.map_of_surjective_injective`, which applies because `g` is
surjective and `Ψ` is injective and semilinear. It has the cardinality of
`b`, so `basisOfLinearIndependentOfCardEqFinrank'` makes it a basis `b'`. No
inverse of `Ψ` is constructed: bijectivity is not needed separately, because
this counting argument already makes `Ψ ∘ b` a basis. Expanding
`f i (b k) = ∑ j c j k • b j` gives

    f i (Ψ (b k)) = Ψ (f i (b k)) = ∑ j, g (c j k) • Ψ (b j).

So the matrices of `f i` in `b'` are `g` applied to those in `b`.
`map_polynomial` gives `map g (polynomial b f) = polynomial b' f`. The
published `polynomial_basis_independent` gives
`polynomial b' f = polynomial b f`.

## The Hodge summand as an inverse-weight space (`Langlands.Shimura.RegularHodge`)

Let `h` be a `ComplexHom` of a real algebra `B` with involution. For a Deligne
point `w` over `ℂ`, let `re` and `im` be its complex coordinates.

**`split_coordinates_of_eq`.** If `DeligneTorus.splitPointsEquiv ℂ w` is
`(u⁻¹, 1)`, then `re + im·i = u⁻¹` and `re - im·i = 1`. This follows from
`splitPointsEquiv_fst` and `splitPointsEquiv_snd`.

**`mul_delignePoints`.** In `ℂ ⊗[ℝ] B`, right multiplication by the first
coordinate of the Deligne value `h.delignePoints ℂ w` is

    y * (h.delignePoints ℂ w).val.1 = re • y + im • action h.hom i y.

The proof uses `deligneAlgebraMap_apply`.

**`mem_submodule_iff_delignePoints`.** For `x ∈ ℂ ⊗[ℝ] B`, the statement is
the following equivalence:

    x ∈ submodule h.hom  ↔  ∀ u : ℂˣ, x * ((h.delignePoints ℂ (split⁻¹ (u, 1)))⁻¹).val.1 = u⁻¹ • x.

The Deligne point `(split⁻¹ (u, 1))⁻¹` has split coordinates `(u⁻¹, 1)`.

- (→) Membership gives `action h.hom i x = i • x` by `mem_submodule_iff_I`.
  Then the right side of `mul_delignePoints` is `(re + im·i) • x = u⁻¹ • x`.
- (←) Take `u = 2`. Then `im ≠ 0`. Otherwise `re = 1/2` and `re = 1`, which
  is a contradiction. The hypothesis says
  `re • x + im • action i x = (re + im·i) • x`, and cancelling `re • x` and
  then the nonzero `im` gives `action i x = i • x`. This is membership by
  `mem_submodule_iff_I`.

## The semilinear transport (`Langlands.Shimura.ComplexMatrix`)

**`galoisTransport s γ`.** This is the additive map
`x ↦ Θ(s̃(Θ⁻¹ x) · γ⁻¹)` on `ℂ ⊗[ℝ] (ℝ ⊗[ℚ] A)`, for `s : ℂ ≃ₐ[ℚ] ℂ` and a unit
`γ` of `ℂ ⊗[ℚ] A`. Its definitional formula is `galoisTransport_apply`. The
following lemmas hold for every `x`, with no restriction to `V₁`:

- `galoisTransport_smul`: `Ψ (c • x) = s c • Ψ x`. Here `Θ` and `Θ⁻¹` are
  `ℂ`-linear and `s̃` is `s`-semilinear.
- `galoisTransport_eq_zero`: `Ψ x = 0` implies `x = 0`. Both `Θ` and `s̃` are
  injective and `γ⁻¹` is a unit.
- `galoisTransport_mul_left`: for every `a : A`,
  `Ψ ((1 ⊗ₜ (1 ⊗ₜ a)) * x) = (1 ⊗ₜ (1 ⊗ₜ a)) * Ψ x`. We have
  `Θ⁻¹ (1 ⊗ₜ (1 ⊗ₜ a)) = 1 ⊗ₜ a` and `s̃ (1 ⊗ₜ a) = 1 ⊗ₜ a`, and `Θ`, `Θ⁻¹`
  and `s̃` are multiplicative. The unit `γ⁻¹` multiplies on the right, so it
  does not interfere with left multiplication.

## The Kottwitz cocharacter (`Langlands.Shimura.CentralSimpleUnitaryData`)

**`kottwitzCocharacterUnit C u`.** This is the unit `N(u)` of `ℂ ⊗[ℚ] A` that
is the first coordinate of
`D.rationalAffinePointsEquiv (CommAlgCat.of ℚ ℂ)` applied to
`D.complexCocharacterValue (D.kottwitzCocharacter C true) u`. In words, it is
the actual first-factor Kottwitz scheme cocharacter evaluated at `u` and read
in the rational algebra model.

**`baseChangeTower_kottwitzCocharacterUnit`.** This identifies `Θ (N(u))`
with `((h₀.delignePoints ℂ (split⁻¹ (u, 1)))⁻¹).val.1`, Kottwitz's inverse
Deligne value of the conjugated homomorphism at the first-factor point. The
proof applies the injective `C.iteratedScalarMatrixEquiv D.totallyRealBasis ℂ`
and compares the matrix at each real embedding `τ`. The right side is
`C.conj_inverse_delignePoints_firstFactor`, because
`h₀ = (C.realComplexHom D.totallyRealBasis).conj` by definition. The left
side is rewritten by `complexAffineCocharacterValue_rational`,
`complexAffinePointMatrices_rational` and
`kottwitzCocharacter_affine_matrices`. After these rewrites both sides agree
by definition.

**`kottwitzCocharacterUnit_galois`.** Suppose
`D.ComplexCocharacterConjugate (D.galoisCocharacter s μ) μ` with
`μ = D.kottwitzCocharacter C true`. Then one unit `γ` satisfies

    N(u) = γ · s̃(N(s⁻¹ u)) · γ⁻¹    for every u : ℂˣ,

where `s⁻¹ u` is `Units.map s.symm.toMonoidHom u`. The conjugacy hypothesis
gives a point `g` with `galoisCocharacter s μ ≫ (innerIso g).hom = μ`. Take
`γ` to be the first coordinate of `rationalAffinePointsEquiv` applied to
`complexRationalPointsEquiv g`. The published `complexCocharacterValue_inner`
writes the value of `μ` as conjugation by that point of the value of
`galoisCocharacter s μ`. `rationalAffinePointsEquiv` is a group
isomorphism, which gives `map_mul` and `map_inv`. Using these requires
`open scoped CategoryTheory.MonObj`. The published
`complexCocharacterValue_galois_coordinates` then rewrites the Galois-twisted
value as `coefficientAut s` applied to the value at `s⁻¹ u`. Its first
coordinate is `s̃` of that value by definition.

**`mem_kottwitzHodgeModule_iff`.** This applies
`mem_submodule_iff_delignePoints` to `h₀` and moves both sides through the
algebra isomorphism `Θ`, using `baseChangeTower_kottwitzCocharacterUnit`. The
result is

    x ∈ V₁  ↔  ∀ u : ℂˣ, Θ⁻¹ x · N(u) = u⁻¹ • Θ⁻¹ x.

**`galoisTransport_mem`.** Suppose `γ` satisfies the conjugation identity of
`kottwitzCocharacterUnit_galois`. Then `x ∈ V₁` implies
`galoisTransport s γ x ∈ V₁`. Write `y = Θ⁻¹ x`. Then `Θ⁻¹ (Ψ x) = s̃(y) γ⁻¹`,
and

    s̃(y) γ⁻¹ · N(u) = s̃(y) γ⁻¹ γ s̃(N(s⁻¹ u)) γ⁻¹ = s̃(y · N(s⁻¹ u)) γ⁻¹
                    = s̃((s⁻¹ u)⁻¹ • y) γ⁻¹ = u⁻¹ • s̃(y) γ⁻¹.

The third equality is the membership of `x` at the point `s⁻¹ u`. The last
uses the semilinearity of `s̃` and `s (s⁻¹ (u⁻¹)) = u⁻¹`.

**`kottwitzHodgeDeterminant_map_galois`.** For every finite family
`a : J → A` and every `s` stabilizing the actual class,
`MvPolynomial.map s (D.kottwitzHodgeDeterminant C a) = D.kottwitzHodgeDeterminant C a`.
The proof takes `γ` from `kottwitzCocharacterUnit_galois` and restricts
`galoisTransport s γ` to an additive endomorphism `Ψ` of `V₁`, using
`galoisTransport_mem`. It then applies `map_polynomial_eq_of_semilinear` with
`g = s`, the basis `Module.finBasis ℂ V₁` and the left actions of
`1 ⊗ₜ (1 ⊗ₜ a i)`. These are exactly the data defining
`kottwitzHodgeDeterminant`. Injectivity, semilinearity and commutation with
the family come from `galoisTransport_eq_zero`, `galoisTransport_smul` and
`galoisTransport_mul_left`.

## The final theorem

The proof unfolds `kottwitzCocharacterReflexField` to
`D.complexCocharacterFixedField (D.kottwitzCocharacter C true)`. Then
`mem_complexCocharacterFixedField` reduces membership to `s c = c` for every
`s` in the actual stabilizer. Taking the coefficient at `d` in
`kottwitzHodgeDeterminant_map_galois` and applying `MvPolynomial.coeff_map`
gives `s (coeff d P) = coeff d P`.

## Provenance and scope

Kottwitz (1992), section 5, printed p.389 (PDF p.17), registered as
`kottwitz-1992-points-shimura-finite-fields`, states that the coefficients of
`det(X₁a₁ + … + Xₜaₜ; V₁)` lie in the reflex field because the isomorphism
class of `V₁` is defined over it. He gives no further argument. This proof
makes that step explicit for the target's actual objects. For each
automorphism stabilizing the actual cocharacter class it constructs an
`s`-semilinear injective map of the whole regular Hodge summand that commutes
with the algebra action, and it derives invariance of the determinant
polynomial from this map. The construction is internal to this project and
follows the route proposed in the task contract.

The file imports the target statement module and
`Langlands.Shimura.Unitary.GaloisCocharacterEvaluation`. It changes no
imported module. It adds the helper theorems above and two helper
definitions, `galoisTransport` and `kottwitzCocharacterUnit`. It uses only the axioms `propext`, `Classical.choice` and `Quot.sound`. It stops
at coefficient membership. It does not construct a polynomial over the reflex
field, does not prove integrality for order inputs, and does not treat the
Lie-section condition or PEL moduli.
