# Semilinearity of the relative reduced norm under the involution

Module: `Langlands.Algebra.CentralSimple.LandherrNormSemilinear`.

Let `E/F` be a separable quadratic extension with `CharZero F`, `B` a finite-dimensional
central simple `E`-algebra (an `F`-algebra through `E`), `τ : FirstKindInvolution F B`
acting on `E` by the conjugation, and `relNorm F E B R : R ⊗_F B → E ⊗_F R` the relative
reduced norm (module `Langlands.Algebra.CentralSimple.LandherrNonsplitLocal`).

- `tensorConj F E R = conjugation F E ⊗ id` on `E ⊗_F R`; `tensorConj_tmul` and
  `tensorConj_naturality` (it commutes with `id ⊗ φ` for `F`-algebra maps `φ : R → S`).
- `exists_eq_one_tmul_add_skewRoot_tmul'`: every element of `E ⊗_F R` is
  `1 ⊗ r₁ + r ⊗ r₂`.
- `relNorm_naturality`: `relNorm S ((φ ⊗ id) z) = (id ⊗ φ) (relNorm R z)` for every
  `F`-algebra map `φ : R → S` of commutative `F`-algebras, by naturality of
  `UnitaryPoints.tensorEquiv` and of the reduced norm.
- `relNorm_baseChange_of_nonsplit`: if some field `K` over `F` in which `d` is not a square
  has the unitary splitting property, then for every commutative `F`-algebra `R` and every
  `z ∈ R ⊗_F B`, `relNorm R (τ_R z) = tensorConj (relNorm R z)`.

## Proof of `relNorm_baseChange_of_nonsplit`

Choose an `F`-basis `β` of `B` and let `P = F[X_i]` be the polynomial ring in
`dim_F B` variables, with generic element `g = Σ X_i ⊗ β_i ∈ P ⊗_F B`; every `w ∈ S ⊗_F B`
is the image of `g` under `φ ⊗ id` for the evaluation `φ : P → S` at the coordinates of `w`.
Let `D = relNorm P (τ_P g) - tensorConj (relNorm P g) = 1 ⊗ D₁ + r ⊗ D₂`. By naturality its
image under every `φ : P → S` is the corresponding difference for `(φ ⊗ id) g`. For
`S = K` this difference vanishes by `relNorm_baseChange_nonsplit`, and applying the
isomorphism `E ⊗_F K ≅ K(√d)` shows `φ(D₁) = φ(D₂) = 0` for all `φ : P → K`. Since `F` is
infinite and embeds in `K`, a polynomial vanishing at all points of `K` (in particular of
`F`) is zero (`MvPolynomial.funext`), so `D = 0`, and specializing to `R` gives the claim.

## Provenance

The identity `Nrd(τ x) = σ(Nrd x)` for an involution of the second kind is classical; here
it is deduced from its validity over one nonsplit field by a generic-element (polynomial identity)
argument. It is used in the proof of Landherr's theorem to see that the relative reduced norm
of a symmetric element is fixed by the conjugation.
