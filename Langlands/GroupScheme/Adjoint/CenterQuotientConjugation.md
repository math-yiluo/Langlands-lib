# Commutators with a point whose conjugates commute with it

Author: Worker 1499.

This internal helper module of the proof of
`Langlands.GroupScheme.CenterQuotientReductiveStatement` proves the geometric
step of the elementary route. It is derived content: the statements are chosen
for this proof and are not items of the cited literature. Everything is in the
namespace `Langlands.GroupScheme.CenterQuotient`.

Notation: `K` is a field, `G` a group scheme over `Spec K`, `ρ` a
`MatrixRepresentation G n`, and `ρ.rationalMatrix g` the invertible matrix of a
rational point `g : Over.mk (𝟙 (Spec K)) ⟶ G.X`. `M = ρ.pointMatrix G.X (𝟙 G.X)`
is the universal matrix, with entries in `Γ(G.X.left, ⊤)`, and
`CentralIntersection.evalPoint g` evaluates global functions at `g`.

## Results for an arbitrary field

- `evalPoint_mapMatrix_pointMatrix_inv`: evaluating the inverse universal matrix
  `M⁻¹` at a rational point `g` gives `ρ(g)⁻¹`. Evaluation is a ring
  homomorphism and `M` evaluates to `ρ(g)` (the Library lemma
  `evalPoint_mapMatrix_pointMatrix`), so the evaluation of `M⁻¹` is a right
  inverse of `ρ(g)`.
- `isIdempotentElem_units_conj`: in any ring, `u π u⁻¹` is idempotent for a unit
  `u` and an idempotent `π`.

## Results over an algebraically closed field

Assume now that `K` is algebraically closed and that `G.X.left` is reduced,
connected and locally of finite type over `K`.

- `mul_conj_eq_of_commute` (**connectedness of the nesting**): let `π` be an
  idempotent matrix that commutes with each conjugate `ρ(g) π ρ(g)⁻¹` over all
  rational points `g`. Then `π (ρ(g) π ρ(g)⁻¹) = π` for every rational point `g`.

  Proof. Let `p` be the constant matrix `π` over `Γ(G.X.left, ⊤)` and
  `F = det (p (M p M⁻¹) + (1 - p))`. At a rational point `g`, `F` evaluates to
  `det E_g`, where `E_g = π (ρ(g) π ρ(g)⁻¹) + (1 - π)` is idempotent (by
  `isIdempotentElem_mul_add_one_sub` of `CenterQuotientLinearAlgebra`, since
  the two idempotents commute). So `F² - F` vanishes at every rational point,
  and `F` is idempotent by the Library lemma
  `CentralIntersection.eq_zero_of_forall_evalPoint_eq_zero`, which uses that
  `G` is reduced and locally of finite type over an algebraically closed field.
  Since `G` is connected, `F` is `0` or `1`
  (`CentralIntersection.eq_zero_or_eq_one_of_isIdempotentElem`). At the identity
  `E_1 = π + (1 - π) = 1`, so `F = 1`. Hence `det E_g = 1` for every `g`. An
  idempotent matrix of determinant `1` is the identity, so `E_g = 1`, that is,
  `π (ρ(g) π ρ(g)⁻¹) = π`.

- `isNilpotent_rationalMatrix_commutator_sub_one` (**commutators are
  unipotent**): let `h` be a rational point such that `ρ(h)` commutes with
  `ρ(g h g⁻¹)` for every rational point `g`. Then `ρ(g h g⁻¹ h⁻¹) - 1` is
  nilpotent for every rational point `g`.

  Proof. Put `γ = ρ(h)` and `γ' = ρ(g h g⁻¹) = ρ(g) γ ρ(g)⁻¹`. The pair commutes
  by hypothesis. Apply the nested-block criterion
  `isNilpotent_sub_of_forall_blockPolynomial`. For a root `c` of the
  characteristic polynomial of `γ` and a different root `c'` of that of `γ'`,
  take the block polynomial `P` of `exists_blockPolynomial`. Then `P(c) = 1`,
  and `P(γ)` is idempotent. Conjugation does not change the characteristic
  polynomial, so `c'` is a root for `γ` different from `c`, and `P(c') = 0`.
  The needed identity `P(γ) P(γ') = P(γ)` follows from
  `mul_conj_eq_of_commute` applied to `π = P(γ)`, because
  `P(γ') = ρ(g) P(γ) ρ(g)⁻¹` (`aeval_units_conj`). Here `π` commutes with every
  conjugate `P(ρ(g') γ ρ(g')⁻¹) = P(ρ(g' h g'⁻¹))`, as polynomials in commuting
  matrices (`commute_aeval`). So `γ' - γ` is nilpotent, and
  `isNilpotent_mul_inv_sub_one` makes `γ' γ⁻¹ - 1 = ρ(g h g⁻¹ h⁻¹) - 1`
  nilpotent.

In the proof of the target, `h` runs over the rational points of the preimage
of a normal unipotent subgroup of the quotient. That preimage is shown to have
commuting rational points, which gives the hypothesis of the last lemma.
