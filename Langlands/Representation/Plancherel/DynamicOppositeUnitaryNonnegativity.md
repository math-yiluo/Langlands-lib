# Nonnegativity of `j_P` at unitary points (target and reduction)

Worker 5. `Langlands.Plancherel.ConditionalDynamicOppositeUnitaryNonnegStatement`
is a Prop-valued target. It says that the Library's canonical scalar `j_P`
of `J_{P|P̄} J_{P̄|P}` is regular with a nonnegative real value at every
unitary unramified character where both chosen continuations are regular.
The module proves the target from the Hermitian adjunction target
`ConditionalDynamicOppositeHermitianAdjunctionStatement` (module
`DynamicOppositeHermitianAdjunctionStatement`):
`conditionalDynamicOppositeUnitaryNonneg_of_hermitianAdjunction`.
It does not prove the Hermitian adjunction. The supporting results on
regular functions, on the compact-picture pairing and on adjoint pairs of
continued operators are proved in full.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI
10.1017/S1474748003000082, registered as `waldspurger-2003-plancherel`, PDF
SHA256 `4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.

- Proof of IV.3 (6), printed p.287 / PDF p.53. `V` carries a positive
  definite Hermitian product, and the compact pictures carry
  `(f, f') = ∫_K (f(k), f'(k)) dk`. For unitary `χ ∈ Im X(M)` the proof uses
  the adjunction `(J_{P̄|P}(π ⊗ χ) f, f') = (f, J_{P|P̄}(π ⊗ χ) f')` and
  deduces
  `j(π ⊗ χ)(e, e) = (e, J_{P|P̄} J_{P̄|P} e) = (J_{P̄|P} e, J_{P̄|P} e)`.
- IV.3, printed p.285 / PDF p.51: `j_P` is the rational function with
  `J_{P|P̄}(π') J_{P̄|P}(π') = j_P(π')` where the induction is irreducible.

## Provenance

The target is derived. Waldspurger does not state nonnegativity of `j` as a
numbered claim. It is the first step of his proof of IV.3 (6): the displayed
identity makes `j(π ⊗ χ)` a ratio of two squared norms at unitary `χ`. The
target records this step for the Library's `conditionalCanonicalRationalScalar`.
The argument of the reduction follows Waldspurger's, with one addition. His
adjunction holds between the continued operators at unitary points. The
Library's adjunction target holds only on the convergence domains, so the
module proves that adjointness passes to the rational continuations
(`continuedOperator_adjoint`).

## The dagger of a regular function

For a function `f` on the unramified characters, `unramifiedDaggerFun ν f`
is `z ↦ conj (f (z†))`, where `z† = unramifiedConjInv ν z = z̄⁻¹` is defined
in `DynamicOppositeHermitianAdjunctionStatement`.

- `unramifiedDaggerFun_evaluation`: the dagger of the evaluation at `g` is
  the evaluation at `g⁻¹`, because `conj (conj (z g)⁻¹) = (z g)⁻¹`.
- `unramifiedDaggerFun_mem`: the dagger preserves
  `unramifiedRegularFunctions ν`. The proof is induction on
  `Algebra.adjoin`. The dagger is additive and multiplicative, conjugates
  constants, and sends generators to generators.
- `unramifiedDagger` is the resulting map on regular functions, with
  `unramifiedDagger_apply`.
- `unramifiedRegularEval z` is evaluation at `z` as a `ℂ`-algebra
  homomorphism on regular functions, with `unramifiedRegularEval_apply`.

## The compact-picture pairing

`compactPictureHermitianPairing h K hK A b` is defined in
`DynamicOppositeHermitianAdjunctionStatement` as
`(φ, ψ) = ∫_K b(φ(k), ψ(k)) dk` against the Haar probability measure
`CompactInduction.measure K hK`. Here `b` is an `M`-invariant positive
definite Hermitian form on `A`, conjugate-linear in its first argument.

- `compactPictureHermitianPairing_integrable`: the integrand is locally
  constant on the compact group `K`, hence integrable.
- `compactPictureInnerCore` is an `InnerProductSpace.Core` structure with
  this pairing. Conjugate symmetry, nonnegativity of the real part,
  additivity and homogeneity in the first argument come from `b` and
  linearity of the integral. For definiteness, if `(φ, φ) = 0` then the
  continuous nonnegative function `k ↦ b(φ(k), φ(k))` vanishes almost
  everywhere. Haar measure on `K` charges every nonempty open set, so the
  function vanishes everywhere, and `φ = 0`.
- `compactPictureHermitianPairing_add_right` and
  `compactPictureHermitianPairing_smul_right`: linearity in the second
  argument, by conjugate symmetry.
- `compactPictureSesq` packages the pairing as a sesquilinear form
  `→ₗ⋆[ℂ] →ₗ[ℂ] ℂ`, with `compactPictureSesq_apply`.
- `compactPictureHermitianPairing_self`: `(φ, φ)` is a nonnegative real
  number.
- `compactPictureHermitianPairing_self_ne_zero`: `(φ, φ) ≠ 0` for `φ ≠ 0`.

## Adjoint pairs of continued operators

This part is generic. `L` is a connected reductive group scheme over a
nonarchimedean local field with the hypotheses of the Library's rational
continuation (`hp`, `hL`). `V` and `W` are complex vector spaces.
`p : RationalOperatorContinuationData Ω A` and
`q : RationalOperatorContinuationData Λ B` continue operator families
`A : Ω → (V →ₗ W)` and `B : Λ → (W →ₗ V)`. Recall that `p` consists of a
denominator `d_p` and a polynomial numerator `N_p` with `N_p = d_p • A` on
`Ω`. Its regular region is `{d_p ≠ 0}`, and there the continued operator is
`d_p⁻¹ • N_p`.

- `conjLeftFunctional s w'` is the linear functional `u ↦ conj (s u w')`.
- `continuedOperator_congr`: the continued operator depends only on the
  underlying parameter, not on the membership proof.
- `continuedOperator_adjoint`. Let `sV`, `sW` be sesquilinear forms. Let `D`
  be a nonempty open set with `D ⊆ Ω` and `D† ⊆ Λ`, and assume
  `sW (A w v) w' = sV v (B w† w')` for `w ∈ D`. Then
  `sW (p.cont z v) w' = sV v (q.cont z† w')` for every `z` regular for `p`
  with `z†` regular for `q`.

  Proof. Fix `v` and `w'`. The functions
  `a₁ = conj (sW (N_p(·) v) w')` and `a₂ = sV v (N_q(·) w')` are regular
  functions, by polynomiality of the numerators. The regular function
  `d_q† a₁ − d_p a₂†` vanishes on `D`. There it equals
  `conj (d_q(w†)) d_p(w) (conj (sW (A w v) w') − conj (sV v (B w† w')))`,
  which is `0` by the hypothesis. By the identity theorem
  `rationalUnramifiedRegular_eq_zero_of_isOpen` it is `0` everywhere.
  Evaluating at `z`, conjugating, and dividing by `conj (d_p(z)) d_q(z†)`
  gives the identity.
- `continuedCompositeRationalScalar_nonnegAt`. Assume in addition that
  `sV u u` and `sW u u` are nonnegative reals, `sV v v ≠ 0`, `z` is regular
  for both `p` and `q`, and `z† = z`. Let `f` be the coefficient
  `continuedCompositeRationalScalar … v ((sV v v)⁻¹ • sV v)` of the
  continued composite. Then `RationalFunctionNonnegAt f z`. The Library's
  presentation `f = a / b` with `b(z) ≠ 0` has value
  `(sV v v)⁻¹ sV v (q.cont z (p.cont z v))` at `z`. By the adjoint identity
  this is `(sV v v)⁻¹ sW (p.cont z v) (p.cont z v)`, a quotient of
  nonnegative reals.

## The target

`ConditionalDynamicOppositeUnitaryNonnegStatement` quantifies over:

- a nonarchimedean local field `F`, an affine group scheme `G` over `F` of
  locally finite type, a cocharacter `χ`, the structural premises `hRefl`,
  `hCST`, `hG : IsConnectedReductive G`, and `P = parabolic χ`,
  `P̄ = oppositeParabolic χ`, `M = levi χ`;
- a compact open subgroup `K` with `G(F) = P K` (`hPK`) and `G(F) = P̄ K`
  (`hOppK`), and the split hypotheses `_hKsplit`, `_hOppKsplit` of the
  Hermitian adjunction target (the Levi projections send `P ∩ K` and
  `P̄ ∩ K` into `K`);
- a smooth complex representation `A` of `M(F)` with
  `_hA : IsUnitarizable A.representation`;
- the conditional data of `conditionalCanonicalRationalScalar`: forward and
  reverse continuations `p`, `q`, nonempty open sets `DForward` and
  `DReverse` inside the forward and reverse full convergence domains, and a
  nonempty open set `D` of parameters with irreducible induction (`hi`);
- `_hdag`: `z ↦ z†` maps `DForward` into `reverseFullDomainRegion χ K hK A`;
- a parameter `z` in `p.regularRegion ∩ q.regularRegion` whose value lies in
  `unitaryUnramifiedCharacters (normCharacters χ)`.

The conclusion is `RationalFunctionNonnegAt … (conditionalCanonicalRationalScalar … p q …) z`:
`j_P` has a presentation `m / n` with `n(z) ≠ 0` and `m(z) / n(z)` a
nonnegative real. By `rationalFunction_value_eq` this value does not depend
on the presentation.

Remarks on the hypotheses.

- The regular regions are those of the supplied data `p` and `q`. Since the
  target quantifies over all data, it applies at every unitary point where
  some pair of data is regular.
- Points outside the common regular region are excluded on purpose. `j_P`
  can have poles at unitary points. For `GL₂` and `A = χ₁ ⊗ χ₂` with
  `χ₁ = χ₂` unramified, Harish-Chandra's `μ`, a nonzero constant multiple
  of `j_P⁻¹`, vanishes at the unitary point `s = 0` of the family
  `χ₁|·|^s ⊗ χ₂|·|^{-s}`, so `j_P` has a pole there.
- `_hdag` is a hypothesis because the Library describes the full domains
  only as the sets where all smooth-dual scalar integrals converge
  absolutely. Absolute convergence of these integrals depends only on
  `|z|`, and `|z†| = |z|⁻¹`, but the Library does not describe the domains
  further. The hypothesis is needed only on the chosen open set `DForward`,
  so it can be met by choosing `DForward` inside a region where both
  integrals are known to converge. No such region is constructed here.
- `_hKsplit`, `_hOppKsplit` and `_hA` are used only in the reduction. The
  first two are passed to the Hermitian target. `_hA` supplies the
  invariant positive form `b`.

## The reduction

`conditionalDynamicOppositeUnitaryNonneg_of_hermitianAdjunction` takes the
Hermitian adjunction target `H` and proves the target. Choose an invariant
positive form `b` from `_hA` and a normalized compact coefficient `(v, ℓ₀)`
with `ℓ₀ v = 1` (`exists_normalized_compactCoefficient`). Then `v ≠ 0`, so
`(v, v)_P ≠ 0`. Apply `continuedCompositeRationalScalar_nonnegAt` with
`sV = ( , )_P` and `sW = ( , )_{P̄}` (`compactPictureSesq` for
`decomposition χ` and `oppositeDecomposition χ`), with the open set
`DForward`, and with the adjointness on `DForward` given by `H` and
`_hdag`. `conditionalCanonicalRationalScalar_eq_extraction` identifies
`j_P` with the coefficient extracted by `v` and `(v, v)_P⁻¹ (v, ·)_P`.
Finally `z† = z` at the unitary point `z`
(`unramifiedConjInv_eq_self_of_mem_unitary`).

The module uses the Borel instances `hermitianAdjunctionPointMeasurable` and
`hermitianAdjunctionPointBorel` of `DynamicOppositeHermitianAdjunctionStatement`
as local instances. It also uses the local instances of
`DynamicOppositeCanonicalScalar`.

## Not proved here

- The Hermitian adjunction target, and the inclusion `_hdag`.
- `j_P ≠ 0` at unitary points, and Waldspurger's IV.3 (6) (`j ≠ 0` for
  square-integrable `π`). These need IV.1 (10) at the unitary point, which
  this module does not use.
- Any statement at unitary points where `j_P` has a pole.

## Axioms

The proved results use only `propext`, `Classical.choice` and `Quot.sound`.
The target is a `def … : Prop` and introduces no axioms.
