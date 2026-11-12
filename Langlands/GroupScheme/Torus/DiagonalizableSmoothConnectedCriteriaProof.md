# Smoothness and connectedness of diagonalizable groups: proof

Worker 3483 (proof and exposition); Worker 217 (submission, corrected list of
published inputs).

`Langlands.GroupScheme.Diagonalizable.diagonalizableSmoothConnectedCriteria.{u}`
proves the proposition
`Langlands.GroupScheme.DiagonalizableSmoothConnectedCriteriaStatement.{u}`
(module `Langlands.GroupScheme.Torus.DiagonalizableSmoothConnectedCriteriaStatement`).
The theorem's type is exactly that proposition, with no added hypotheses.

## The statement

Let `k` be a field with characteristic exponent `p` (`ExpChar k p`) and let
`Λ` be a finitely generated abelian group (`AddGroup.FG Λ`), both in the
universe `u`. Write `D(Λ)` for `Diagonalizable.groupScheme (CommRingCat.of k) Λ`,
the spectrum of the group algebra `k[Λ] = AddMonoidAlgebra k Λ`. The statement
is the conjunction of:

1. `D(Λ)` is connected if and only if every element of finite order of `Λ` is
   killed by some power `p ^ n`;
2. `D(Λ)` is smooth over `k` if and only if `p • x = 0` implies `x = 0` in `Λ`;
3. `D(Λ)` is smooth and connected if and only if `Λ` is a free `ℤ`-module.

This is Milne, *Algebraic Groups* (2017), Remark 12.5 (source ID
`milne-2017-algebraic-groups`); the statement's own Markdown gives the
quotations and the reading of Milne's "p-torsion".

## The proof

Milne states the remark without proof. The Lean proof works with the group
algebra `k[Λ]` and uses the structure of finitely generated abelian groups.
All auxiliary results are in the namespace
`Langlands.GroupScheme.Diagonalizable.SmoothConnectedCriteria`; none is private.

### From the scheme to the group algebra

- `connectedSpace_groupScheme_iff`: connectedness of the underlying space of
  `D(Λ)` is, by definition, connectedness of `PrimeSpectrum k[Λ]` (the proof
  is `Iff.rfl`).
- `smooth_groupScheme_iff`: the structure morphism of `D(Λ)` is
  `Spec.map` of `algebraMap k k[Λ]`, so Mathlib's `HasRingHomProperty.Spec_iff`
  and `RingHom.smooth_algebraMap` identify its smoothness with
  `Algebra.Smooth k k[Λ]`.
- `isReduced_of_smooth`: if `D(Λ)` is smooth over `k`, its stalks are domains
  (the Library theorem `AlgebraicGeometry.Smooth.isDomain_and_isIntegrallyClosed_stalk`,
  ported from the Anthropic FLT formalization; its hypotheses that
  `Γ(Spec k, ⊤)` is a domain and integrally closed are found by instance search
  from the Library instances `CharacterLatticeProof.isDomain_sections_spec` and
  `CharacterLatticeProof.isIntegrallyClosed_sections_spec`), so the scheme is
  reduced (Mathlib's `isReduced_of_isReduced_stalk`), and `affine_isReduced_iff`
  makes `k[Λ]` a reduced ring.

### Idempotents and connectedness

For a commutative ring `A`, Mathlib's `PrimeSpectrum.isClopen_iff` says that
the clopen subsets of `PrimeSpectrum A` are the basic opens of idempotents.

- `eq_zero_or_one_of_connectedSpace`: if `PrimeSpectrum A` is connected, every
  idempotent `e` is `0` or `1`. The basic open of `e` is clopen, hence empty or
  everything. If it is empty, `e` is nilpotent (`basicOpen_eq_bot_iff`), and a
  nilpotent idempotent is `0`. If it is everything, the basic open of `1 - e`
  is empty, so `1 - e = 0`.
- `connectedSpace_of_forall_idempotent`: conversely, if `A` is nonzero and its
  only idempotents are `0` and `1`, then `PrimeSpectrum A` is connected
  (`connectedSpace_iff_clopen`).
- `geomSum_mul_self` and `isIdempotentElem_geomSum`: if `g ^ m = 1` and
  `c * m = 1`, then `S = ∑_{i < m} g ^ i` satisfies `S * g = S` (Mathlib's
  `geom_sum_mul`), hence `S * S = m * S`, and `c * S` is idempotent.

### Part 1, connected implies `p`-power torsion

`exists_pow_nsmul_eq_zero` assumes that the only idempotents of `k[Λ]` are `0`
and `1` and lets `x` have finite order `N`. Suppose no `p ^ n • x` vanishes.
`exists_pow_mul_ne_zero` writes `N = p ^ a * m` with `(m : k) ≠ 0`: for `p = 1`
take `a = 0` and `m = N` (characteristic zero); for prime `p` use
`Nat.exists_eq_pow_mul_and_not_dvd` and `CharP.cast_eq_zero_iff`. Then
`y = p ^ a • x` is nonzero and `m • y = 0`, so `g = single y 1` satisfies
`g ^ m = 1`, and `e = m⁻¹ ∑_{i < m} g ^ i` is idempotent. The augmentation
`AddMonoidAlgebra.lift k k Λ 1` sends `e` to `m⁻¹ * m = 1`, so `e ≠ 0`. If
`e = 1`, then `(g - 1) * e = 0` gives `single y 1 = single 0 1`, so `y = 0`.
Both cases contradict the hypothesis.

### Part 1, `p`-power torsion implies connected

`eq_zero_or_one_of_pTorsion` shows that all idempotents of `k[Λ]` are `0` or
`1` when every element of finite order of `Λ` is killed by a power of `p`.

1. The published `Diagonalizable.exists_freeFiniteEquiv` gives
   `b : Λ ≃+ (I → ℤ) × A` with `I` a finite type and `A` a finite group. Each
   `a : A` gives the element `b.symm (0, a)` of finite order, hence some
   `p ^ n` kills `a`; taking the maximum over the finite `A` gives one `N` with
   `p ^ N • a = 0` for all `a : A`.
2. `pow_expChar_pow_eq`: for every `f : k[F × A]`, `f ^ p ^ N` equals the image
   of `f` under `k[F × A] → k[F]` (induced by the projection), followed by
   raising coefficients to the power `p ^ N` (`iterateFrobenius`) and by
   `k[F] → k[F × A]` induced by `v ↦ (p ^ N • v, 0)`. Both sides are additive
   in `f` (`add_pow_expChar_pow`, after `expChar_of_injective_algebraMap` gives
   `k[F × A]` the characteristic exponent `p`), and on `single z r` both are
   `single (p ^ N • z) (r ^ p ^ N)`, because `p ^ N • z.2 = 0`.
3. `eq_zero_or_one_free`: the idempotents of `k[I → ℤ]` are `0` and `1`,
   because the split torus `D(I → ℤ)` (published `isSplitTorus_free`) is
   connected (published `IsSplitTorus.connectedSpace`).
4. `eq_zero_or_one_prod`: assume that the only idempotents of `k[F]` are `0`
   and `1` (for `F = I → ℤ` this is step 3). For an idempotent `e` of
   `k[F × A]`, its image in `k[F]` is idempotent, hence `0` or `1`, and
   `e = e ^ p ^ N` is the image of that under the ring maps of step 2, hence
   `0` or `1`.
5. The algebra isomorphism `AddMonoidAlgebra.domCongr k k b` transports the
   result from `k[(I → ℤ) × A]` to `k[Λ]`.

`k[Λ]` is nonzero, so `connectedSpace_of_forall_idempotent` gives
connectedness.

### Part 2, smooth implies no `p`-torsion

`eq_zero_of_isReduced`: if `k[Λ]` is reduced and `p • x = 0`, then
`(single x 1 - 1) ^ p = single (p • x) 1 - 1 = 0` (`sub_pow_expChar` with the
characteristic exponent of `k[Λ]`), so `single x 1 = 1 = single 0 1` and
`x = 0`. Combined with `isReduced_of_smooth` this is the forward direction.

### Part 2, no `p`-torsion implies smooth

`Algebra.Smooth k k[Λ]` is formal smoothness together with finite
presentation; the latter follows from finite generation of `k[Λ]` over the
noetherian `k` (`Algebra.FinitePresentation.of_finiteType`). For formal
smoothness, `formallySmooth_of_forall` uses Mathlib's criterion
`Algebra.FormallySmooth.of_comp_surjective`: for every `k`-algebra `B` and
ideal `I` with `I ^ 2 = ⊥`, every `k`-algebra map `g : k[Λ] → B ⧸ I` lifts to
`k[Λ] → B`. Algebra maps out of `k[Λ]` are homomorphisms from `Λ` to the
multiplicative monoid (`AddMonoidAlgebra.lift`), and their values are units,
so it suffices to lift a homomorphism `Λ → (B ⧸ I)ˣ` to `Λ → Bˣ`.

1. `mul_eq_zero_of_sq_eq_bot`: products of two elements of `I` vanish.
2. `exists_unit_lift`: every unit `v` of `B ⧸ I` lifts to a unit of `B`. Lift
   `v` and `v⁻¹` to `b` and `c`; then `a = b * c - 1 ∈ I`, and
   `b * (c * (1 - a)) = 1 - a * a = 1`.
3. `exists_unit_lift_pow_eq_one`: if moreover `v ^ n = 1` and `n` is a unit of
   `B`, the lift can be chosen with `u ^ n = 1`. Take a unit lift `u₀`; then
   `a = u₀ ^ n - 1 ∈ I`, and with `c * n = 1` the unit
   `u = u₀ * (1 - c * a)` still lifts `v` and satisfies
   `u ^ n = (1 + a) * (1 - n * c * a) = 1`, using `(1 - c * a) ^ n = 1 - n * c * a`
   (proved by induction, since `(c * a) ^ 2 = 0`) and `a * a = 0`.
4. `exists_lift_free_prod_zmod`: for a surjective homomorphism `π : U →+ V`
   of abelian groups, and `m : ι → ℕ` such that every `v` with `m i • v = 0`
   lifts to some `u` with `m i • u = 0`, every homomorphism
   `(Fin n →₀ ℤ) × ⨁ i, ZMod (m i) →+ V` lifts along `π`. The lift is built
   from chosen lifts of the images of the basis vectors (`Finsupp.liftAddHom`
   and `zmultiplesHom`) and of the generators `1 : ZMod (m i)` (`ZMod.lift`,
   `DirectSum.toAddMonoid`), combined by `AddMonoidHom.coprod`; the identity
   `π ∘ lift = χ` is checked on generators (`Finsupp.addHom_ext'`,
   `AddMonoidHom.ext_int`, `DirectSum.addHom_ext'` and `zmod_addHom_ext`).
5. `primePow_ne_zero`: write `Λ ≃+ (Fin n →₀ ℤ) × ⨁ i, ZMod (q i ^ e i)` with
   primes `q i` (Mathlib's `AddCommGroup.equiv_free_prod_directSum_zmod`). If no
   nonzero element of `Λ` is killed by `p`, then each `q i ^ e i` is nonzero in
   `k`. In characteristic zero this is automatic. For prime `p`, if
   `q i ^ e i` vanished in `k`, then `p = q i` and `e i ≠ 0`, and the element
   of `Λ` corresponding to `q i ^ (e i - 1)` in the `i`-th summand would be
   nonzero and killed by `p`.
6. In `formallySmooth_of_forall`, `π` is `Units.map` of the quotient map,
   written additively; it is surjective by step 2, and step 3 provides the
   torsion lifts because each `q i ^ e i` is a unit of `B` (it is a nonzero
   element of `k`, step 5). Step 4, applied to the given homomorphism composed
   with the decomposition, gives the lift; `AddMonoidAlgebra.algHom_ext`
   checks that the resulting algebra map lifts `g`.

### Part 3

The forward direction is the published `Diagonalizable.free_of_smooth_connected`.
For the reverse direction, a `ℤ`-basis of the free, finitely generated `Λ`
(`Module.Free.chooseBasis`) makes `D(Λ)` a split torus by the published
`Diagonalizable.isSplitTorus`, and split tori over a field are smooth
(`IsSplitTorus.smooth`) and connected (`IsSplitTorus.connectedSpace`).

The module sets the options `backward.isDefEq.respectTransparency false`,
`backward.isDefEq.respectTransparency.types false` and
`backward.defeqAttrib.useBackward true` for the whole file. The theorem depends
only on the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Published inputs

The list below is every Library declaration that the module's declarations
refer to directly, as read from the compiled constants (`getUsedConstants` over
all declarations of this module), together with its module.

Theorems and instances:

- `Langlands.GroupScheme.Diagonalizable.exists_freeFiniteEquiv` and
  `Langlands.GroupScheme.Diagonalizable.isSplitTorus_free`
  (`Langlands.GroupScheme.Torus.DiagonalizablePowerDecomposition`).
- `Langlands.GroupScheme.Diagonalizable.isSplitTorus`
  (`Langlands.GroupScheme.Torus.Diagonalizable`).
- `Langlands.GroupScheme.Diagonalizable.free_of_smooth_connected`
  (`Langlands.GroupScheme.Torus.SmoothConnectedKernelCocharacters`).
- `Langlands.GroupScheme.IsSplitTorus.smooth` (`Langlands.GroupScheme.Torus.Split`).
- `Langlands.GroupScheme.IsSplitTorus.connectedSpace`
  (`Langlands.GroupScheme.Torus.SplitReductiveProof`).
- `AlgebraicGeometry.Smooth.isDomain_and_isIntegrallyClosed_stalk`
  (`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Smooth_isDomain_and_isIntegrallyClosed_stalk`).
- The instances `Langlands.GroupScheme.CharacterLatticeProof.isDomain_sections_spec`
  and `Langlands.GroupScheme.CharacterLatticeProof.isIntegrallyClosed_sections_spec`
  (`Langlands.GroupScheme.Rational.CharacterLatticeProof`), used by instance
  search for the hypotheses of the previous theorem.

Definitions:

- `Langlands.GroupScheme.DiagonalizableSmoothConnectedCriteriaStatement`
  (`Langlands.GroupScheme.Torus.DiagonalizableSmoothConnectedCriteriaStatement`),
  the target.
- `Langlands.GroupScheme.Diagonalizable.groupScheme`
  (`Langlands.GroupScheme.Torus.Diagonalizable`),
  `Langlands.GroupScheme.IsSplitTorus` (`Langlands.GroupScheme.Torus.Split`) and
  `Langlands.CommGroupScheme.toGrp` (`Langlands.AbelianScheme.GroupScheme`).

From Mathlib, among others: `AddCommGroup.equiv_free_prod_directSum_zmod`,
`Algebra.FormallySmooth.of_comp_surjective`,
`Algebra.FinitePresentation.of_finiteType`, `HasRingHomProperty.Spec_iff`,
`RingHom.smooth_algebraMap`, `isReduced_of_isReduced_stalk`,
`affine_isReduced_iff`, `PrimeSpectrum.isClopen_iff`,
`PrimeSpectrum.basicOpen_eq_bot_iff`, `expChar_of_injective_algebraMap` and
`iterateFrobenius`.
