# Proof of the canonical pairing and opposite Jacquet duality

Author: Worker 112.

This module proves `Langlands.Parabolic.OppositeDualityStatement` as the theorem
`Langlands.Parabolic.oppositeDualityStatement`. It is the pair of
`canonicalPairingClause` (existence and uniqueness of the bilinear form with the
canonical asymptotics) and `oppositeJacquetDualityClause` (every such form induces
the equivalence of the normalized opposite Jacquet module of the smooth dual with the
smooth dual of the normalized upper Jacquet module). The statement is Casselman's
Theorem III.6.2 and Corollary III.6.3 (Bill Casselman, *Introduction to admissible
representations of p-adic groups*, Chapter III, revision April 29, 2019,
`casselman-2019-jacquet-module`, pages 7–8), for the standard block parabolics of
`GL_n` over a finite extension of `ℚ_p`.

Both clauses come from the abstract stable evaluation pairing of
`Langlands.Representation.Jacquet.StablePairingProof` and its asymptotics in
`Langlands.Representation.Jacquet.StablePairingAsymptotics`. The pairing data and
the auxiliary lemmas in this module are internal to this project and add no
statement to the Library. The closing theorem has no hypotheses beyond those of the
target. Admissibility of `ρ` is the only assumption on the representation. Rank zero
and shapes with at most one block are not treated separately: the Library's
`deepChamberNonempty` and `uniformCompactBlockContraction` cover them, and every
argument below is uniform in the shape.

## Orientation

The target pairs the opposite quotient of the smooth dual,
`Coinvariants (smoothContragredient ρ) B.oppositeUnipotentSubgroup`, with the upper
quotient `Coinvariants ρ B.unipotentSubgroup`. In the abstract framework the pairing
has type `Coinvariants (smoothContragredient ρ) D.N →ₗ Coinvariants ρ D.Nbar →ₗ ℂ`.
So this module takes `D.N` to be the opposite radical and `D.Nbar` the upper
radical. This is the orientation of the asymptotics module (its `Nbar` plays the role
of the upper radical `U`). It is the reverse of `standardPairingData` in
`Langlands.Representation.Parabolic.NaturalJacquetDualityProof`. The contracting
element of the data is therefore `g = (B.blockScalar a)⁻¹` for a strictly
contracting tuple `a`. Conjugation by `g⁻¹ = B.blockScalar a` contracts the upper
radical, and conjugation by `g` contracts the opposite radical.

## Iwahori lemmas

For a block shape `B`:

- `HasBlockIwahoriFactorization.factor_upper`: a subgroup `K` with block Iwahori
  factorization also factors each `k ∈ K` as upper times Levi times lower, with all
  three factors in `K`. It applies the Library factorization
  (`HasBlockIwahoriFactorization.factor`, lower times Levi times upper) to `k⁻¹` and
  inverts.
- `HasBlockIwahoriFactorization.lower_conj_inv_pow`: for a weakly contracting `a`
  and `l ∈ K` in the opposite radical,
  `(blockScalar a)⁻ʳ l (blockScalar a)ʳ ∈ K` for every `r`. This is induction on
  `r` with the lower conjugation clause of the factorization.
- `eventually_pow_inv_conj_mem`: for a strictly contracting `a`, a compact set `C`
  and an identity neighbourhood `U`, every sufficiently high power `s` satisfies
  `(blockScalar a)⁻ˢ l (blockScalar a)ˢ ∈ U` for all `l ∈ C` in the opposite
  radical. The Library's `uniformCompactBlockContraction`, applied to the compact
  set `C ∩ oppositeUnipotentSubgroup` (closed by `isClosed_oppositeUnipotentSubgroup`),
  gives a depth `ε`. Then `strictPowersEventuallyDeep` makes the powers `aˢ`
  `ε`-deep from some `r` on. The block scalar of `aˢ` is `(blockScalar a)ˢ`
  (`map_pow`).

## The opposite pairing data

`oppositePairingData F T B a ha`, for a strictly contracting tuple `a`, is the
`Jacquet.StablePairingData` on `GeneralLinear n F.Carrier` with

- `N = B.oppositeUnipotentSubgroup`, `Nbar = B.unipotentSubgroup`,
  `M = B.leviSubgroup`, with the Library normalizer inclusions
  `leviSubgroup_le_normalizer_oppositeUnipotentSubgroup` and
  `leviSubgroup_le_normalizer_unipotentSubgroup`;
- `g = (B.blockScalar a)⁻¹`, which commutes with `M` because the block scalar does
  (`blockScalar_commute_of_mem_leviSubgroup`);
- good subgroups the compact open subgroups with block Iwahori factorization.

The axioms are checked as follows. Good subgroups form a neighbourhood basis by
`exists_compactOpenSubgroup_hasBlockIwahoriFactorization`. They are stable under
Levi conjugation by `isCompact_conjOpenSubgroup` and
`hasBlockIwahoriFactorization_conj` (from `NaturalJacquetDualityProof`). The
`N`-`M`-`Nbar` factorization is `factor_upper`. The lower axiom
`g⁻¹ (K ∩ Nbar) g ⊆ K` is the upper conjugation clause of the factorization for `a`.
The upper axiom `gʳ (K ∩ N) g⁻ʳ ⊆ K` is `lower_conj_inv_pow`. Depth is
`eventually_pow_inv_conj_mem` with `C = K₀` and `U = K₁`.

`oppositePairingData_admits` shows that every admissible `ρ` satisfies `Admits`:

- `duality`: fixed spaces are finite-dimensional by admissibility, so the Library's
  `compactCompression_stableEvaluationDuality` applies.
- The smooth contragredient is admissible by
  `isAdmissible_smoothContragredient_of_compact_cofinal`, since compact open
  subgroups are cofinal.
- The canonical-lift conditions for the dual and the radical `D.N` (opposite) and
  the element `g` come from the Library's `blockOppositeStableImageJacquetBijective`
  and `blockOppositePowerKernelJacquet`, applied to `smoothContragredient ρ`.
- The conditions for `ρ` and the radical `D.Nbar` (upper) concern `g⁻¹`, rewritten to
  `blockScalar a`. They come from `blockStableImageJacquetBijective` and
  `blockPowerKernelJacquet` applied to `ρ`.

Only the surjective half of bijectivity and one inclusion of each kernel equality
are used.

`isContractingElement_blockScalar`: the block scalar of every weakly contracting
tuple `c` is a contracting element of the opposite data in the sense of
`IsContractingElement`. It commutes with `M` and with `g`, since block scalars form a
commutative image. It conjugates `K ∩ Nbar` (upper) and, through its inverse,
`K ∩ N` (opposite) into `K` by the two clauses of the factorization for `c`.

## The asymptotic formula in unnormalized form

`leviHalfModulus_mul_normalizedAction`: on quotient representatives, the positive
half `T.leviHalfModulus B m` times a linear form applied to the normalized upper
action of `B.leviEquiv m` on `[w]` equals the form applied to
`[ρ(leviEmbedding m) w]`. This is `normalizedActionOfModulus_mk`: the normalized
action is `√δ(m)⁻¹` times the descended action, and `δ` evaluated at
`B.leviEquiv m` is `T.leviModulus B m`.

`canonicalPairingAsymptotics_iff` rewrites `CanonicalPairingAsymptotics` as: for
each `v` and `ℓ` there is `ε` with `0 < ε ≤ 1` such that
`ℓ(ρ(blockScalar c) v) = b [ℓ] [ρ(blockScalar c) v]` for every `ε`-deep tuple `c`
(`IsDeeplyContracting`). The target's ratio inequalities are `IsDeeplyContracting`
by definition. Its element `aM` is `blockScalarLevi c`, embedded as
`blockScalar c`.

## Stable pairings are exactly the forms with the canonical asymptotics

`canonicalPairingAsymptotics_of_isStablePairing`: a stable pairing `b` of the
opposite data has the canonical asymptotics. By `IsStablePairing.hasAsymptotics`
and `HasAsymptotics.exists`, each pair `(v, ℓ)` has a good `K` and a finite set `S`
of upper unipotent elements. The formula then holds for every contracting element
`x` with `x S x⁻¹ ⊆ K`. `uniformCompactBlockContraction` for the finite set `S`
gives `ε ≤ 1` such that every `ε`-deep `c` conjugates `S` into `K`. Such `c` is
weakly contracting (as `ε ≤ 1`), so its block scalar is a contracting element.

`isStablePairing_of_canonicalPairingAsymptotics`: conversely, a form `b` with the
canonical asymptotics is a stable pairing. Let `K` be good, `ℓ` a `K`-fixed smooth
functional and `t` a `K`-fixed vector in the stable image of compression by
`g⁻¹ = blockScalar a`.

1. The formula `ℓ(ρ(blockScalar c) w) = b [ℓ] [ρ(blockScalar c) w]` is linear in
   `w`. The fixed space `V^K` is finite-dimensional by admissibility. Taking the
   minimum of the depths for a finite spanning set gives one `ε` that works for
   every `w ∈ V^K` (induction over the `Finset`, then `Submodule.span_induction`).
2. `strictPowersEventuallyDeep` gives `r` with `aʳ` `ε`-deep. As `t` is in the
   stable image, `t` is the `r`-th compression power of some `w ∈ V^K`. By
   `compressedAction_inv_pow_apply` that is the `K`-average of `ρ(g⁻ʳ) w`.
3. `mk_averageMap_apply` shows that this average has the same upper class as
   `ρ(g⁻ʳ) w`. Its hypotheses are `commute_pow` and the upper axiom of the data.
   `smoothDualPairing_averageMap` shows `ℓ(t) = ℓ(ρ(g⁻ʳ) w)`, since `ℓ` is
   `K`-fixed.
4. Since `g⁻ʳ = blockScalar (aʳ)`, step 1 gives
   `b [ℓ] [t] = b [ℓ] [ρ(g⁻ʳ) w] = ℓ(ρ(g⁻ʳ) w) = ℓ(t)`.

`stablePairing_eq`: two stable pairings for the same data and an admissible input
coincide. Given classes `x` and `y`, `exists_common_lift` provides a good `K`, a
`K`-fixed lift `ℓ` of `x` and a stable `K`-fixed lift `t` of `y`; both pairings send
`(x, y)` to `ℓ(t)`.

## The two clauses

`canonicalPairingClause`: fix a `1`-deep (hence strictly contracting) tuple `a` from
`deepChamberNonempty`. For admissible `ρ`, `exists_isStablePairing` gives a stable
pairing `b`. It has the canonical asymptotics by the first direction above. Any other
form `b'` with the canonical asymptotics is a stable pairing by the second
direction, so `b' = b` by `stablePairing_eq`.

`oppositeJacquetDualityClause`: given admissible `ρ` and `b` with the canonical
asymptotics, `b` is a stable pairing for the data of a fixed `1`-deep tuple.
`IsStablePairing.exists_equiv` is applied with

- `L = M = B.leviSubgroup` and `ι` the identity `ContinuousMulEquiv.refl`;
- `χU = inverseHalfCharacter δ⁻¹` and `χO = inverseHalfCharacter δ`, where `δ` is
  the target's full modulus on the embedded Levi. Their product is `1` by
  `inverseHalfCharacter_mul_inverseHalfCharacter_inv`. The kernel of `χO` is open by
  `isOpen_ker_inverseHalfCharacter`, since the kernel of `δ` is the preimage of the
  open kernel of `T.leviModulus B` (`isOpen_ker_leviModulus`) under the continuous
  map `(B.leviEquivContinuous).symm`;
- `σU = JopDual` (the opposite quotient of the smooth dual, normalized by `δ⁻¹`),
  `eX` the identity, and `σO = J` (the upper quotient of `ρ`, normalized by `δ`).

Both compatibility hypotheses hold by definition on quotient representatives,
since `normalizedActionOfModulus` is the character twist of the descended action by
the inverse half character. The resulting
`E : Representation.Equiv JopDual (smoothContragredient J)` satisfies
`(E x).1 y = b x y`, in particular on the classes of `ℓ` and `v` as the target
requires.

## Named consequences

For use elsewhere the module also exposes:

- `exists_canonicalPairingAsymptotics`: every admissible `ρ` has a form with the
  canonical asymptotics.
- `eq_of_canonicalPairingAsymptotics`: two such forms are equal.
- `exists_oppositeJacquetDualityEquiv`: a single equivalence
  `E : Representation.Equiv JopDual (smoothContragredient J)` agrees with every form
  having the canonical asymptotics on quotient representatives.
- `subsingleton_oppositeJacquet_smoothContragredient`: if the upper Jacquet quotient
  of an admissible `ρ` is trivial, so is the opposite Jacquet quotient of its smooth
  dual. The smooth dual of a trivial module is trivial, and `E` is injective.
- `canonicalPairingAsymptotics_iff`, `oppositePairingData`,
  `oppositePairingData_admits` and the two directions of the stable-pairing
  characterization, described above.

The closing theorem uses only the axioms `propext`, `Classical.choice` and
`Quot.sound`.
