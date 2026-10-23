# Prime-adic multiplicative Tate comparison under base change

This internal construction extends the finite and divisibility-indexed
multiplicative base-change comparison to prime-power Tate modules. It
imports `MultiplicativeIntegralBaseChange`; all declarations are in
`Langlands.GroupScheme.Gm.TateComparison`.

## Inputs and construction

Let `b : S' ⟶ S` be a morphism of schemes in the same universe,
`T : Over S'` a test scheme, and `p : ℕ` a prime, supplied by
`[Fact p.Prime]`. The actual Tate module
`Tate.PrimeAdic.Integral (Gm S').toGrp T p` consists of coherent
sections of the kernels of multiplication by `p^n`, including `n = 0`.
Its topology and its `ℤ_[p]` action are the existing product-subspace
topology and residue action. No finite-étaleness, invertibility,
connectedness, finiteness of sections, or field hypothesis is required.

`primeIntegralBaseChange b T p` is a continuous `ℤ_[p]`-linear
equivalence to `Tate.PrimeAdic.Integral (Gm S).toGrp
((Over.map b).obj T) p`. It composes the canonical continuous root
comparison at `T` with the inverse root comparison at the test scheme
whose structure morphism is composed with `b`. These comparisons have
exactly the same intermediate root limit: the underlying test scheme
and its global section ring have not changed. Thus continuity of the
map and its inverse and scalar compatibility come from the existing
bundled comparisons.

`primeIntegralEquiv_primeIntegralBaseChange` proves that the resulting
coherent root family is unchanged. Its proof cancels the target root
equivalence with its inverse.

## Actual geometric coordinates

`evaluation_primeIntegralBaseChange` states that evaluation at `n`
is precisely `levelBaseChange b T (p^n)` applied to the original
coordinate. This equality is definitional.

`evaluation_primeIntegralBaseChange_eq_actual` then proves that this
coordinate is

```text
Tate.levelBaseChange b (Gm S).toGrp T (p^n)
  (Tate.levelMap T (Gm.baseChangeIso b).inv (p^n)
    (Tate.PrimeAdic.evaluation (Gm S').toGrp T p n x)).
```

The first map applied here is induced by the inverse of the canonical
isomorphism from the pullback of `Gm S` to `Gm S'`; the second is the
actual torsion pullback identification. The proof invokes the finite
`levelBaseChange_eq_actual` at `p^n`. Therefore the new equivalence
is tied at every coordinate to the actual geometric pullback. It is
not parameterized by an arbitrary comparison, and no additional generic
prime-adic pullback map is introduced in this unit.

## Extraction and naturality

For a predicate `P : ℕ → Prop` and `hP : ∀ n, P (p^n)`,
`toPrime_integralBaseChange` proves that extracting the prime-power
coordinates after the selected integral base-change equivalence equals
applying `primeIntegralBaseChange` after extraction.
`fullToPrime_integralBaseChange` gives the full specialization.
`awayToPrime_awayBaseChange` uses the away scalar bundle for any
natural modulus `m` and requires `Nat.Coprime p m`. All three
identities are definitional: both sides select and compare the same
finite coordinates. They do not assert that extraction is an
isomorphism.

For any morphism `a : T' ⟶ T` over `S'`,
`primeIntegralBaseChange_testRestrict` proves that restriction of actual
torsion sections commutes with base change. The target restriction is
along `(Over.map b).map a`. The proof applies the injective target
root comparison and uses its restriction formula and base-change
invariance; the maps on global sections are definitionally the same.

For any commutative ring object `R` and `t : Spec R ⟶ S'`,
`primeIntegralBaseChangeAt b p t` is the continuous linear equivalence
at `t` and `t ≫ b`. The theorem
`affinePrimeIntegralEquiv_primeIntegralBaseChangeAt` identifies their
images in `TateTwist.Integral R p`. Its proof applies the root map
induced by the canonical `Scheme.ΓSpecIso R` to the root-family
invariance above. Field-valued and geometric points are special cases.

## Provenance and scope

The unit is internally derived from the canonical multiplicative root
comparisons, the finite actual-pullback equation, the existing
prime-power coordinate extraction, and test-scheme restriction. No new
result is attributed to external literature. The proofs preserve roots
as roots, without choosing compatible generators, bases or a twist
trivialization.

This unit covers the integral prime-adic comparison. It makes no
compactness, rank, rational comparison, monodromy pullback, pairing
compatibility, iterated-base-change coherence or PEL completion claim.
Those remain separate constructions or obligations of the parent task.
