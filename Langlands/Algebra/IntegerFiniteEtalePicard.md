# Finite étale algebras over `ℤ` have trivial Picard groups

This internal algebraic helper supplies the arithmetic Picard-group input for the
`Spec ℤ` case of Conrad, *Reductive group schemes* (2014), Remark 7.2.13 (page 259 of
the cited PDF, source `conrad-2014-reductive-group-schemes`). The remark says that the
proof of Proposition 7.2.12 only uses that every finite étale cover of the base has
trivial Picard group, so the conclusion also holds over `Spec ℤ`. Conrad does not prove
the Picard-group fact. The proof here is our own. It uses Mathlib's consequence of
the Hermite–Minkowski theorem that a finite unramified domain over `ℤ` of
characteristic zero is `ℤ` itself.

## Declarations

`FiniteEtaleAlgebrasHaveTrivialPicard R` (in universes `u` for `R` and `v` for the
algebras) says that every commutative `R`-algebra `R'` that is étale (`Algebra.Etale R R'`)
and finite as an `R`-module (`Module.Finite R R'`) has subsingleton `CommRing.Pic R'`. With
`v = u` this is exactly the hypothesis of clause 1 of
`Langlands.GroupScheme.ReductivePicardTrivialQuasiSplitInnerFormStatement`.

`subsingleton_pic_of_ringEquiv` transports a trivial Picard group backwards along a ring
isomorphism `R ≃+* S`. `Langlands.CommutativeAlgebra.subsingleton_pic_of_ringEquiv` proves
the same fact in the other direction, but it sits in a module with heavy geometric
imports.

`subsingleton_pic_of_bijective_algebraMap_pi` says: let `B : ι → Type v` be a finite family
of `R`-algebras with trivial Picard groups. If the structure map `R → ∀ i, B i` is
bijective, then `R` has trivial Picard group.

The remaining declarations use the canonical `ℤ`-algebra structure `Ring.toIntAlgebra`:

- `injective_includeRight_rat`: a flat `ℤ`-algebra `A` injects into `ℚ ⊗[ℤ] A`.
- `isReduced_of_etale_int`: an étale `ℤ`-algebra is reduced.
- `intCast_mem_nonZeroDivisors`: a nonzero integer is a non-zero-divisor in an étale
  `ℤ`-algebra.
- `bijective_intCast_of_surjective`: take a module-finite étale `ℤ`-algebra `A` and a
  characteristic-zero domain `B` with a surjective ring map `A → B`. Then `ℤ → B` is
  bijective.
- `bijective_intCast_quotient_minimalPrime`: for every minimal prime `p` of such an `A`,
  `ℤ → A ⧸ p` is bijective.
- `minimalPrimePoint A hp : A →+* ℤ` is the resulting `ℤ`-point. It has kernel `p`
  (`ker_minimalPrimePoint`), and `intCast_minimalPrimePoint` says that it inverts `ℤ → A`
  modulo `p`.
- `isCoprime_of_mem_minimalPrimes`: distinct minimal primes of `A` are comaximal.
- `subsingleton_pic_of_etale_int`: **every module-finite étale `ℤ`-algebra has trivial
  Picard group.**
- `finiteEtaleAlgebrasHaveTrivialPicard_of_ringEquiv_int`: **if `R ≃+* ℤ`, then
  `FiniteEtaleAlgebrasHaveTrivialPicard R` holds** (in any universes). This is the form
  needed to derive clause 2 of the target from clause 1.

## Proofs

*Transport along an isomorphism.* `Pic.mapRingHom` is functorial
(`mapRingHom_mapRingHom`, `mapRingHom_id_apply`). So `mapRingHom e.symm` is a left inverse
of `mapRingHom e`, and the latter is injective into a subsingleton.

*Products.* We use `CommRing.Pic.subsingleton_iff`. Let `M` be an invertible `R`-module.
Each `B i ⊗[R] M` is an invertible `B i`-module (Mathlib instance), hence free of rank one
because `Pic (B i)` is trivial (`Module.Invertible.free_iff_linearEquiv`). The chain of
`R`-linear equivalences

`M ≃ R ⊗[R] M ≃ (∀ i, B i) ⊗[R] M ≃ ∀ i, (B i ⊗[R] M) ≃ ∀ i, B i ≃ R`

uses `TensorProduct.lid`, the bijective structure map (`LinearEquiv.ofBijective`) tensored
with `M`, `TensorProduct.piLeft`, the rank-one trivializations with scalars restricted to
`R`, and the inverse of the structure map. So `M` is free.

*Reducedness and torsion-freeness.* An étale algebra is smooth and hence flat over `ℤ`, so
`A → ℚ ⊗[ℤ] A`, `a ↦ 1 ⊗ a`, is injective (`Module.Flat.rTensor_preserves_injective_linearMap`
applied to `ℤ → ℚ`). The algebra `ℚ ⊗[ℤ] A` is étale over the field `ℚ` by base change, so it
is reduced (`Algebra.FormallyUnramified.isReduced_of_field`). Hence `A` is reduced. If
`n ≠ 0`, then the image of `n` in `ℚ ⊗[ℤ] A` is a unit. So `n * y = 0` in `A` forces
`y = 0`.

*Minimal primes.* Let `f : A → B` be surjective, with `B` a characteristic-zero domain.
Then `B` is module-finite over `ℤ` (`Module.Finite.of_surjective`) and formally unramified
over `ℤ` (`Algebra.FormallyUnramified.of_surjective`), so it is unramified over `ℤ`.
Characteristic zero makes `ℤ → B` injective, which gives `FaithfulSMul ℤ B`. Mathlib's
`bijective_algebraMap_int_of_finite_of_unramified` (Hermite–Minkowski) then gives that
`ℤ → B` is bijective. For a minimal prime `p`, the quotient `A ⧸ p` is a domain. It has
characteristic zero: a minimal prime consists of zero divisors
(`Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes`), while nonzero integers are
non-zero-divisors in `A`.

*Comaximality.* Let `p ≠ q` be minimal primes with `p ⊔ q ≠ ⊤`. Write `φ` and `ψ` for
their `ℤ`-points. Then `x - φ(x) ∈ p` and `x - ψ(x) ∈ q`, so `φ(x) - ψ(x)` lies in the
proper ideal `J = (p ⊔ q) ∩ ℤ`. By Krull's intersection theorem in `ℤ`
(`Ideal.iInf_pow_eq_bot_of_isDomain`), `⋂ₙ Jⁿ = 0`. Formal unramifiedness of `A` over `ℤ`
(`Algebra.FormallyUnramified.ext_of_iInf`) shows that two `ℤ`-algebra maps `A → ℤ` that
agree modulo `J` are equal. So `φ = ψ`, and taking kernels gives `p = q`, a contradiction.

*Conclusion.* `A` is Noetherian (`Algebra.FiniteType.isNoetherianRing`), so it has finitely
many minimal primes (`minimalPrimes.finite_of_isNoetherianRing`). Their intersection is the
nilradical (`Ideal.sInf_minimalPrimes`), which is zero because `A` is reduced. So
`A → ∀ p, A ⧸ p` is injective. It is surjective by the Chinese remainder theorem
(`Ideal.pi_quotient_surjective`) and comaximality. Each `A ⧸ p ≅ ℤ` has trivial Picard
group: `Subsingleton (CommRing.Pic ℤ)` is found by instance search (Mathlib proves it for
GCD domains), and the transport lemma moves it to `A ⧸ p`. The product lemma then
gives `Subsingleton (CommRing.Pic A)`.

*Clause-2 form.* Suppose `R ≃+* ℤ`. Then `ℤ → R` is bijective, so `R` is étale and
module-finite over `ℤ` (`Algebra.Etale.of_equiv`, `Module.Finite.equiv`). A module-finite
étale `R`-algebra `R'` is then module-finite and étale over `ℤ` (`Algebra.Etale.comp`,
`Module.Finite.trans`), and the previous theorem applies.

## Scope

These are commutative-algebra results only. They construct no group schemes and prove
nothing about inner forms. The affine-space Picard input of clause 3 is not treated here.
