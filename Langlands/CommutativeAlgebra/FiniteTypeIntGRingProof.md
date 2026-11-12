# Finite-type integer algebras are G-rings: proof

Module: `Langlands.CommutativeAlgebra.FiniteTypeIntGRingProof`.

Authors: Worker 5181, with Worker 5143 (helper module
`FiniteTypeIntGRing/SurjectiveCompletion`).

`Langlands.CommutativeAlgebra.finiteTypeIntGRing.{u}` proves exactly
`Langlands.CommutativeAlgebra.FiniteTypeIntGRingStatement.{u}`, imported
unchanged from `Langlands.CommutativeAlgebra.FiniteTypeIntGRingStatement`:

```lean
∀ (S : Type u) [CommRing S] [Algebra.FiniteType ℤ S], IsGRing S
```

The universe `u` is arbitrary, and no hypothesis is added: `S` may be
nonreduced or not a domain, every prime of `S` is covered, the completion is
the actual `AdicCompletion` of `S_p` at its maximal ideal, and the
geometric-regularity test is the published `GeometricallyRegular`. The
regularity of the twisted fibres is in fact proved for every finite field
extension `k'` of the residue field, not only for the purely inseparable ones
the definition requires.

## Route

The statement is Stacks Project, More on Algebra, Proposition 15.51.12,
parts (3) and (5) (Tag 07GG; registered source
`stacks-regular-maps-g-rings-2026-11-11`). The Stacks proof shows that `ℤ` is
a G-ring and ascends along finite-type maps (Proposition 15.51.10). The Lean
proof takes a different, direct route. For a prime localization `A = S_p`
and a prime `q` of `A`, the domain `A ⧸ q` is generated, up to units, by
the images of the polynomial ring `R₀[X_1, …, X_n]`, where `R₀ = ℤ` or
`R₀ = ZMod ℓ` according to the characteristic of `κ(q)`. The twisted formal
fibre `k' ⊗_{κ(q)} (κ(q) ⊗_A Â)` is identified with a fibre of a polynomial
ring over the completion of a localization of `R₀[X]`. That fibre is shown to
be regular by a Jacobian criterion, with derivations extended to the
completion. The helper modules, all under
`Langlands/CommutativeAlgebra/FiniteTypeIntGRing/` and in the namespace
`Langlands.CommutativeAlgebra.FiniteTypeIntGRing`, are:

- `RegularQuotient`: a quotient of a regular local ring by elements with
  independent classes in `𝔪/𝔪²` is regular;
- `JacobianQuotient`: the same with independence tested by a derivation into a
  residue-field vector space;
- `CompletionRegular`: the completion of a regular local ring is regular;
- `CompletionDerivation`: Leibniz maps extend to adic completions;
- `PolynomialJacobian`: cotangent independence implies independence of
  gradients when the residue field is formally smooth over the base;
- `FiberRegular`: a fibre of a regular algebra over a polynomial ring is
  regular when the partial derivatives extend;
- `PolynomialFiber`: a fibre of `B₀[Y]` is a base change `K ⊗[A₀] B₀`;
- `LocalDerivation`: the derivations on completed localizations of
  polynomial rings, and regularity of their fibres;
- `SurjectiveCompletion` (Worker 5143): completion commutes with base change
  to quotients of Noetherian local rings;
- `TensorFiberRegular`: the general theorem
  `isRegularRing_tensor_fiber_adicCompletion`, assembling the above.

Each helper module has its own Markdown file describing its statements and
proofs.

## Declarations in this module

Namespace `Langlands.CommutativeAlgebra.FiniteTypeIntGRing`. Let `S` be a
commutative ring, `p` a prime of `S`, `q` an ideal of `A = S_p`,
`f : ℤ[X_1, …, X_n] →ₐ[ℤ] S` and `h₀ : R₀ →+* A ⧸ q` a ring map from a
commutative ring `R₀`.

- `quotientGen p q f h₀ : R₀[X_1, …, X_n] →+* A ⧸ q` is the evaluation map
  extending `h₀` with `X_i ↦` the image of `f (X_i)`.
- `quotientGen_map`: on the image of `P ∈ ℤ[X]` under the coefficient map
  `ℤ → R₀` it is the image of `f P`. Proof: compare the two ring maps on
  constants and variables (`MvPolynomial.ringHom_ext`); on constants both are
  the integer cast.
- `quotientGen_spec p q f h₀ hf a`: if `f` is surjective, then every
  `a ∈ A ⧸ q` satisfies `a * quotientGen v = quotientGen u` for some `u`, `v`
  with `quotientGen v` a unit. Proof: lift `a` to a fraction `s / t` of `A`
  with `t ∉ p` (`IsLocalization.mk'_surjective`), and write `s = f u`,
  `t = f v`. Take the images of `u`, `v` in `R₀[X]`. By `quotientGen_map`
  the denominator maps to the image of `t`, a unit of `A`, and
  `IsLocalization.mk'_spec` gives the equation.
- `formallySmooth_int_of_charZero K`: a field `K` of characteristic zero that
  is an essentially finite type `ℤ`-algebra is formally smooth over `ℤ`.
  Proof: `ℚ` is a localization of `ℤ`, hence formally smooth over `ℤ`
  (`Algebra.FormallySmooth.of_isLocalization`). `K` is essentially of finite
  type over `ℚ` (`Algebra.EssFiniteType.of_comp`), hence formally smooth over
  the perfect field `ℚ` (Mathlib's instance
  `Algebra.FormallySmooth.of_perfectField`). Composition gives the claim
  (`Algebra.FormallySmooth.comp`). The scalar tower `ℤ → ℚ → K` holds for the
  given `ℤ`-algebra structure on `K` because ring maps out of `ℤ` are integer
  casts (`eq_intCast`).

Namespace `Langlands.CommutativeAlgebra`:

- `finiteTypeIntGRing : FiniteTypeIntGRingStatement.{u}`.

## Proof of the main theorem

Let `S : Type u` be a finite-type `ℤ`-algebra.

1. *Noetherian.* `ℤ` is Noetherian, so `S` is
   (`Algebra.FiniteType.isNoetherianRing`).
2. *Flatness.* For a prime `p` of `S` with `A = S_p`, the completion `Â` is
   flat over the Noetherian ring `A` (Mathlib's instance
   `AdicCompletion.flat_of_isNoetherian`).
3. *Presentation.* Choose a surjection `f : ℤ[X_1, …, X_n] →ₐ[ℤ] S`
   (`Algebra.FiniteType.iff_quotient_mvPolynomial''`).
4. *Twisted fibres.* Fix a prime `q` of `A` and a finite field extension
   `k'` of `κ(q)` (in universe `u`). The claim is that
   `k' ⊗[κ(q)] q.Fiber Â` is regular. This is
   `isRegularRing_tensor_fiber_adicCompletion` (module `TensorFiberRegular`),
   applied with `g = quotientGen p q f h₀` and `hg = quotientGen_spec`, for a
   regular ring `R₀` and a map `h₀` chosen by the characteristic of `κ(q)`:
   - If `ringChar κ(q) = 0`, take `R₀ = ℤ` (regular as a Dedekind domain,
     Mathlib instance) and `h₀` the integer cast. The smoothness hypothesis
     concerns fields `K` of characteristic `0`, hence `CharZero K`
     (`ringChar.eq_iff`, `CharP.charP_to_charZero`), and is
     `formallySmooth_int_of_charZero`.
   - Otherwise `ℓ = ringChar κ(q)` is a prime (`CharP.char_prime_of_ne_zero`).
     The map `A ⧸ q → κ(q)` is injective
     (`Ideal.injective_algebraMap_quotient_residueField`), so `A ⧸ q` has
     characteristic `ℓ` (`RingHom.charP`). Take `R₀ = ZMod ℓ`, a field and
     hence regular, and `h₀ = ZMod.castHom`. The smoothness hypothesis holds
     for every essentially finite type field extension of the perfect field
     `ZMod ℓ` (Mathlib's instance `Algebra.FormallySmooth.of_perfectField`).
5. *Geometric regularity.* For finite purely inseparable `k'` this is the
   regularity half of `GeometricallyRegular κ(q) (q.Fiber Â)`. For the
   Noetherian half, apply step 4 with `k' = κ(q)`: the ring
   `κ(q) ⊗[κ(q)] q.Fiber Â` is regular, hence Noetherian, and
   `Algebra.TensorProduct.lid` identifies it with `q.Fiber Â`
   (`isNoetherianRing_of_ringEquiv`).

Together, steps 1, 2 and 5 give `IsGRing S`: Noetherianity and, for every
prime `p`, flatness of `S_p → Ŝ_p` with Noetherian geometrically regular
fibres over every prime of `S_p`.

## Imported Library results

- `Langlands.CommutativeAlgebra.FiniteTypeIntGRingStatement` and the
  definitions `IsGRing`, `RegularAlgebra`, `GeometricallyRegular` from
  `Langlands.CommutativeAlgebra.RegularRingMaps` (through the statement
  module).
- `regularLocalLocalizations` from
  `Langlands.CommutativeAlgebra.RegularLocalLocalizationsProof` (in
  `TensorFiberRegular`).
- `AdicCompletion.isNoetherianRing_of_isNoetherianRing` and the AnthropicFLT
  completion results listed in `CompletionRegular.md` and
  `SurjectiveCompletion.md`.

No G-ring, regular-completion, approximation, desingularization or Popescu
assertion is assumed; the axioms used are `propext`, `Classical.choice` and
`Quot.sound`.
