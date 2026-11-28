# A regular local chart cut out by one equation in a localized polynomial ring

Module `Langlands.CommutativeAlgebra.ArithmeticRegularLocalApproximation.LocalChart`.

This module is an internal step of the proof of
`Langlands.CommutativeAlgebra.ArithmeticRegularLocalApproximationStatement`. Starting from a
regular finite type `R₀`-algebra `D` mapping to a local ring `Λ` that maps locally to `W'`, it
builds the ring `P` that is completed in
`Langlands.CommutativeAlgebra.ArithmeticRegularLocalApproximation.Chart`. First localize `D[X]`
at the inverse image of the maximal ideal of `W'` under evaluation at `ϖ`.
The image of `F_D` is a regular parameter in this localization. Quotienting by it gives an
essentially finite type regular local `R₀`-algebra `P` with a local homomorphism `P → W'` induced
by evaluation at `ϖ`.

In the proof of Deligne, SGA 7 I, Exposé I, Lemma 0.5.1, the corresponding regular algebras come
from Néron desingularization of finite type subalgebras of the trait. Here regularity of `P`
follows from the regularity of `D` and the regular parameter property of the image of `F_D`.

## Local homomorphisms out of localizations and quotients

- `isUnit_of_mem_primeCompl_comap f Q hQ s`: for `f : A → B` with `B` local and
  `Q = f⁻¹(𝔪_B)`, every `s ∉ Q` maps to a unit of `B`.
- `isLocalHom_lift_atPrime f Q hQ`: with the same hypotheses, the extension
  `IsLocalization.lift : A_Q → B` of `f` is a local homomorphism. If `a / s` maps to a unit,
  then `f a = (image of a/s) · f s` is a unit, so `a ∉ Q` and `a / s` is a unit of `A_Q`
  (`IsLocalization.AtPrime.isUnit_mk'_iff`).
- `isLocalHom_quotient_lift I f hI`: a local homomorphism `f : A → B` vanishing on `I` induces
  a local homomorphism `A ⧸ I → B`; a preimage of a unit is a unit already in `A`.

## Main theorem

`exists_regularChart` assumes:

- `R₀ : Type u` is a commutative ring all of whose elements are integers
  (`Int.castRingHom R₀` is surjective);
- `W'` is a local ring and `ϖ` lies in its maximal ideal;
- `ψ : Λ → W'` is a local homomorphism of local rings;
- `D` is a finite type `R₀`-algebra which is a regular ring, and `h : D → Λ` is a ring map;
- `F_D ∈ D[X]` satisfies `F_D(ϖ) = 0`, where `D[X] → W'` is `eval₂ (ψ ∘ h) ϖ`;
- `h` of the constant coefficient of `F_D` does not lie in `𝔪_Λ²`.

It concludes that there are a regular local ring `P : Type u` with finitely generated residue
field, a local homomorphism `P → W'`, and a ring map `π : D[X] → P` with
`(P → W') ∘ π = eval₂ (ψ ∘ h) ϖ` and `π F_D = 0`.

Proof. Write `Φ = eval₂ (ψ ∘ h) ϖ : D[X] → W'` and `ev₀ = eval₂ h 0 : D[X] → Λ`.

1. For every `s ∈ D[X]`, `Φ s - ψ (ev₀ s)` is the difference of the values at `ϖ` and at `0`
   of the polynomial `s` mapped to `W'[X]`. It is divisible by `ϖ - 0`
   (`Polynomial.sub_dvd_eval_sub`), hence lies in `𝔪_{W'}`.
2. Hence `Q := Φ⁻¹(𝔪_{W'})` equals `ev₀⁻¹(𝔪_Λ)`, since `ψ` is local: `ev₀ s ∈ 𝔪_Λ` if and
   only if `ψ (ev₀ s) ∈ 𝔪_{W'}`. The ideal `Q` is prime.
3. Let `R' = D[X]_Q`. It is a regular local ring, because `D[X]` is a regular ring
   (Mathlib's instance for polynomial rings over regular rings). Both `Φ` and `ev₀` extend to
   local homomorphisms `Φ' : R' → W'` and `ev : R' → Λ` by `isLocalHom_lift_atPrime`.
4. Let `x` be the image of `F_D` in `R'`. Then `Φ' x = 0`, so `x ∈ 𝔪_{R'}`. If `x` lay in
   `𝔪_{R'}²`, the local map `ev` would send it into `𝔪_Λ²`; but `ev x = ev₀ F_D = h (F_D(0))`,
   the image of the constant coefficient (`Polynomial.eval₂_at_zero`), which is not there.
   Hence `P := R' ⧸ (x)` is a regular local ring by
   `RegularLocalFactorial.isRegularLocalRing_quotient_span_singleton`.
5. `Φ'` vanishes on `(x)` and induces a local map `P → W'` (`isLocalHom_quotient_lift`). Put
   `π = (R' → P) ∘ (D[X] → R')`; then `(P → W') ∘ π = Φ` and `π F_D = 0`.
6. Every element of the residue field of `P` is the image of some `a / s` with `a, s ∈ D[X]`,
   hence a quotient of values of the composite `D[X] → P → κ(P)`. Since `D[X]` is of finite
   type over `R₀`, `fieldFG_of_forall_eq_div` (module
   `Langlands.CommutativeAlgebra.ArithmeticRegularLocalApproximation.ResidueFields`) shows that
   the residue field is finitely generated.
