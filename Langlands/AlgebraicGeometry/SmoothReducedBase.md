# Smooth algebras and schemes over a reduced base are reduced

Module `Langlands.AlgebraicGeometry.SmoothReducedBase`.

## Results

- `isReduced_of_smooth_of_isNoetherianRing`: a smooth algebra over a noetherian reduced ring is
  reduced.
- `isReduced_of_smooth`: a smooth algebra over any reduced commutative ring is reduced.
- `isReduced_of_smooth_over_spec`: a scheme with a smooth morphism to `Spec R` is reduced if
  `R` is reduced.
- `isReduced_of_smooth_of_isReduced`: a scheme with a smooth morphism to a reduced scheme is
  reduced.

The Library module `Langlands.AlgebraicGeometry.SmoothReducedProof` has these results only over
a domain or a field (`isReduced_of_smooth_of_domain`, `isReduced_of_smooth_over_field`). The
Mathlib instances that make a fibre product reduced need a locally noetherian base. This module
removes both restrictions. The local-ring Isomorphism Theorem needs it: fibre products of smooth
schemes over a reduced, possibly non-noetherian, local ring must be reduced.

## Proof

1. Noetherian base. Let `B` be noetherian and reduced, and let `S` be a smooth `B`-algebra.
   `B` has finitely many minimal primes (`minimalPrimes.finite_of_isNoetherianRing`). Their
   intersection is the nilradical (`Ideal.sInf_minimalPrimes`), which is zero, so the map
   `B → ∏ B ⧸ p` is injective. `S` is flat over `B`, so the map stays injective after tensoring
   with `S`. Let `x ∈ S` be nilpotent. In each factor `(B ⧸ p) ⊗[B] S` the image `1 ⊗ x` is
   nilpotent. That factor is smooth over the domain `B ⧸ p`, so it is reduced by the Library's
   `isReduced_of_smooth_of_domain`, and `1 ⊗ x = 0` there. Mathlib's
   `TensorProduct.piLeft` turns these zeros into `1 ⊗ x = 0` in `(∏ B ⧸ p) ⊗[B] S`. By
   injectivity, `1 ⊗ x = 0` in `B ⊗[B] S`, so `x = 0`.
2. General base. Let `R` be reduced and `A` a smooth `R`-algebra. Mathlib's
   `Algebra.Smooth.exists_subalgebra_fg` gives a finitely generated subring `A₀ ⊆ R`, a smooth
   `A₀`-algebra `B₀`, and an `R`-algebra isomorphism `A ≃ R ⊗[A₀] B₀`. `A₀` is noetherian
   (Hilbert basis theorem, `Algebra.FiniteType.isNoetherianRing`) and reduced, being a subring
   of `R`. Mathlib's `IsReduced.tensorProduct_of_flat_of_forall_fg`, applied to the flat
   `A₀`-algebra `B₀`, reduces the reducedness of `B₀ ⊗[A₀] R` to that of `B₀ ⊗[A₀] D` for the
   finitely generated `A₀`-subalgebras `D ⊆ R`. Each such `D` is noetherian and reduced, and
   `D ⊗[A₀] B₀` is smooth over `D`, so step 1 applies. Commuting the tensor factors and
   transporting along `A ≃ R ⊗[A₀] B₀` gives that `A` is reduced.
3. Schemes over `Spec R`. This copies the Library proof of `isReduced_of_smooth_over_field`.
   On each affine chart `U` of `X`, the ring map `R → Γ(U)` is smooth, so `Γ(U)` is reduced by
   step 2, and `U` is reduced. Reducedness is checked on an open cover.
4. Schemes over a reduced scheme `S`. Pull the affine open cover of `S` back along `f`. Each
   piece is smooth over an affine open `Spec Rᵢ` of `S` (`pullback.snd`). `Rᵢ` is reduced
   because `Spec Rᵢ` is (`affine_isReduced_iff`), so step 3 applies.

## Provenance

That a scheme smooth over a reduced scheme is reduced is a standard fact of scheme theory. The
proof above is written for this module. It is built from the Library's domain case and from the
Mathlib results named above; it does not follow a particular printed source.
