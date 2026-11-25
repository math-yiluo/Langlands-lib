# Spectrally close maps out of an unramified algebra are equal

This is a helper module of `QuasiEtaleLiftCompatibilityProof`. It contains
the analytic form of the algebraic core of the uniqueness in Berkovich's Key
Lemma 7.2 (*Vanishing cycles for formal schemes*, 1994, §7, printed p.560).
The route is the diagonal trick of `DiagonalAnnihilator`, not Berkovich's
Krasner-lemma argument.

- `spectrum_sum_le`: points of a Banach spectrum are subadditive on finite
  sums.
- `spectrum_apply_le_norm`: for a bounded `K`-algebra map `φ : S → C` and a
  point `x` of the spectrum of `C`, `x (φ a) ≤ ‖a‖`. This holds because
  `BanachSpectrum.comap φ x` is a point of the spectrum of `S`.
- `exists_unramified_rigidity_bound`: let `f : R → S` be a bounded map of
  finite type between normed `K`-algebras, and let `e ∈ S` kill `Ω[S⁄R]` (for
  the algebra structure given by `f`). Then there are a finite set `G ⊆ S`,
  an exponent `n` and a constant `M ≥ 0` with the following property. Let
  `φ₁ φ₂ : S → C` be bounded `K`-algebra maps to a presented affinoid algebra
  that agree on the image of `f`. Suppose that every point `x` of the spectrum
  of `C` satisfies `M · ∑_{g ∈ G} x(φ₁ g - φ₂ g) < x(φ₁ e)ⁿ`. Then `φ₁ = φ₂`.

Proof of the last statement. `G` is a finite set of generators of `S` over
`R`. Take `n` and `c_g` from `exists_diagonal_annihilator`. Write each `c_g`
as a finite sum of pure tensors `∑ a ⊗ b` (`TensorProduct.exists_finset`).
Let `M_g = ∑ ‖a‖ ‖b‖`, and let `M = ∑_g M_g`. Let `Ψ` be the map from
`exists_tensorProduct_lift`. At a point `x`, `spectrum_apply_le_norm` gives
`x(Ψ c_g) ≤ M_g`. Therefore
`x(Ψ t) ≥ x(φ₁ e)ⁿ - M · ∑_g x(φ₁ g - φ₂ g) > 0`, so `Ψ t` vanishes at no
point. By the Library's
`PresentedAffinoidAlgebra.isUnit_iff_forall_ne_zero`, `Ψ t` is a unit, and
`eq_of_isUnit_image` gives `φ₁ = φ₂`.
