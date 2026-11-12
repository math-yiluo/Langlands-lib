# Nonempty fibres near the generic point, and non-containment of generic hyperplanes

Author: Worker 5132.

This helper module of the hyperplane-slicing step `FamilyLangWeilSlicingStatement` proves two
facts. First, a consequence of Chevalley's theorem on constructible images near the generic
point of an integral base. Second, for parameters off a proper closed subset, the hyperplane
does not contain the fibre.

## Provenance

Provenance: internal. The first result comes from Chevalley's theorem on constructible images,
in Mathlib as `PrimeSpectrum.isConstructible_comap_image`. Combined with the
Library's `exists_open_constructible_membership_on_generic`, a constructible set containing the
generic point contains a nonempty open set. The second result is the "few hyperplanes contain
the fibre" step of the proof route in the Markdown of `FamilyLangWeilSlicingStatement`, here in
spread-out form. The formulations are specific to this proof.

## Declarations

- `exists_ne_zero_forall_nontrivial_tensor Q hQ` (Chevalley near the generic point): let `R` be
  a Noetherian domain and `B` a finitely generated `R`-algebra with a prime `Q` lying over
  `(0)`. Then there is `r ≠ 0` such that `K ⊗[R] B` is nontrivial for every field `K` over `R`
  with `r ↦ r_K ≠ 0`. Proof: the image of `Spec B → Spec R` is constructible and contains the
  generic point, so it contains a basic open `D(r)` with `r ≠ 0`. For `K` as above,
  `p = ker (R → K)` lies in `D(r)`, so `κ(p) ⊗[R] B` is nontrivial
  (`PrimeSpectrum.nontrivial_iff_mem_rangeComap`). Then `K ⊗[κ(p)] (κ(p) ⊗[R] B) ≅ K ⊗[R] B` is
  nontrivial because `κ(p) → K` is injective and `K` is flat over `κ(p)`.
- `hyp_not_mem_nilradical_of_nontrivial g K α`: for coefficients `α` in an `R`-algebra `P` and a
  field `K` over `P`, assume `K ⊗[P] (P ⊗[R] A)[1/h]` is nontrivial, where `h = hyp R g α`. Then
  the hyperplane element `hyp R g (α in K)` of `K ⊗[R] A` is not nilpotent. Proof: its image in
  `K ⊗[P] (P ⊗[R] A)[1/h]` is a unit, and a unit in a nontrivial ring is not nilpotent.
- `exists_ne_zero_forall_hyp_not_mem_nilradical g hF θ`: let `R` be a Noetherian domain and `A`
  a finitely generated `R`-algebra with a point `θ : A →ₐ[R] F` in a field `F` into which `R`
  injects. Then there is a nonzero `c ∈ 𝒫 = R[a_*, a_0, …, a_{n-1}]` such that, for every field
  `K` over `R` and `β : Option (Fin n) → K` with `c(β) ≠ 0`, the element
  `β_* ⊗ 1 + ∑ᵢ βᵢ ⊗ gᵢ` of `K ⊗[R] A` is not nilpotent. Proof: let `E = Frac (F[a])`. The point
  `θ` gives `𝒫 ⊗[R] A → E`, sending the universal hyperplane element `h` to
  `a_* + ∑ᵢ aᵢ θ(gᵢ) ≠ 0`. This extends to `(𝒫 ⊗[R] A)[1/h] → E`, whose kernel is a prime lying
  over `(0) ⊂ 𝒫` because `𝒫 → E` is injective. The first result, applied over the Noetherian
  domain `𝒫`, gives `c`. For `β` with `c(β) ≠ 0`, the second result applies with `P = 𝒫` and
  the `𝒫`-algebra structure `aeval β` on `K`.
