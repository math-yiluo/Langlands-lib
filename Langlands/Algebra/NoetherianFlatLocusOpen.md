# Openness of the flat locus over a Noetherian base

Author: Worker 1103.

This helper module supplies the generic-fibre and local-flatness steps for
openness of the flat locus of a finite type algebra over a Noetherian ring.
The final openness theorem is reused from the published
`Module.Flat.isOpen_setOf_flat_localization_atPrime`, imported from the
Anthropic FLT port. It is an input to
`Langlands.Algebra.FlatFinitePresentationModel` (Stacks Algebra,
Lemma 10.168.1(1)). The module adds no axioms. The main theorems live in
`Langlands.Algebra` and the helper lemmas in
`Langlands.Algebra.NoetherianFlatLocus`.

## Provenance

- The openness conclusion is the special case `M = S` with `R` Noetherian and `S` of
  finite type over `R` of Stacks Project, Algebra, Theorem 10.129.4
  (Tag 00RC). Stacks treats this Noetherian case inside the proof of 00RC,
  using exact complexes (Lemma 10.129.3).
- The helper proofs retain the route of H. Matsumura,
  *Commutative Ring Theory*, Theorem 24.3: Nagata's openness criterion
  (`Langlands.Algebra.isOpen_of_stableUnderGeneralization_of_forall_exists`,
  module `Langlands.Algebra.NagataOpennessCriterion`), generic flatness
  (`Langlands.Algebra.GenericFlatness.genFlat_of_finiteType`, by Worker 866)
  and the local flatness criterion. The local flatness criterion comes from
  the Library: `Langlands.Algebra.localFlatnessCriterion` (Stacks 10.99.7,
  Tag 00MK) and its ideal variant
  `Langlands.Algebra.idealTensor_injective_of_quotient_flat`.
- The lemmas in `NoetherianFlatLocus` are standard internal steps of that
  argument, stated separately.

## Declarations

### Helper lemmas (`Langlands.Algebra.NoetherianFlatLocus`)

`rTensor_map_injective`: let `R'` be a localization of `A` at a submonoid `S`
and `X` an `R'`-module. If `J ⊗[A] X → X` is injective for an ideal `J` of
`A`, then `J R' ⊗[R'] X → X` is injective. The proof builds the comparison map
`ψ : J ⊗[A] X → J R' ⊗[R'] X`, `a ⊗ x ↦ a ⊗ x`, and shows it is surjective:
an element `y ∈ J R'` has the form `a / s` with `a ∈ J`, and
`y ⊗ x = ψ (a ⊗ (1/s) x)`. The map `ψ` commutes with the two inclusions into
`X`. So injectivity of the first inclusion gives injectivity of the second.

`exists_forall_rTensor_injective`: let `B` be a Noetherian `A`-algebra, `I` an
ideal of `A` that is finite as an `A`-module, and `Q` a prime of `B`. If
`I ⊗[A] B_Q → B_Q` is injective, then some `g ∉ Q` makes
`I ⊗[A] B_{Q'} → B_{Q'}` injective for every prime `Q'` with `g ∉ Q'`.
Proof: let `K` be the kernel of `B ⊗[A] I → B ⊗[A] A`, a finite `B`-module
since `B` is Noetherian. Localizing at `Q` kills `K`, so `Q` is outside the
support of `K` and some `g ∉ Q` annihilates `K`. For `Q'` with `g ∉ Q'`,
write an element of the kernel at `Q'` as `w / s` with `w ∈ B ⊗[A] I`. Some
`t ∉ Q'` puts `t w` in `K`, so `g t w = 0` and the element is zero.

`flat_atPrime_of_le`: if `Q' ≤ Q` are primes of `B` and `B_Q` is flat over
`A`, then `B_{Q'}` is flat over `A`, since `B_{Q'}` is a localization of
`B_Q`.

`flat_of_isLocalization_of_flat_away`: if `Y` is a localization of a ring `C`
at a submonoid containing `c` and `C[1/c]` is flat over `R`, then `Y` is flat
over `R`, since `Y` is a localization of `C[1/c]`.

`flat_quotient_tensor_atPrime`: let `p` be an ideal of `A` and `a ∈ A`. If
`((A ⧸ p) ⊗[A] B)[1/a]` is flat over `A ⧸ p` and the image of `a` in `B` is not
in the prime `Q'`, then `(A ⧸ p) ⊗[A] B_{Q'}` is flat over `A ⧸ p`. The proof
identifies `(A ⧸ p) ⊗[A] B_{Q'}` with a localization of `(A ⧸ p) ⊗[A] B`
(Mathlib's `IsLocalization.tensorProduct_tensorProduct_right`) at a submonoid
containing the image of `a`, and applies the previous lemma.

`flat_atPrime_of_rTensor_injective`: the local flatness criterion at a prime
`Q'` of `B`, for Noetherian `A` and `B`. Let `p` be an ideal of `A` contained
in `Q' ∩ A`. If `p ⊗[A] B_{Q'} → B_{Q'}` is injective and
`(A ⧸ p) ⊗[A] B_{Q'}` is flat over `A ⧸ p`, then `B_{Q'}` is flat over `A`.
Proof: the Library's ideal variant gives injectivity for the larger ideal
`p' = Q' ∩ A`. By `rTensor_map_injective` this holds for the maximal ideal
`p' A_{p'}` of the local ring `A_{p'}`. The local flatness criterion for the
local homomorphism `A_{p'} → B_{Q'}` then makes `B_{Q'}` flat over `A_{p'}`,
hence over `A`.

### Main theorems (`Langlands.Algebra`)

`isOpen_flatLocus_of_generic`: let `A` be Noetherian and `B` a finite type
`A`-algebra. Assume that for every prime `p` of `A` there is `a ∉ p` with
`((A ⧸ p) ⊗[A] B)[1/a]` flat over `A ⧸ p`. Then the set of primes `Q` of `B`
with `B_Q` flat over `A` is open in `Spec B`. Proof by Nagata's criterion on
the Noetherian ring `B`. The set is stable under generization by
`flat_atPrime_of_le`. Given `Q` in the set, put `p = Q ∩ A`. Flatness of
`B_Q` makes `p ⊗[A] B_Q → B_Q` injective, so
`exists_forall_rTensor_injective` gives `g ∉ Q`. The hypothesis gives
`a ∉ p`. For every prime `Q' ⊇ Q` avoiding `a g`, the lemmas
`flat_quotient_tensor_atPrime` and `flat_atPrime_of_rTensor_injective` (with
the ideal `p ≤ Q' ∩ A`) show that `B_{Q'}` is flat over `A`.

`exists_flat_away_quotient_tensor`: for Noetherian `A`, a finite type
`A`-algebra `B` and a prime `p` of `A`, some `a ∉ p` makes
`((A ⧸ p) ⊗[A] B)[1/a]` flat over `A ⧸ p`. This is the flatness form of
generic flatness (Stacks Algebra, Lemma 10.118.1, Tag 051R) over the
Noetherian domain `A ⧸ p`.
The Lean proof applies Worker 866's `genFlat_of_finiteType` to the module
`(A ⧸ p) ⊗[A] B` over itself. This gives a nonzero `d ∈ A ⧸ p` such that
the localized module at the powers of `d` is flat. Then `d` is lifted to
`a ∈ A`, and the localized module is identified with the localization
`Localization.Away` of the ring.

The imported `Module.Flat.isOpen_setOf_flat_localization_atPrime` states
openness of the same flat locus. The two preceding helper theorems also
derive that proposition, so the integrated Library keeps the existing
public declaration instead of introducing a duplicate final theorem.
