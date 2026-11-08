# The stabilizer of the standard restricted apartment

For a supplied abstract Tits system `h : IsTitsSystem B N π S`, this module
proves that, when the system is saturated (axiom TS 5,
`IsSaturated B N : ⋂_{n ∈ N} n B n⁻¹ = B ∩ N`), the elements `g` with
`restrictedApartment B π S g = restrictedApartment B π S 1` are exactly the
elements of `N`. Here `restrictedApartment B π S g` is the existing set of
parabolic subgroups `(g n) G_X (g n)⁻¹` with `n ∈ N` and `X` admissible. Since
`restrictedApartment B π S g` is the conjugate of the standard apartment by
`g` (existing `image_conjugateSubgroup_restrictedApartment`), this is the
statement that the stabilizer of the standard apartment under conjugation is
`N`, for the restricted building of KP Proposition 1.5.18.

Source correspondence: the proof of KP Proposition 7.6.8 (book p. 266) uses
this equality for `G(k)^0` and attributes it to Proposition 1.5.13. The printed
statement of Proposition 1.5.13 (p. 60) does not contain it, and the 2024
corrections add no such clause. This module therefore does not cite it as a
statement of Proposition 1.5.13. It proves the equality directly, from Bruhat
disjointness and the saturation axiom TS 5 (KP Definition 1.4.1). It is an
internal deduction from the existing Tits-system, Borel-chamber and
restricted-apartment APIs.

## Chambers of an apartment

`standardParabolicSubgroup_empty` identifies `G_∅` with `B`.
`conjugate_borel_mem_restrictedApartment` shows that the apartment based at `a`
contains every chamber `(a n) B (a n)⁻¹`, `n ∈ N`. In particular
`borel_mem_restrictedApartment_one` puts `B` in the standard apartment.

`exists_mul_mem_of_borel_mem`: if `B` lies in the apartment based at `a`,
then `B = (a n) G_X (a n)⁻¹` for some `n` and admissible `X`. So
`(a n) B (a n)⁻¹ ≤ B`, and the existing `conjugate_borel_le_iff` gives
`a n ∈ B`.

`mem_conjugate_borel_of_mem` is the key Bruhat argument. Let `b ∈ B`, and
suppose the apartment based at `b` contains `m B m⁻¹` for some `m ∈ N`. Then
`m B m⁻¹ = (b n) G_X (b n)⁻¹ ⊇ (b n) B (b n)⁻¹`. Inclusion of Borel conjugates
is equality (existing `conjugate_borel_eq_of_le`), so
`k = m⁻¹ b n ∈ B` (existing `conjugate_borel_eq_iff`). The element `m⁻¹ b`
lies in the cell `C(π(m)⁻¹)` and also, as `k n⁻¹`, in the cell `C(π(n)⁻¹)`.
Bruhat disjointness gives `π(m) = π(n)`. Hence `m⁻¹ n` lies in the kernel
of `π`, which is in `B`. Then `m⁻¹ b m = k (m⁻¹ n)⁻¹ ∈ B`, that is,
`b ∈ m B m⁻¹`.

## The stabilizer subgroup

`restrictedApartmentStabilizer` is the subgroup of elements `g` whose
apartment `restrictedApartment B π S g` is the standard apartment, that is,
the stabilizer of the standard apartment under conjugation. It is closed
under products and inverses because conjugating the apartment based at `k` by
`g` gives the apartment based at `g k` (existing
`image_conjugateSubgroup_restrictedApartment`).

## Saturated systems

The remaining results assume `hsat : IsSaturated B N`.

`mem_normalizer_of_forall_mem`: if `b ∈ B` and the apartment based at `b`
contains every `m B m⁻¹` (`m ∈ N`), then `b` lies in every `m B m⁻¹`. By
saturation `b ∈ B ∩ N`.

`restrictedApartment_eq_one_of_forall`: an apartment containing every
chamber `m B m⁻¹` of the standard apartment is the standard apartment. It
contains `B`, so after right multiplication by some `n ∈ N` (existing
`restrictedApartment_mul_normalizer`) its base point `a n` lies in `B`. By the
previous lemma, `a n ∈ N`, so the apartment is the standard one.

`mem_normalizer_of_restrictedApartment_eq` proves that `g ∈ N` when the
apartment based at `g` is the standard apartment. That apartment contains `B`,
so `g n ∈ B` for some `n ∈ N`. It also contains every `m B m⁻¹`, so
`g n ∈ N` and `g ∈ N`. `restrictedApartment_eq_one_iff` adds the converse from
`restrictedApartment_mul_normalizer`. `restrictedApartmentStabilizer_eq`
restates this as equality of the stabilizer subgroup with `N`.

## Scope

These are statements about an arbitrary supplied saturated Tits system. They
do not concern any valuation quotient or its apartments, and prove no witness
of `RootValuationBuildingConstructionStatement`.
