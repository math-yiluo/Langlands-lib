# Places below a common extension along an isomorphism of subfields

This module was written for the proof that the Mackey components at the auxiliary place are
distinct under Harris's exact-stabilizer condition. It compares places of two isomorphic subfields
that lie below the same place of a larger field. It is used to transport spectral data along
an isomorphism between two subfields of one number field `L`.

## Transport

Let `K`, `K'`, `L` be number fields with algebra maps `K → L` and `K' → L`, and let
`e : K ≃+* K'` satisfy `algebraMap K' L (e x) = algebraMap K L x` for all `x`. Let `u` be a
finite place of `L` (a height-one prime of `𝓞 L`).

- `finitePlaceEquiv_under`: `finitePlaceEquiv e (u.under (𝓞 K')) = u.under (𝓞 K)`. Here
  `finitePlaceEquiv e` is the published bijection between finite places of `K'` and of `K`
  that pulls a prime back along `e`. Both sides consist of the `x ∈ 𝓞 K` whose image in
  `𝓞 L` lies in `u`.
- `inertiaDeg_eq_of_ringEquiv`: the inertia degree of `u` over `K` equals that over `K'`.
  The ring isomorphism `𝓞 K ≃+* 𝓞 K'` induced by `e` maps the prime below `u` in `𝓞 K` onto
  the prime below `u` in `𝓞 K'` (previous item). It therefore gives an isomorphism of
  residue fields that is compatible with their maps into the residue field of `u`, and the
  two residue degrees agree (`Algebra.finrank_eq_of_equiv_equiv`).

## Degree one

- `inertiaDeg_eq_one_of_finrank_eq_one`: if `[L : K] = 1`, every finite place of `L` has
  inertia degree `1` over `K`. The published identity `Σ e_i f_i = [L : K]` over the places
  above `u ∩ K` forces `e f ≤ 1` for `u`, and both factors are positive.

## Provenance

Standard algebraic number theory (Neukirch, Algebraic Number Theory, I.8), stated for the
Library's `finitePlaceEquiv`. Internal to the project.
