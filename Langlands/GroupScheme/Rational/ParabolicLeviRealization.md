# One cocharacter realizing a rational parabolic and a rational Levi

Authors: Worker 1491 and Worker 1294.

This module shows that a rational parabolic `j : P → G` of a connected reductive
group `G` over a field `k`, together with a rational Levi `l : L → P` of it, is
the dynamic parabolic and dynamic centralizer of one cocharacter. It is
conditional on two published statements, which appear as explicit hypotheses:

- `ParabolicDynamicStatement`: every rational parabolic `j : P → G` of a
  connected reductive `G` has `range j = P_G(χ)` for some cocharacter `χ`.
- `DynamicGeometricUnipotentRadicalStatement`: a closed representative of
  `U_G(χ)`, factored through a representative of `P_G(χ)`, is a geometric
  unipotent radical (`IsGeometricUnipotentRadical`).

Nothing else is assumed. The torus-lift step uses the proved theorem
`Dynamic.exists_unipotent_conj_of_mul_inv_mem` (Worker 1515), and the remaining
steps use the lemmas of `Rational.DynamicLeviConjugacyReduction`.
The two structural statements are assumptions, not proved by this module.
Worker 1491 supplied the simultaneous-realization proof and its supporting
transport lemmas; Worker 1294 added the chosen cocharacter and its specification.

## Mathematical source and provenance

The statement is internal. It packages the first half of the argument in
`Rational.DynamicLeviConjugacyReduction` for use by other proofs. Over an
algebraically closed field it is the standard fact that a Levi subgroup of
`P_G(χ)` is `Z_G(χ')` for a `U_G(χ)`-conjugate `χ'` of `χ`. Compare
Conrad–Gabber–Prasad, *Pseudo-reductive groups* (2nd ed., 2015),
Proposition 2.1.8(2) (printed p.53, PDF p.79), for `P_G(χ) = Z_G(χ) ⋉ U_G(χ)`. The
proof here is derived from the Library results named below. It does not follow a
particular source.

## Declarations

- `range_eq_of_range_comp_inv_eq f e F h`: over any base, for `f : H → G`, an
  automorphism `e : G ≅ G` and a subgroup functor `F` of `G`, if
  `range (f ≫ e⁻¹) = e^{-1}(F)` (`F.comap e.hom`), then `range f = F`. Both
  inclusions are checked on points of every test scheme.
- `parabolic_comp_innerIso_eq χ hu`: over any base, if the base point `u` lies in
  `P_G(χ)`, then `P_G(χ ≫ Int(u)) = P_G(χ)`. Write `c` for the constant point of
  `u` on a test scheme `T`. By `Dynamic.parabolic_eq_comap_of_iso` and
  `comp_innerIso_hom`, `y ∈ P_G(χ)(T)` if and only if
  `c y c⁻¹ ∈ P_G(χ ≫ Int(u))(T)`. Apply this to `y = c⁻¹ x c`, and use
  `c ∈ P_G(χ)(T)`.
- `exists_cocharacter_parabolic_levi hPD hGUR hG hj hl`: for a field `k`, a
  connected reductive `G`, a parabolic `j : P → G` (`IsParabolicSubgroup j`) and
  a rational Levi `l : L → P` (`IsRationalLeviSubgroup l`), there is a
  cocharacter `ψ : 𝔾_m → G` with

  - `range j = P_G(ψ)` and
  - `range (l ≫ j) = Z_G(ψ)`,

  as subgroup functors, that is, on every test scheme over `Spec k`.
- `parabolicLeviRealizingCocharacter hPD hGUR hG hj hl` chooses such a
  cocharacter. Its companion theorem
  `parabolicLeviRealizingCocharacter_spec` gives both image equalities for that
  single choice and the original supplied morphisms.

## Proof of `exists_cocharacter_parabolic_levi`

1. `ParabolicDynamicStatement` gives `χ` with `range j = P_G(χ)`. So `j`
   represents `P_G(χ)`.
2. `IsRationalLeviSubgroup.exists_unipotentRadical_retraction` gives a geometric
   unipotent radical `r : U → P` and a retraction `q : P → L` with `l ≫ q = 𝟙`
   whose kernel is `range r`. By `mem_range_radical_iff`, which uses
   `DynamicGeometricUnipotentRadicalStatement`, this kernel consists of the
   points `x` of `P` with `x ≫ j ∈ U_G(χ)`.
3. By `leviCocharacter_mul_inv_mem`, the Levi cocharacter
   `χ_L = (χ factored through j) ≫ q ≫ l ≫ j` satisfies
   `χ_L · χ⁻¹ ∈ U_G(χ)(𝔾_m)`. Then `Dynamic.exists_unipotent_conj_of_mul_inv_mem`
   gives a rational point `v ∈ U_G(χ)(k)` with `χ ≫ Int(v) = χ_L`.
4. Take `ψ = χ ≫ Int(v)`. Since `v ∈ U_G(χ)(k) ⊆ P_G(χ)(k)`,
   `parabolic_comp_innerIso_eq` gives `P_G(ψ) = P_G(χ) = range j`.
5. `range_comp_innerIso_inv_eq_centralizer` gives
   `range (l ≫ j ≫ Int(v)⁻¹) = Z_G(χ)`. By `Dynamic.centralizer_eq_comap_of_iso`,
   `Z_G(χ)` is the preimage of `Z_G(ψ)` under `Int(v)`. So
   `range_eq_of_range_comp_inv_eq` gives `range (l ≫ j) = Z_G(ψ)`.
