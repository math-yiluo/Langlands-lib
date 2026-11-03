# Formal smoothness of weight subgroups with positive weights

Let `σ : TorusAction F I` be a split-torus action on a corepresented group functor
`F` with representing algebra `B` (`e : (F ⋙ forget GrpCat).CorepresentableBy B`;
see `Rational.TorusGrading`), and let `P` be a subsemigroup of the character
lattice `I → ℤ` with `0 ∉ P`. This module proves that if `B` is formally smooth
over `R`, then so is the coordinate algebra `B ⧸ weightIdeal e σ P` of the weight
subgroup `U_P = weightSubgroup e σ P` (`Rational.TorusWeightSubgroups`). All
declarations are in namespace `Langlands.GroupScheme.Corepresented`.

## Statements

Coefficient lemmas for a group algebra `A[Λ]` over a commutative ring `A`, with `Λ`
an additive commutative group and `N` an ideal of `A`:

- `coeff_mul_add_eq`: `(x * y)_{m + m'} = x_m y_{m'}` when all other products of
  coefficients contributing to `m + m'` vanish.
- `mul_eq_zero_of_mem` and `mul_eq_zero_of_forall_coeff_mem`: if `N ^ 2 = ⊥`, a
  product of two elements of `N`, or of two elements of `A[Λ]` with all
  coefficients in `N`, is zero.
- `coeff_zero_mul_of_mem`: if `N ^ 2 = ⊥` and all nonconstant coefficients of `x`
  and `y` lie in `N`, then `(x * y)_0 = x_0 y_0`.
- `coeff_zero_mul_of_supported`: if `x`, `y` are supported on `{0} ∪ P` with
  `0 ∉ P`, then `(x * y)_0 = x_0 y_0`.
- `coeffZeroHom φ h`, for an algebra map `φ : T →ₐ[S] A[Λ]` whose constant
  coefficient is multiplicative (`h`), is the algebra map `f ↦ (φ f)_0`
  (`coeffZeroHom_apply`).

Supported elements (`supportedSubalgebra I A M` for a submonoid `M`):

- `supportedMap M g` applies an algebra map `g : A →ₐ[R] A'` coefficientwise
  (`coeff_supportedMap`). It is surjective when `g` is (`supportedMap_surjective`,
  lifting coefficients by a section fixing `0`).
- For an ideal `N` of `A`, `coeff_mem_of_supportedMap_eq_zero` says that an element
  in the kernel of reduction modulo `N` has all coefficients in `N`, and
  `supportedMap_ker_sq` says that this kernel is square-zero if `N` is.

Points:

- `coord_hat_mem_supportedSubalgebra`: if the coordinates of `x` vanish on all
  weight components of weights outside `M`, the coordinates of `hat σ x` are
  supported on `M`.
- `coord_comp_eq_zero_of_mem_weightSubgroup`: for `x ∈ U_P`, the coordinate of a
  weight component of weight outside `{0} ∪ P` vanishes.
- `exponentValue_inv` (`m(t⁻¹) = (-m)(t)`), `laurentMap g` (coefficientwise
  application of `g` to group algebras), and `units_map_laurentMap` (it maps the
  inverse universal units to the inverse universal units).

Main results, assuming `Algebra.FormallySmooth R B`, `0 ∉ P`:

- `exists_lift_mem_weightSubgroup`: for an `R`-algebra `C`, an ideal `N` with
  `N ^ 2 = ⊥` and `u₀ ∈ U_P(C ⧸ N)`, there is `u ∈ U_P(C)` mapping to `u₀`.
- `formallySmooth_quotient_weightIdeal`: `B ⧸ weightIdeal e σ P` is formally smooth
  over `R`.

## Proof of the lifting theorem

Write `M = {0} ∪ P`, `Q = C ⧸ N` and `π : C → Q`.

1. Since `u₀ ∈ U_P`, the coordinates of `hat σ u₀` are supported on `M`, giving an
   algebra map `B → S_M(Q)` into the supported subalgebra. Coefficientwise
   reduction `S_M(C) → S_M(Q)` is surjective with square-zero kernel, so formal
   smoothness of `B` lifts it to `B → S_M(C)`. The point `X` over `C[I → ℤ]` with
   these coordinates maps to `hat σ u₀` and has coordinates supported on `M`.
2. Let `Y = σ.act (universalUnits I C)⁻¹ X`. By naturality of the action,
   `Y` maps to `σ.act (univ)⁻¹ (hat σ u₀) = u₀` viewed over constants. So all
   nonconstant coefficients of the coordinates of `Y` lie in `N`, and on a
   homogeneous function `h` of weight `m`, `coord Y h = coord X h · X^{-m}`.
3. Since `N ^ 2 = ⊥`, the constant coefficient of `coord Y` is an algebra map
   (`coeff_zero_mul_of_mem`); let `v` be the point over `C` with these coordinates.
   Then `v` maps to `u₀`, and for `m ∉ M`, `coord v (comp m f)` is the `m`-th
   coefficient of `coord X (comp m f)`, which is `0`.
4. Hence the coordinates of `hat σ v` are supported on `M` with `0 ∉ P`, so their
   constant coefficient is again an algebra map (`coeff_zero_mul_of_supported`);
   let `w` be the point with these coordinates, i.e. `coord w f = coord v (comp 0 f)`.
   By `comp_comp`, the weight components of `w` agree with those of `v` in weight
   `0` and vanish otherwise. Then `hat σ w` and `hat σ v` have supported
   coordinates that agree modulo the supported ideal of `P`, so
   `w⁻¹ v ∈ U_P` by `inv_mul_mem_kerSubgroup` and `weightCondition_iff`.
   Finally `w` maps to `1` over `Q`, because the weight-`0` components of `u₀` equal
   their counits (`0 ∉ P`, `eq_one_iff`, `counit_comp`). So `u = w⁻¹ v` maps to `u₀`.

For formal smoothness, `Algebra.FormallySmooth.of_comp_surjective` reduces to
lifting an algebra map `B ⧸ weightIdeal → C ⧸ N`. Its composite with the quotient
map is a point `u₀ ∈ U_P(C ⧸ N)` by `isCutOutBy_weightIdeal`; a lift `u ∈ U_P(C)`
has coordinates killing the weight ideal, and `Ideal.Quotient.liftₐ` gives the
required lift.

## Provenance

Internal supporting material for the proof of
`Langlands.GroupScheme.RelativeRoot.CyclicWeightFiltrationStatement` (task
023326af). Conrad–Gabber–Prasad, *Pseudo-reductive groups*, 2nd ed., §3.3
(the paragraph before Lemma 3.3.8, printed p.111), use that the subgroups attached
to the cyclic tails `{n • a : n ≥ j}` are smooth and connected, which they obtain
from the dynamic method (Proposition 3.3.6). This module instead gives a
self-contained infinitesimal-lifting proof of formal smoothness for any semigroup
of weights not containing `0`; the route is internal to this formalization.
