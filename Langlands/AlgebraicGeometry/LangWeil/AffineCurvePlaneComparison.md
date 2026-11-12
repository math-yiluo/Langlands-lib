# Affine curves over a domain and plane curves over finite fields

Lean module: `Langlands.AlgebraicGeometry.LangWeil.AffineCurvePlaneComparison`, namespace
`Langlands.AlgebraicGeometry.LangWeil.CurvePlane`.

This module is the affine algebraic core of the proof of
`Langlands.AlgebraicGeometry.LangWeil.FamilyCurvePlaneComparisonStatement` (Task 5581).
The scheme-theoretic reduction to it is in `FamilyCurvePlaneReduction` (Worker 189).

## The statement `AffineCurvePlaneComparison`

`AffineCurvePlaneComparison : Prop` says: let `A` be a Noetherian domain with fraction field
`K`, and `R` a finitely generated `A`-algebra such that

- the nilradical of `AlgebraicClosure K ⊗[A] R` is prime (the geometric generic fibre is
  irreducible), and
- `K ⊗[A] R` has Krull dimension `1` (the generic fibre is a curve).

Then there are a nonzero `a : A` and `B : ℕ` such that for every finite field `κ` in the
same universe with an `A`-algebra structure in which `a` is nonzero and with `B < #κ`,
there is a polynomial `p ∈ κ[X 0, X 1]` that is irreducible over `AlgebraicClosure κ`, has
degree in each variable between `1` and `B`, and whose number of zeros in `κ²` differs from
the number of `A`-algebra maps `R → κ` by at most `B`.

Provenance: derived; an internal intermediate statement. It is the affine, generic-fibre
form of the plane-model comparison in the curve case of Lang–Weil: Lang and Weil,
*Number of points of varieties in finite fields* (1954; registered source
`lang-weil-1954-number-of-points`), p.819, and Tao, *The Lang–Weil bound* (2012;
registered source `tao-2012-lang-weil-bound`), Section 2, reduce a curve to a birational
plane model with a bounded change in point counts. Neither states this exact assertion.
The hypothesis `B < #κ` is not used by the proof; it is kept to match the target
statement. The proof below does not use that `A` is Noetherian either; that hypothesis is
kept because the reduction supplies it.

## Auxiliary lemmas

- `ringKrullDim_quotient_of_le_nilradical`: quotienting by an ideal of nilpotents keeps the
  Krull dimension (the zero locus is all of `Spec`).
- `nilradical_tensor_isPrime_of_algebraicClosure`: if `AlgebraicClosure F ⊗[A] B` has prime
  nilradical, so does `F ⊗[A] B` (it injects via `cancelBaseChange` and `includeRight`;
  Library `nilradical_isPrime_of_injective`).
- `finite_algHom_of_finiteType`: a finite type algebra has finitely many algebra maps to a
  finite ring (they are determined by the images of generators).
- `card_eq_card_subtype_add_card_subtype_not`, `eval_map_eq_eval_uniqueAlgEquiv`: counting
  and bookkeeping between `MvPolynomial (Fin 1)` and `Polynomial`.

## Dimension of the generic fibre of a Noether normalization

`ringKrullDim_tensor_eq_of_integral_after_away`: if `z : Fin d → C` is algebraically
independent over `A`, every `r ^ n • c` is integral over `A[z]` and `r` is nonzero in the
field `K`, then `K ⊗[A] C` has Krull dimension `d`. *Proof.* `aeval (1 ⊗ z)` from
`K[X_1, …, X_d]` into `K ⊗[A] C` is injective (Library
`tensor_aeval_injective_of_integral_after_away`) and integral, since `r` becomes a unit;
integral injective extensions keep the dimension and `K[X_1, …, X_d]` has dimension `d`
(Library lemmas `ringKrullDim_eq_of_isIntegral_of_injective` and
`ringKrullDim_mvPolynomial_fin` from the module
`Langlands.AnthropicFLT.P2M.Sol.S_Ideal_height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType`).

## Count on one finite field

`abs_card_sub_card_zeros_le`: for a one-dimensional hypersurface model `(z, w, F, g, r, q, e)`
of `C` (as in `CurvePlaneFibrePoints.card_algHom_good_eq`), a finite field `κ` in which `F`
stays irreducible, `r` and the leading coefficient of `g` are nonzero, and a bound `N` on the
`A`-algebra maps `C ⧸ (g(z)) → κ`,
`|#(C →ₐ[A] κ) - #zeros(planePoly F_κ)| ≤ N + deg g · deg F`.

*Proof.* Split both sides by whether `g(z)` (respectively `g` at the `Z`-coordinate) vanishes.
The two "good" parts have equal size: `card_algHom_good_eq` followed by `algHomEquivZeros`.
The bad points of `C` factor through `C ⧸ (g(z))`, so there are at most `N`; the bad zeros
number at most `deg g · deg F` by `card_zeros_planePoly_root_le`. Hence the difference of
the totals lies between `-deg g · deg F` and `N`.

## The case of a domain

`exists_bound_of_isDomain`: the conclusion (without `B < #κ`) for a finite type `A`-algebra
`C` that is a domain with `A → C` injective, with prime nilradical of
`AlgebraicClosure K ⊗[A] C` and `dim K ⊗[A] C = 1`.

*Proof.*

1. The fraction field of `C` contains no element separable over the fraction field of `A`
   outside it (Library `nilradical_tensor_fractionField_isPrime` and
   `forall_isSeparable_mem_range_of_tensor_nilradical_isPrime`).
2. The Library lemma `exists_hypersurfaceModel_uniform_of_separablyClosed_range` gives a
   hypersurface model `(r, d, z, w, F, g, q, e)` with `F` absolutely irreducible over the
   algebraic closure of the fraction field. By the dimension lemma, `d = 1`.
3. Absolute irreducibility spreads: the Library theorem
   `MvPolynomial.exists_ne_zero_and_forall_irreducible_map_of_irreducible_map_algebraicClosure`,
   applied to `G = planePoly F`, gives `b ≠ 0` such that `G` stays irreducible under every
   ring map to a field not killing `b`; in particular over `κ` and over `AlgebraicClosure κ`.
4. `1 ⊗ g(z)` is not nilpotent in `K ⊗[A] C` (it is the image of the nonzero `g` under the
   injective `aeval`), so `K ⊗[A] (C ⧸ (g(z)))` has dimension zero
   (`fiber_quotient_krullDimLE_zero` in the companion module `CurvePlaneZeroDimensional`),
   and `exists_card_algHom_le_of_krullDimLE_zero` (same module) gives
   `a₀ ≠ 0` and `N` bounding the `κ`-points of `C ⧸ (g(z))` when `a₀` is nonzero in `κ`.
5. Take `a = r · b · a₀ · lc(g)` and `B = deg F + deg_Z G + N + deg g · deg F`. For `κ` with
   `a ↦ ≠ 0`, the count lemma gives the bound with `p = planePoly F_κ`, whose `X 0`-degree is
   `deg F > 0` (an irreducible monic `F_κ` is not constant) and whose `X 1`-degree is at most
   `deg_Z G`. If its `X 1`-degree is `0`, `p` is replaced by the diagonal `X 0 - X 1`, which
   has degree `1` in each variable and, like `planePoly F_κ` in that case, exactly `#κ`
   zeros (`card_zeros_planePoly_of_degreeOf_one_eq_zero`).

## Main theorem

`affineCurvePlaneComparison : AffineCurvePlaneComparison`.

*Proof.* Let `I ⊆ R` be the preimage of the nilradical of `AlgebraicClosure K ⊗[A] R`
under `r ↦ 1 ⊗ r`. It is prime, and `C = R ⧸ I` is a domain into which `A` injects (the
image of a nonzero element of `A` in `AlgebraicClosure K ⊗[A] R` is a unit, so it is not in
the nilradical, a proper ideal).
By the Library lemma `nilradical_tensor_quotient_isPrime_iff`, `AlgebraicClosure K ⊗[A] C`
still has prime nilradical; `K ⊗[A] C ≅ (K ⊗[A] R) ⧸ I·(K ⊗[A] R)` by
`tensorQuotientEquiv`, a quotient by nilpotents (Library
`nilpotent_tensor_of_algebraicClosure`), so it still has dimension `1`. The domain case
gives `a` and `B` for `C`. The Library lemma `exists_ne_zero_forall_tensor_nilpotent` gives
`s ≠ 0` such that, over every ring in which `s` is a unit, elements `b` of `R` with `1 ⊗ b`
nilpotent in `K ⊗[A] R` keep `1 ⊗ b` nilpotent. Elements of `I` have this property
(`nilpotent_tensor_of_algebraicClosure`). Over a finite field `κ` with `a · s ↦ ≠ 0`, an
`A`-algebra map `φ : R → κ` sends `b ∈ I` to the image of the nilpotent `1 ⊗ b ∈ κ ⊗[A] R`
under the induced `κ`-algebra map `κ ⊗[A] R → κ` (`AlgHom.liftEquiv`), hence to `0`. So
`R →ₐ[A] κ` and `C →ₐ[A] κ` have the same cardinality (`Ideal.Quotient.liftₐ`), and the
polynomial and bound from the domain case work for `R` with `a · s` in place of `a`.
