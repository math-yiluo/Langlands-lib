# Commutator relations of root groups on every test scheme

This module proves clause 4 of
[`AffineSplitRootSubgroupSpanningStatement`](AffineSplitRootSubgroupSpanningStatement.md), the
commutator relations of Conrad, *Reductive group schemes* (2014), Proposition 5.1.14,
p.145. It adds theorems only: no definitions, statements or axioms. Both theorems are in
`Langlands.GroupScheme.LocalSplitCell`.

## Setting

The binders are those of the target statement. `R` is any commutative ring.
`G : GroupScheme (Spec R)` is affine over the base and `IsReductive`. `i : 𝔾_m^I ⟶ G` is a
coordinate split torus that is a fibrewise maximal torus (`IsFibrewiseMaximalTorus`), with
fibrewise root datum `P` (`IsFibrewiseRootDatumOf`). `v : J → (Ga R ⟶ G)` is a family of
root parametrizations (`IsRootParametrization`).

## `exists_rootPoint_comm_cone_sections`

Let `β ≠ ε` be roots with `α_β ≠ -α_ε`. Let `L` be a duplicate-free list of roots, with
exponents `ex r = (d_S, d_T)`, both at least one, such that
`α_{L r} = d_S α_β + d_T α_ε`. Assume that `L` contains every root of the form
`d_S α_β + d_T α_ε` with `d_S, d_T ≥ 1`. Then there are constants `C r ∈ R` such that,
for every scheme `Z` over `Spec R` and all `x, y ∈ Γ(Z, 𝒪_Z)`,

`(u_β(x) u_ε(y))⁻¹ (u_ε(y) u_β(x)) = ∏_r u_{L r}(C_r x^{d_S} y^{d_T})`.

The Library's `exists_rootPoint_comm_cone` in `Reductive.LocalSplitConeCommutator` has the
same hypotheses, but its identity holds only on affine test schemes `Spec B`. The proof
here follows the same route and replaces the last step by the Library's
`IsUnivComm.posComm_eq_sections` (`Reductive.LocalSplitHeightCommutator`), which evaluates
the universal commutator polynomials at global functions on an arbitrary `Z`:

1. `exists_base_isPos_pair` gives a base `b` for which `β` and `ε` are positive, and
   `exists_coPairing_eq_height` gives a cocharacter `ν` whose pairing with each root is a
   fixed positive multiple of its `b`-height. Every member of `L` is then `b`-positive.
2. `exists_cell_initial` gives an open big cell whose positive enumeration begins with `L`.
3. `exists_isUnivComm` gives universal commutator polynomials `E` for the root groups at
   `β` and `ε`. A weight argument (`IsUnivComm.eq_zero_of_forall_ne` and
   `IsUnivComm.weight`, together with the linear independence of `α_β` and `α_ε` in the
   reduced root datum) shows two things. The coordinates outside the initial segment `L`
   vanish. The coordinate at `L r` is the single monomial of bidegree `ex r`.
4. `IsUnivComm.posComm_eq_sections` and `orderedProduct_initial` turn this into the
   displayed identity on `Z`. The constant `C r` is the coefficient of that monomial.

## `exists_commutator_orderedProduct` (clause 4)

For roots `a`, `c` with `α_c ≠ α_a` and `α_c ≠ -α_a`, and every enumeration `e` of the
roots `d` with `α_d = p α_a + q α_c` and `p, q > 0`, there are exponents `p k, q k > 0`
with `α_{e k} = p k α_a + q k α_c` and constants `C k ∈ R` such that, on every scheme `Z`
over `Spec R` and for all `x, y ∈ Γ(Z, 𝒪_Z)`,

`u_a(x) u_c(y) u_a(-x) u_c(-y) = ∏_k u_{e k}(C_k x^{p k} y^{q k})`,

where `C_k` acts through `scalarMap Z`. This is clause 4 of the target statement verbatim.

The proof chooses `p k`, `q k` from the defining property of `e k`. It applies the previous
theorem with `β = c`, `ε = a`, `L = List.ofFn e`, and exponents `ex = (q, p)`. The cone
hypothesis holds because `e` is surjective. That theorem is evaluated at `(-y, -x)`.
Since `u_a(-x) = u_a(x)⁻¹` (`rootPoint_neg`), its left side becomes the commutator in the
target. The resulting constants are `C k = C'_k · (-1)^{p k + q k}`.
