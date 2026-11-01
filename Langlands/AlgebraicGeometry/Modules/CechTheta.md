# Degree-one Čech cocycles and `H¹` as a relation

Author: Worker 274.

This module relates Čech `1`-cocycles of a Čech-acyclic `𝒪_P`-module `M` to classes in
`H¹(P, M) = (relativeCohomology f 1).obj M` for `f : P ⟶ Spec R`. It defines when a cocycle
represents a class and proves that this relation is a well-defined, additive, `R`-linear map
from cocycles onto `H¹` that kills coboundaries. It is a helper for the proof of
`Langlands.AbelianScheme.FieldStructureSheafH1DimensionBoundStatement`. It contains no `sorry`
and no new axioms.

## Provenance

The construction is the comparison of Čech `H¹` with derived `H¹` through an injective
embedding, as in the proof of The Stacks Project, Cohomology of Sheaves, Lemma
`lemma-cech-h1` (tag 0B8R) and Cohomology of Schemes, Lemma 01XD (registered source
`stacks-flasque-affine-vanishing-kunneth-a04446e5`). It follows the Library proof of
`Langlands.AlgebraicGeometry.Modules.CechDegreeOne.exists_cocycle`, which builds a cocycle from a
class; that theorem gives no linearity, so the relation is set up here in the direction from
cocycles to classes. Its exact form is a project choice.

## Definitions

All declarations are in namespace `Langlands.AlgebraicGeometry.Modules.CechTheta`. Throughout,
`f : P ⟶ Spec R`, `M : P.Modules`, `V : ι → P.Opens`, `I = Injective.under M`,
`Q = cokernel (Injective.ι M)`, and `HasDerivedCategory` instances for `P.Modules` and
`ModuleCat R` are fixed.

- `conn f M : (relativeGlobalSections f).obj Q ⟶ (relativeCohomology f 1).obj M` is the inverse
  of `rightDerivedZeroIsoSelf` at `Q` followed by the connecting morphism
  `DerivedPlus.rightDerivedδ … 0 1` of `0 ⟶ M ⟶ I ⟶ Q ⟶ 0`
  (`PushforwardInjectiveAcyclic.injectiveSc_shortExact M`).
- `sc f a W : Γ(P, W)` is the restriction to `W` of `structureRingHom f a`, for `a : R`.
- `smulC f V a c` multiplies each component of a Čech cochain `c` of a module by `sc f a`.
- `Rep f M V z x` (for `z : Cech.C M.presheaf V 1` and `x : H¹(P, M)`) holds if there are a
  `0`-cochain `t` of `I` and `q : Γ(Q, ⊤)` with `d t = ι z`, `q|_{V σ} = π (t σ)` for all `σ`,
  and `conn f M q = x`.

## Results

- `conn_π`: `conn` kills global sections of `Q` that come from `I`.
- `exists_π_eq_of_conn_eq_zero`: a global section of `Q` killed by `conn` comes from `I`
  (exactness of `R⁰Γ(I) → R⁰Γ(Q) → R¹Γ(M)`).
- `conn_surjective`: `conn` is surjective, since `R¹Γ(I) = 0`.
- `conn_add`, `conn_sub`, `conn_zero`, `conn_smul`: `conn` is additive and
  `conn (structureRingHom f a • q) = a • conn q`.
- `map_sc`, `res_smul`, `res_sc_smul`, `d_smulC`, `smulC_zero`, `map_smulC`: restriction, the Čech
  differential and maps of modules commute with `smulC`.
- `rep_add`, `rep_smul`: `Rep z x → Rep z' x' → Rep (z + z') (x + x')` and
  `Rep z x → Rep (smulC f V a z) (a • x)`.
- `rep_d`: `Rep (d y) 0` for every `0`-cochain `y`.
- `rep_unique`: if `V` covers `P`, a cochain represents at most one class.
- `rep_eq_zero_of_d`: if `V` covers `P`, a coboundary represents only `0`.
- `exists_rep`: if `V` is finite and covers `P`, every cocycle represents a class.
- `exists_cocycle_rep`: if `M` is Čech-acyclic and the members of `V` are affine, every class is
  represented by a cocycle.
