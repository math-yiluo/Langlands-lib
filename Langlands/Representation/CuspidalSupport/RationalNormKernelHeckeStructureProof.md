# Proof of Renard VI.4.3: the structure of A = H(G, ρ)

Author: Worker 40.

`Langlands.CuspidalSupport.rationalNormKernelHecke_structure` proves the published
`Langlands.CuspidalSupport.RationalNormKernelHeckeStructureStatement.{uF, uV}`, with both
universes arbitrary and no added hypothesis. Source: David Renard, *Représentations des
groupes réductifs p-adiques*, VI.4.3 "Structure de A", printed pp.154–155 / PDF
pp.160–161 (registered source `renard-2026-representations-groupes-reductifs-padiques`).

The proof applies the generic results of the supporting module
`Langlands.Representation.CuspidalSupport.NormalHeckeLines` (see its Markdown) to the open
normal subgroup H = ⁰G = `rationalCommonNormKernel G`. It adds three facts about ⁰G and a
lattice lemma, all proved in this file.

## Lattice helpers (section `Lattice`)

- `exists_basis_of_smul_mem`: let L be a finite free, torsion-free ℤ-module, and M a
  submodule containing k • L for some k ≠ 0. Then M has a basis indexed by
  `Fin (finrank ℤ L)`. Mathlib's `Submodule.basisOfPid` gives M a basis indexed by
  `Fin m`. Then m ≤ finrank L by `Submodule.finrank_le`. Also finrank L ≤ m, since
  v ↦ k • v is an injective linear map L → M (`smul_right_injective`, which uses
  torsion-freeness) and `LinearMap.finrank_le_finrank_of_injective` applies. The basis
  is then reindexed along m = finrank L.
- `exists_latticeBasis`: let f : G → C be a surjective homomorphism onto a commutative
  group C with kernel H, where `Additive C` is a finite free, torsion-free ℤ-module of
  rank n. Let N be a subgroup of G of finite index. Then there are x : Fin n → G with
  every x i ∈ N such that each g ∈ N has exactly one e : Fin n → ℤ with
  g (x₁^{e₁} ⋯ xₙ^{eₙ})⁻¹ ∈ H. The product is written `(List.ofFn fun i => x i ^ e i).prod`.
  - Proof: let K = f(N) ⊆ C. K has finite index, since its index divides that of N
    (`Subgroup.index_map_dvd`). Hence c^{[C:K]} ∈ K for every c ∈ C
    (`Subgroup.pow_index_mem`; K is normal because C is commutative). The previous
    lemma, applied to K as a ℤ-submodule M of `Additive C` with k = [C:K], gives a basis
    b of M indexed by `Fin n`. Choose x i ∈ N with f(x i) = b i.
  - The condition g (∏ x_i^{e_i})⁻¹ ∈ H = ker f is equivalent to f(g) = ∏ b_i^{e_i}.
    Additively this reads f(g) = Σ e_i b_i = `b.equivFun.symm e` in M. For g ∈ N,
    f(g) ∈ M, so the unique solution is e = `b.equivFun (f g)`.

## Facts about ⁰G

- `rationalNormKernelQuotient_twoUniqueProds`: G(F) ⧸ ⁰G has the two-unique-products
  property. The proof follows the published `rationalNormKernelQuotient_uniqueProds`
  (RationalNormKernelEndDomainProof). The published `rationalNormKernelQuotientEquiv`
  and the valuation g ↦ (χ ↦ ord χ(g)) give an injective homomorphism into
  `Multiplicative (rationalCharacters G → ℤ)`. That group has two unique products
  (Mathlib: ℤ is a linearly ordered group, and the property passes to function types).
  `TwoUniqueProds.of_injective_mulHom` pulls it back.
- `mul_mul_inv_mem_rationalCommonNormKernel`: a b (b a)⁻¹ ∈ ⁰G for all a, b ∈ G(F).
  The published projection `rationalValuationImageProjection G` has kernel ⁰G
  (`rationalValuationImageProjection_ker`) and a commutative target.

## Main proof

The proof introduces the field, the group and the instances of the statement. It then
copies the setup of the published `rationalNormKernelEnd_separation`: F is second
countable, so G(F) and the subgroup ⁰G are second countable, hence separable. The
remaining inputs are:

- irreducibility of ρ (the hypothesis);
- `hrank : Module.rank ℂ ρ ≤ ℵ₀`, from the published
  `Whittaker.MirabolicRigidity.rank_le_aleph0`, since ρ is smooth and irreducible and ⁰G
  is separable;
- openness of ⁰G (`isOpen_rationalCommonNormKernel`) and its normality (published
  instance);
- two unique products of G(F) ⧸ ⁰G (lemma above);
- `Module.Free` and `Module.Finite` over ℤ for `Additive (rationalDiscreteValuationImage G)`,
  from the published `rationalReductiveImage_free_finite G hG` (this uses that G is
  connected reductive), with torsion-freeness from the published instance
  `rationalImage_isTorsionFree`.

The published `rationalNormKernelHecke G ρ` and `rationalNormKernelConvolution G ρ` are by
definition `NormalHecke.heckeSubmodule ⁰G ρ` and `NormalHecke.heckeConvolution ⁰G ρ`. The
local predicates `InF`, `IsTwistHom` and `InN` of the statement are by definition
`NormalHecke.InLine`, `NormalHecke.IsTwistHom` and `NormalHecke.InStab`. The witness is
ε = `NormalHecke.unitHecke ⁰G ρ hH`, and the conjuncts are proved as follows.

- ε ∈ F_1, ε(1) = 1, and ε is a two-sided unit on A: `inLine_unitHecke`, `unitHecke_one`,
  `unitHecke_conv`, `conv_unitHecke`.
- Item 1: injectivity is `eq_zero_of_inLine`. A twisted intertwiner is a value at x by
  `exists_inLine_of_isTwistHom`. Conversely, φ(x) is twisted by `isTwistHom_apply`.
- Item 2: `exists_eq_smul_of_inLine hrank` and `exists_inLine_ne_zero_iff`.
- Item 3: `inStab_of_apply_ne_zero`.
- Item 4 (VI.4.3.1): `inLine_conv`.
- Item 5: `exists_conv_inverse`.
- Item 6 (VI.4.3.2): `exists_conv_eq_smul`, with commutativity from
  `mul_mul_inv_mem_rationalCommonNormKernel`.
- Item 7: N = `stabSubgroup ⁰G ρ`, with membership iff `InN` by definition, and ⁰G ≤ N by
  `le_stabSubgroup`. N has finite index: it contains ⁰G and the centre of G(F)
  (`center_le_stabSubgroup`), and ⁰G ⊔ Z(G(F)) has finite index by the published
  `rationalCommonNormKernel_sup_center_finiteIndex F G hG`. Apply `exists_latticeBasis`
  to f = `rationalValuationImageProjection G` (surjective, with kernel ⁰G). With N = ⊤ it
  gives the basis y of G(F) modulo ⁰G. With N = `stabSubgroup ⁰G ρ` it gives the basis x
  of N modulo ⁰G. Both have length n = finrank ℤ of the valuation image Λ(G).
- Item 8: the span statement is `heckeSubmodule_eq_span`. The characterisation of units
  (VI.4.3.3) is `isUnit_iff_inLine`, using two unique products of G(F) ⧸ ⁰G.

`lean_check` reports that the theorem depends only on the axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Relation to the source

Renard derives the units from the twisted Laurent polynomial structure of A over ⁰G\N.
The Lean proof gets them directly from a leading-term argument with two unique products
on G(F) ⧸ ⁰G. For item 7, Renard notes that N contains ⁰G·Z(G), which has finite index.
The Lean proof uses this fact (the published finite-index theorem) together with the
freeness and finiteness of the valuation image, and builds the bases of ⁰G\N and of
Λ(G) = ⁰G\G from a basis of a finite-index sublattice (`Submodule.basisOfPid`). The
dimension bound for F_x uses the countable-dimension Schur lemma.
