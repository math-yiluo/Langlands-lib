# The lines F_x(ρ) of the Hecke algebra of an open normal subgroup

Author: Worker 40.

This supporting module is written for the proof of Renard VI.4.3, "Structure de A"
(the statement `RationalNormKernelHeckeStructureStatement`). It extends the generic
modules `NormalSubgroupHecke` (Worker 1789), `NormalSubgroupHeckeDomain` and
`NormalHeckeGrading` (Worker 1826), all in namespace
`Langlands.CuspidalSupport.NormalHecke`. Source: David Renard, *Représentations des
groupes réductifs p-adiques* (registered source
`renard-2026-representations-groupes-reductifs-padiques`), VI.4.3, printed
pp.154–155 / PDF pp.160–161. Renard states these facts for H = ⁰G. This module proves
them for any open normal subgroup H of a topological group G, under hypotheses named
in each lemma. All declarations are internal helpers.

## Setting

G is a group with a topology, H a subgroup of G and ρ a smooth complex representation
of H (`SmoothRep ℂ H`). `heckeSubmodule H ρ` is the published space H(G, ρ) of functions
φ : G → End(ρ) with φ(h g h') = ρ(h) φ(g) ρ(h') for h, h' ∈ H, whose support meets only
finitely many cosets of H. `heckeConvolution H ρ φ ψ` is the published convolution
(φ ∗ ψ)(x) = Σ_{q ∈ G/H} φ(q̂) ψ(q̂⁻¹ x), where q̂ = `q.out` is the chosen representative
of q. Most lemmas assume `H.Normal`. Some also assume `ρ.representation.IsIrreducible`.
The unit section further assumes `IsTopologicalGroup G` and `hH : IsOpen H`.

## Definitions (internal)

These mirror the local definitions of the target statement word for word, with H in
place of ⁰G.

- `InLine H ρ x φ`: φ ∈ H(G, ρ), and φ(g) ≠ 0 implies g x⁻¹ ∈ H. This is Renard's
  line F_x(ρ) of functions supported in H x.
- `IsTwistHom H ρ x T`: for all h, h' ∈ H with h' = x⁻¹ h x, T ρ(h') = ρ(h) T. So T is
  an intertwiner from ρ^x : h ↦ ρ(x⁻¹ h x) to ρ.
- `InStab H ρ x`: there is a bijective T with `IsTwistHom H ρ x T`, i.e. ρ^x ≅ ρ.
- `stabSubgroup H ρ` (H normal): the subgroup of G with carrier {x | `InStab H ρ x`}.
  This is Renard's N.
- `unitHecke H ρ hH` (H open and normal, ρ irreducible, G a topological group): the
  Hecke function `heckeEquiv H ρ hH 1` of the identity endomorphism of ind_H^G ρ,
  under the published isomorphism `heckeEquiv` of VI.4.2. This is the unit ε.

## Lines and twisted intertwiners (section `Algebra`)

- `isTwistHom_apply`: for φ ∈ H(G, ρ), the value φ(g) is a twisted intertwiner for g.
  This is the bi-invariance (published `hecke_mul_left`, `hecke_mul_right`) applied to
  h g = g h' when h' = g⁻¹ h g.
- `zero_inLine`, `InLine.smul`, `InLine.of_mul_inv_mem`: 0 lies in every line, lines
  are closed under scalars, and F_x = F_{x'} when x x'⁻¹ ∈ H.
- `eq_of_inLine`: two elements of F_x agreeing at x are equal. For g x⁻¹ ∈ H write
  g = (g x⁻¹) x and use left H-equivariance; otherwise both values vanish.
  `eq_zero_of_inLine` and `inLine_apply_ne_zero` are the cases ψ = 0 and its
  contrapositive.
- `exists_inLine_of_isTwistHom` (H normal): every twisted intertwiner T for x is φ(x)
  for some φ ∈ F_x. Here φ(g) = ρ(g x⁻¹) T if g x⁻¹ ∈ H and 0 otherwise. Its membership
  in H(G, ρ) is the published `inverseFunction_mem` applied to x⁻¹.
- `IsTwistHom.map_conj`, `IsTwistHom.map_conj'`: pointwise forms of the intertwining
  relation.
- `IsTwistHom.bijective` (H normal, ρ irreducible): a nonzero twisted intertwiner is
  bijective. Injectivity is the published `injective_of_twisted` with the conjugation
  k ↦ x k x⁻¹ of H. The range is ρ(H)-stable by `map_conj'` and nonzero, so it is
  everything (published `mem_of_isIrreducible`).
- `ne_zero_of_bijective`, `bijective_mul`, `exists_inverse_of_bijective`: elementary
  facts about bijective endomorphisms. The first uses a nonzero vector of the
  irreducible ρ.
- `IsTwistHom.exists_eq_smul` (Schur): if T is a bijective twisted intertwiner for x,
  S another one, and ρ is irreducible of countable dimension
  (`hrank : Module.rank ℂ ρ ≤ ℵ₀`), then S = c T. The map T⁻¹ S is an ordinary
  self-intertwiner of ρ, and the published `countableDimensionalSchur` makes it a scalar.
- `IsTwistHom.mul`: if T is twisted for x and S for y, then T S is twisted for x y.
  `IsTwistHom.of_inverse`: a two-sided inverse of a twisted T for x is twisted for x⁻¹.
- `stabSubgroup` is a subgroup: the identity is twisted for 1; products and inverses
  come from `mul`, `of_inverse` and the bijectivity lemmas. `mem_stabSubgroup` unfolds
  it.
- `le_stabSubgroup`: H ≤ N, with T = ρ(x) for x ∈ H. `center_le_stabSubgroup`: the
  centre of G lies in N, with T = id.
- `inStab_of_apply_ne_zero` (H normal, ρ irreducible): if φ ∈ H(G, ρ) and φ(g) ≠ 0,
  then g ∈ N, by `isTwistHom_apply` and `IsTwistHom.bijective`.
- `exists_inLine_ne_zero_iff`: F_x ≠ 0 if and only if `InStab H ρ x`. One direction is
  the previous lemma. For the other, the line element with value a bijective T is
  nonzero.
- `exists_eq_smul_of_inLine` (hrank): if φ, ψ ∈ F_x and φ ≠ 0, then ψ = c φ. Apply
  Schur to φ(x), ψ(x), then `eq_of_inLine`.
- `heckeSubmodule_eq_span` (H normal): H(G, ρ) is the ℂ-span of the union of the
  lines. A Hecke function φ is the finite sum, over the cosets q meeting its support,
  of its restrictions φ·1_q. Each restriction is bi-invariant (H-translation preserves
  cosets) and lies in F_{q̂}.
- `heckeConvolution_zero_left/right`: convolution with 0 is 0.
- `exists_heckeConvolution_ne_zero_of_uniqueMul` (H normal, ρ irreducible): suppose
  a b is a unique product of the coset supports S(φ), S(ψ) ⊆ G/H. Then φ ∗ ψ is nonzero
  at some point of the coset a b. The convolution there has the single term
  φ(â) ψ(â⁻¹ g y), an injective map (published `hecke_injective`) composed with a
  nonzero one. This repeats the argument of the published
  `heckeConvolution_ne_zero`, which is stated for `UniqueProds`.

## The unit and the structure rules (section `Unit`)

Here G is a topological group, H is open and normal, and ρ is irreducible.

- `unitHecke_one`: ε(1) = id (published `endValue_one_one`). `inLine_unitHecke`:
  ε ∈ F_1, since ε vanishes off H (published `endValue_one_of_not_mem`).
  `unitHecke_ne_zero`: ε ≠ 0.
- `exists_heckeEquiv_eq`: every φ ∈ H(G, ρ) is `heckeEquiv H ρ hH α` for some α.
  `heckeConvolution_mem`: H(G, ρ) is closed under convolution. `unitHecke_conv`,
  `conv_unitHecke`: ε ∗ φ = φ = φ ∗ ε for φ ∈ H(G, ρ). All three use the published
  `heckeEquiv_mul` (composition corresponds to convolution) and the group laws in
  End(ind_H^G ρ).
- `inLine_conv` (VI.4.3.1): for φ ∈ F_x and ψ ∈ F_y, φ ∗ ψ ∈ F_{xy} and
  (φ ∗ ψ)(x y) = φ(x) ψ(y). Support: if the term φ(q̂) ψ(q̂⁻¹ g) is nonzero, then
  g (x y)⁻¹ = (q̂ x⁻¹)(x (q̂⁻¹ g y⁻¹) x⁻¹) ∈ H by normality. Value: only the coset of x
  contributes. With x̂ = x k for k ∈ H, the term is φ(x) ρ(k) ρ(k⁻¹) ψ(y) = φ(x) ψ(y).
- `exists_conv_inverse` (item 5): a nonzero φ ∈ F_x has a two-sided inverse ψ ∈ F_{x⁻¹}.
  φ(x) is bijective with inverse U, and U is twisted for x⁻¹. Take ψ ∈ F_{x⁻¹} with
  ψ(x⁻¹) = U. By (VI.4.3.1), φ ∗ ψ and ψ ∗ φ lie in F_1 with value id at 1, so both
  equal ε by `eq_of_inLine`.
- `exists_conv_eq_smul` (VI.4.3.2): assume hrank and that G/H is commutative, in the
  form a b (b a)⁻¹ ∈ H for all a, b. Then for nonzero φ ∈ F_x and ψ ∈ F_y,
  φ ∗ ψ = c ψ ∗ φ with c ≠ 0. Both products are nonzero (their values at x y and y x
  are bijective) and lie in the same line F_{xy} = F_{yx}, which has dimension at most
  one.
- `exists_inLine_of_conv_eq_unitHecke` (`TwoUniqueProds (G ⧸ H)`): if φ ∗ ψ = ε with
  φ ≠ 0, then φ lies in some line. Every unique product a b of S(φ) × S(ψ) satisfies
  a b = 1, because φ ∗ ψ = ε is nonzero somewhere in the coset a b and ε is supported
  in H. If |S(φ)| ≥ 2, then |S(φ) × S(ψ)| ≥ 2 (ψ ≠ 0 since ε ≠ 0). Mathlib's
  `TwoUniqueProds.uniqueMul_of_one_lt_card` then gives two distinct unique products
  p₁ ≠ p₂. Both multiply to 1, so uniqueness of p₁ forces p₁ = p₂, a contradiction.
  Hence S(φ) is one coset, and φ ∈ F_{g₀} for any g₀ with φ(g₀) ≠ 0.
- `isUnit_iff_inLine` (VI.4.3.3, `TwoUniqueProds (G ⧸ H)`): for φ ∈ H(G, ρ), φ has a
  two-sided convolution inverse in H(G, ρ) exactly when φ ≠ 0 and φ lies in some line.
  The forward direction uses the previous lemma, and φ ≠ 0 because ε ≠ 0. The reverse
  direction is `exists_conv_inverse`.

## Relation to the source

Renard proves these facts for H = ⁰G. In this module, normality of H replaces
properties of ⁰G. Commutativity of G/H is an explicit hypothesis of the commutation
rule, and the two-unique-products property is an explicit hypothesis for the units.
Renard obtains the units from the twisted Laurent polynomial structure of A. Here they
come from the leading-term argument on G/H, which needs no basis of ⁰G\N. The
dimension bound uses the countable-dimension Schur lemma, through the hypothesis
`hrank`.
