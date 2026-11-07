# The center of End(ind_H^G ρ)

Author: Worker 1826.

This is a supporting module for the proofs of Renard VI.4.4 (the Theorem
`RationalSummandEndCenterStatement`, the Corollary
`RationalSummandEndNoetherianStatement` and the Proposition
`RationalSummandCenterGroupAlgebraStatement`). It continues the modules
`Langlands.Algebra.RankOneGradedAlgebra`,
`Langlands.Representation.CuspidalSupport.NormalHeckeGrading`,
`Langlands.Representation.CuspidalSupport.NormalHeckeTwist` and
`Langlands.Representation.CuspidalSupport.NormalHeckeModule`. Source: David Renard,
*Représentations des groupes réductifs p-adiques* (registered source
`renard-2026-representations-groupes-reductifs-padiques`), VI.4.4, printed
pp.155–159 / PDF pp.161–165. Declarations of these modules are cited by their
names without qualification; `NormalHeckeTwist` and `NormalHeckeModule` are accepted
candidates awaiting integration into the Library.

The results here are generic versions of the three statements of VI.4.4. Renard works
with G the rational points of a reductive group, H = ⁰G, and B an irreducible
representation π (lifted to the carrier universe of the induced representation). Here
G, H, ρ, B are arbitrary under the hypotheses listed below, which the application must
verify. All declarations are internal helpers; none of them is a statement of the book.

## Setting

Namespace `Langlands.CuspidalSupport.NormalHecke`. G is a topological group, H a
subgroup with `hH : IsOpen H`, and ρ a smooth complex representation of H. From
`mem_radical_iff` on, H is normal, ρ is irreducible, and
`hrank : Module.rank ℂ ρ ≤ ℵ₀`. I = `inducedRep H ρ` = ind_H^G ρ. p : G → ι is a degree
for H in the sense of `IsDegree` (`hp`), where ι is an additive commutative group with
decidable equality. End(I) is graded by `component H ρ hH p` (`gradedAlgebra`), and
this grading is a rank-one grading (`isRankOneGrading ρ hH hp hrank`); its support and
radical are those of `Langlands.Algebra.RankOneGradedAlgebra`.

B is a smooth representation of G in the carrier universe of I, with:

- `[FiniteDimensional ℂ (I ⟶ B)]` and `[Nontrivial (I ⟶ B)]`;
- `hcyc`: for every nonzero φ : I → B and every ψ : I → B there is α ∈ End(I) with
  α ≫ φ = ψ.

`homAction H ρ B` (α acts by φ ↦ α ≫ φ) is then surjective onto
End_ℂ(I ⟶ B) (`surjective_homAction`, Burnside).

The results on the radical, the center and the group algebra also assume:

- `hiso`: for every character ω : G → ℂˣ with open kernel (`hω`) and H ≤ ker ω, every
  ℂ-linear bijection Ψ : (I ⟶ B ⊗ ω) ≃ (I ⟶ B) with Ψ(α ≫ φ) = α ≫ Ψ(φ) for all
  α ∈ End(I) and all φ comes from an isomorphism, i.e. `Nonempty (B.twist ω hω ≅ B)`.
  Only the existence of such an isomorphism is required, not a relation with Ψ.

and a subgroup T of G with

- `hT`: g ∈ T if and only if ω(g) = 1 for every character ω with open kernel,
  H ≤ ker ω and B ⊗ ω ≅ B.

## Characters from degrees

- `degreeCharacter hp χ` (**definition**, internal): for an additive homomorphism
  χ : ι → `Additive ℂˣ`, the character g ↦ χ(p g) of G. `degreeCharacter_apply` (by
  `rfl`).
- `le_ker_degreeCharacter`: its kernel contains H, since p vanishes on H.
- `isOpen_ker_degreeCharacter hH hp χ`: its kernel is open, as a subgroup containing
  the open subgroup H (Mathlib's `Subgroup.isOpen_mono`).
- `exists_degree_eq`: if `component H ρ hH p a` has a nonzero element, then a = p(g)
  for some g (`eq_zero_of_mem_component`).

## The radical

`mem_radical_iff g`: p(g) lies in the radical of the grading if and only if ω(g) = 1
for every character ω with open kernel, H ≤ ker ω and B ⊗ ω ≅ B. Thus, by `hT`, T is
the set of g with p(g) in the radical.

Proof. (⇒) If p(g) is in the radical, some u of degree p(g) acts as the identity on
I ⟶ B (`exists_mem_map_eq_one` of `RankOneGradedAlgebra`, using surjectivity). An
isomorphism e : B ⊗ ω ≅ B gives the equivariant bijection φ ↦ φ ≫ e
(Mathlib's `Linear.homCongr`), and `eq_one_of_homEquiv` gives ω(g) = 1.

(⇐) Suppose p(g) is not in the radical; we produce ω with H ≤ ker ω, open kernel,
B ⊗ ω ≅ B and ω(g) ≠ 1. In both cases below we find a unit v of End(I) and an
additive χ : ι → `Additive ℂˣ` with α v = ω(g') (v α) for every g' and every α of
degree p(g'), where ω = `degreeCharacter hp χ`. `twistModuleEquiv_comp`
then makes `twistModuleEquiv ρ hH ω hω hωH B v` an equivariant bijection, so
B ⊗ ω ≅ B by `hiso`.

- If p(g) is in the support, pick a nonzero w of degree p(g). The abstract
  `exists_mul_eq_smul_mul` gives a nonzero homogeneous v with w v = c (v w), c ≠ 1;
  v is a unit (`isUnit_of_mem`). `exists_commutation_hom` gives an
  additive β on the support with x v = β(a) (v x) for x of degree a, and
  `exists_addMonoidHom_extend` extends β to χ on ι. Degrees outside the support
  carry only 0, so the commutation relation holds for every g'. Comparing with w
  gives ω(g) = β(p g) = c ≠ 1.
- If p(g) is not in the support, `exists_addMonoidHom_ne_zero` gives χ vanishing on
  the support with χ(p g) ≠ 0; take v = 1. The relation α · 1 = ω(g') (1 · α) holds
  because ω(g') = 1 when p(g') is in the support and α = 0 otherwise. Here
  ω(g) ≠ 1.

## The center

`mem_center_iff_endValue α`: α is central if and only if the values
`endValue H ρ hH α g` (the linear map w ↦ α(f_w)(g) of ρ, where f_w is the function
supported on H with f_w(1) = w) vanish for every g ∉ T.

Proof. By the abstract `mem_center_iff`, α is central if and only if its homogeneous
components of degrees outside the radical vanish. `endValue_decompose` says that the
degree-a component of α has the values of α at the points of degree a and vanishes
elsewhere, and endomorphisms of I are determined by their values (`end_ext`). Combine with `mem_radical_iff` and `hT`.

## The center as a group algebra

`exists_algEquiv_center_quotient`: there is a ℂ-algebra isomorphism
e : ℂ[T ⧸ (H ∩ T)] ≃ center of End(I) (`MonoidAlgebra ℂ (T ⧸ H.subgroupOf T)` and
`Subalgebra.center ℂ (End I)`) such that for every t ∈ T the image ψ_t of the class of
t satisfies:

- `endValue H ρ hH ψ_t g = 0` whenever g t ∉ H;
- ψ_t ≫ φ = ω(t) φ for every character ω with open kernel and H ≤ ker ω, and every
  φ : I → B ⊗ ω.

Proof. The abstract `exists_algEquiv_center` gives an isomorphism
e₀ : ℂ[radical] ≃ center with e₀(a) of degree a acting as the identity on I ⟶ B. The
map t ↦ −p(t) is a homomorphism f : T → radical (by `mem_radical_iff`); its kernel is
H ∩ T (p vanishes exactly on H), and it is surjective, since every degree of the
radical lies in the support and so is a value of p (`exists_degree_eq`). Hence
T ⧸ (H ∩ T) ≅ radical (Mathlib's `QuotientGroup.quotientKerEquivOfSurjective`), and e
is e₀ composed with the induced isomorphism of group algebras
(`MonoidAlgebra.domCongr`). So ψ_t = e₀(f t) has degree −p(t) = p(t⁻¹), which is the
first property: g t ∉ H means p(g) ≠ −p(t). For the second, the twist law
`twistHomEquiv_comp` with g₀ = t⁻¹ gives Φ(ψ_t ≫ φ) = ω(t) (ψ_t ≫ Φ(φ)) = ω(t) Φ(φ),
where Φ = `twistHomEquiv` and ψ_t acts as the identity on I ⟶ B. Since Φ is
injective, ψ_t ≫ φ = ω(t) φ.

The Proposition of VI.4.4 uses the elements of H t⁻¹ (equivalently, the support
condition g t ∉ H ⇒ value 0) and the scalar ω(t); this is the form stated here.

## Freeness and noetherianity

These two results need `hcyc` but neither `hiso` nor T.

- `exists_basis_center`: End(I) has a basis over its center indexed by
  `Fin ((finrank ℂ (I ⟶ B))^2)`. The abstract `basis` is indexed by the cosets
  support ⧸ radical, which by `finite_cosets_and_card_eq` form a finite set of
  cardinality (finrank ℂ (I ⟶ B))^2; reindex by `Finite.equivFin` and `finCongr`.
- `isNoetherianRing_end` (with `[Module.Finite ℤ ι]`): End(I) and End(I)ᵐᵒᵖ are
  noetherian rings. The radical is a subgroup of the finitely generated abelian
  group ι, hence finitely generated (ℤ is noetherian). The center is isomorphic to
  ℂ[radical] (`exists_algEquiv_center`), hence noetherian
  (`isNoetherianRing_of_algEquiv_monoidAlgebra`), and the cosets are finite, so the
  abstract `isNoetherianRing_of_finite` applies.

## Relation to the source

Renard proves the Theorem through his Lemma on the operators attached to H_W and the
finiteness of the group X(G)(π) of unramified characters fixing π. This module avoids
both: the center is computed in the abstract rank-one graded algebra, the rank m² over
the center comes from the trace count of `RankOneGradedAlgebra` applied to the
simple module I ⟶ B of dimension m, and the identification of the radical with T uses
the hypothesis `hiso`, which the application derives from the full faithfulness of
VI.4.1. In the application, B is the lift of π and m = dim Hom(I, π).
