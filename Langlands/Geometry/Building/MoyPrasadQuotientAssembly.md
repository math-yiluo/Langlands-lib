# Assembling abstract quotient isomorphisms

The module `Langlands.Geometry.Building.MoyPrasadQuotientAssembly` contains three
pieces of general group theory and lattice theory. The proof of the supplied-data
Moy–Prasad isomorphism (module `Langlands.Geometry.Building.KPMoyPrasadIsomorphismProof`)
uses them. None of them mentions buildings. The only Library notion involved is
`HasMoyPrasadQuotientIso` (module `Langlands.Geometry.Building.KPMoyPrasadIsomorphismStatement`).

## Quotients by a subgroup that contains the commutators

Let `H₁ H₂ : Subgroup Γ` be subgroups of a group `Γ`.

- `subgroupOf_normal_of_commutator_le`: if `⁅H₁, H₁⁆ ≤ H₂`, then
  `H₂.subgroupOf H₁` (that is, `H₂ ∩ H₁` viewed inside `H₁`) is normal in `H₁`.
  For `g ∈ H₁` and `n ∈ H₂ ∩ H₁`, the commutator `g n g⁻¹ n⁻¹` lies in `H₂`, and so does
  `g n g⁻¹ = (g n g⁻¹ n⁻¹) n`.
- `quotient_mul_comm_of_commutator_le`: under the same hypothesis, and given the normality
  instance, the quotient `H₁ ⧸ H₂.subgroupOf H₁` is commutative. For `a, b ∈ H₁`, the
  element `(b a)⁻¹ (a b) = a⁻¹ b⁻¹ a b` is a commutator of two elements of `H₁`, so it
  lies in `H₂`.
- `quotientCommGroupOfCommutatorLE` (an `abbrev`) packages this as a `CommGroup` structure
  on `H₁ ⧸ H₂.subgroupOf H₁` extending the quotient group structure. It is not an instance.
  A proof that needs to multiply images in `H₁ / H₂` in any order introduces it locally.

## Equal kernels give `HasMoyPrasadQuotientIso`

`hasMoyPrasadQuotientIso_of_ker_eq`: let `K` be a group, and let
`Θ : K →* H₁ ⧸ H₂.subgroupOf H₁` and `Λ : K →* Multiplicative (g₁ ⧸ g₂.addSubgroupOf g₁)`
be surjective homomorphisms with `Θ.ker = Λ.ker`, where `g₁ g₂ : AddSubgroup M` for an
abelian group `M`. Then `HasMoyPrasadQuotientIso H₁ H₂ g₁ g₂` holds.

The proof composes the first isomorphism theorem for `Θ` (inverted), the identification of
the quotients of `K` by the equal kernels, and the first isomorphism theorem for `Λ`
(`QuotientGroup.quotientKerEquivOfSurjective`, `QuotientGroup.quotientMulEquivOfEq`).
The result is a multiplicative equivalence `e : H₁ ⧸ H₂.subgroupOf H₁ ≃* Multiplicative (g₁ ⧸ g₂.addSubgroupOf g₁)`.
The witness of `HasMoyPrasadQuotientIso` is `e` composed with the quotient map
`H₁ → H₁ ⧸ H₂.subgroupOf H₁`. It is surjective, and its kernel is the kernel of the quotient
map, namely `H₂.subgroupOf H₁`.

## Induced maps of additive quotients

`addSubgroupQuotientMap f h₁ h₂`: for an additive homomorphism `f : M →+ N` of abelian
groups and additive subgroups `A₂, A₁` of `M` and `B₂, B₁` of `N` with `f(A₁) ⊆ B₁` and
`f(A₂) ⊆ B₂`, this is the induced homomorphism
`A₁ ⧸ A₂.addSubgroupOf A₁ →+ B₁ ⧸ B₂.addSubgroupOf B₁` (built with `QuotientAddGroup.map`).
No inclusion `A₂ ≤ A₁` is needed, because `A₂.addSubgroupOf A₁` is `A₂ ∩ A₁` inside `A₁`.
`addSubgroupQuotientMap_mk` records its value on the class of `X ∈ A₁`: the class of `f X`.
It holds by `rfl`.

## Grouping an independent family

`iSupIndep_biSup_of_pairwise_disjoint`: in a complete, modular, compactly generated lattice
(for example the lattice of submodules of a module), let `f : ι → α` be an independent family
(`iSupIndep f`) and `T : κ → Set ι` a family of pairwise disjoint index sets. Then the family
`k ↦ ⨆ i ∈ T k, f i` is independent. For each `k`, Mathlib's
`iSupIndep.disjoint_biSup_biSup` makes the supremum over `T k` disjoint from the supremum
over the union of the other `T k'`. That union contains every other grouped supremum.

## Provenance

Internal. These are standard facts of group theory and lattice theory, isolated for the
assembly step of the proof of KP Theorem 13.5.1 (1) on supplied data. KP's proof
(Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*, 2023, proof of Theorem 13.5.1,
printed pp. 475–476) uses that `P_{x,r} / P_{x,s}` is abelian when
`[P_{x,r}, P_{x,r}] ⊆ P_{x,s}`. It also uses that the Lie algebra decomposes as a direct sum
of grouped weight spaces.
