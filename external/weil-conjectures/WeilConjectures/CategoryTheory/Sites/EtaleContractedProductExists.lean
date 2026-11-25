/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.Sites.ContractedProductPresentation
import WeilConjectures.CategoryTheory.Sites.EtaleContractedProductUniversal

/-! # Existence of contracted products of étale torsors

Source: Stacks Project, Tags 03AH and 03AJ, contracted-product construction in
lem-sc-etale-torsor-pushout-extension
(blueprint: lem-sc-etale-contracted-product-exists).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace CategoryTheory.Sheaf.Torsor

/-- The sheafified orbit quotient of a torsor and the new coefficient group is a torsor.
Source: Stacks Project, Tags 03AH and 03AJ; the contracted-product construction of
lem-sc-etale-torsor-pushout-extension.
(blueprint: lem-sc-etale-contracted-product-exists)

Proof: Form the orbit presheaf of T × G' under (g,t,h) ↦ (g +ᵥ t,h - φ(g)) and sheafify.
The quotient maps are natural and invariant. Translation in the second factor commutes
with the antidiagonal action, hence descends and then extends to sheafification. On any
cover trivializing T by a section t₀, each orbit has the unique representative (t₀,h);
thus the quotient sheaf is locally G', with its translation action. This proves local
nonemptiness and simple transitivity, so the quotient is a G'-torsor. An invariant natural
map to any sheaf factors uniquely through the orbit presheaf and then uniquely through
sheafification; these two universal properties give ContractedProductPresentation. -/
theorem etale_contracted_product_exists (S : Scheme.{u})
    {G G' : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (φ : G ⟶ G') (T : Torsor G) :
    ∃ T' : Torsor G', Nonempty (ContractedProductPresentation.{u, u} S φ T T') := by
  obtain ⟨vadd, ⟨hz, ha, hn, hb, hq⟩, _⟩ := exists_contracted_product_action S φ T
  let T' : Torsor G' :=
    { sheaf := contractedOrbitSheaf S φ T
      vadd := vadd
      zero_vadd := hz
      add_vadd := ha
      map_vadd := fun f g t ↦ hn f g t
      bijective_vadd := hb
      nonemptySieve_mem := contractedOrbitSheaf_nonemptySieve_mem S φ T }
  refine ⟨T', ⟨?_⟩⟩
  exact
    { quotient := contractedOrbitQuotient S φ T
      quotient_natural := fun f t h ↦ contractedOrbitQuotient_natural S φ T f t h
      quotient_invariant := contractedOrbitQuotient_invariant S φ T
      quotient_vadd := hq
      universal := contracted_product_universal S φ T }

end CategoryTheory.Sheaf.Torsor
