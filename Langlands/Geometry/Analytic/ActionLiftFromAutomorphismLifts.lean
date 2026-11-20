import Langlands.Geometry.Analytic.NearIdentitySubgroup
import Langlands.Geometry.Analytic.QuasiEtaleRigidity.QuasiEtaleRigid

/-! # Lifts of continuous actions from lifts of near-identity automorphisms -/

noncomputable section

universe u v z

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

variable {G : Type z} [Group G] [TopologicalSpace G]

/-- **Uniqueness of lifts.** Two lifts of a continuous action along a rigid morphism agree on
an open subgroup. -/
theorem ActionLift.exists_agreeOn [IsTopologicalGroup G]
    {X U : LocalizedCategory.{u, v, v} (K := K)} {ρ : G →* Aut X} {f : U ⟶ X} (hf : IsRigid f)
    (a b : ActionLift ρ f) : ∃ N : Subgroup G, a.AgreeOn b N := by
  obtain ⟨N, hN, ha, hb, h⟩ := exists_open_subgroup_intertwining (f := 𝟙 U)
    (Category.id_comp f) hf
    (fun τ => ⟨{τ}, fun φ hφ => by
      rw [Category.comp_id]
      exact hφ τ (Finset.mem_singleton_self τ)⟩) a b
  refine ⟨N, hN, ha, hb, fun g hg => ?_⟩
  have h' := h g hg
  rw [Category.comp_id, Category.id_comp] at h'
  exact Iso.ext h'.symm

/-- **Existence of lifts** of a continuous action along a rigid morphism `f` with compact
source, from lifts of near-identity automorphisms. -/
theorem nonempty_actionLift_of_automorphismLift [IsTopologicalGroup G]
    {X U : LocalizedCategory.{u, v, v} (K := K)} {ρ : G →* Aut X} {f : U ⟶ X}
    (hρ : IsContinuousAction ρ) (hf : IsRigid f)
    (hL : ∀ E : Finset (TestTriple (presentationOf U)),
      ∃ D : Finset (TestTriple (presentationOf X)), ∀ σ : Aut X,
        (∀ τ ∈ D, σ ∈ nearIdentity τ) →
          ∃ ψ : U ⟶ U, ψ ≫ f = f ≫ σ.hom ∧ ∀ τ ∈ E, IsNear τ ψ (𝟙 U)) :
    Nonempty (ActionLift ρ f) := by
  classical
  obtain ⟨E₀, hE₀⟩ := hf
  -- Lifts near the identity are unique.
  have huniq : ∀ (σ : Aut X) (ψ₁ ψ₂ : U ⟶ U), ψ₁ ≫ f = f ≫ σ.hom → ψ₂ ≫ f = f ≫ σ.hom →
      (∀ τ ∈ E₀, IsNear τ ψ₁ (𝟙 U)) → (∀ τ ∈ E₀, IsNear τ ψ₂ (𝟙 U)) → ψ₁ = ψ₂ :=
    fun σ ψ₁ ψ₂ h₁ h₂ n₁ n₂ =>
      hE₀ U (𝟙 U) ψ₁ ψ₂ (h₁.trans h₂.symm) fun τ hτ => ⟨(n₁ τ hτ).symm, (n₂ τ hτ).symm⟩
  obtain ⟨D₀, hD₀⟩ := hL E₀
  -- The open subgroup.
  let N₀ : Subgroup (Aut X) := ⨅ τ ∈ D₀, nearIdentitySubgroup τ
  let H : Subgroup G := N₀.comap ρ
  have hmemH : ∀ g : G, g ∈ H ↔ ∀ τ ∈ D₀, ρ g ∈ nearIdentity τ := by
    intro g
    change ρ g ∈ N₀ ↔ _
    simp only [N₀, Subgroup.mem_iInf, mem_nearIdentitySubgroup]
  have hHnhds : (H : Set G) ∈ 𝓝 (1 : G) := by
    have h : (⋂ τ ∈ D₀, ρ ⁻¹' nearIdentity τ) ∈ 𝓝 (1 : G) :=
      (Filter.biInter_finset_mem D₀).2 fun τ _ => hρ τ
    refine Filter.mem_of_superset h fun g hg => ?_
    rw [SetLike.mem_coe, hmemH]
    intro τ hτ
    exact Set.mem_iInter₂.1 hg τ hτ
  have hHopen : IsOpen (H : Set G) := Subgroup.isOpen_of_mem_nhds H hHnhds
  -- The chosen lifts.
  have hex : ∀ h : H, ∃ ψ : U ⟶ U, ψ ≫ f = f ≫ (ρ h).hom ∧ ∀ τ ∈ E₀, IsNear τ ψ (𝟙 U) :=
    fun h => hD₀ (ρ h) ((hmemH h).1 h.2)
  choose ψ hψf hψn using hex
  have hψ_one : ψ 1 = 𝟙 U := by
    refine huniq (ρ ((1 : H) : G)) _ _ (hψf 1) ?_ (hψn 1) fun τ _ => isNear_id τ
    rw [Subgroup.coe_one, map_one, Category.id_comp]
    exact (Category.comp_id f).symm
  have hψ_mul : ∀ h h' : H, ψ (h * h') = ψ h' ≫ ψ h := by
    intro h h'
    refine huniq (ρ ((h * h' : H) : G)) _ _ (hψf (h * h')) ?_ (hψn (h * h'))
      fun τ hτ => IsNear.comp_of_isNear_id (hψn h' τ hτ) (hψn h τ hτ)
    rw [Category.assoc, hψf h, ← Category.assoc, hψf h', Category.assoc, Subgroup.coe_mul,
      map_mul]
    rfl
  have hψ_inv : ∀ h : H, ψ h ≫ ψ h⁻¹ = 𝟙 U := by
    intro h
    rw [← hψ_mul, inv_mul_cancel, hψ_one]
  have hψ_inv' : ∀ h : H, ψ h⁻¹ ≫ ψ h = 𝟙 U := by
    intro h
    rw [← hψ_mul, mul_inv_cancel, hψ_one]
  -- The action.
  let act : H →* Aut U :=
    { toFun := fun h => ⟨ψ h, ψ h⁻¹, hψ_inv h, hψ_inv' h⟩
      map_one' := Iso.ext hψ_one
      map_mul' := fun h h' => Iso.ext (hψ_mul h h') }
  have hcont : IsContinuousAction act := by
    intro τ
    obtain ⟨D, hD⟩ := hL (insert τ E₀)
    let W : Set G := (H : Set G) ∩ ⋂ σ ∈ D, ρ ⁻¹' nearIdentity σ
    have hW : W ∈ 𝓝 ((1 : H) : G) :=
      Filter.inter_mem hHnhds ((Filter.biInter_finset_mem D).2 fun σ _ => hρ σ)
    refine Filter.mem_of_superset (continuous_subtype_val.continuousAt.preimage_mem_nhds hW) ?_
    intro h hh
    obtain ⟨ψ', hψ'f, hψ'n⟩ := hD (ρ h) fun σ hσ => Set.mem_iInter₂.1 hh.2 σ hσ
    have heq : ψ' = ψ h := huniq (ρ h) _ _ hψ'f (hψf h)
      (fun σ hσ => hψ'n σ (Finset.mem_insert_of_mem hσ)) (hψn h)
    change IsNear τ (ψ h) (𝟙 U)
    rw [← heq]
    exact hψ'n τ (Finset.mem_insert_self τ E₀)
  exact ⟨{ subgroup := H
           isOpen_subgroup := hHopen
           action := act
           isContinuousAction := hcont
           equivariant := fun h => hψf h }⟩

end Langlands.Analytic.SaturatedAtlasPresentation
