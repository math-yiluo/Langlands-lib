import Langlands.Geometry.Analytic.QuasiEtaleRigidity.StrongNearComposition
import Langlands.Geometry.Analytic.LocalActionLifts

/-! # Compatibility of lifts from rigidity and postcomposition of test relations -/

noncomputable section

universe u v z

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- The uniqueness part of Berkovich's Key Lemma 7.2 (commutative diagrams) for a morphism
`p : U ⟶ X`: there is a finite set `E` of test triples on `U` such that two morphisms `ψ₁ ψ₂`
to `U` with `ψ₁ ≫ p = ψ₂ ≫ p` which are both `E`-near a common morphism `ψ` are equal. -/
def IsRigid {U X : LocalizedCategory.{u, v, v} (K := K)} (p : U ⟶ X) : Prop :=
  ∃ E : Finset (TestTriple (presentationOf U)), ∀ (V : LocalizedCategory.{u, v, v} (K := K))
    (ψ ψ₁ ψ₂ : V ⟶ U), ψ₁ ≫ p = ψ₂ ≫ p → (∀ τ ∈ E, IsNear τ ψ ψ₁ ∧ IsNear τ ψ ψ₂) → ψ₁ = ψ₂

variable {G : Type z} [Group G] [TopologicalSpace G]

/-- By continuity of a lift, its elements near `1` are near the identity for a test triple. -/
theorem ActionLift.eventually_isNear {X U : LocalizedCategory.{u, v, v} (K := K)}
    {ρ : G →* Aut X} {p : U ⟶ X} (a : ActionLift ρ p) (τ : TestTriple (presentationOf U)) :
    {g : G | ∃ hg : g ∈ a.subgroup, IsNear τ (a.action ⟨g, hg⟩).asIso.hom (𝟙 U)} ∈ 𝓝 (1 : G) := by
  have h := a.isContinuousAction τ
  have himg := (a.isOpen_subgroup.isOpenMap_subtype_val).image_mem_nhds h
  refine Filter.mem_of_superset himg ?_
  rintro _ ⟨g, hg, rfl⟩
  exact ⟨g.2, hg⟩

/-- The lift subgroup is a neighbourhood of `1`. -/
theorem ActionLift.subgroup_mem_nhds {X U : LocalizedCategory.{u, v, v} (K := K)}
    {ρ : G →* Aut X} {p : U ⟶ X} (a : ActionLift ρ p) :
    (a.subgroup : Set G) ∈ 𝓝 (1 : G) :=
  a.isOpen_subgroup.mem_nhds a.subgroup.one_mem

/-- **Deduction of the compatibility of lifts.** If `p` is rigid and postcomposition with `f`
carries finitely many test relations to the identity of `V` into any given test relation, then
`f` intertwines the two lifts on an open subgroup. -/
theorem exists_open_subgroup_intertwining [IsTopologicalGroup G]
    {X U V : LocalizedCategory.{u, v, v} (K := K)} {ρ : G →* Aut X} {p : U ⟶ X} {q : V ⟶ X}
    {f : V ⟶ U} (hfpq : f ≫ p = q) (hrigid : IsRigid p)
    (hpost : ∀ τ : TestTriple (presentationOf U), ∃ E : Finset (TestTriple (presentationOf V)),
      ∀ φ : V ⟶ V, (∀ σ ∈ E, IsNear σ φ (𝟙 V)) → IsNear τ (φ ≫ f) f)
    (a : ActionLift ρ p) (b : ActionLift ρ q) :
    ∃ N : Subgroup G, IsOpen (N : Set G) ∧ ∃ (ha : N ≤ a.subgroup) (hb : N ≤ b.subgroup),
      ∀ (g : G) (hg : g ∈ N), (b.action ⟨g, hb hg⟩).asIso.hom ≫ f = f ≫ (a.action ⟨g, ha hg⟩).asIso.hom := by
  classical
  obtain ⟨E, hE⟩ := hrigid
  choose Ep hEp using hpost
  let N : Subgroup G :=
    { carrier := {g | ∃ (ha : g ∈ a.subgroup) (hb : g ∈ b.subgroup),
        (b.action ⟨g, hb⟩).asIso.hom ≫ f = f ≫ (a.action ⟨g, ha⟩).asIso.hom}
      one_mem' := by
        refine ⟨a.subgroup.one_mem, b.subgroup.one_mem, ?_⟩
        have h1 : a.action ⟨1, a.subgroup.one_mem⟩ = 1 := map_one a.action
        have h2 : b.action ⟨1, b.subgroup.one_mem⟩ = 1 := map_one b.action
        rw [h1, h2]
        exact (Category.id_comp f).trans (Category.comp_id f).symm
      mul_mem' := by
        rintro g h ⟨hga, hgb, hg⟩ ⟨hha, hhb, hh⟩
        refine ⟨a.subgroup.mul_mem hga hha, b.subgroup.mul_mem hgb hhb, ?_⟩
        have h1 : a.action ⟨g * h, a.subgroup.mul_mem hga hha⟩ =
            a.action ⟨g, hga⟩ * a.action ⟨h, hha⟩ := map_mul a.action ⟨g, hga⟩ ⟨h, hha⟩
        have h2 : b.action ⟨g * h, b.subgroup.mul_mem hgb hhb⟩ =
            b.action ⟨g, hgb⟩ * b.action ⟨h, hhb⟩ := map_mul b.action ⟨g, hgb⟩ ⟨h, hhb⟩
        rw [h1, h2]
        change ((b.action ⟨h, hhb⟩).asIso.hom ≫ (b.action ⟨g, hgb⟩).asIso.hom) ≫ f =
          f ≫ ((a.action ⟨h, hha⟩).asIso.hom ≫ (a.action ⟨g, hga⟩).asIso.hom)
        rw [Category.assoc, hg, ← Category.assoc, hh, Category.assoc]
      inv_mem' := by
        rintro g ⟨hga, hgb, hg⟩
        refine ⟨a.subgroup.inv_mem hga, b.subgroup.inv_mem hgb, ?_⟩
        have h1 : a.action ⟨g⁻¹, a.subgroup.inv_mem hga⟩ = (a.action ⟨g, hga⟩)⁻¹ :=
          map_inv a.action ⟨g, hga⟩
        have h2 : b.action ⟨g⁻¹, b.subgroup.inv_mem hgb⟩ = (b.action ⟨g, hgb⟩)⁻¹ :=
          map_inv b.action ⟨g, hgb⟩
        rw [h1, h2]
        change (b.action ⟨g, hgb⟩).asIso.inv ≫ f = f ≫ (a.action ⟨g, hga⟩).asIso.inv
        rw [← Category.comp_id ((b.action ⟨g, hgb⟩).asIso.inv ≫ f),
          ← (a.action ⟨g, hga⟩).asIso.hom_inv_id, Category.assoc, ← Category.assoc f, ← hg]
        rw [Category.assoc]
        exact Iso.inv_hom_id_assoc (b.action ⟨g, hgb⟩).asIso _ }
  let W : Set G := (a.subgroup : Set G) ∩ (b.subgroup : Set G) ∩
    ((⋂ τ ∈ E, {g : G | ∃ hg : g ∈ a.subgroup, IsNear τ (a.action ⟨g, hg⟩).asIso.hom (𝟙 U)}) ∩
      ⋂ τ ∈ E, ⋂ σ ∈ Ep τ, {g : G | ∃ hg : g ∈ b.subgroup, IsNear σ (b.action ⟨g, hg⟩).asIso.hom (𝟙 V)})
  have hW : W ∈ 𝓝 (1 : G) := by
    refine Filter.inter_mem (Filter.inter_mem a.subgroup_mem_nhds b.subgroup_mem_nhds)
      (Filter.inter_mem ((Filter.biInter_finset_mem E).2 fun τ _ => a.eventually_isNear τ)
        ((Filter.biInter_finset_mem E).2 fun τ _ =>
          (Filter.biInter_finset_mem (Ep τ)).2 fun σ _ => b.eventually_isNear σ))
  have hWN : W ⊆ (N : Set G) := by
    rintro g ⟨⟨hga, hgb⟩, hgE, hgEp⟩
    refine ⟨hga, hgb, ?_⟩
    have hgE' : ∀ τ ∈ E, IsNear τ (a.action ⟨g, hga⟩).asIso.hom (𝟙 U) := by
      intro τ hτ
      obtain ⟨_, h⟩ := Set.mem_iInter₂.mp hgE τ hτ
      exact h
    have hgEp' : ∀ τ ∈ E, ∀ σ ∈ Ep τ, IsNear σ (b.action ⟨g, hgb⟩).asIso.hom (𝟙 V) := by
      intro τ hτ σ hσ
      obtain ⟨_, h⟩ := Set.mem_iInter₂.mp (Set.mem_iInter₂.mp hgEp τ hτ) σ hσ
      exact h
    refine hE V f _ _ ?_ fun τ hτ => ⟨?_, ?_⟩
    · rw [Category.assoc, hfpq, b.equivariant ⟨g, hgb⟩, Category.assoc,
        a.equivariant ⟨g, hga⟩, ← Category.assoc, hfpq]
    · exact (hEp τ _ fun σ hσ => hgEp' τ hτ σ hσ).symm
    · have h := (hgE' τ hτ).precomp f
      rw [Category.comp_id] at h
      exact h.symm
  refine ⟨N, Subgroup.isOpen_of_mem_nhds N (Filter.mem_of_superset hW hWN),
    fun g hg => hg.1, fun g hg => hg.2.1, fun g hg => hg.2.2⟩

end Langlands.Analytic.SaturatedAtlasPresentation
