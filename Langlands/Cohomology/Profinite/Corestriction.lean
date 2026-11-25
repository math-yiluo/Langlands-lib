import Langlands.Cohomology.Profinite.Shapiro

namespace Langlands.ProfiniteCohomology

open CategoryTheory Limits Topology

universe u

variable {k G : Type u} [CommRing k] [Group G]

section Maps

variable (U : Subgroup G)

section Trace

variable (A : Rep.{u} k G)

noncomputable def coindTraceTerm (c : G ⧸ U) :
    Rep.coind U.subtype (Rep.res U.subtype A) →ₗ[k] A :=
  A.ρ c.out ∘ₗ (LinearMap.proj c.out⁻¹).comp
    (Representation.coindV U.subtype (Rep.res U.subtype A).ρ).subtype

theorem coindTraceTerm_apply (f : Rep.coind U.subtype (Rep.res U.subtype A)) (x : G) :
    coindTraceTerm U A (x : G ⧸ U) f = A.ρ x (f.1 x⁻¹) := by
  change A.ρ (x : G ⧸ U).out (f.1 (x : G ⧸ U).out⁻¹) = A.ρ x (f.1 x⁻¹)
  obtain ⟨u, hu⟩ : ∃ u : U, (x : G ⧸ U).out = x * u := by
    have h := QuotientGroup.mk_out_eq_mul U x
    obtain ⟨u, hu⟩ := h
    exact ⟨u, hu⟩
  rw [hu]
  have h1 : (x * (u : G))⁻¹ = U.subtype u⁻¹ * x⁻¹ := by simp
  rw [h1, f.2 u⁻¹ x⁻¹]
  change A.ρ (x * u) (A.ρ (u⁻¹ : U) (f.1 x⁻¹)) = _
  rw [← Module.End.mul_apply, ← map_mul]
  simp

variable [U.FiniteIndex]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

noncomputable def coindTrace : Rep.coind U.subtype (Rep.res U.subtype A) ⟶ A :=
  Rep.ofHom ⟨∑ c : G ⧸ U, coindTraceTerm U A c, fun g => by
    ext f
    change (∑ c : G ⧸ U, coindTraceTerm U A c) ((Rep.coind U.subtype (Rep.res U.subtype A)).ρ g f) =
      A.ρ g ((∑ c : G ⧸ U, coindTraceTerm U A c) f)
    rw [LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
    refine (Fintype.sum_equiv (MulAction.toPerm g) _ _ fun c => ?_).symm
    induction c using QuotientGroup.induction_on with
    | H x =>
      simp only [MulAction.toPerm_apply, MulAction.Quotient.smul_mk]
      rw [coindTraceTerm_apply, coindTraceTerm_apply]
      change A.ρ g (A.ρ x (f.1 x⁻¹)) = A.ρ (g * x) (f.1 ((g * x)⁻¹ * g))
      rw [← Module.End.mul_apply, ← map_mul]
      simp [mul_inv_rev, mul_assoc]⟩

theorem coindTrace_hom_apply (f : Rep.coind U.subtype (Rep.res U.subtype A)) :
    (coindTrace U A).hom f = ∑ c : G ⧸ U, coindTraceTerm U A c f := by
  simp [coindTrace]

theorem coindUnit_comp_coindTrace : coindUnit U A ≫ coindTrace U A = U.index • 𝟙 A := by
  ext a
  change (coindTrace U A).hom ((coindUnit U A).hom a) = (U.index • 𝟙 A : A ⟶ A).hom a
  rw [coindTrace_hom_apply]
  have h : ∀ c : G ⧸ U, coindTraceTerm U A c ((coindUnit U A).hom a) = a := fun c => by
    induction c using QuotientGroup.induction_on with
    | H x =>
      rw [coindTraceTerm_apply, coindUnit_hom_apply, ← Module.End.mul_apply, ← map_mul]
      simp
  simp only [h, Finset.sum_const, Finset.card_univ]
  rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card, Rep.nsmul_hom]
  rfl

end Trace

end Maps

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (U : OpenSubgroup G)

section Corestriction

variable (A : Rep.{u} k G) [IsSmoothRep A]

set_option backward.isDefEq.respectTransparency false in
-- The coefficient map `coindUnit` is used at the definitionally equal type `Rep.res (.id G) _ ⟶ _`.
theorem res_eq_coindUnit_shapiroMap (n : ℕ) :
    res A (U : Subgroup G) n =
      map (.id G) (coindUnit (U : Subgroup G) A) n ≫
        shapiroMap U (Rep.res (U : Subgroup G).subtype A) n := by
  rw [shapiroMap, ← map_comp]
  erw [coindUnit_comp_coindEvalOne]
  rfl

omit [CompactSpace G] in
theorem map_id_nsmul {B : Rep.{u} k G} [IsSmoothRep B] (f : A ⟶ B) (m n : ℕ) :
    map (.id G) (m • f : A ⟶ B) n = m • map (.id G) f n := by
  have h : cochainsMap (.id G) (m • f : A ⟶ B) = m • cochainsMap (.id G) f := by
    induction m with
    | zero =>
      rw [zero_smul, zero_smul]
      exact cochainsMap_id_zero
    | succ m ih =>
      rw [succ_nsmul, succ_nsmul, ← ih]
      ext i c : 3
      rfl
  unfold map
  rw [h]
  exact (HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.up ℕ) n).map_nsmul

noncomputable def cores (n : ℕ) :
    cohomology (Rep.res (U : Subgroup G).subtype A) n ⟶ cohomology A n :=
  inv (shapiroMap U (Rep.res (U : Subgroup G).subtype A) n) ≫
    map (.id G) (coindTrace (U : Subgroup G) A) n

theorem res_comp_cores (n : ℕ) :
    res A (U : Subgroup G) n ≫ cores U A n = (U : Subgroup G).index • 𝟙 _ := by
  rw [res_eq_coindUnit_shapiroMap, cores, Category.assoc, IsIso.hom_inv_id_assoc,
    ← map_id_comp, coindUnit_comp_coindTrace, map_id_nsmul, map_id]

end Corestriction

end Langlands.ProfiniteCohomology
