import Langlands.GroupScheme.IntegralModel
import Langlands.GroupScheme.Reductive.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Integral points of closed subgroups of an integral model -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

omit [IsDomain R] in
/-- The spectrum map of the fraction field has trivial kernel. -/
theorem ker_specAlgebraMap : (Spec.algebraMap R K).ker = ⊥ := by
  have ha : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have h : Function.Injective
      (((Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫
        CommRingCat.ofHom (algebraMap R K)).hom) :=
    ha.comp (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom).1
  rw [← Scheme.ΓSpecIso_naturality] at h
  change Function.Injective
    ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom ∘
      (Spec.algebraMap R K).appTop.hom) at h
  have h' : Function.Injective (Spec.algebraMap R K).appTop.hom := h.of_comp
  rw [Scheme.ker_of_isAffine, (RingHom.injective_iff_ker_eq_bot _).mp h']
  ext U
  simp

omit [IsDomain R] in
/-- Restricting a morphism from `Spec R` to the generic point does not change its kernel. -/
theorem ker_specAlgebraMap_comp {X : Scheme.{u}} (x : Spec (CommRingCat.of R) ⟶ X) :
    (Spec.algebraMap R K ≫ x).ker = x.ker := by
  rw [Scheme.Hom.ker_comp, ker_specAlgebraMap, Scheme.IdealSheafData.map_bot]

variable {G : GroupScheme (Spec (CommRingCat.of K))}
  (M : IntegralModel R K G)
  {H : GroupScheme (Spec (CommRingCat.of R))}

/-- The generic fibre of an integral homomorphism into the model, followed by the
supplied generic identification of the model. -/
def genericHom (j : H ⟶ M.group) :
    (GroupScheme.baseChange (Spec.algebraMap R K)).obj H ⟶ G :=
  (GroupScheme.baseChange (Spec.algebraMap R K)).map j ≫ M.genericIso.hom

/-- The integral sections of `H`, sent through `j` and then to generic points of `G`. -/
def subgroupPointMap (j : H ⟶ M.group) : rationalPoints H →* rationalPoints G :=
  M.integralPointMap.comp (rationalPoints.map j)

/-- The two routes from integral sections of `H` to generic points of `G` agree. -/
theorem subgroupPointMap_apply (j : H ⟶ M.group) (h : rationalPoints H) :
    M.subgroupPointMap j h =
      rationalPoints.map (M.genericHom j)
        (baseChangeSectionHom (Spec.algebraMap R K) H h) := by
  change baseChangeSectionHom (Spec.algebraMap R K) M.group (h ≫ j.hom.hom) ≫
      M.genericIso.hom.hom.hom =
    baseChangeSectionHom (Spec.algebraMap R K) H h ≫
      ((GroupScheme.baseChange (Spec.algebraMap R K)).map j ≫ M.genericIso.hom).hom.hom
  rw [baseChangeSectionHom_naturality, Category.assoc]
  rfl

/-- Integral sections of `H` give integral points lying in the generic image of `H`. -/
theorem range_subgroupPointMap_le (j : H ⟶ M.group) :
    (M.subgroupPointMap j).range ≤
      M.integralPoints ⊓ (rationalPoints.map (M.genericHom j)).range := by
  rintro _ ⟨h, rfl⟩
  exact ⟨⟨rationalPoints.map j h, rfl⟩,
    ⟨baseChangeSectionHom (Spec.algebraMap R K) H h, (M.subgroupPointMap_apply j h).symm⟩⟩

/-- **Integrality through a closed subgroup.** If an integral section of the model has
generic image in the generic fibre of a closed subgroup `H`, it is the image of an
integral section of `H`, and that section restricts to the given generic point. -/
theorem exists_eq_of_integralPointMap_eq (j : H ⟶ M.group) (hj : IsClosedSubgroup j)
    (x : M.integralSections)
    (y : rationalPoints ((GroupScheme.baseChange (Spec.algebraMap R K)).obj H))
    (hxy : M.integralPointMap x = rationalPoints.map (M.genericHom j) y) :
    ∃ h : rationalPoints H, rationalPoints.map j h = x ∧
      baseChangeSectionHom (Spec.algebraMap R K) H h = y := by
  have : IsClosedImmersion j.hom.hom.left := hj
  -- Cancel the generic identification.
  have hsec : baseChangeSectionHom (Spec.algebraMap R K) M.group x =
      y ≫ ((GroupScheme.baseChange (Spec.algebraMap R K)).map j).hom.hom := by
    have h1 : baseChangeSectionHom (Spec.algebraMap R K) M.group x ≫
          M.genericIso.hom.hom.hom =
        (y ≫ ((GroupScheme.baseChange (Spec.algebraMap R K)).map j).hom.hom) ≫
          M.genericIso.hom.hom.hom := by
      rw [Category.assoc]
      exact hxy
    have h2 := congrArg (fun z => z ≫ M.genericIso.inv.hom.hom) h1
    simpa only [Category.assoc, ← Grp.comp_hom_hom, Iso.hom_inv_id, Grp.id_hom_hom,
      Category.comp_id] using h2
  -- The underlying scheme maps over `Spec R`.
  have hleft : Spec.algebraMap R K ≫ x.left =
      (y.left ≫ pullback.fst H.X.hom (Spec.algebraMap R K)) ≫ j.hom.hom.left := by
    rw [← baseChangeSectionHom_fst (Spec.algebraMap R K) M.group x, hsec, Over.comp_left,
      Category.assoc, Category.assoc]
    congr 1
    exact pullback.lift_fst _ _ _
  have hker : j.hom.hom.left.ker ≤ x.left.ker := by
    have hk := (y.left ≫ pullback.fst H.X.hom (Spec.algebraMap R K)).le_ker_comp
      j.hom.hom.left
    rwa [← hleft, ker_specAlgebraMap_comp] at hk
  let l := IsClosedImmersion.lift j.hom.hom.left x.left hker
  have hl : l ≫ j.hom.hom.left = x.left := IsClosedImmersion.lift_fac _ _ _
  have hw : l ≫ H.X.hom = (Over.mk (𝟙 (Spec (CommRingCat.of R)))).hom := by
    rw [← Over.w j.hom.hom, ← Category.assoc, hl, Over.w x]
  refine ⟨Over.homMk l hw, ?_, ?_⟩
  · apply Over.OverMorphism.ext
    change l ≫ j.hom.hom.left = x.left
    exact hl
  · apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · rw [baseChangeSectionHom_fst, ← cancel_mono j.hom.hom.left]
      exact ((Category.assoc _ _ _).trans (congrArg _ hl)).trans hleft
    · have h1 := (baseChangeSectionHom (Spec.algebraMap R K) H (Over.homMk l hw)).w
      have h2 := y.w
      change _ ≫ pullback.snd H.X.hom (Spec.algebraMap R K) = _ at h1
      change _ ≫ pullback.snd H.X.hom (Spec.algebraMap R K) = _ at h2
      rw [h1, h2]

/-- **Integral points of a closed subgroup.** For a closed subgroup `H` of the model, the
integral points of the model that lie in the generic image of `H` are exactly the images
of the integral sections of `H`. -/
theorem integralPoints_inf_range_genericHom (j : H ⟶ M.group) (hj : IsClosedSubgroup j) :
    M.integralPoints ⊓ (rationalPoints.map (M.genericHom j)).range =
      (M.subgroupPointMap j).range := by
  refine le_antisymm ?_ (M.range_subgroupPointMap_le j)
  rintro g ⟨⟨x, rfl⟩, ⟨y, hy⟩⟩
  obtain ⟨h, rfl, -⟩ := M.exists_eq_of_integralPointMap_eq j hj x y hy.symm
  exact ⟨h, rfl⟩

end Langlands.GroupScheme.IntegralModel
