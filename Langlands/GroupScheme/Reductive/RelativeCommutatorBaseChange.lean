import Langlands.GroupScheme.Reductive.RelativeDerivedInputs

/-! # Base change of fppf-local commutator membership -/

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.RelativeDerived

private theorem commutator_map_mem {A B : Type*} [Group A] [Group B]
    (f : A →* B) {x : A} (hx : x ∈ _root_.commutator A) :
    f x ∈ _root_.commutator B := by
  have hle : (_root_.commutator A).map f ≤ _root_.commutator B := by
    rw [map_commutator_eq]
    exact Subgroup.commutator_mono le_top le_top
  exact hle (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)

private theorem commutator_mulEquiv_iff {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (x : A) :
    e x ∈ _root_.commutator B ↔ x ∈ _root_.commutator A := by
  constructor
  · intro hx
    have h := commutator_map_mem e.symm.toMonoidHom hx
    change e.symm (e x) ∈ _root_.commutator A at h
    simpa only [e.symm_apply_apply] using h
  · exact commutator_map_mem e.toMonoidHom

variable {S S' : Scheme.{u}} (b : S' ⟶ S) (G : GroupScheme S)

/-- The pullback equivalence on points identifies the fppf-local commutator predicates. -/
theorem locallyCommutator_baseChange_iff (T : Over S')
    (x : T ⟶ ((GroupScheme.baseChange b).obj G).X) :
    LocallyCommutator x ↔ LocallyCommutator (baseChangePointsEquiv b G T x) := by
  constructor
  · rintro ⟨𝒰, h𝒰⟩
    refine ⟨𝒰, fun i => ?_⟩
    let V : Over S' := Over.mk (𝒰.f i ≫ T.hom)
    let W : Over S := Over.mk (𝒰.f i ≫ (T.hom ≫ b))
    let a : V ⟶ T := Over.homMk (𝒰.f i) rfl
    let r : W ⟶ (Over.map b).obj V := Over.homMk (𝟙 _) (by
      change (𝟙 _) ≫ ((𝒰.f i ≫ T.hom) ≫ b) = 𝒰.f i ≫ (T.hom ≫ b)
      simp only [Category.id_comp, Category.assoc])
    let f : (V ⟶ ((GroupScheme.baseChange b).obj G).X) →* (W ⟶ G.X) :=
      (((yonedaGrp.obj G).map r.op).hom).comp (baseChangePointsEquiv b G V).toMonoidHom
    have he : f (a ≫ x) =
        (Over.homMk (𝒰.f i) rfl : W ⟶ (Over.map b).obj T) ≫
          baseChangePointsEquiv b G T x := by
      apply Over.OverMorphism.ext
      change (𝟙 _) ≫ ((𝒰.f i ≫ x.left) ≫ pullback.fst G.X.hom b) =
        𝒰.f i ≫ (x.left ≫ pullback.fst G.X.hom b)
      simp only [Category.id_comp, Category.assoc]
    rw [← he]
    exact commutator_map_mem f (h𝒰 i)
  · rintro ⟨𝒰, h𝒰⟩
    refine ⟨𝒰, fun i => ?_⟩
    let V : Over S' := Over.mk (𝒰.f i ≫ T.hom)
    let W : Over S := Over.mk (𝒰.f i ≫ (T.hom ≫ b))
    let a : V ⟶ T := Over.homMk (𝒰.f i) rfl
    let r : (Over.map b).obj V ⟶ W := Over.homMk (𝟙 _) (by
      change (𝟙 _) ≫ (𝒰.f i ≫ (T.hom ≫ b)) = (𝒰.f i ≫ T.hom) ≫ b
      simp only [Category.id_comp, Category.assoc])
    let f : (W ⟶ G.X) →* ((Over.map b).obj V ⟶ G.X) :=
      ((yonedaGrp.obj G).map r.op).hom
    have he : f ((Over.homMk (𝒰.f i) rfl : W ⟶ (Over.map b).obj T) ≫
        baseChangePointsEquiv b G T x) = baseChangePointsEquiv b G V (a ≫ x) := by
      apply Over.OverMorphism.ext
      change (𝟙 _) ≫ (𝒰.f i ≫ (x.left ≫ pullback.fst G.X.hom b)) =
        (𝒰.f i ≫ x.left) ≫ pullback.fst G.X.hom b
      simp only [Category.id_comp, Category.assoc]
    apply (commutator_mulEquiv_iff (baseChangePointsEquiv b G V) (a ≫ x)).mp
    rw [← he]
    exact commutator_map_mem f (h𝒰 i)

/-- Pullback identifies the actual sets of fppf-local commutator points. -/
def locallyCommutatorBaseChangeEquiv (T : Over S') :
    {x : T ⟶ ((GroupScheme.baseChange b).obj G).X // LocallyCommutator x} ≃
      {x : (Over.map b).obj T ⟶ G.X // LocallyCommutator x} where
  toFun x := ⟨baseChangePointsEquiv b G T x.val,
    (locallyCommutator_baseChange_iff b G T x.val).mp x.property⟩
  invFun x := ⟨(baseChangePointsEquiv b G T).symm x.val,
    (locallyCommutator_baseChange_iff b G T _).mpr (by
      simpa only [MulEquiv.apply_symm_apply] using x.property)⟩
  left_inv x := Subtype.ext ((baseChangePointsEquiv b G T).symm_apply_apply x.val)
  right_inv x := Subtype.ext ((baseChangePointsEquiv b G T).apply_symm_apply x.val)

end Langlands.GroupScheme.RelativeDerived
