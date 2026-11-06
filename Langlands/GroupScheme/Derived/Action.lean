import Langlands.GroupScheme.Derived.Functoriality
import Langlands.GroupScheme.Derived.FieldBaseChangeAssembly
import Langlands.GroupScheme.AutomorphicAction.BaseChange
import Langlands.GroupScheme.Reductive.UnipotentRadicalAction

/-! # Automorphic actions on full derived subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {H G D : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom H.X.hom] [IsAffineHom G.X.hom] {d : D ⟶ G}

set_option backward.isDefEq.respectTransparency.types false in
/-- Every actual affine group action by automorphisms preserves a supplied
closed representative of the full derived subgroup, on every test scheme. -/
theorem IsDerivedSubgroup.isStable (hd : IsDerivedSubgroup d)
    (a : AutomorphicAction H G) : a.IsStable (SubgroupFunctor.range d) := by
  let : IsClosedImmersion d.hom.hom.left := hd.1
  let : IsAffineHom D.X.hom := by
    rw [← d.hom.hom.w]
    infer_instance
  let W := H.X ⊗ D.X
  let b := W.hom
  let : IsAffineHom b := by
    change IsAffineHom (CategoryTheory.Limits.pullback.fst H.X.hom D.X.hom ≫ H.X.hom)
    let : IsAffineHom (CategoryTheory.Limits.pullback.fst H.X.hom D.X.hom) :=
      MorphismProperty.pullback_fst _ _ (inferInstance : IsAffineHom D.X.hom)
    infer_instance
  let T₀ : Over W.left := Over.mk (𝟙 W.left)
  let e : (Over.map b).obj T₀ ≅ W := Over.isoMk (Iso.refl _) (by simp [T₀, b])
  let h : T₀ ⟶ ((GroupScheme.baseChange b).obj H).X :=
    (baseChangePointsEquiv b H T₀).symm (e.hom ≫ fst H.X D.X)
  let x : T₀ ⟶ ((GroupScheme.baseChange b).obj G).X :=
    (baseChangePointsEquiv b G T₀).symm (e.hom ≫ snd H.X D.X ≫ d.hom.hom)
  have heq := derivedSubgroup_baseChange_eq_of_field b G
  have hx : x ∈ (derivedSubgroup ((GroupScheme.baseChange b).obj G)).carrier T₀ := by
    rw [← heq]
    change baseChangePointsEquiv b G T₀ x ∈ (derivedSubgroup G).carrier _
    rw [MulEquiv.apply_symm_apply, ← hd.2]
    exact SubgroupFunctor.mem_range.mpr ⟨e.hom ≫ snd H.X D.X, Category.assoc _ _ _⟩
  have ha := mem_derivedSubgroup_comp ((a.baseChange b).sectionIso h).hom hx
  rw [AutomorphicAction.comp_sectionIso_hom] at ha
  have hu : toUnit T₀ = 𝟙 T₀ := toUnit_unique _ _
  rw [hu, Category.id_comp, ← heq] at ha
  change baseChangePointsEquiv b G T₀ ((a.baseChange b).act h x) ∈
    (derivedSubgroup G).carrier _ at ha
  rw [a.baseChangePointsEquiv_act, MulEquiv.apply_symm_apply,
    MulEquiv.apply_symm_apply, ← a.naturality] at ha
  have ha' := (derivedSubgroup G).comp_mem e.inv ha
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] at ha'
  intro T t g hg
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hg
  rw [hd.2]
  have hres := (derivedSubgroup G).comp_mem (lift t y) ha'
  simpa only [a.naturality, lift_fst, lift_snd_assoc] using hres

/-- The actual induced action on a supplied full derived-subgroup representative. -/
def IsDerivedSubgroup.action (hd : IsDerivedSubgroup d)
    (a : AutomorphicAction H G) : AutomorphicAction H D :=
  a.onRepresentedSubgroup d hd.isRepresentedBy (by
    rw [← hd.2]
    exact hd.isStable a)

/-- The derived inclusion intertwines the induced and original actions. -/
theorem IsDerivedSubgroup.action_act_comp (hd : IsDerivedSubgroup d)
    (a : AutomorphicAction H G) {T : Over (Spec (CommRingCat.of k))}
    (h : T ⟶ H.X) (x : T ⟶ D.X) :
    (hd.action a).act h x ≫ d.hom.hom = a.act h (x ≫ d.hom.hom) :=
  a.onRepresentedSubgroup_act_comp d hd.isRepresentedBy _ h x

/-- The full derived subgroup of a closed normal affine subgroup is normal
in the ambient affine group, on every test scheme. -/
theorem IsDerivedSubgroup.isNormal_comp (hd : IsDerivedSubgroup d)
    {A : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom A.X.hom]
    (i : G ⟶ A) (hi : IsClosedSubgroup i)
    (hn : (SubgroupFunctor.range i).IsNormal) :
    (SubgroupFunctor.range (d ≫ i)).IsNormal := by
  let : IsClosedImmersion i.hom.hom.left := hi
  have hiRep : (SubgroupFunctor.range i).IsRepresentedBy i :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  let a := AutomorphicAction.conjugation (𝟙 A)
  have hs : a.IsStable (SubgroupFunctor.range i) := by
    intro T g x hx
    simpa only [a, AutomorphicAction.conjugation_act, Grp.id_hom_hom,
      Category.comp_id] using hn T g x (Subgroup.mem_top _) hx
  let aG := a.onRepresentedSubgroup i hiRep hs
  have hD := hd.isStable aG
  intro T g x _ hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  have hy := hD T g (y ≫ d.hom.hom) (SubgroupFunctor.mem_range.mpr ⟨y, rfl⟩)
  obtain ⟨z, hz⟩ := SubgroupFunctor.mem_range.mp hy
  refine SubgroupFunctor.mem_range.mpr ⟨z, ?_⟩
  rw [Grp.comp_hom_hom, ← Category.assoc, hz]
  change aG.act g (y ≫ d.hom.hom) ≫ i.hom.hom = _
  rw [AutomorphicAction.onRepresentedSubgroup_act_comp]
  simp only [a, AutomorphicAction.conjugation_act, Grp.id_hom_hom,
    Category.comp_id, Category.assoc]

end Langlands.GroupScheme
