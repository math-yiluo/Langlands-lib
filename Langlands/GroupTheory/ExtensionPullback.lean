import Mathlib.GroupTheory.GroupExtension.Defs
import Mathlib.GroupTheory.Subgroup.Center

/-! # Pullback of a group extension -/

namespace Langlands.GroupTheory

variable {A E B D X : Type*} [Group A] [Group E] [Group B] [Group D] [Group X]

/-- The subgroup of pairs with equal images in the base group. -/
def pullbackSubgroup (p : E →* B) (f : D →* B) : Subgroup (E × D) :=
  (p.comp (MonoidHom.fst E D)).eqLocus (f.comp (MonoidHom.snd E D))

/-- The group of pairs `(e, d)` satisfying `p e = f d`. -/
abbrev Pullback (p : E →* B) (f : D →* B) := ↥(pullbackSubgroup p f)

/-- The first coordinate map from the pullback. -/
def pullbackFst (p : E →* B) (f : D →* B) : Pullback p f →* E :=
  (MonoidHom.fst E D).comp (pullbackSubgroup p f).subtype

/-- The second coordinate map from the pullback. -/
def pullbackSnd (p : E →* B) (f : D →* B) : Pullback p f →* D :=
  (MonoidHom.snd E D).comp (pullbackSubgroup p f).subtype

@[simp] theorem pullbackFst_apply (p : E →* B) (f : D →* B) (z : Pullback p f) :
    pullbackFst p f z = z.1.1 := rfl

@[simp] theorem pullbackSnd_apply (p : E →* B) (f : D →* B) (z : Pullback p f) :
    pullbackSnd p f z = z.1.2 := rfl

/-- The coordinate maps give the same homomorphism to the base group. -/
theorem pullback_condition (p : E →* B) (f : D →* B) :
    p.comp (pullbackFst p f) = f.comp (pullbackSnd p f) :=
  MonoidHom.ext fun z => z.property

/-- A compatible pair of homomorphisms lifts to the pullback by pairing its values. -/
def pullbackLift (p : E →* B) (f : D →* B) (u : X →* E) (v : X →* D)
    (h : p.comp u = f.comp v) : X →* Pullback p f :=
  (u.prod v).codRestrict (pullbackSubgroup p f) (fun x => DFunLike.congr_fun h x)

@[simp] theorem pullbackFst_comp_lift (p : E →* B) (f : D →* B)
    (u : X →* E) (v : X →* D) (h : p.comp u = f.comp v) :
    (pullbackFst p f).comp (pullbackLift p f u v h) = u := rfl

@[simp] theorem pullbackSnd_comp_lift (p : E →* B) (f : D →* B)
    (u : X →* E) (v : X →* D) (h : p.comp u = f.comp v) :
    (pullbackSnd p f).comp (pullbackLift p f u v h) = v := rfl

/-- The two coordinate maps determine a homomorphism into the pullback. -/
theorem pullback_hom_ext {p : E →* B} {f : D →* B} {u v : X →* Pullback p f}
    (h₁ : (pullbackFst p f).comp u = (pullbackFst p f).comp v)
    (h₂ : (pullbackSnd p f).comp u = (pullbackSnd p f).comp v) : u = v :=
  MonoidHom.ext fun x => Subtype.ext <|
    Prod.ext (DFunLike.congr_fun h₁ x) (DFunLike.congr_fun h₂ x)

/-- The pullback extension has the original kernel, embedded by `a ↦ (S.inl a, 1)`. -/
def pullbackExtension (S : GroupExtension A E B) (f : D →* B) :
    GroupExtension A (Pullback S.rightHom f) D where
  inl := pullbackLift S.rightHom f S.inl 1 (by simp)
  rightHom := pullbackSnd S.rightHom f
  inl_injective := by
    intro a b h
    exact S.inl_injective (congrArg (pullbackFst S.rightHom f) h)
  range_inl_eq_ker_rightHom := by
    apply Subgroup.ext
    intro z
    change (∃ a, _ = z) ↔ z.1.2 = 1
    constructor
    · rintro ⟨a, rfl⟩
      rfl
    · intro hz
      have h : S.rightHom z.1.1 = f z.1.2 := z.property
      have hz₁ : z.1.1 ∈ S.inl.range := by
        rw [S.range_inl_eq_ker_rightHom, MonoidHom.mem_ker, h, hz, map_one]
      obtain ⟨a, ha⟩ := hz₁
      exact ⟨a, Subtype.ext (Prod.ext ha hz.symm)⟩
  rightHom_surjective := by
    intro d
    obtain ⟨e, he⟩ := S.rightHom_surjective (f d)
    exact ⟨⟨(e, d), he⟩, rfl⟩

@[simp] theorem pullbackFst_comp_inl (S : GroupExtension A E B) (f : D →* B) :
    (pullbackFst S.rightHom f).comp (pullbackExtension S f).inl = S.inl := rfl

/-- Pullback preserves centrality of the kernel. -/
theorem pullbackExtension_central (S : GroupExtension A E B) (f : D →* B)
    (hS : S.inl.range ≤ Subgroup.center E) :
    (pullbackExtension S f).inl.range ≤ Subgroup.center (Pullback S.rightHom f) := by
  rintro _ ⟨a, rfl⟩
  apply Subgroup.mem_center_iff.mpr
  intro z
  apply Subtype.ext
  refine Prod.ext (Subgroup.mem_center_iff.mp (hS ⟨a, rfl⟩) z.1.1) ?_
  change z.1.2 * 1 = 1 * z.1.2
  simp

/-- The homomorphism `d ↦ (1, d)` from the kernel of the base map into the pullback. -/
def pullbackKerLift (p : E →* B) (f : D →* B) : f.ker →* Pullback p f :=
  pullbackLift p f 1 f.ker.subtype (MonoidHom.ext fun d => (map_one p).trans d.property.symm)

@[simp] theorem pullbackFst_comp_kerLift (p : E →* B) (f : D →* B) :
    (pullbackFst p f).comp (pullbackKerLift p f) = 1 := rfl

@[simp] theorem pullbackSnd_comp_kerLift (p : E →* B) (f : D →* B) :
    (pullbackSnd p f).comp (pullbackKerLift p f) = f.ker.subtype := rfl

/-- The extension pulled back along `ker f → D → B` splits by `d ↦ (1, d)`. -/
def pullbackKerSplitting (S : GroupExtension A E B) (f : D →* B) :
    (pullbackExtension S (f.comp f.ker.subtype)).Splitting where
  __ := pullbackLift S.rightHom (f.comp f.ker.subtype) 1 (MonoidHom.id _)
    (MonoidHom.ext fun d => (map_one S.rightHom).trans d.property.symm)
  rightInverse_rightHom _ := rfl

end Langlands.GroupTheory
