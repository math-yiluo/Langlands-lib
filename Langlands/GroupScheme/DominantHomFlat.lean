import Langlands.GroupScheme.OrbitMapFlatProof
import Mathlib.RingTheory.RingHom.FaithfullyFlat

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-!
# Dominant homomorphisms onto reduced groups are flat
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj
open AlgebraicGeometry TopologicalSpace
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.DominantHomFlat

/-- Flatness descends along a faithfully flat second factor. -/
theorem _root_.RingHom.Flat.of_comp_faithfullyFlat {R S T : Type*} [CommRing R] [CommRing S]
    [CommRing T] {f : R →+* S} {g : S →+* T} (hg : g.FaithfullyFlat) (h : (g.comp f).Flat) :
    f.Flat := by
  algebraize [f, g, g.comp f]
  have : Module.FaithfullyFlat S T := hg
  have : Module.Flat R T := h
  show Module.Flat R S
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro N P _ _ _ _ φ hφ
  rw [← LinearMap.baseChange_eq_ltensor,
    ← Module.FaithfullyFlat.lTensor_injective_iff_injective S T (φ.baseChange S)]
  have key : ∀ x, TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T P
      (LinearMap.lTensor T (φ.baseChange S) x) = LinearMap.lTensor T φ
        (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T N x) := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul t y =>
      induction y using TensorProduct.inductionOn with
      | tmul s n => simp
      | add a b ha hb => simp only [TensorProduct.tmul_add, map_add, ha, hb]
    | add a b ha hb => simp only [map_add, ha, hb]
  have hinj := Module.Flat.lTensor_preserves_injective_linearMap (M := T) φ hφ
  intro x y hxy
  have := congrArg (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T P) hxy
  rw [key, key] at this
  exact (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T N).injective (hinj this)

section Stalks

variable {X X' Y Y' : Scheme.{u}}

/-- Flatness near a point gives flatness of the stalk map there. -/
theorem flat_stalkMap_of_flatNear (f : X ⟶ Y) (z : X) (hz : OrbitMapFlat.FlatNear f z) :
    (f.stalkMap z).hom.Flat := by
  obtain ⟨U, V, hzV, e, hflat⟩ := hz
  rw [← RingHom.Flat.respectsIso.arrow_mk_iso_iff (Scheme.Hom.resLEStalkMap f e ⟨z, hzV⟩)]
  exact Flat.stalkMap _ _

/-- Local flatness descends through a commuting square whose horizontal maps are flat. -/
theorem flat_stalkMap_of_comm (f : X ⟶ Y) (f' : X' ⟶ Y') (g : Y' ⟶ Y) (g' : X' ⟶ X)
    (h : f' ≫ g = g' ≫ f) [Flat g] [Flat g'] (z : X') (hz : (f'.stalkMap z).hom.Flat) :
    (f.stalkMap (g' z)).hom.Flat := by
  have h1 : ((f' ≫ g).stalkMap z).hom.Flat := by
    rw [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp]
    exact RingHom.Flat.comp (Flat.stalkMap g (f' z)) hz
  rw [Scheme.Hom.stalkMap_congr_hom _ _ h z, CommRingCat.hom_comp,
    RingHom.Flat.respectsIso.cancel_left_isIso] at h1
  rw [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp] at h1
  refine RingHom.Flat.of_comp_faithfullyFlat ?_ h1
  algebraize [(g'.stalkMap z).hom]
  have : Module.Flat _ _ := Flat.stalkMap g' z
  have : IsLocalHom (algebraMap (X.presheaf.stalk (g' z)) (X'.presheaf.stalk z)) :=
    inferInstanceAs (IsLocalHom (g'.stalkMap z).hom)
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

end Stalks

section Shear

variable {C : Type*} [Category C] [CartesianMonoidalCategory C] {G T : C} [GrpObj G]

/-- The left shear `(t, x) ↦ (t, u t * x)` of `T ⊗ G`. -/
def shearLeft (u : T ⟶ G) : T ⊗ G ≅ T ⊗ G where
  hom := lift (fst T G) ((fst T G ≫ u) * snd T G)
  inv := lift (fst T G) ((fst T G ≫ u)⁻¹ * snd T G)
  hom_inv_id := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [MonObj.comp_mul, GrpObj.comp_inv]
  inv_hom_id := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [MonObj.comp_mul]

theorem shearLeft_hom_snd (u : T ⟶ G) :
    (shearLeft u).hom ≫ snd T G = (fst T G ≫ u) * snd T G :=
  lift_snd _ _

/-- The right shear `(x, t) ↦ (x * u t, t)` of `G ⊗ T`. -/
def shearRight (u : T ⟶ G) : G ⊗ T ≅ G ⊗ T where
  hom := lift (fst G T * (snd G T ≫ u)) (snd G T)
  inv := lift (fst G T * (snd G T ≫ u)⁻¹) (snd G T)
  hom_inv_id := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [MonObj.comp_mul, GrpObj.comp_inv]
  inv_hom_id := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [MonObj.comp_mul]

theorem shearRight_hom_fst (u : T ⟶ G) :
    (shearRight u).hom ≫ fst G T = fst G T * (snd G T ≫ u) :=
  lift_fst _ _

end Shear

section Flatness

variable {S : Scheme.{u}} {G T : Over S} [GrpObj G]

/-- Left translation by a family of points parametrised by a flat scheme is flat. -/
theorem flat_mul_left (u : T ⟶ G) [Flat T.hom] :
    Flat ((fst T G ≫ u) * snd T G).left := by
  rw [← shearLeft_hom_snd, Over.comp_left, Over.snd_left]
  infer_instance

/-- Right translation by a family of points parametrised by a flat scheme is flat. -/
theorem flat_mul_right (u : T ⟶ G) [Flat T.hom] :
    Flat (fst G T * (snd G T ≫ u)).left := by
  rw [← shearRight_hom_fst, Over.comp_left, Over.fst_left]
  infer_instance

/-- Left translation by a family of points parametrised by a surjective scheme is surjective. -/
theorem surjective_mul_left (u : T ⟶ G) [Surjective T.hom] :
    Surjective ((fst T G ≫ u) * snd T G).left := by
  rw [← shearLeft_hom_snd, Over.comp_left, Over.snd_left]
  infer_instance

end Flatness

section Dominant

variable {k : Type u} [Field k]

/-- A dominant homomorphism of group schemes over a field, of finite type and quasi-compact,
onto a reduced locally noetherian group scheme is flat. -/
theorem flat_of_isDominant {A B : GroupScheme (Spec (.of k))} (f : A ⟶ B)
    [LocallyOfFiniteType f.hom.hom.left] [QuasiCompact f.hom.hom.left]
    [IsLocallyNoetherian B.X.left] [IsReduced B.X.left] [IsDominant f.hom.hom.left] :
    Flat f.hom.hom.left := by
  have : Subsingleton (Spec (CommRingCat.of k)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  set φ := f.hom.hom with hφ
  refine Flat.of_stalkMap φ.left fun x => ?_
  obtain ⟨U, hU, hflat⟩ := OrbitMapFlat.exists_open_flatNear φ.left (φ.left x)
  obtain ⟨w, hw⟩ := φ.left.denseRange.exists_mem_open U.isOpen hU
  let W : A.X.left.Opens := φ.left ⁻¹ᵁ U
  let W' : Over (Spec (.of k)) := Over.mk (W.ι ≫ A.X.hom)
  let ιW : W' ⟶ A.X := Over.homMk W.ι rfl
  have hW : Flat (ιW ≫ φ).left := by
    refine Flat.of_stalkMap _ fun z => ?_
    rw [Over.comp_left, Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp]
    have : Flat ιW.left := inferInstanceAs (Flat W.ι)
    exact RingHom.Flat.comp (flat_stalkMap_of_flatNear φ.left _ (hflat _ z.2))
      (Flat.stalkMap ιW.left z)
  have : Surjective W'.hom := ⟨fun s => ⟨⟨w, hw⟩, Subsingleton.elim _ _⟩⟩
  let g' : W' ⊗ A.X ⟶ A.X := (fst W' A.X ≫ ιW) * snd W' A.X
  let f' : W' ⊗ A.X ⟶ B.X ⊗ A.X := (ιW ≫ φ) ▷ A.X
  let g : B.X ⊗ A.X ⟶ B.X := fst B.X A.X * (snd B.X A.X ≫ φ)
  have hsq : f' ≫ g = g' ≫ φ := by
    simp only [f', g, g', MonObj.comp_mul, MonObj.mul_comp, whiskerRight_fst,
      whiskerRight_snd_assoc, Category.assoc]
  have hsq' : f'.left ≫ g.left = g'.left ≫ φ.left := by
    rw [← Over.comp_left, hsq, Over.comp_left]
  have : Flat g.left := flat_mul_right _
  have : Flat g'.left := flat_mul_left _
  have : Flat f'.left :=
    MorphismProperty.pullbackMap (P := @Flat) hW
      (by change Flat (𝟙 A.X.left); infer_instance) (Over.w (ιW ≫ φ)).symm (by simp)
  have : Surjective g'.left := surjective_mul_left _
  obtain ⟨z, hz⟩ := g'.left.surjective x
  rw [← hz]
  exact flat_stalkMap_of_comm φ.left f'.left g.left g'.left hsq' z (Flat.stalkMap _ z)

/-- A flat homomorphism of group schemes over a field onto an irreducible group scheme is
surjective. -/
theorem surjective_of_flat {A B : GroupScheme (Spec (.of k))} (f : A ⟶ B)
    [Flat f.hom.hom.left] [IrreducibleSpace B.X.left] :
    Surjective f.hom.hom.left := by
  have : Subsingleton (Spec (CommRingCat.of k)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  set φ := f.hom.hom with hφ
  refine ⟨fun b => ?_⟩
  let T : Over (Spec (.of k)) := Over.mk (B.X.left.fromSpecResidueField b ≫ B.X.hom)
  let tb : T ⟶ B.X := Over.homMk (B.X.left.fromSpecResidueField b) rfl
  let α : T ⊗ A.X ⟶ B.X := (fst T A.X ≫ tb) * (snd T A.X ≫ φ)
  have hα : α = T ◁ φ ≫ ((fst T B.X ≫ tb) * snd T B.X) := by
    simp only [α, MonObj.comp_mul, whiskerLeft_fst_assoc, whiskerLeft_snd]
  have : Flat (T ◁ φ).left :=
    MorphismProperty.pullbackMap (P := @Flat)
      (by change Flat (𝟙 T.left); infer_instance) ‹Flat φ.left› (by simp) (Over.w φ).symm
  have : Flat ((fst T B.X ≫ tb) * snd T B.X).left := flat_mul_left _
  have hαf : Flat α.left := by
    rw [hα, Over.comp_left]
    infer_instance
  -- The generic point of `B` lies in the images of `α` and `φ`.
  have hgen : ∀ {Z : Scheme.{u}} (g : Z ⟶ B.X.left) [Flat g] (z : Z),
      genericPoint B.X.left ∈ Set.range g := fun g _ z => by
    obtain ⟨z', -, hz'⟩ := Flat.generalizingMap g (genericPoint_specializes (g z))
    exact ⟨z', hz'⟩
  have : Nonempty T.left := inferInstanceAs (Nonempty (Spec (B.X.left.residueField b)))
  obtain ⟨t⟩ := this
  let s : T ⟶ T ⊗ A.X := lift (𝟙 T) (toUnit T ≫ η[A.X])
  obtain ⟨p, hp⟩ := hgen α.left (s.left t)
  obtain ⟨a, ha⟩ := hgen φ.left ((toUnit T ≫ η[A.X]).left t)
  obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback p a (hp.trans ha.symm)
  let P : Over (Spec (.of k)) := Over.mk (Limits.pullback.snd α.left φ.left ≫ A.X.hom)
  let p1 : P ⟶ T ⊗ A.X := Over.homMk (Limits.pullback.fst α.left φ.left) (by
    simp only [P, Over.mk_hom]
    rw [← Over.w α, ← Over.w φ, Limits.pullback.condition_assoc])
  let p2 : P ⟶ A.X := Over.homMk (Limits.pullback.snd α.left φ.left) rfl
  have hsq : p1 ≫ α = p2 ≫ φ := by
    ext1
    exact Limits.pullback.condition
  have key : p1 ≫ fst T A.X ≫ tb = (p2 * (p1 ≫ snd T A.X)⁻¹) ≫ φ := by
    rw [MonObj.mul_comp, GrpObj.inv_comp, ← hsq]
    simp only [α, MonObj.comp_mul, Category.assoc, mul_inv_cancel_right]
  refine ⟨(p2 * (p1 ≫ snd T A.X)⁻¹).left z, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, ← key]
  simp only [Over.comp_left, Scheme.Hom.comp_apply, tb, Over.homMk_left]
  exact Scheme.fromSpecResidueField_apply b _

end Dominant

end Langlands.GroupScheme.DominantHomFlat
