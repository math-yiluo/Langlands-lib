import Langlands.Geometry.FormalGroup.DeligneStructuralCoherence

/-! # The homogeneous projectors of a graded sheaf -/

noncomputable section

universe u

namespace Langlands.DeligneFormalSpace.GradedPiSheaf

open CategoryTheory
open scoped BigOperators

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  {d : ℕ} [NeZero d] {R : Sheaf J CommRingCat.{u}}
  {a b : (R.obj ⋙ CategoryTheory.forget CommRingCat).sections}
  (M : GradedPiSheaf d R a) (N : GradedPiSheaf d R b)

/-- The endomorphism of the total sheaf projecting to the actual homogeneous part. -/
def componentProjector (i : ZMod d) : M.module ⟶ M.module :=
  M.projection i ≫ M.componentInclusion i

theorem hom_ext_componentInclusions {V : SheafOfModules (ringSheaf R)}
    {f g : M.module ⟶ V}
    (h : ∀ i, M.componentInclusion i ≫ f = M.componentInclusion i ≫ g) : f = g := by
  calc
    f = (∑ i, M.projection i ≫ M.componentInclusion i) ≫ f := by
      rw [M.sum_projection_inclusion, Category.id_comp]
    _ = (∑ i, M.projection i ≫ M.componentInclusion i) ≫ g := by
      simp only [Preadditive.sum_comp, Category.assoc, h]
    _ = g := by rw [M.sum_projection_inclusion, Category.id_comp]

/-- Compute a canonical component projector from any split presentation of the components. -/
theorem componentProjector_of_splitting
    {W : ZMod d → SheafOfModules (ringSheaf R)}
    (j : ∀ i, W i ⟶ M.module) (p : ∀ i, M.module ⟶ W i)
    (e : ∀ i, W i ≅ M.componentSheaf i)
    (he : ∀ i, (e i).hom ≫ M.componentInclusion i = j i)
    (hdiag : ∀ i, j i ≫ p i = 𝟙 (W i))
    (hoff : ∀ {i k}, k ≠ i → j k ≫ p i = 0) (i : ZMod d) :
    M.componentProjector i = p i ≫ j i := by
  apply M.hom_ext_componentInclusions
  intro k
  apply (cancel_epi (e k).hom).mp
  by_cases hk : k = i
  · subst k
    simp only [componentProjector, ← Category.assoc, M.inclusion_projection,
      he, hdiag, Category.id_comp]
  · simp only [componentProjector, ← Category.assoc, M.inclusion_projection_ne hk,
      Limits.comp_zero, Limits.zero_comp, he, hoff hk]

variable {M N} {i : ZMod d}

private theorem componentIso_hom_inclusion_aux (f : M.module ⟶ N.module)
    (h : M.componentProjector i ≫ f = f ≫ N.componentProjector i) :
    (M.componentInclusion i ≫ f ≫ N.projection i) ≫ N.componentInclusion i =
      M.componentInclusion i ≫ f := by
  calc
    _ = M.componentInclusion i ≫ (f ≫ N.componentProjector i) := by
      simp only [componentProjector, Category.assoc]
    _ = M.componentInclusion i ≫ (M.componentProjector i ≫ f) := by rw [h]
    _ = _ := by simp only [componentProjector, ← Category.assoc,
      M.inclusion_projection, Category.id_comp]

private theorem componentIso_inv_projector_aux (e : M.module ≅ N.module)
    (h : M.componentProjector i ≫ e.hom = e.hom ≫ N.componentProjector i) :
    N.componentProjector i ≫ e.inv = e.inv ≫ M.componentProjector i := by
  apply (cancel_mono e.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, h, Iso.inv_hom_id_assoc]

/-- An isomorphism of total sheaves intertwining the projectors restricts to a component iso. -/
def componentIsoOfProjector (e : M.module ≅ N.module)
    (h : M.componentProjector i ≫ e.hom = e.hom ≫ N.componentProjector i) :
    M.componentSheaf i ≅ N.componentSheaf i where
  hom := M.componentInclusion i ≫ e.hom ≫ N.projection i
  inv := N.componentInclusion i ≫ e.inv ≫ M.projection i
  hom_inv_id := by
    let : Mono (M.componentInclusion i) := inferInstanceAs (Mono ((M.component i).ι))
    apply (cancel_mono (M.componentInclusion i)).mp
    rw [Category.assoc, componentIso_hom_inclusion_aux e.inv (componentIso_inv_projector_aux e h),
      ← Category.assoc, componentIso_hom_inclusion_aux e.hom h,
      Category.assoc, e.hom_inv_id, Category.comp_id, Category.id_comp]
  inv_hom_id := by
    let : Mono (N.componentInclusion i) := inferInstanceAs (Mono ((N.component i).ι))
    apply (cancel_mono (N.componentInclusion i)).mp
    rw [Category.assoc, componentIso_hom_inclusion_aux e.hom h,
      ← Category.assoc, componentIso_hom_inclusion_aux e.inv (componentIso_inv_projector_aux e h),
      Category.assoc, e.inv_hom_id, Category.comp_id, Category.id_comp]

@[reassoc]
theorem componentIsoOfProjector_hom_inclusion (e : M.module ≅ N.module)
    (h : M.componentProjector i ≫ e.hom = e.hom ≫ N.componentProjector i) :
    (componentIsoOfProjector e h).hom ≫ N.componentInclusion i =
      M.componentInclusion i ≫ e.hom :=
  componentIso_hom_inclusion_aux e.hom h

section Schemes

open AlgebraicGeometry

variable {S S' : Scheme.{u}} {c c' : Γ(S, ⊤)}
  (T : GradedPiSheaf d S.sheaf (schemeScalar S c))

/-- Structural pullback carries the actual homogeneous projector to the corresponding projector. -/
theorem componentProjector_pullback (f : S' ⟶ S) (i : ZMod d) :
    (T.pullback f).componentProjector i = (Scheme.Modules.pullback f).map (T.componentProjector i) := by
  calc
    _ = T.pullbackProjection f i ≫ T.pullbackInclusion f i :=
      (T.pullback f).componentProjector_of_splitting
        (T.pullbackInclusion f) (T.pullbackProjection f) (T.pullbackComponentIso f)
        (T.pullbackComponentIso_hom_inclusion f) (T.pullbackInclusion_projection f)
        (fun h => T.pullbackInclusion_projection_ne f h) i
    _ = _ := ((Scheme.Modules.pullback f).map_comp (T.projection i) (T.componentInclusion i)).symm

/-- Restate the scalar power relation along an equality of global scalars. -/
def changeScalar (h : c = c') : GradedPiSheaf d S.sheaf (schemeScalar S c') where
  module := T.module
  pi := T.pi
  pi_pow U := h ▸ T.pi_pow U
  component := T.component
  isInternal := T.isInternal
  pi_mem := T.pi_mem

end Schemes

end Langlands.DeligneFormalSpace.GradedPiSheaf
