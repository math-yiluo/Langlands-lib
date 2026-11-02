import Mathlib.Algebra.Category.ModuleCat.Stalk
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.RingTheory.Flat.Basic

/-!
# Relative flatness for actual scheme modules

The scalar action is restriction of the canonical action of the source local
ring along the actual stalk map of the scheme morphism.
-/

universe u

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules

variable {X Y : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false

/-- The actual module stalk, with its canonical source-local-ring action. -/
noncomputable abbrev stalk (M : X.Modules) (x : X) :=
  M.presheaf.stalk x

/-- The source-local-ring action on an actual module stalk. -/
noncomputable instance stalkModule (M : X.Modules) (x : X) :
    Module (X.presheaf.stalk x) (stalk M x) :=
  inferInstanceAs (Module (X.presheaf.stalk x) ↑(TopCat.Presheaf.stalk M.val.presheaf x))

/-- The module stalk is a module over the base local ring through the structure map. -/
noncomputable abbrev relativeStalkModule (f : X ⟶ Y) (M : X.Modules) (x : X) :
    Module (Y.presheaf.stalk (f x)) (stalk M x) :=
  Module.compHom _ (f.stalkMap x).hom

/-- Flatness relative to `f` means flatness of every actual module stalk over
the base local ring at its image, through `f.stalkMap`. -/
def IsFlatOver (f : X ⟶ Y) (M : X.Modules) : Prop :=
  ∀ x : X, letI := relativeStalkModule f M x
    Module.Flat (Y.presheaf.stalk (f x)) (stalk M x)

/-- A morphism of actual module sheaves acts linearly on source-local-ring stalks. -/
noncomputable def stalkMap {M N : X.Modules} (φ : M ⟶ N) (x : X) :
    stalk M x →ₗ[X.presheaf.stalk x] stalk N x where
  toFun := (TopCat.Presheaf.stalkFunctor Ab x).map φ.mapPresheaf
  map_add' := map_add _
  map_smul' r m := by
    dsimp only [stalk, Scheme.Modules.presheaf] at *
    obtain ⟨U, hxU, r, rfl⟩ := X.presheaf.exists_germ_eq r
    obtain ⟨V, hVU, hxV, m, rfl⟩ := M.presheaf.exists_le_germ_eq m hxU
    rw [← X.presheaf.germ_res_apply (homOfLE hVU) x hxV r]
    erw [← PresheafOfModules.germ_smul M.val x V hxV]
    simp only [TopCat.Presheaf.stalkFunctor_map_germ_apply, Scheme.Modules.mapPresheaf_app]
    erw [Scheme.Modules.Hom.app_smul, PresheafOfModules.germ_smul]
    erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
    rfl

/-- A module isomorphism gives the actual linear equivalence of its stalks. -/
noncomputable def stalkIso {M N : X.Modules} (e : M ≅ N) (x : X) :
    stalk M x ≃ₗ[X.presheaf.stalk x] stalk N x :=
  LinearEquiv.ofBijective (stalkMap e.hom x) (by
    change Function.Bijective ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map e.hom.mapPresheaf)
    have : IsIso e.hom.mapPresheaf := (Scheme.Modules.toPresheaf X).map_isIso e.hom
    exact ConcreteCategory.bijective_of_isIso _)

/-- Stalk maps are linear over a base local ring via its actual structure map. -/
noncomputable def relativeStalkMap (f : X ⟶ Y) {M N : X.Modules} (φ : M ⟶ N) (x : X) :
    letI := relativeStalkModule f M x
    letI := relativeStalkModule f N x
    stalk M x →ₗ[Y.presheaf.stalk (f x)] stalk N x := by
  letI := relativeStalkModule f M x
  letI := relativeStalkModule f N x
  exact {
    toFun := stalkMap φ x
    map_add' := (stalkMap φ x).map_add
    map_smul' := fun r m => (stalkMap φ x).map_smul ((f.stalkMap x) r) m }

/-- A module isomorphism gives the same stalk equivalence over the base local ring. -/
noncomputable def relativeStalkIso (f : X ⟶ Y) {M N : X.Modules} (e : M ≅ N) (x : X) :
    letI := relativeStalkModule f M x
    letI := relativeStalkModule f N x
    stalk M x ≃ₗ[Y.presheaf.stalk (f x)] stalk N x := by
  letI := relativeStalkModule f M x
  letI := relativeStalkModule f N x
  exact LinearEquiv.ofBijective (relativeStalkMap f e.hom x) (stalkIso e x).bijective

/-- Relative stalk flatness is invariant under actual module isomorphisms. -/
lemma isFlatOver_iff_of_iso (f : X ⟶ Y) {M N : X.Modules} (e : M ≅ N) :
    IsFlatOver f M ↔ IsFlatOver f N := by
  constructor <;> intro h x
  · let := relativeStalkModule f M x
    let := relativeStalkModule f N x
    exact (Module.Flat.equiv_iff (relativeStalkIso f e x)).mp (h x)
  · let := relativeStalkModule f M x
    let := relativeStalkModule f N x
    exact (Module.Flat.equiv_iff (relativeStalkIso f e x)).mpr (h x)

/-- The relative flatness property on the actual category of source modules. -/
def isFlatOver (f : X ⟶ Y) : ObjectProperty X.Modules := IsFlatOver f

instance (f : X ⟶ Y) : (isFlatOver f).IsClosedUnderIsomorphisms where
  of_iso e h := (isFlatOver_iff_of_iso f e).mp h

end Langlands.AlgebraicGeometry.Modules
