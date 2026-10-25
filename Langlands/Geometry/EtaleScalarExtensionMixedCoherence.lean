import Langlands.Geometry.EtaleEquivariantScalarExtensionPullback
import Langlands.Geometry.EtaleEquivariantScalarExtensionCoherence

/-!
# Coefficient and geometric coherence for sheafified scalar extension
-/

noncomputable section

namespace Langlands.Geometry.EtaleCohomologyAction

open CategoryTheory AlgebraicGeometry EtalePullback Langlands.Cohomology

universe u w

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
variable (φ : R →+* A) (ψ : A →+* B)
variable {X Y : Scheme.{u}} (f : Y ⟶ X) [Etale f]

/-- Maps out of restricted extension are determined by the pulled-back extension unit. -/
theorem sheafExtensionPullback_unit_hom_ext (F : EtaleDerivedSections.ModuleSheaf X R)
    {E : EtaleDerivedSections.ModuleSheaf Y A}
    (a b : (restriction f (ModuleCat.{u} A)).obj ((sheafExtendScalars φ X).obj F) ⟶ E)
    (h : (restriction f (ModuleCat.{u} R)).map ((sheafExtensionUnit φ X).app F) ≫
        (sheafRestrictScalars φ Y).map a =
      (restriction f (ModuleCat.{u} R)).map ((sheafExtensionUnit φ X).app F) ≫
        (sheafRestrictScalars φ Y).map b) : a = b := by
  have h' : (sheafExtendScalarsPullbackIso φ f).inv.app F ≫ a =
      (sheafExtendScalarsPullbackIso φ f).inv.app F ≫ b := by
    apply (sheafExtensionHomEquiv φ Y _ E).injective
    rw [sheafExtensionHomEquiv_apply, sheafExtensionHomEquiv_apply,
      ← sheafExtensionUnit_pullback φ f F]
    simp only [Functor.map_comp, ← Category.assoc]
    rw [Category.assoc _ _ ((sheafRestrictScalars φ Y).map
      ((sheafExtendScalarsPullbackIso φ f).inv.app F)),
      ← Functor.map_comp, Iso.hom_inv_id_app]
    erw [(sheafRestrictScalars φ Y).map_id]
    apply Sheaf.hom_ext
    ext U x
    exact congrArg (fun k => k.hom.app U x) h
  have h'' := congrArg (fun k => (sheafExtendScalarsPullbackIso φ f).hom.app F ≫ k) h'
  simpa only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp] using h''

/-- The geometric comparison commutes with removal of identity coefficient extension. -/
theorem sheafExtendScalarsPullbackIso_ring_id
    (F : EtaleDerivedSections.ModuleSheaf X R) :
    (sheafExtendScalarsPullbackIso (RingHom.id R) f).hom.app F ≫
        (sheafExtendScalarsIdIso Y).hom.app ((restriction f (ModuleCat.{u} R)).obj F) =
      (restriction f (ModuleCat.{u} R)).map ((sheafExtendScalarsIdIso X).hom.app F) := by
  apply sheafExtensionPullback_unit_hom_ext (RingHom.id R) f F
  rw [Functor.map_comp, ← Category.assoc, sheafExtensionUnit_pullback, sheafExtensionUnit_id]
  have h := congrArg ((restriction f (ModuleCat.{u} R)).map) (sheafExtensionUnit_id X F)
  apply Sheaf.hom_ext
  ext U x
  exact congrArg (fun k => k.hom.app U x) h.symm

/-- The composite unit equation remains valid after geometric restriction. -/
theorem sheafExtensionUnit_comp_pullback (F : EtaleDerivedSections.ModuleSheaf X R) :
    (restriction f (ModuleCat.{u} R)).map ((sheafExtensionUnit (ψ.comp φ) X).app F) ≫
        (sheafRestrictScalars (ψ.comp φ) Y).map
          ((restriction f (ModuleCat.{u} B)).map
            ((sheafExtendScalarsCompIso φ ψ X).hom.app F)) =
      (restriction f (ModuleCat.{u} R)).map ((sheafExtensionUnit φ X).app F) ≫
        (sheafRestrictScalars φ Y).map
          ((restriction f (ModuleCat.{u} A)).map
            ((sheafExtensionUnit ψ X).app ((sheafExtendScalars φ X).obj F))) ≫
        (sheafRestrictScalarsCompIso φ ψ Y).inv.app
          ((restriction f (ModuleCat.{u} B)).obj
            ((sheafExtendScalars ψ X).obj ((sheafExtendScalars φ X).obj F))) := by
  have h := sheafExtensionUnit_comp φ ψ X F
  apply Sheaf.hom_ext
  ext U x
  exact congrArg (fun k => k.hom.app ((siteMap f).op.obj U) x) h

/-- Geometric pullback is compatible with splitting a composite coefficient extension. -/
theorem sheafExtendScalarsPullbackIso_ring_comp
    (F : EtaleDerivedSections.ModuleSheaf X R) :
    (sheafExtendScalarsPullbackIso (ψ.comp φ) f).hom.app F ≫
        (sheafExtendScalarsCompIso φ ψ Y).hom.app ((restriction f (ModuleCat.{u} R)).obj F) =
      (restriction f (ModuleCat.{u} B)).map ((sheafExtendScalarsCompIso φ ψ X).hom.app F) ≫
        (sheafExtendScalarsPullbackIso ψ f).hom.app ((sheafExtendScalars φ X).obj F) ≫
        (sheafExtendScalars ψ Y).map ((sheafExtendScalarsPullbackIso φ f).hom.app F) := by
  apply sheafExtensionPullback_unit_hom_ext (ψ.comp φ) f F
  rw [Functor.map_comp, ← Category.assoc, sheafExtensionUnit_pullback,
    sheafExtensionUnit_comp]
  rw [Functor.map_comp]
  simp only [← Category.assoc]
  erw [sheafExtensionUnit_comp_pullback φ ψ f F]
  simp only [Category.assoc]
  rw [← (sheafRestrictScalarsCompIso φ ψ Y).inv.naturality]
  simp only [Functor.comp_map, Functor.map_comp, ← Category.assoc]
  rw [Category.assoc _ _ ((sheafRestrictScalars φ Y).map
      ((sheafRestrictScalars ψ Y).map
        ((sheafExtendScalarsPullbackIso ψ f).hom.app ((sheafExtendScalars φ X).obj F)))),
    ← Functor.map_comp, sheafExtensionUnit_pullback ψ f ((sheafExtendScalars φ X).obj F)]
  rw [Category.assoc _ _ ((sheafRestrictScalars φ Y).map
      ((sheafRestrictScalars ψ Y).map
        ((sheafExtendScalars ψ Y).map ((sheafExtendScalarsPullbackIso φ f).hom.app F)))),
    ← Functor.map_comp]
  have hn := (sheafExtensionUnit ψ Y).naturality
    ((sheafExtendScalarsPullbackIso φ f).hom.app F)
  simp only [Functor.comp_map, Functor.id_map] at hn
  erw [← hn]
  simp only [Functor.map_comp, ← Category.assoc]
  rw [sheafExtensionUnit_pullback φ f F]
  rfl

/-- Compare composite extension and pullback with two extensions after pullback. -/
def sheafExtendScalarsCompPullbackIso :
    sheafExtendScalars (ψ.comp φ) X ⋙ restriction f (ModuleCat.{u} B) ≅
      restriction f (ModuleCat.{u} R) ⋙ (sheafExtendScalars φ Y ⋙ sheafExtendScalars ψ Y) :=
  sheafExtendScalarsPullbackIso (ψ.comp φ) f ≪≫
    Functor.isoWhiskerLeft (restriction f (ModuleCat.{u} R))
      (sheafExtendScalarsCompIso φ ψ Y)

/-- The mixed comparison can also be computed by pulling back the two extensions in order. -/
theorem sheafExtendScalarsCompPullbackIso_hom_app
    (F : EtaleDerivedSections.ModuleSheaf X R) :
    (sheafExtendScalarsCompPullbackIso φ ψ f).hom.app F =
      (restriction f (ModuleCat.{u} B)).map ((sheafExtendScalarsCompIso φ ψ X).hom.app F) ≫
        (sheafExtendScalarsPullbackIso ψ f).hom.app ((sheafExtendScalars φ X).obj F) ≫
        (sheafExtendScalars ψ Y).map ((sheafExtendScalarsPullbackIso φ f).hom.app F) :=
  sheafExtendScalarsPullbackIso_ring_comp φ ψ f F

variable {G : Type w} [Group G]
variable (ρ : G →* (Aut X)ᵐᵒᵖ) (τ : G →* (Aut Y)ᵐᵒᵖ)
variable (hf : ∀ g, f ≫ (aut ρ g).hom = (aut τ g).hom ≫ f)

/-- Equivariant geometric pullback respects the identity coefficient extension comparison. -/
theorem scalarExtensionEquivariantPullbackIso_ring_id (F : EquivariantSheaf R ρ) :
    (scalarExtensionEquivariantPullbackIso (RingHom.id R) ρ τ f hf).hom.app F ≫
        (scalarExtensionIdIso τ).hom.app ((equivariantPullback R ρ τ f hf).obj F) =
      (equivariantPullback R ρ τ f hf).map ((scalarExtensionIdIso ρ).hom.app F) := by
  apply TranslationAction.Equivariant.Hom.ext
  exact sheafExtendScalarsPullbackIso_ring_id f F.obj

/-- Equivariant geometric pullback respects splitting composite coefficient extension. -/
theorem scalarExtensionEquivariantPullbackIso_ring_comp (F : EquivariantSheaf R ρ) :
    (scalarExtensionEquivariantPullbackIso (ψ.comp φ) ρ τ f hf).hom.app F ≫
        (scalarExtensionCompIso φ ψ τ).hom.app ((equivariantPullback R ρ τ f hf).obj F) =
      (equivariantPullback B ρ τ f hf).map ((scalarExtensionCompIso φ ψ ρ).hom.app F) ≫
        (scalarExtensionEquivariantPullbackIso ψ ρ τ f hf).hom.app
          ((scalarExtensionFunctor φ ρ).obj F) ≫
        (scalarExtensionFunctor ψ τ).map
          ((scalarExtensionEquivariantPullbackIso φ ρ τ f hf).hom.app F) := by
  apply TranslationAction.Equivariant.Hom.ext
  exact sheafExtendScalarsPullbackIso_ring_comp φ ψ f F.obj

/-- The mixed comparison as a natural isomorphism of geometric equivariant sheaves. -/
def scalarExtensionCompEquivariantPullbackIso :
    scalarExtensionFunctor (ψ.comp φ) ρ ⋙ equivariantPullback B ρ τ f hf ≅
      equivariantPullback R ρ τ f hf ⋙
        (scalarExtensionFunctor φ τ ⋙ scalarExtensionFunctor ψ τ) :=
  scalarExtensionEquivariantPullbackIso (ψ.comp φ) ρ τ f hf ≪≫
    Functor.isoWhiskerLeft (equivariantPullback R ρ τ f hf)
      (scalarExtensionCompIso φ ψ τ)

/-- The equivariant mixed comparison has the two-step formula. -/
theorem scalarExtensionCompEquivariantPullbackIso_hom_app (F : EquivariantSheaf R ρ) :
    (scalarExtensionCompEquivariantPullbackIso φ ψ f ρ τ hf).hom.app F =
      (equivariantPullback B ρ τ f hf).map ((scalarExtensionCompIso φ ψ ρ).hom.app F) ≫
        (scalarExtensionEquivariantPullbackIso ψ ρ τ f hf).hom.app
          ((scalarExtensionFunctor φ ρ).obj F) ≫
        (scalarExtensionFunctor ψ τ).map
          ((scalarExtensionEquivariantPullbackIso φ ρ τ f hf).hom.app F) :=
  scalarExtensionEquivariantPullbackIso_ring_comp φ ψ f ρ τ hf F

/-- Forgetting equivariance recovers the ordinary mixed comparison. -/
@[simp] theorem scalarExtensionCompEquivariantPullbackIso_hom_app_hom
    (F : EquivariantSheaf R ρ) :
    ((scalarExtensionCompEquivariantPullbackIso φ ψ f ρ τ hf).hom.app F).hom =
      (sheafExtendScalarsCompPullbackIso φ ψ f).hom.app F.obj := rfl

end Langlands.Geometry.EtaleCohomologyAction
