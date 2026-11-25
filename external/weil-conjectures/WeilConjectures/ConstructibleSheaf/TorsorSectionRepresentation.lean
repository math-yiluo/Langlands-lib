/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.TorsorAssociatedModule

/-!
# The representation on sections over a torsor

Source: Stacks Project, Tags 0DV5 (3), 0DV6 and 0A3R.
(blueprint: def-weil-pbc-torsor-section-representation)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Scheme.GaloisCover

variable {V : Scheme.{u}} (ℓ : ℕ) {P : Type u} [Group P] [Finite P]
  (c : Scheme.GaloisCover (ULift.{u + 1} P) V)
  (F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))))

/-- The torsor as an object of the small etale site. 
(blueprint: def-weil-pbc-torsor-section-representation)
-/
abbrev sectionObject : V.Etale :=
  have := c.etale
  Etale.mk c.π

/-- Deck transformations acting on the site object. 
(blueprint: def-weil-pbc-torsor-section-representation)
-/
def sectionDeck (g : P) : c.sectionObject ⟶ c.sectionObject :=
  MorphismProperty.Over.homMk (c.smul ⟨g⟩) (c.smul_π ⟨g⟩)

/-- The sections over the cover, with scalars transported to the unlifted field. 
(blueprint: def-weil-pbc-torsor-section-representation)
-/
noncomputable abbrev sectionModule : ModuleCat.{u + 1} (ZMod ℓ) :=
  (ModuleCat.restrictScalars
    (ULift.ringEquiv.symm.toRingHom : ZMod ℓ →+* ULift.{u + 1} (ZMod ℓ))).obj
    (F.obj.obj (op c.sectionObject))

/-- The canonical representation on sections over the torsor. A group element acts by
restriction along its inverse deck transformation. Thus this is a left action, with the
same convention as equivariant functions in `associatedModuleFunctor`.
Source: Stacks Project, Tags 0DV5 (3), 0DV6 and 0A3R.
(blueprint: def-weil-pbc-torsor-section-representation) -/
noncomputable def sectionRepresentation : Rep.{u + 1} (ZMod ℓ) P :=
  Rep.of (X := c.sectionModule ℓ F)
    { toFun g := ((ModuleCat.restrictScalars
        (ULift.ringEquiv.symm.toRingHom : ZMod ℓ →+* ULift.{u + 1} (ZMod ℓ))).map
          (F.obj.map (c.sectionDeck g⁻¹).op)).hom
      map_one' := by
        have hd : c.sectionDeck (1 : P) = 𝟙 _ := by
          apply Scheme.EtaleTorsor.etaleHom_ext
          exact c.one_smul
        simp [hd]
        rfl
      map_mul' g h := by
        have hd (a b : P) : c.sectionDeck (a * b) =
            c.sectionDeck b ≫ c.sectionDeck a := by
          apply Scheme.EtaleTorsor.etaleHom_ext
          exact c.mul_smul ⟨a⟩ ⟨b⟩
        simp only [mul_inv_rev, hd, op_comp, Functor.map_comp]
        rfl }

/-- The coefficient-lifted equivariant section presheaf for the canonical representation. 
(blueprint: def-weil-pbc-torsor-section-representation)
-/
noncomputable abbrev sectionRepresentationPresheaf :
    V.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)) :=
  c.equivariantModulePresheaf ℓ (c.sectionRepresentation ℓ F) ⋙
    ModuleCat.restrictScalars
      (ULift.ringEquiv.toRingHom : ULift.{u + 1} (ZMod ℓ) →+* ZMod ℓ)

/-- The diagonal normalization of the evaluation map: a section over the torsor evaluates
at each diagonal point to itself. 
(blueprint: def-weil-pbc-torsor-section-representation)
-/
def SectionEvaluationNormalized
    (α : F.obj ⟶ c.sectionRepresentationPresheaf ℓ F) : Prop :=
  ∀ (s : F.obj.obj (op c.sectionObject)) (y : c.P),
    ((α.app (op c.sectionObject) s).val)
      (pullback.lift (f := c.π) (g := c.π) (𝟙 c.P) (𝟙 c.P) (by simp) y) = s

end AlgebraicGeometry.Scheme.GaloisCover
