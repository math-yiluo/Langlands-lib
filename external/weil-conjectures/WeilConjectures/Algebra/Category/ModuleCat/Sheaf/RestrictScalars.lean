/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Sites.Adjunction

/-!
# Restriction of scalars for sheaves of modules over a constant ring

Let `f : R →+* S` be a ring morphism and `J` a Grothendieck topology. Composing with
`ModuleCat.restrictScalars f` sends sheaves of `S`-modules to sheaves of `R`-modules
(`CategoryTheory.Sheaf.restrictScalars`). Since `ModuleCat.restrictScalars f` is left adjoint
to coextension of scalars, so is this functor on sheaves
(`CategoryTheory.Sheaf.restrictCoextendScalarsAdj`). It is also a right adjoint, so it is exact
and induces a functor `D(J, S) ⥤ D(J, R)` on derived categories. A left adjoint of restriction of
scalars on modules which preserves sheaves gives a left adjoint on sheaves
(`CategoryTheory.Sheaf.sheafComposeRestrictScalarsAdj`). Restricting along `g` and then
along `f` is restricting along `g ∘ f` (`CategoryTheory.Sheaf.restrictScalarsCompIso`).
-/

@[expose] public section

universe w v u

open CategoryTheory Limits

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {R S : Type w} [CommRing R] [CommRing S] (f : R →+* S)

instance : PreservesLimitsOfSize.{v, max u v} (ModuleCat.restrictScalars.{w} f) :=
  (ModuleCat.extendRestrictScalarsAdj f).rightAdjoint_preservesLimits

/-- Restriction of scalars along `f : R →+* S`, from sheaves of `S`-modules to sheaves of
`R`-modules. -/
noncomputable abbrev restrictScalars :
    Sheaf J (ModuleCat.{w} S) ⥤ Sheaf J (ModuleCat.{w} R) :=
  sheafCompose J (ModuleCat.restrictScalars f)

/-- Restriction of scalars on sheaves is left adjoint to coextension of scalars, both computed
objectwise. -/
noncomputable def restrictCoextendScalarsAdj :
    restrictScalars J f ⊣ sheafCompose J (ModuleCat.coextendScalars f) :=
  Adjunction.restrictFullyFaithful
    ((ModuleCat.restrictCoextendScalarsAdj f).whiskerRight Cᵒᵖ)
    (fullyFaithfulSheafToPresheaf J _) (fullyFaithfulSheafToPresheaf J _) (Iso.refl _)
    (Iso.refl _)

instance : (restrictScalars J f).IsLeftAdjoint :=
  (restrictCoextendScalarsAdj J f).isLeftAdjoint

/-- If a functor `G` on modules is left adjoint to restriction of scalars and composing with `G`
preserves sheaves, then composing sheaves with `G` is left adjoint to restriction of scalars of
sheaves, both being computed objectwise. -/
noncomputable def sheafComposeRestrictScalarsAdj {G : ModuleCat.{w} R ⥤ ModuleCat.{w} S}
    [J.HasSheafCompose G] (adj : G ⊣ ModuleCat.restrictScalars f) :
    sheafCompose J G ⊣ restrictScalars J f :=
  Adjunction.restrictFullyFaithful (adj.whiskerRight Cᵒᵖ)
    (fullyFaithfulSheafToPresheaf J _) (fullyFaithfulSheafToPresheaf J _) (Iso.refl _)
    (Iso.refl _)

instance [HasWeakSheafify J (ModuleCat.{w} S)] : (restrictScalars J f).IsRightAdjoint := by
  have := (ModuleCat.extendRestrictScalarsAdj f).isRightAdjoint
  infer_instance

instance : (restrictScalars J f).Additive where
  map_add {_ _ _ _} := by
    ext : 3
    rfl

variable {T : Type w} [CommRing T] (g : S →+* T) (gf : R →+* T) (hgf : gf = g.comp f)

/-- Restricting scalars along `g` and then along `f` is restricting scalars along `g ∘ f`,
computed objectwise by `ModuleCat.restrictScalarsComp'`. -/
noncomputable def restrictScalarsCompIso :
    restrictScalars J g ⋙ restrictScalars J f ≅ restrictScalars J gf :=
  NatIso.ofComponents
    (fun F ↦ (fullyFaithfulSheafToPresheaf J _).preimageIso
      (Functor.isoWhiskerLeft F.obj (ModuleCat.restrictScalarsComp' f g gf hgf).symm))
    (fun {F G} φ ↦ (fullyFaithfulSheafToPresheaf J _).map_injective (by
      ext U : 2
      exact ((ModuleCat.restrictScalarsComp' f g gf hgf).inv.naturality (φ.hom.app U)).symm))

end CategoryTheory.Sheaf
