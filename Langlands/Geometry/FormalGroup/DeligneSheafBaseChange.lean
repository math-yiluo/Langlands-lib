import Langlands.Geometry.FormalGroup.DeligneRationalSheaf
import Mathlib.CategoryTheory.Sites.Adjunction
import Mathlib.Topology.Sheaves.Functors

/-! # Coefficient comparisons for actual inverse images of Deligne sheaves -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.DeligneFormalSpace

open CategoryTheory TopologicalSpace AlgebraicGeometry

variable {O R : Type u} [CommRing O] [CommRing R]
  {X Y : TopCat.{u}}

/-- Scalar restriction on the actual module sheaves. -/
def coefficientRestriction (ρ : O →+* R) (X : TopCat.{u}) :
    X.Sheaf (ModuleCat.{u} R) ⥤ X.Sheaf (ModuleCat.{u} O) :=
  sheafCompose (Opens.grothendieckTopology X) (ModuleCat.restrictScalars ρ)

/-- Scalar extension followed by actual sheafification. -/
def coefficientExtension (ρ : O →+* R) (X : TopCat.{u}) :
    X.Sheaf (ModuleCat.{u} O) ⥤ X.Sheaf (ModuleCat.{u} R) :=
  Sheaf.composeAndSheafify (Opens.grothendieckTopology X) (ModuleCat.extendScalars ρ)

/-- The sheaf tensor extension is left adjoint to actual scalar restriction. -/
def coefficientExtensionAdjunction (ρ : O →+* R) (X : TopCat.{u}) :
    coefficientExtension ρ X ⊣ coefficientRestriction ρ X :=
  Sheaf.adjunction (Opens.grothendieckTopology X) (ModuleCat.extendRestrictScalarsAdj ρ)

/-- Coextension of scalars on the actual module sheaves. -/
def coefficientCoextension (ρ : O →+* R) (X : TopCat.{u}) :
    X.Sheaf (ModuleCat.{u} O) ⥤ X.Sheaf (ModuleCat.{u} R) :=
  sheafCompose (Opens.grothendieckTopology X) (ModuleCat.coextendScalars ρ)

/-- Scalar restriction is also a left adjoint on actual sheaves. -/
def coefficientRestrictionAdjunction (ρ : O →+* R) (X : TopCat.{u}) :
    coefficientRestriction ρ X ⊣ coefficientCoextension ρ X :=
  Adjunction.restrictFullyFaithful
    ((ModuleCat.restrictCoextendScalarsAdj ρ).whiskerRight (Opens X)ᵒᵖ)
    (fullyFaithfulSheafToPresheaf _ _) (fullyFaithfulSheafToPresheaf _ _)
    (Iso.refl _) (Iso.refl _)

/-- Inverse image commutes with actual tensor extension and sheafification. -/
def inverseImageExtensionIso (ρ : O →+* R) (f : X ⟶ Y) :
    coefficientExtension ρ Y ⋙ TopCat.Sheaf.pullback (ModuleCat.{u} R) f ≅
      TopCat.Sheaf.pullback (ModuleCat.{u} O) f ⋙ coefficientExtension ρ X :=
  ((coefficientExtensionAdjunction ρ Y).comp
    (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} R) f)).leftAdjointUniq
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} O) f).comp
        (coefficientExtensionAdjunction ρ X))

/-- Inverse image commutes with actual restriction of coefficient scalars. -/
def inverseImageRestrictionIso (ρ : O →+* R) (f : X ⟶ Y) :
    coefficientRestriction ρ Y ⋙ TopCat.Sheaf.pullback (ModuleCat.{u} O) f ≅
      TopCat.Sheaf.pullback (ModuleCat.{u} R) f ⋙ coefficientRestriction ρ X :=
  ((coefficientRestrictionAdjunction ρ Y).comp
    (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} O) f)).leftAdjointUniq
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} R) f).comp
        (coefficientRestrictionAdjunction ρ X))

/-- The top open is terminal in the actual open-set category. -/
def topOpenIsTerminal (X : TopCat.{u}) : Limits.IsTerminal (⊤ : Opens X) :=
  Limits.IsTerminal.ofUniqueHom (fun U => homOfLE (show U ≤ ⊤ from le_top))
    (fun _ _ => Subsingleton.elim _ _)

/-- Inverse image preserves the actual constant module-sheaf functor. -/
def inverseImageConstantIso (f : X ⟶ Y) :
    constantSheaf (Opens.grothendieckTopology Y) (ModuleCat.{u} O) ⋙
        TopCat.Sheaf.pullback (ModuleCat.{u} O) f ≅
      constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} O) :=
  ((constantSheafAdj _ _ (topOpenIsTerminal Y)).comp
    (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} O) f)).leftAdjointUniq
      (constantSheafAdj _ _ (topOpenIsTerminal X))

variable {F : Type u} [Field F] [Algebra O F]

/-- The constructed coefficient extension is precisely the existing rationalization. -/
def coefficientExtensionRationalIso (X : TopCat.{u}) :
    coefficientExtension (algebraMap O F) X ≅ rationalSheafFunctor F X :=
  Iso.refl _

/-- The actual rationalization and inverse-image functors commute. -/
def inverseImageRationalIso (f : X ⟶ Y) :
    rationalSheafFunctor F Y ⋙ TopCat.Sheaf.pullback (ModuleCat.{u} F) f ≅
      TopCat.Sheaf.pullback (ModuleCat.{u} O) f ⋙ rationalSheafFunctor F X :=
  inverseImageExtensionIso (algebraMap O F) f

/-- The existing integral rationalization map is the actual coefficient adjunction unit. -/
theorem rationalUnit_eq_adjunctionUnit (M : X.Sheaf (ModuleCat.{u} O)) :
    rationalUnit F X M =
      (coefficientExtensionAdjunction (algebraMap O F) X).unit.app M := by
  apply Sheaf.hom_ext
  exact (Sheaf.adjunction_unit_app_hom (Opens.grothendieckTopology X)
    (ModuleCat.extendRestrictScalarsAdj (algebraMap O F)) M).symm

/-- The inverse-image rationalization comparison intertwines every actual sheaf map. -/
theorem inverseImageRationalIso_naturality (f : X ⟶ Y)
    {M N : Y.Sheaf (ModuleCat.{u} O)} (g : M ⟶ N) :
    (TopCat.Sheaf.pullback (ModuleCat.{u} F) f).map
        ((rationalSheafFunctor F Y).map g) ≫
        (inverseImageRationalIso (F := F) f).hom.app N =
      (inverseImageRationalIso (F := F) f).hom.app M ≫
        (rationalSheafFunctor F X).map
          ((TopCat.Sheaf.pullback (ModuleCat.{u} O) f).map g) :=
  (inverseImageRationalIso (F := F) f).hom.naturality g

section Structural

variable {S S' : Scheme.{u}} (f : S' ⟶ S) (φ : O →+* Γ(S, ⊤))

/-- The structural coefficient map after the actual pullback on global sections. -/
def pulledGlobalScalar : O →+* Γ(S', ⊤) :=
  f.appTop.hom.comp φ

/-- The scalar actions used in structural and ordinary pushforward agree. -/
theorem structuralScalar_pushforward (U : S.Opens) (a : O) :
    (f.app U).hom ((S.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom (φ a)) =
      (S'.presheaf.map (homOfLE (show f ⁻¹ᵁ U ≤ ⊤ from le_top)).op).hom
        (pulledGlobalScalar f φ a) := by
  have h := f.naturality (homOfLE (show U ≤ ⊤ from le_top)).op
  exact congrArg (fun k => k.hom (φ a)) h

/-- Forgetting structural scalars commutes with actual pushforward. -/
def structuralPushforwardIso :
    Scheme.Modules.pushforward f ⋙ structuralOSheafFunctor S φ ≅
      structuralOSheafFunctor S' (pulledGlobalScalar f φ) ⋙
        TopCat.Sheaf.pushforward (ModuleCat.{u} O) f.base := by
  refine NatIso.ofComponents (fun M => ObjectProperty.isoMk _ ?_) ?_
  · refine NatIso.ofComponents (fun U => ?_) ?_
    · let A := (((Scheme.Modules.pushforward f ⋙
          structuralOSheafFunctor S φ).obj M).obj.obj U)
      let B := (((structuralOSheafFunctor S' (pulledGlobalScalar f φ) ⋙
          TopCat.Sheaf.pushforward (ModuleCat.{u} O) f.base).obj M).obj.obj U)
      refine (show A ≃ₗ[O] B from {
        toFun := fun x => x
        invFun := fun x => x
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
        map_smul' := fun a x => ?_ }).toModuleIso
      change (f.app U.unop).hom
          ((S.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op).hom (φ a)) •
            (show M.val.obj (.op (f ⁻¹ᵁ U.unop)) from x) =
        (S'.presheaf.map
          (homOfLE (show f ⁻¹ᵁ U.unop ≤ ⊤ from le_top)).op).hom
            (pulledGlobalScalar f φ a) •
              (show M.val.obj (.op (f ⁻¹ᵁ U.unop)) from x)
      rw [structuralScalar_pushforward]
    · intro U V g
      ext x
      rfl
  · intro M N g
    apply Sheaf.hom_ext
    ext U x
    rfl

/-- The actual structural adjunction unit, regarded as an ordinary O-sheaf map. -/
def structuralPullbackUnit :
    structuralOSheafFunctor S φ ⟶
      Scheme.Modules.pullback f ⋙ structuralOSheafFunctor S' (pulledGlobalScalar f φ) ⋙
        TopCat.Sheaf.pushforward (ModuleCat.{u} O) f.base :=
  Functor.whiskerRight (Scheme.Modules.pullbackPushforwardAdjunction f).unit
      (structuralOSheafFunctor S φ) ≫
    Functor.whiskerLeft (Scheme.Modules.pullback f) (structuralPushforwardIso f φ).hom

/-- The canonical map from inverse image to underlying structural pullback. -/
def structuralPullbackComparison :
    structuralOSheafFunctor S φ ⋙ TopCat.Sheaf.pullback (ModuleCat.{u} O) f.base ⟶
      Scheme.Modules.pullback f ⋙ structuralOSheafFunctor S' (pulledGlobalScalar f φ) where
  app M :=
    ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} O) f.base).homEquiv _ _).symm
      ((structuralPullbackUnit f φ).app M)
  naturality {M N} g := by
    apply ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} O)
      f.base).homEquiv _ _).injective
    dsimp only [Functor.comp_map]
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
    simp only [Equiv.apply_symm_apply]
    exact (structuralPullbackUnit f φ).naturality g

/-- The comparison is characterized by the actual structural adjunction unit. -/
theorem structuralPullbackComparison_unit (M : S.Modules) :
    (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} O) f.base).unit.app
        ((structuralOSheafFunctor S φ).obj M) ≫
      (TopCat.Sheaf.pushforward (ModuleCat.{u} O) f.base).map
        ((structuralPullbackComparison f φ).app M) =
      (structuralOSheafFunctor S φ).map
          ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) ≫
        (structuralPushforwardIso f φ).hom.app ((Scheme.Modules.pullback f).obj M) := by
  exact ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} O)
    f.base).homEquiv _ _).apply_symm_apply ((structuralPullbackUnit f φ).app M)

namespace SheafPreDatum

variable {d : ℕ} [NeZero d] {π : O} (D : SheafPreDatum d π F φ)

/-- Inverse image of the actual total u, followed by structural scalar extension. -/
def inverseImageU :
    (TopCat.Sheaf.pullback (ModuleCat.{u} O) f.base).obj
        (latticeScalarSheaf d π (S : TopCat) D.eta.lattice.sheaf) ⟶
      (structuralOSheafFunctor S' (pulledGlobalScalar f φ)).obj
        ((Scheme.Modules.pullback f).obj D.tangent.graded.module) :=
  (TopCat.Sheaf.pullback (ModuleCat.{u} O) f.base).map D.u ≫
    (structuralPullbackComparison f φ).app D.tangent.graded.module

/-- Inverse image of the actual homogeneous restriction of u. -/
def inverseImageUComponent (i : ZMod d) :
    (TopCat.Sheaf.pullback (ModuleCat.{u} O) f.base).obj (D.eta.lattice.component i) ⟶
      (structuralOSheafFunctor S' (pulledGlobalScalar f φ)).obj
        ((Scheme.Modules.pullback f).obj (D.tangent.graded.componentSheaf i)) :=
  (TopCat.Sheaf.pullback (ModuleCat.{u} O) f.base).map (D.uComponent i) ≫
    (structuralPullbackComparison f φ).app (D.tangent.graded.componentSheaf i)

/-- The pulled-back total map still commutes with the actual Pi operators. -/
theorem inverseImageU_pi :
    (TopCat.Sheaf.pullback (ModuleCat.{u} O) f.base).map
        (latticePi d π (S : TopCat) D.eta.lattice.sheaf) ≫ inverseImageU f φ D =
      inverseImageU f φ D ≫
        (structuralOSheafFunctor S' (pulledGlobalScalar f φ)).map
          ((Scheme.Modules.pullback f).map D.tangent.graded.pi) := by
  let P := TopCat.Sheaf.pullback (ModuleCat.{u} O) f.base
  change P.map _ ≫ (P.map D.u ≫ _) = (P.map D.u ≫ _) ≫ _
  rw [← Category.assoc, ← P.map_comp, D.uPi, P.map_comp, Category.assoc]
  exact congrArg (fun k => P.map D.u ≫ k)
    ((structuralPullbackComparison f φ).naturality D.tangent.graded.pi)

/-- The homogeneous pulled-back maps remain restrictions of the same total u. -/
theorem inverseImageUComponent_inclusion (i : ZMod d) :
    inverseImageUComponent f φ D i ≫
        (structuralOSheafFunctor S' (pulledGlobalScalar f φ)).map
          ((Scheme.Modules.pullback f).map (D.tangent.graded.componentInclusion i)) =
      (TopCat.Sheaf.pullback (ModuleCat.{u} O) f.base).map (D.eta.lattice.inclusion i) ≫
        inverseImageU f φ D := by
  let P := TopCat.Sheaf.pullback (ModuleCat.{u} O) f.base
  change (P.map (D.uComponent i) ≫ _) ≫ _ =
    P.map (D.eta.lattice.inclusion i) ≫ (P.map D.u ≫ _)
  have h := (structuralPullbackComparison f φ).naturality
    (D.tangent.graded.componentInclusion i)
  dsimp only [Functor.comp_map] at h
  rw [Category.assoc, ← h, ← Category.assoc, ← P.map_comp,
    D.uComponent_inclusion, P.map_comp, Category.assoc]

end SheafPreDatum

end Structural

end Langlands.DeligneFormalSpace
