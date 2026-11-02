import Langlands.Sheaf.Renard.RingedBasisModules

/-!
# Constructing module sheaves from module structures on original sections

The adapter consumes the actual section modules and the literal semilinear
restriction law. It retains the original additive sheaf and its restrictions.
-/

open CategoryTheory Opposite TopologicalSpace

universe u r v

namespace Langlands.Sheaf.Renard

variable {X : Type u} [TopologicalSpace X] {B : OpenBasis X}
  {S : (BasisOpen B)ᵒᵖ ⥤ RingCat.{r}}

namespace BasisSheaf

/-- The literal scalar restriction law for module structures on the original sections. -/
def SemilinearRestrictions (F : BasisSheaf.{u,v} B)
    (S : (BasisOpen B)ᵒᵖ ⥤ RingCat.{r})
    [∀ U : BasisOpen B, Module (S.obj (op U)) (Sections F.obj.obj U)] : Prop :=
  ∀ {U V : BasisOpen B} (h : U.obj ≤ V.obj) (a : S.obj (op V))
    (m : Sections F.obj.obj V),
    restriction F.obj.obj h (a • m) =
      ringRestriction S h a • restriction F.obj.obj h m

/-- Scalar preservation for an actual morphism of the original additive sheaves. -/
def PreservesModuleScalars (F G : BasisSheaf.{u,v} B)
    (S : (BasisOpen B)ᵒᵖ ⥤ RingCat.{r})
    [∀ U : BasisOpen B, Module (S.obj (op U)) (Sections F.obj.obj U)]
    [∀ U : BasisOpen B, Module (S.obj (op U)) (Sections G.obj.obj U)]
    (f : F ⟶ G) : Prop :=
  ∀ (U : BasisOpen B) (a : S.obj (op U)) (m : Sections F.obj.obj U),
    f.hom.hom.app (op U) (a • m) = a • f.hom.hom.app (op U) m

end BasisSheaf

namespace BasisModuleSheaf

variable (F : BasisSheaf.{u,v} B)
  [∀ U : BasisOpen B, Module (S.obj (op U)) (Sections F.obj.obj U)]

/-- The source restriction law supplies semilinearity on every opposite inclusion arrow. -/
theorem semilinear_map (hF : F.SemilinearRestrictions S)
    {P Q : (BasisOpen B)ᵒᵖ} (f : P ⟶ Q) (a : S.obj P)
    (m : F.obj.obj.obj P) :
    F.obj.obj.map f (a • m) = S.map f a • F.obj.obj.map f m := by
  have hf : f = (basisHom f.unop.hom.le).op := Subsingleton.elim _ _
  simpa only [hf, restriction, ringRestriction] using hF f.unop.hom.le a m

/-- Construct an actual module sheaf from module structures on the original sheaf sections. -/
noncomputable def ofBasisSheaf (hF : F.SemilinearRestrictions S) :
    BasisModuleSheaf.{u,r,v} S :=
  ⟨PresheafOfModules.ofPresheaf F.obj.obj
    (fun {_ _} f a m => semilinear_map F hF f a m), F.property⟩

@[simp]
theorem ofBasisSheaf_presheaf (hF : F.SemilinearRestrictions S) :
    (ofBasisSheaf F hF).obj.presheaf = F.obj.obj := rfl

/-- The module adapter uses exactly the given section group and the supplied action. -/
@[simp]
theorem ofBasisSheaf_sections (hF : F.SemilinearRestrictions S) (U : BasisOpen B) :
    (ofBasisSheaf F hF).sections U =
      ModuleCat.of (S.obj (op U)) (Sections F.obj.obj U) := rfl

/-- Restriction values are the original restrictions of the given basis sheaf. -/
@[simp]
theorem ofBasisSheaf_restrict (hF : F.SemilinearRestrictions S)
    {U V : BasisOpen B} (h : U.obj ≤ V.obj) (m : Sections F.obj.obj V) :
    (ofBasisSheaf F hF).restrict h m = restriction F.obj.obj h m := rfl

/-- Forgetting the supplied module structure recovers the original bundled sheaf. -/
@[simp]
theorem ofBasisSheaf_toBasisSheaf (hF : F.SemilinearRestrictions S) :
    (moduleSheafToBasisSheaf S).obj (ofBasisSheaf F hF) = F := rfl

variable (G : BasisSheaf.{u,v} B)
  [∀ U : BasisOpen B, Module (S.obj (op U)) (Sections G.obj.obj U)]

/-- Lift a sheaf morphism with its explicit componentwise scalar-preservation proof. -/
noncomputable def ofBasisSheafHom (hF : F.SemilinearRestrictions S)
    (hG : G.SemilinearRestrictions S) (f : F ⟶ G)
    (hf : BasisSheaf.PreservesModuleScalars F G S f) :
    ofBasisSheaf F hF ⟶ ofBasisSheaf G hG :=
  homMk f.hom.hom hf

@[simp]
theorem ofBasisSheafHom_app (hF : F.SemilinearRestrictions S)
    (hG : G.SemilinearRestrictions S) (f : F ⟶ G)
    (hf : BasisSheaf.PreservesModuleScalars F G S f)
    (U : BasisOpen B) (m : Sections F.obj.obj U) :
    app (ofBasisSheafHom F G hF hG f hf) U m = f.hom.hom.app (op U) m := rfl

/-- The lift recovers the given underlying sheaf morphism, including its actual values. -/
@[simp]
theorem ofBasisSheafHom_toBasisSheaf (hF : F.SemilinearRestrictions S)
    (hG : G.SemilinearRestrictions S) (f : F ⟶ G)
    (hf : BasisSheaf.PreservesModuleScalars F G S f) :
    (moduleSheafToBasisSheaf S).map (ofBasisSheafHom F G hF hG f hf) = f := by
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  ext U m
  rfl

end BasisModuleSheaf

end Langlands.Sheaf.Renard
