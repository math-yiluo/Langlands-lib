import Langlands.Sheaf.Renard.BasisAllOpenEquivalence
import Langlands.Sheaf.Renard.RingedBasisModuleAdapter
import Langlands.Sheaf.Renard.RingedBasisModuleGluing
import Langlands.Sheaf.Renard.LocallyConstantScalarSheaf
import Langlands.Sheaf.Renard.ProjectorPresheaf

/-!
# Module sheaves on a basis and on all opens

Renard (9 July 2026), last paragraph of II.2.1 (printed p.37 / PDF p.43) for sheaves of modules
(II.2.3, printed p.38 / PDF p.44), used in the II.2.5 Remark (printed p.39 / PDF p.45): for a
ring presheaf defined on all opens, sheaves of modules on a chosen basis and on all opens form
equivalent categories. The published additive equivalence `BasisAllOpen.equivalence` is lifted
to module sheaves.
-/

noncomputable section

namespace Langlands.Sheaf.Renard.ModuleBasisChange

open CategoryTheory Opposite TopologicalSpace BasisAllOpen

universe u r v

variable {X : Type u} [TopologicalSpace X]

/-- A ring presheaf on all opens, restricted to the chosen basis `B`. -/
abbrev basisRing (B : OpenBasis X) (R : (Opens X)ᵒᵖ ⥤ RingCat.{r}) :
    (BasisOpen B)ᵒᵖ ⥤ RingCat.{r} :=
  (basisInclusion B).op ⋙ R

/-- The same ring presheaf on the published basis of all opens. -/
abbrev allOpenRing (R : (Opens X)ᵒᵖ ⥤ RingCat.{r}) :
    (BasisOpen (allOpenBasis X))ᵒᵖ ⥤ RingCat.{r} :=
  basisRing (allOpenBasis X) R

variable {B : OpenBasis X} {R : (Opens X)ᵒᵖ ⥤ RingCat.{r}}

/-- Restriction of a scalar on `V` to a basis member `U ⊆ V`, as a scalar of the basis ring. -/
def restrictScalar {V : Opens X} (a : R.obj (op V)) (U : Inside B V) :
    (basisRing B R).obj (op U.val) :=
  (R.map (homOfLE U.property).op).hom a

theorem restrictScalar_one {V : Opens X} (U : Inside B V) :
    restrictScalar (1 : R.obj (op V)) U = 1 :=
  RingHom.map_one _

theorem restrictScalar_mul {V : Opens X} (a b : R.obj (op V)) (U : Inside B V) :
    restrictScalar (a * b) U = restrictScalar a U * restrictScalar b U :=
  RingHom.map_mul _ _ _

theorem restrictScalar_add {V : Opens X} (a b : R.obj (op V)) (U : Inside B V) :
    restrictScalar (a + b) U = restrictScalar a U + restrictScalar b U :=
  RingHom.map_add _ _ _

theorem restrictScalar_zero {V : Opens X} (U : Inside B V) :
    restrictScalar (0 : R.obj (op V)) U = 0 :=
  RingHom.map_zero _

/-- Restricting twice is restricting once. -/
theorem ringRestriction_restrictScalar {V : Opens X} (a : R.obj (op V)) (U W : Inside B V)
    (h : W.val.obj ≤ U.val.obj) :
    (ringRestriction (basisRing B R) h).hom (restrictScalar a U) = restrictScalar a W := by
  have hc : (homOfLE U.property).op ≫ (homOfLE h).op =
      ((homOfLE W.property).op : op V ⟶ op W.val.obj) := Subsingleton.elim _ _
  change (R.map (homOfLE h).op).hom ((R.map (homOfLE U.property).op).hom a) =
    (R.map (homOfLE W.property).op).hom a
  rw [← hc, R.map_comp]
  rfl

/-- Restriction of a scalar to a smaller open, then to a basis member. -/
theorem restrictScalar_restrict {U V : Opens X} (h : U ≤ V) (a : R.obj (op V))
    (W : Inside B U) :
    restrictScalar ((R.map (homOfLE h).op).hom a) W =
      restrictScalar a ⟨W.val, W.property.trans h⟩ := by
  have hc : (homOfLE h).op ≫ (homOfLE W.property).op =
      ((homOfLE (W.property.trans h)).op : op V ⟶ op W.val.obj) := Subsingleton.elim _ _
  change (R.map (homOfLE W.property).op).hom ((R.map (homOfLE h).op).hom a) =
    (R.map (homOfLE (W.property.trans h)).op).hom a
  rw [← hc, R.map_comp]
  rfl

/-! ## Extension of a module sheaf on the basis to all opens -/

section Extension

variable (M : BasisModuleSheaf.{u,r,max u v} (basisRing B R))

/-- Componentwise action on compatible families: `(a • s)_U = a|_U • s_U`. -/
def familySMul {V : Opens X} (a : R.obj (op V)) (s : Families M.obj.presheaf V) :
    Families M.obj.presheaf V :=
  ⟨fun U => @HSMul.hSMul _ (M.sections U.val) (M.sections U.val) _ (restrictScalar a U)
      (s.val U), by
    intro U W h
    refine (M.restrict_smul h (restrictScalar a U) (s.val U)).trans ?_
    exact congrArg₂ (fun (b : (basisRing B R).obj (op W.val)) (m : M.sections W.val) => b • m)
      (ringRestriction_restrictScalar a U W h) (s.property U W h)⟩

theorem familySMul_apply {V : Opens X} (a : R.obj (op V)) (s : Families M.obj.presheaf V)
    (U : Inside B V) :
    (familySMul M a s).val U =
      @HSMul.hSMul _ (M.sections U.val) (M.sections U.val) _ (restrictScalar a U) (s.val U) :=
  rfl

/-- The module structure on compatible families over `V`, over the ring `R(V)`. -/
instance familyModule (V : Opens X) : Module (R.obj (op V)) (Families M.obj.presheaf V) where
  smul := familySMul M
  one_smul s := families_ext fun U => by
    change restrictScalar (1 : R.obj (op V)) U • s.val U = s.val U
    rw [restrictScalar_one, one_smul]
  mul_smul a b s := families_ext fun U => by
    change restrictScalar (a * b) U • s.val U = restrictScalar a U • (restrictScalar b U • s.val U)
    rw [restrictScalar_mul, mul_smul]
  smul_zero a := families_ext fun U => smul_zero (restrictScalar a U : (basisRing B R).obj _)
  smul_add a s t := families_ext fun U =>
    smul_add (restrictScalar a U : (basisRing B R).obj _) (s.val U) (t.val U)
  add_smul a b s := families_ext fun U => by
    change restrictScalar (a + b) U • s.val U = restrictScalar a U • s.val U +
      restrictScalar b U • s.val U
    rw [restrictScalar_add, add_smul]
  zero_smul s := families_ext fun U => by
    change restrictScalar (0 : R.obj (op V)) U • s.val U = 0
    rw [restrictScalar_zero, zero_smul]

theorem family_smul_apply {V : Opens X} (a : R.obj (op V)) (s : Families M.obj.presheaf V)
    (U : Inside B V) :
    (a • s).val U =
      @HSMul.hSMul _ (M.sections U.val) (M.sections U.val) _ (restrictScalar a U) (s.val U) :=
  rfl

/-- The underlying additive sheaf of the extension: the published compatible-family
extension `BasisAllOpen.extension`. -/
abbrev extensionSheaf : BasisSheaf.{u,max u v} (allOpenBasis X) :=
  (BasisAllOpen.extension B).obj ((moduleSheafToBasisSheaf (basisRing B R)).obj M)

instance extensionModule (V : BasisOpen (allOpenBasis X)) :
    Module ((allOpenRing R).obj (op V)) (Sections (extensionSheaf M).obj.obj V) :=
  inferInstanceAs (Module (R.obj (op V.obj)) (Families M.obj.presheaf V.obj))

theorem extension_semilinear :
    (extensionSheaf M).SemilinearRestrictions (allOpenRing R) := by
  intro U V h a s
  apply families_ext
  intro W
  exact congrArg (fun b => @HSMul.hSMul _ (M.sections W.val) (M.sections W.val) _ b
    (s.val ⟨W.val, W.property.trans h⟩)) (restrictScalar_restrict h a W).symm

/-- The extension of a module sheaf on the basis to a module sheaf on all opens. -/
def extensionObj : BasisModuleSheaf.{u,r,max u v} (allOpenRing R) :=
  BasisModuleSheaf.ofBasisSheaf (S := allOpenRing R) (extensionSheaf M) (extension_semilinear M)

end Extension

/-- Morphisms act componentwise on compatible families, preserving the componentwise action. -/
def extensionMap {M N : BasisModuleSheaf.{u,r,max u v} (basisRing B R)} (φ : M ⟶ N) :
    extensionObj M ⟶ extensionObj N :=
  BasisModuleSheaf.ofBasisSheafHom (S := allOpenRing R) (extensionSheaf M) (extensionSheaf N)
    (extension_semilinear M) (extension_semilinear N)
    ((BasisAllOpen.extension B).map ((moduleSheafToBasisSheaf (basisRing B R)).map φ))
    (fun _ a s => families_ext fun U =>
      (BasisModuleSheaf.app φ U.val).hom.map_smul (restrictScalar a U) (s.val U))

variable (B R) in
/-- The extension functor on module sheaves. -/
def extension :
    BasisModuleSheaf.{u,r,max u v} (basisRing B R) ⥤
      BasisModuleSheaf.{u,r,max u v} (allOpenRing R) where
  obj := extensionObj
  map := extensionMap
  map_id _ := BasisModuleSheaf.hom_ext fun _ _ => rfl
  map_comp _ _ := BasisModuleSheaf.hom_ext fun _ _ => rfl

/-! ## Restriction of a module sheaf on all opens to the basis -/

section Restriction

variable (N : BasisModuleSheaf.{u,r,max u v} (allOpenRing R))

/-- The underlying additive sheaf of the restriction: the published `sheafBasisRestriction`. -/
abbrev restrictionSheaf : BasisSheaf.{u,max u v} B :=
  (sheafBasisRestriction B).obj ((moduleSheafToBasisSheaf (allOpenRing R)).obj N)

instance restrictionModule (U : BasisOpen B) :
    Module ((basisRing B R).obj (op U)) (Sections (restrictionSheaf (B := B) N).obj.obj U) :=
  inferInstanceAs (Module ((allOpenRing R).obj (op (allOpen U.obj)))
    (N.obj.obj (op (allOpen U.obj))))

theorem restriction_semilinear :
    (restrictionSheaf (B := B) N).SemilinearRestrictions (basisRing B R) := by
  intro U V h a m
  exact N.restrict_smul (U := allOpen U.obj) (V := allOpen V.obj) h a m

/-- The restriction of a module sheaf on all opens to the basis. -/
def restrictionObj : BasisModuleSheaf.{u,r,max u v} (basisRing B R) :=
  BasisModuleSheaf.ofBasisSheaf (S := basisRing B R) (restrictionSheaf (B := B) N)
    (restriction_semilinear N)

end Restriction

/-- Morphisms restrict to the basis with the same components. -/
def restrictionMap {M N : BasisModuleSheaf.{u,r,max u v} (allOpenRing R)} (φ : M ⟶ N) :
    restrictionObj (B := B) M ⟶ restrictionObj (B := B) N :=
  BasisModuleSheaf.ofBasisSheafHom (S := basisRing B R) (restrictionSheaf (B := B) M)
    (restrictionSheaf (B := B) N) (restriction_semilinear M) (restriction_semilinear N)
    ((sheafBasisRestriction B).map ((moduleSheafToBasisSheaf (allOpenRing R)).map φ))
    (fun U a m => (BasisModuleSheaf.app φ (allOpen U.obj)).hom.map_smul a m)

variable (B R) in
/-- The restriction functor on module sheaves. -/
def restriction :
    BasisModuleSheaf.{u,r,max u v} (allOpenRing R) ⥤
      BasisModuleSheaf.{u,r,max u v} (basisRing B R) where
  obj := restrictionObj
  map := restrictionMap
  map_id _ := BasisModuleSheaf.hom_ext fun _ _ => rfl
  map_comp _ _ := BasisModuleSheaf.hom_ext fun _ _ => rfl

/-! ## Unit and counit -/

section Unit

variable (M : BasisModuleSheaf.{u,r,max u v} (basisRing B R))

/-- The published `basisSectionIso` is linear over `R(U)`. -/
def unitLinearEquiv (U : BasisOpen B) :
    M.obj.obj (op U) ≃ₗ[(basisRing B R).obj (op U)]
      ((restriction B R).obj ((extension B R).obj M)).obj.obj (op U) :=
  AddEquiv.toLinearEquiv (basisSectionIso M.obj.presheaf U) (fun a t => families_ext fun W =>
    M.restrict_smul W.property a t)

/-- The unit isomorphism, the published `basisSectionIso` on each basis member. -/
def unitObjIso : M ≅ (restriction B R).obj ((extension B R).obj M) :=
  ObjectProperty.isoMk _ (PresheafOfModules.isoMk
    (fun U => (unitLinearEquiv M U.unop).toModuleIso) (by
      intro U V f
      ext t
      exact basisSectionIso_restriction M.obj.presheaf f.unop.hom.le t))

end Unit

section Counit

variable (N : BasisModuleSheaf.{u,r,max u v} (allOpenRing R))

/-- The inverse of the counit, the published restriction-family map, is linear. -/
def counitSymmLinearEquiv (V : BasisOpen (allOpenBasis X)) :
    N.obj.obj (op V) ≃ₗ[(allOpenRing R).obj (op V)]
      ((extension B R).obj ((restriction B R).obj N)).obj.obj (op V) :=
  AddEquiv.toLinearEquiv
    (counitSectionIso B ((moduleSheafToBasisSheaf (allOpenRing R)).obj N) V.obj).symm
    (fun a s => families_ext fun U =>
      N.restrict_smul (U := allOpen U.val.obj) (V := V) U.property a s)

/-- The counit isomorphism, the published gluing `counitSectionIso` on every open. -/
def counitObjIso : (extension B R).obj ((restriction B R).obj N) ≅ N :=
  ObjectProperty.isoMk _ (PresheafOfModules.isoMk
    (fun V => (counitSymmLinearEquiv (B := B) N V.unop).symm.toModuleIso) (by
      intro U V f
      ext s
      exact counitSectionIso_restriction B ((moduleSheafToBasisSheaf (allOpenRing R)).obj N)
        f.unop.hom.le s))

end Counit

variable (B R) in
/-- Renard II.2.1 (last paragraph) for sheaves of modules over a ring presheaf defined on all
opens: module sheaves on the basis `B` and on all opens are equivalent. The functors are the
published compatible-family extension and the restriction to `B`, with their module
structures; the unit and counit are the published `basisSectionIso` and `counitSectionIso`. -/
def equivalence :
    BasisModuleSheaf.{u,r,max u v} (basisRing B R) ≌
      BasisModuleSheaf.{u,r,max u v} (allOpenRing R) where
  functor := extension B R
  inverse := restriction B R
  unitIso := NatIso.ofComponents unitObjIso (by
    intro M N φ
    apply BasisModuleSheaf.hom_ext
    intro U t
    exact basisSectionIso_naturality ((moduleSheafToBasisSheaf _).map φ).hom.hom U t)
  counitIso := NatIso.ofComponents counitObjIso (by
    intro M N φ
    apply BasisModuleSheaf.hom_ext
    intro V s
    exact counitSectionIso_naturality B ((moduleSheafToBasisSheaf _).map φ) V.obj s)
  functor_unitIso_comp M := by
    apply BasisModuleSheaf.hom_ext
    intro V s
    exact congrArg (fun φ => (φ.hom.hom.app (op V)).hom s)
      (BasisAllOpen.extension_unit_counit ((moduleSheafToBasisSheaf (basisRing B R)).obj M))

/-- The equivalence forgets to the published additive equivalence. -/
theorem extension_forget :
    extension.{u,r,v} B R ⋙ moduleSheafToBasisSheaf (allOpenRing R) =
      moduleSheafToBasisSheaf (basisRing B R) ⋙ BasisAllOpen.extension B :=
  rfl

theorem restriction_forget :
    restriction.{u,r,v} B R ⋙ moduleSheafToBasisSheaf (basisRing B R) =
      moduleSheafToBasisSheaf (allOpenRing R) ⋙ sheafBasisRestriction B :=
  rfl

/-! ## Locally constant scalars: Renard's `𝒞^∞_X − Mod(X)` on a basis -/

section LocallyConstant

variable (B) in
/-- Sheaves of `𝒞^∞_X`-modules on the basis `B`: module sheaves over the published locally
constant ring presheaf `LocallyConstantScalar.basisRingPresheaf B ℂ`. -/
abbrev ScalarModuleSheaf : Type (u + 1) :=
  BasisModuleSheaf.{u,u,u} (LocallyConstantScalar.basisRingPresheaf B ℂ)

variable (B) in
/-- Sheaves of `𝒞^∞_X`-modules on a basis and on all opens are equivalent. -/
def scalarEquivalence : ScalarModuleSheaf B ≌ ScalarModuleSheaf (allOpenBasis X) :=
  equivalence.{u,u,u} B (LocallyConstantScalar.ringPresheaf X ℂ)

/-- Renard's base `T_c`: sheaves of `𝒞^∞_X`-modules on the compact opens of a t.d. space and on
all opens are equivalent. -/
def compactScalarEquivalence (hX : Langlands.Topology.IsLocallyProfinite X) :
    ScalarModuleSheaf (ProjectorBasisSheaf.compactOpenBasis hX) ≌
      ScalarModuleSheaf (allOpenBasis X) :=
  scalarEquivalence (ProjectorBasisSheaf.compactOpenBasis hX)

end LocallyConstant

end Langlands.Sheaf.Renard.ModuleBasisChange
