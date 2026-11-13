import Langlands.Sheaf.Renard.VectorSheafScalars
import Langlands.Sheaf.Renard.RingedBasisModuleGluing
import Langlands.Sheaf.Renard.RingedBasisModuleAdapter
import Langlands.Sheaf.Renard.AllOpenMathlibSheaf
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Complex vector sheaves and sheaves of `𝒞^∞_X`-modules

Renard (9 July 2026), II.2.5 Remark, printed p.39 / PDF p.45: the notions of sheaf of
complex vector spaces and of sheaf of `𝒞^∞_X`-modules are equivalent; the categories are
equivalent, also for sheaves on all opens. This file constructs the equivalence on all opens.
-/

noncomputable section

namespace Langlands.Sheaf.Renard.VectorSheafModuleEquivalence

open CategoryTheory TopologicalSpace Opposite
open VectorSheafScalars (VectorSheaf)

universe u

section Ringed

variable (X : Type u) [TopologicalSpace X]

/-- Renard's ringed space `(X, 𝒞^∞_X)` on the published basis of all opens: the published
locally constant ring presheaf with its published sheaf proof. -/
def scalarRingedBasis : RingedBasis.{u,u} (allOpenBasis X) where
  ring := LocallyConstantScalar.basisRingPresheaf (allOpenBasis X) ℂ
  isSheaf := LocallyConstantScalar.sheafCondition (allOpenBasis X) ℂ

/-- Renard's category `𝒞^∞_X − Mod(X)` of sheaves of `𝒞^∞_X`-modules, on all opens. -/
abbrev ModuleSheaf : Type (u + 1) :=
  RingedBasis.ModuleSheaf.{u,u,u} (scalarRingedBasis X)

end Ringed

variable {X : Type u} [TopologicalSpace X]

/-- A locally constant function on `U`, read as a section over `U` of the ring sheaf `𝒞^∞_X`
(the identity map; it only fixes the type used for the module action). -/
abbrev scalar {U : Opens X} (f : LocallyConstant U ℂ) :
    (scalarRingedBasis X).ring.obj (op (allOpen U)) :=
  f

/-! ## From complex vector sheaves to sheaves of `𝒞^∞_X`-modules -/

section ToModule

/-- The underlying additive Mathlib sheaf of a complex vector sheaf. -/
abbrev additiveSheaf (F : VectorSheaf X) : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of X) :=
  (sheafCompose (Opens.grothendieckTopology (TopCat.of X))
    (forget₂ (ModuleCat.{u} ℂ) AddCommGrpCat.{u})).obj F

/-- The same sections, as a Renard sheaf on the published basis of all opens. -/
abbrev basisSheaf (F : VectorSheaf X) : BasisSheaf.{u,u} (allOpenBasis X) :=
  (AllOpenMathlib.fromMathlib X).obj (additiveSheaf F)

/-- The published locally constant action `VectorSheafScalars.module` on the sections. -/
instance basisModule (F : VectorSheaf X) (U : BasisOpen (allOpenBasis X)) :
    Module ((scalarRingedBasis X).ring.obj (op U)) (Sections (basisSheaf F).obj.obj U) :=
  inferInstanceAs (Module (LocallyConstant U.obj ℂ) (F.presheaf.obj (op U.obj)))

/-- Restrictions are semilinear along the ring restriction (`VectorSheafScalars.restrict_smul`). -/
theorem semilinearRestrictions (F : VectorSheaf X) :
    (basisSheaf F).SemilinearRestrictions (scalarRingedBasis X).ring := by
  intro _ _ h a m
  exact VectorSheafScalars.restrict_smul F h a m

/-- A complex vector sheaf as a sheaf of `𝒞^∞_X`-modules (Renard II.2.5 Proposition). -/
def toModuleObj (F : VectorSheaf X) : ModuleSheaf X :=
  BasisModuleSheaf.ofBasisSheaf (S := (scalarRingedBasis X).ring) (basisSheaf F)
    (semilinearRestrictions F)

/-- Morphisms of complex vector sheaves preserve the locally constant scalars
(`VectorSheafScalars.app_smul`). -/
def toModuleMap {F G : VectorSheaf X} (φ : F ⟶ G) : toModuleObj F ⟶ toModuleObj G :=
  BasisModuleSheaf.ofBasisSheafHom (S := (scalarRingedBasis X).ring) (basisSheaf F)
    (basisSheaf G) (semilinearRestrictions F) (semilinearRestrictions G)
    ((AllOpenMathlib.fromMathlib X).map
      ((sheafCompose (Opens.grothendieckTopology (TopCat.of X))
        (forget₂ (ModuleCat.{u} ℂ) AddCommGrpCat.{u})).map φ))
    (fun _ a m => VectorSheafScalars.app_smul φ a m)

variable (X) in
/-- The functor from complex vector sheaves to sheaves of `𝒞^∞_X`-modules. -/
def toModule : VectorSheaf X ⥤ ModuleSheaf X where
  obj := toModuleObj
  map := toModuleMap
  map_id _ := BasisModuleSheaf.hom_ext fun _ _ => rfl
  map_comp _ _ := BasisModuleSheaf.hom_ext fun _ _ => rfl

theorem toModule_sections (F : VectorSheaf X) (U : Opens X) :
    (AllOpenModuleSheaf.sections ((toModule X).obj F) U : Type u) = F.presheaf.obj (op U) :=
  rfl

theorem toModule_restrict (F : VectorSheaf X) {U V : Opens X} (h : U ≤ V)
    (s : F.presheaf.obj (op V)) :
    AllOpenModuleSheaf.restrict ((toModule X).obj F) h s = F.presheaf.map (homOfLE h).op s :=
  rfl

/-- The action on the module sheaf is the published glued action `f • s`, with germs
`f(x) s(x)`. -/
theorem toModule_smul (F : VectorSheaf X) {U : Opens X} (f : LocallyConstant U ℂ)
    (s : AllOpenModuleSheaf.sections ((toModule X).obj F) U) :
    scalar f • s = VectorSheafScalars.smul F f s :=
  rfl

theorem toModule_map_app {F G : VectorSheaf X} (φ : F ⟶ G) (U : Opens X)
    (s : F.presheaf.obj (op U)) :
    AllOpenModuleSheaf.app ((toModule X).map φ) U s = φ.hom.app (op U) s :=
  rfl

variable (X) in
/-- Forgetting the new action recovers the published additive sheaf of `F` on the basis of
all opens. -/
theorem toModule_forget :
    toModule X ⋙ moduleSheafToBasisSheaf (scalarRingedBasis X).ring =
      sheafCompose (Opens.grothendieckTopology (TopCat.of X))
          (forget₂ (ModuleCat.{u} ℂ) AddCommGrpCat.{u}) ⋙ AllOpenMathlib.fromMathlib X :=
  rfl

end ToModule

/-! ## From sheaves of `𝒞^∞_X`-modules to complex vector sheaves -/

section ToVector

/-- Restriction of scalars along the constant functions `ℂ → 𝒞^∞(U)`. -/
abbrev vectorSections (M : ModuleSheaf X) (U : Opens X) : ModuleCat.{u} ℂ :=
  (ModuleCat.restrictScalars (LocallyConstantScalar.constants ℂ U)).obj
    (AllOpenModuleSheaf.sections M U)

/-- The complex structure is the action of the constant functions. -/
theorem vectorSections_smul (M : ModuleSheaf X) (U : Opens X) (c : ℂ)
    (m : vectorSections M U) :
    c • m = scalar (LocallyConstantScalar.constants ℂ U c) •
      (show AllOpenModuleSheaf.sections M U from m) :=
  rfl

/-- The original restriction is complex linear for the complex structures of the constants. -/
def vectorRestrictLinear (M : ModuleSheaf X) {U V : Opens X} (h : U ≤ V) :
    vectorSections M V →ₗ[ℂ] vectorSections M U where
  toFun m := AllOpenModuleSheaf.restrict M h m
  map_add' m n := map_add (AllOpenModuleSheaf.restrict M h) m n
  map_smul' c m := by
    change AllOpenModuleSheaf.restrict M h (scalar (LocallyConstantScalar.constants ℂ V c) •
        (show AllOpenModuleSheaf.sections M V from m)) =
      scalar (LocallyConstantScalar.constants ℂ U c) • AllOpenModuleSheaf.restrict M h m
    rw [AllOpenModuleSheaf.restrict_smul]
    exact congrArg (fun a => a • AllOpenModuleSheaf.restrict M h m)
      (LocallyConstantScalar.restrict_constants ℂ h c)

/-- The restriction as a morphism of complex vector spaces. -/
def vectorRestrict (M : ModuleSheaf X) {U V : Opens X} (h : U ≤ V) :
    vectorSections M V ⟶ vectorSections M U :=
  ModuleCat.ofHom (X := vectorSections M V) (Y := vectorSections M U) (vectorRestrictLinear M h)

theorem vectorRestrict_apply (M : ModuleSheaf X) {U V : Opens X} (h : U ≤ V)
    (m : vectorSections M V) :
    vectorRestrict M h m = AllOpenModuleSheaf.restrict M h m :=
  rfl

/-- The presheaf of complex vector spaces underlying a sheaf of `𝒞^∞_X`-modules. -/
def vectorPresheaf (M : ModuleSheaf X) : TopCat.Presheaf (ModuleCat.{u} ℂ) (TopCat.of X) where
  obj U := vectorSections M U.unop
  map f := vectorRestrict M f.unop.le
  map_id U := by
    ext m
    exact BasisModuleSheaf.restrict_self M (allOpen U.unop) m
  map_comp f g := by
    ext m
    change AllOpenModuleSheaf.restrict M _ m =
      AllOpenModuleSheaf.restrict M g.unop.le (AllOpenModuleSheaf.restrict M f.unop.le m)
    exact (BasisModuleSheaf.restrict_comp M (U := allOpen _) (V := allOpen _) (W := allOpen _)
      g.unop.le f.unop.le m).symm

/-- Forgetting the complex structure gives the published additive Mathlib sheaf of `M`. -/
theorem vectorPresheaf_forget₂ (M : ModuleSheaf X) :
    vectorPresheaf M ⋙ forget₂ (ModuleCat.{u} ℂ) AddCommGrpCat.{u} =
      ((AllOpenMathlib.toMathlib X).obj
        ((moduleSheafToBasisSheaf (scalarRingedBasis X).ring).obj M)).obj :=
  rfl

theorem vectorPresheaf_isSheaf (M : ModuleSheaf X) : (vectorPresheaf M).IsSheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheaf_comp'
    (forget₂ (ModuleCat.{u} ℂ) AddCommGrpCat.{u}), vectorPresheaf_forget₂]
  exact ((AllOpenMathlib.toMathlib X).obj
    ((moduleSheafToBasisSheaf (scalarRingedBasis X).ring).obj M)).property

/-- A sheaf of `𝒞^∞_X`-modules as a complex vector sheaf (Renard II.2.5 Remark). -/
def toVectorObj (M : ModuleSheaf X) : VectorSheaf X :=
  ⟨vectorPresheaf M, vectorPresheaf_isSheaf M⟩

/-- A morphism of module sheaves, complex linear for the constants. -/
def toVectorApp {M N : ModuleSheaf X} (f : M ⟶ N) (U : Opens X) :
    vectorSections M U ⟶ vectorSections N U :=
  (ModuleCat.restrictScalars (LocallyConstantScalar.constants ℂ U)).map
    (AllOpenModuleSheaf.app f U)

/-- Morphisms of module sheaves give morphisms of complex vector sheaves. -/
def toVectorMap {M N : ModuleSheaf X} (f : M ⟶ N) : toVectorObj M ⟶ toVectorObj N :=
  ObjectProperty.homMk
    { app := fun U => toVectorApp f U.unop
      naturality := fun U V g => by
        ext m
        change AllOpenModuleSheaf.app f V.unop (AllOpenModuleSheaf.restrict M g.unop.le m) =
          AllOpenModuleSheaf.restrict N g.unop.le (AllOpenModuleSheaf.app f U.unop m)
        exact BasisModuleSheaf.app_restrict f (U := allOpen V.unop) (V := allOpen U.unop)
          g.unop.le m }

variable (X) in
/-- The functor from sheaves of `𝒞^∞_X`-modules to complex vector sheaves. -/
def toVector : ModuleSheaf X ⥤ VectorSheaf X where
  obj := toVectorObj
  map := toVectorMap
  map_id M := by
    apply Sheaf.hom_ext
    ext U m
    rfl
  map_comp f g := by
    apply Sheaf.hom_ext
    ext U m
    rfl

theorem toVector_sections (M : ModuleSheaf X) (U : Opens X) :
    (((toVector X).obj M).presheaf.obj (op U) : Type u) = AllOpenModuleSheaf.sections M U :=
  rfl

theorem toVector_restrict (M : ModuleSheaf X) {U V : Opens X} (h : U ≤ V)
    (m : ((toVector X).obj M).presheaf.obj (op V)) :
    ((toVector X).obj M).presheaf.map (homOfLE h).op m = AllOpenModuleSheaf.restrict M h m :=
  rfl

theorem toVector_map_app {M N : ModuleSheaf X} (f : M ⟶ N) (U : Opens X)
    (m : ((toVector X).obj M).presheaf.obj (op U)) :
    ((toVector X).map f).hom.app (op U) m = AllOpenModuleSheaf.app f U m :=
  rfl

variable (X) in
/-- Forgetting the complex structure recovers the published additive Mathlib sheaf of `M`. -/
theorem toVector_forget :
    toVector X ⋙ sheafCompose (Opens.grothendieckTopology (TopCat.of X))
        (forget₂ (ModuleCat.{u} ℂ) AddCommGrpCat.{u}) =
      moduleSheafToBasisSheaf (scalarRingedBasis X).ring ⋙ AllOpenMathlib.toMathlib X :=
  rfl

end ToVector

/-! ## The equivalence -/

section Equivalence

/-- The unit component: identity on sections, complex linear by
`VectorSheafScalars.constants_smul`. -/
def unitLinearEquiv (F : VectorSheaf X) (U : Opens X) :
    F.presheaf.obj (op U) ≃ₗ[ℂ] ((toVector X).obj ((toModule X).obj F)).presheaf.obj (op U) where
  toFun s := s
  invFun s := s
  map_add' _ _ := rfl
  map_smul' c s := (VectorSheafScalars.constants_smul F c s).symm
  left_inv _ := rfl
  right_inv _ := rfl

/-- The unit component as an isomorphism of complex vector spaces. -/
def unitApp (F : VectorSheaf X) (U : Opens X) :
    F.presheaf.obj (op U) ≅ ((toVector X).obj ((toModule X).obj F)).presheaf.obj (op U) :=
  (unitLinearEquiv F U).toModuleIso

/-- The unit isomorphism `F ≅ toVector (toModule F)`, identity on sections. -/
def unitObjIso (F : VectorSheaf X) : F ≅ (toVector X).obj ((toModule X).obj F) :=
  ObjectProperty.isoMk _ (NatIso.ofComponents (fun U => unitApp F U.unop) (by
    intro U V g
    ext s
    rfl))

/-- On the restriction of `f` to its fibre at `x`, the given action of `f` is the constant
`f(x)`. Hence the published glued action recovers the given action. -/
theorem smul_toVector (M : ModuleSheaf X) {U : Opens X} (f : LocallyConstant U ℂ)
    (m : AllOpenModuleSheaf.sections M U) :
    VectorSheafScalars.smul ((toVector X).obj M) f m = scalar f • m := by
  refine ((VectorSheafScalars.eq_smul_iff ((toVector X).obj M) f m (scalar f • m)).mpr ?_).symm
  intro x hx
  have hle := VectorSheafScalars.fiber_le f ⟨x, hx⟩
  have hmem := VectorSheafScalars.mem_fiber_self f ⟨x, hx⟩
  have hres : LocallyConstantScalar.restrict ℂ hle f =
      LocallyConstantScalar.constants ℂ (VectorSheafScalars.fiber f ⟨x, hx⟩) (f ⟨x, hx⟩) := by
    apply LocallyConstant.ext
    intro y
    exact VectorSheafScalars.apply_eq_of_mem_fiber (X := X) (U := U) f ⟨x, hx⟩ y.property
  have key : ((toVector X).obj M).presheaf.map (homOfLE hle).op (scalar f • m) =
      f ⟨x, hx⟩ • ((toVector X).obj M).presheaf.map (homOfLE hle).op m := by
    change AllOpenModuleSheaf.restrict M hle (scalar f • m) =
      scalar (LocallyConstantScalar.constants ℂ (VectorSheafScalars.fiber f ⟨x, hx⟩)
        (f ⟨x, hx⟩)) • AllOpenModuleSheaf.restrict M hle m
    rw [AllOpenModuleSheaf.restrict_smul]
    exact congrArg (fun a => a • AllOpenModuleSheaf.restrict M hle m) hres
  rw [← TopCat.Presheaf.germ_res_apply ((toVector X).obj M).presheaf (homOfLE hle) x hmem
    (scalar f • m), key, map_smul,
    TopCat.Presheaf.germ_res_apply ((toVector X).obj M).presheaf (homOfLE hle) x hmem m]

/-- The counit component on basis opens: identity on sections, linear over `𝒞^∞(U)` by
`smul_toVector`. -/
def counitLinearEquiv (M : ModuleSheaf X) (U : BasisOpen (allOpenBasis X)) :
    ((toModule X).obj ((toVector X).obj M)).obj.obj (op U) ≃ₗ[(scalarRingedBasis X).ring.obj (op U)]
      M.obj.obj (op U) where
  toFun m := m
  invFun m := m
  map_add' _ _ := rfl
  map_smul' f m := smul_toVector M (U := U.obj) f m
  left_inv _ := rfl
  right_inv _ := rfl

/-- The counit component as an isomorphism of `𝒞^∞(U)`-modules. -/
def counitApp (M : ModuleSheaf X) (U : BasisOpen (allOpenBasis X)) :
    ((toModule X).obj ((toVector X).obj M)).obj.obj (op U) ≅ M.obj.obj (op U) :=
  (counitLinearEquiv M U).toModuleIso

/-- The counit isomorphism `toModule (toVector M) ≅ M`, identity on sections. -/
def counitObjIso (M : ModuleSheaf X) : (toModule X).obj ((toVector X).obj M) ≅ M :=
  ObjectProperty.isoMk _ (PresheafOfModules.isoMk (fun U => counitApp M U.unop) (by
    intro U V g
    ext m
    rfl))

variable (X) in
/-- Renard II.2.5 Remark, on all opens: complex vector sheaves and sheaves of
`𝒞^∞_X`-modules form equivalent categories. Both functors keep the sections and
restriction maps; the unit and counit are identities on sections. -/
def equivalence : VectorSheaf X ≌ ModuleSheaf X where
  functor := toModule X
  inverse := toVector X
  unitIso := NatIso.ofComponents unitObjIso (by
    intro F G φ
    apply Sheaf.hom_ext
    ext U s
    rfl)
  counitIso := NatIso.ofComponents counitObjIso (by
    intro M N f
    apply BasisModuleSheaf.hom_ext
    intro U m
    rfl)
  functor_unitIso_comp F := by
    apply BasisModuleSheaf.hom_ext
    intro U m
    rfl

theorem equivalence_functor : (equivalence X).functor = toModule X := rfl

theorem equivalence_inverse : (equivalence X).inverse = toVector X := rfl

theorem equivalence_unitIso_hom_app (F : VectorSheaf X) (U : Opens X)
    (s : F.presheaf.obj (op U)) :
    ((equivalence X).unitIso.hom.app F).hom.app (op U) s = s :=
  rfl

theorem equivalence_counitIso_hom_app (M : ModuleSheaf X) (U : Opens X)
    (m : AllOpenModuleSheaf.sections M U) :
    AllOpenModuleSheaf.app ((equivalence X).counitIso.hom.app M) U m = m :=
  rfl

end Equivalence

end Langlands.Sheaf.Renard.VectorSheafModuleEquivalence
