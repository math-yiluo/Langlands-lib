import Langlands.Sheaf.Renard.LocallyConstantScalarConstants
import Mathlib.Topology.Sheaves.Stalks
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits

/-!
# Locally constant scalars on complex vector sheaves

Renard (9 July 2026), II.2.5 Proposition, printed p.38 / PDF p.44.
Sections over an open `U` are glued from constant multiples on the open
fibres of a locally constant function on `U`.
-/

noncomputable section

namespace Langlands.Sheaf.Renard.VectorSheafScalars

open CategoryTheory TopologicalSpace Opposite

universe u

/-- Mathlib's filtered-colimit cocone of complex vector spaces, at carrier universe `u`.
Mathlib's own instance only covers coefficient rings in the carrier universe. -/
instance forget₂_preservesFilteredColimits :
    Limits.PreservesFilteredColimitsOfSize.{u, u}
      (forget₂ (ModuleCat.{u} ℂ) AddCommGrpCat.{u}) where
  preserves_filtered_colimits _ _ _ :=
    { preservesColimit := fun {G} =>
        Limits.preservesColimit_of_preserves_colimit_cocone
          (ModuleCat.FilteredColimits.colimitCoconeIsColimit G)
          (AddCommGrpCat.FilteredColimits.colimitCoconeIsColimit
            (G ⋙ forget₂ (ModuleCat.{u} ℂ) AddCommGrpCat.{u})) }

/-- Germs of complex vector sheaves at every carrier universe are computed elementwise. -/
instance forget_preservesFilteredColimits :
    Limits.PreservesFilteredColimits (forget (ModuleCat.{u} ℂ)) :=
  Limits.comp_preservesFilteredColimits (forget₂ (ModuleCat.{u} ℂ) AddCommGrpCat.{u})
    (forget AddCommGrpCat.{u})

variable {X : Type u} [TopologicalSpace X]

/-- Renard's complex vector sheaves: Mathlib sheaves of complex vector spaces on `X`. -/
abbrev VectorSheaf (X : Type u) [TopologicalSpace X] :=
  TopCat.Sheaf (ModuleCat.{u} ℂ) (TopCat.of X)

section Fiber

variable {U : Opens X} (f : LocallyConstant U ℂ)

/-- The open subset of `U` where `f` takes its value at `x`. -/
def fiber (x : U) : Opens X where
  carrier := Subtype.val '' {y : U | f y = f x}
  is_open' := U.isOpen.isOpenMap_subtype_val _ (f.isLocallyConstant.isOpen_fiber _)

theorem fiber_le (x : U) : fiber f x ≤ U := by
  rintro _ ⟨y, -, rfl⟩
  exact y.property

theorem mem_fiber_self (x : U) : (x : X) ∈ fiber f x :=
  ⟨x, rfl, rfl⟩

theorem apply_eq_of_mem_fiber (x : U) {y : X} (hy : y ∈ fiber f x) :
    f ⟨y, fiber_le f x hy⟩ = f x := by
  obtain ⟨z, hz, rfl⟩ := hy
  exact hz

theorem le_iSup_fiber : U ≤ ⨆ x, fiber f x := fun y hy =>
  Opens.mem_iSup.mpr ⟨⟨y, hy⟩, mem_fiber_self f ⟨y, hy⟩⟩

end Fiber

variable (F : VectorSheaf X)

section Gluing

variable {U : Opens X}

/-- The constant multiple of the restricted section on one fibre. -/
def fiberSection (f : LocallyConstant U ℂ) (s : F.presheaf.obj (op U)) (x : U) :
    F.presheaf.obj (op (fiber f x)) :=
  f x • F.presheaf.map (homOfLE (fiber_le f x)).op s

theorem germ_fiberSection (f : LocallyConstant U ℂ) (s : F.presheaf.obj (op U)) (x : U)
    (y : X) (hy : y ∈ fiber f x) :
    F.presheaf.germ (fiber f x) y hy (fiberSection F f s x) =
      f x • F.presheaf.germ U y (fiber_le f x hy) s := by
  rw [fiberSection, map_smul, TopCat.Presheaf.germ_res_apply]

theorem isCompatible (f : LocallyConstant U ℂ) (s : F.presheaf.obj (op U)) :
    TopCat.Presheaf.IsCompatible F.presheaf (fiber f) (fiberSection F f s) := by
  intro x y
  apply TopCat.Presheaf.section_ext F
  intro z hz
  rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply,
    germ_fiberSection, germ_fiberSection, ← apply_eq_of_mem_fiber f x hz.1,
    ← apply_eq_of_mem_fiber f y hz.2]

/-- The glued section `f • s`, Renard's `(f s)(x) = f(x) s(x)`. -/
def smul (f : LocallyConstant U ℂ) (s : F.presheaf.obj (op U)) : F.presheaf.obj (op U) :=
  (F.existsUnique_gluing' (fiber f) U (fun x => homOfLE (fiber_le f x))
    (le_iSup_fiber f) (fiberSection F f s) (isCompatible F f s)).exists.choose

theorem restrict_smul_fiber (f : LocallyConstant U ℂ) (s : F.presheaf.obj (op U)) (x : U) :
    F.presheaf.map (homOfLE (fiber_le f x)).op (smul F f s) = fiberSection F f s x :=
  (F.existsUnique_gluing' (fiber f) U (fun x => homOfLE (fiber_le f x))
    (le_iSup_fiber f) (fiberSection F f s) (isCompatible F f s)).exists.choose_spec x

/-- The germ formula of the source: the germ of `f • s` at `x` is `f(x)` times that of `s`. -/
theorem germ_smul (f : LocallyConstant U ℂ) (s : F.presheaf.obj (op U)) (x : X)
    (hx : x ∈ U) :
    F.presheaf.germ U x hx (smul F f s) = f ⟨x, hx⟩ • F.presheaf.germ U x hx s := by
  rw [← TopCat.Presheaf.germ_res_apply F.presheaf (homOfLE (fiber_le f ⟨x, hx⟩)) x
    (mem_fiber_self f ⟨x, hx⟩), restrict_smul_fiber, germ_fiberSection]

/-- Sections of a vector sheaf are determined by their germs. -/
theorem ext_germ {s t : F.presheaf.obj (op U)}
    (h : ∀ (x : X) (hx : x ∈ U), F.presheaf.germ U x hx s = F.presheaf.germ U x hx t) :
    s = t :=
  TopCat.Presheaf.section_ext F U s t h

/-- The glued section is the unique section with the source germ formula. -/
theorem eq_smul_iff (f : LocallyConstant U ℂ) (s t : F.presheaf.obj (op U)) :
    t = smul F f s ↔ ∀ (x : X) (hx : x ∈ U),
      F.presheaf.germ U x hx t = f ⟨x, hx⟩ • F.presheaf.germ U x hx s := by
  constructor
  · rintro rfl x hx
    exact germ_smul F f s x hx
  · intro h
    exact ext_germ F fun x hx => by rw [h, germ_smul]

end Gluing

section Module

variable {U : Opens X}

/-- Renard II.2.5 Proposition: sections over `U` form a module over locally constant
complex functions on `U`. -/
instance module : Module (LocallyConstant U ℂ) (F.presheaf.obj (op U)) where
  smul := smul F
  one_smul s := by
    change smul F 1 s = s
    exact ext_germ F fun x hx => by rw [germ_smul, LocallyConstant.one_apply, one_smul]
  mul_smul f g s := by
    change smul F (f * g) s = smul F f (smul F g s)
    exact ext_germ F fun x hx => by
      rw [germ_smul, germ_smul, germ_smul, LocallyConstant.mul_apply, mul_smul]
  smul_zero f := by
    change smul F f 0 = 0
    exact ext_germ F fun x hx => by rw [germ_smul, map_zero, smul_zero]
  smul_add f s t := by
    change smul F f (s + t) = smul F f s + smul F f t
    exact ext_germ F fun x hx => by
      rw [germ_smul, map_add, map_add, germ_smul, germ_smul, smul_add]
  add_smul f g s := by
    change smul F (f + g) s = smul F f s + smul F g s
    exact ext_germ F fun x hx => by
      rw [germ_smul, map_add, germ_smul, germ_smul, LocallyConstant.add_apply, add_smul]
  zero_smul s := by
    change smul F 0 s = 0
    exact ext_germ F fun x hx => by
      rw [germ_smul, LocallyConstant.zero_apply, zero_smul, map_zero]

theorem smul_eq (f : LocallyConstant U ℂ) (s : F.presheaf.obj (op U)) :
    f • s = smul F f s := rfl

/-- Renard's formula `(f s)(x) = f(x) s(x)`, read on germs. -/
@[simp]
theorem germ_lc_smul (f : LocallyConstant U ℂ) (s : F.presheaf.obj (op U)) (x : X)
    (hx : x ∈ U) :
    F.presheaf.germ U x hx (f • s) = f ⟨x, hx⟩ • F.presheaf.germ U x hx s :=
  germ_smul F f s x hx

/-- On an open where `f` is constant, `f • s` restricts to the constant multiple. -/
theorem restrict_smul_of_eq {V : Opens X} (h : V ≤ U) (f : LocallyConstant U ℂ) (c : ℂ)
    (hf : ∀ (x : X) (hx : x ∈ V), f ⟨x, h hx⟩ = c) (s : F.presheaf.obj (op U)) :
    F.presheaf.map (homOfLE h).op (f • s) = c • F.presheaf.map (homOfLE h).op s :=
  ext_germ F fun x hx => by
    rw [TopCat.Presheaf.germ_res_apply, germ_lc_smul, map_smul,
      TopCat.Presheaf.germ_res_apply, hf x hx]

/-- Constant functions act through the original complex structure. -/
@[simp]
theorem constants_smul (c : ℂ) (s : F.presheaf.obj (op U)) :
    LocallyConstantScalar.constants ℂ U c • s = c • s :=
  ext_germ F fun x hx => by
    rw [germ_lc_smul, map_smul, LocallyConstantScalar.constants_apply]

/-- The algebra map gives the same constant action. -/
theorem algebraMap_smul (c : ℂ) (s : F.presheaf.obj (op U)) :
    algebraMap ℂ (LocallyConstant U ℂ) c • s = c • s :=
  constants_smul F c s

instance isScalarTower : IsScalarTower ℂ (LocallyConstant U ℂ) (F.presheaf.obj (op U)) where
  smul_assoc c f s := ext_germ F fun x hx => by
    rw [germ_lc_smul, map_smul, germ_lc_smul, LocallyConstant.smul_apply,
      smul_eq_mul, mul_smul]

instance smulCommClass : SMulCommClass ℂ (LocallyConstant U ℂ) (F.presheaf.obj (op U)) where
  smul_comm c f s := ext_germ F fun x hx => by
    rw [map_smul, germ_lc_smul, germ_lc_smul, map_smul, smul_comm]

end Module

section Restriction

/-- Restriction is semilinear over the restriction of scalars. -/
theorem restrict_smul {U V : Opens X} (h : U ≤ V) (f : LocallyConstant V ℂ)
    (s : F.presheaf.obj (op V)) :
    F.presheaf.map (homOfLE h).op (f • s) =
      LocallyConstantScalar.restrict ℂ h f • F.presheaf.map (homOfLE h).op s :=
  ext_germ F fun x hx => by
    rw [TopCat.Presheaf.germ_res_apply, germ_lc_smul, germ_lc_smul,
      TopCat.Presheaf.germ_res_apply]
    rfl

/-- Restriction as an actual semilinear map along Mathlib's pullback of scalars. -/
def restrictSemilinear {U V : Opens X} (h : U ≤ V) :
    F.presheaf.obj (op V) →ₛₗ[LocallyConstantScalar.restrict ℂ h] F.presheaf.obj (op U) where
  toFun := F.presheaf.map (homOfLE h).op
  map_add' := map_add _
  map_smul' := restrict_smul F h

@[simp]
theorem restrictSemilinear_apply {U V : Opens X} (h : U ≤ V) (s : F.presheaf.obj (op V)) :
    restrictSemilinear F h s = F.presheaf.map (homOfLE h).op s := rfl

end Restriction

section Morphisms

variable {F} {G : VectorSheaf X}

/-- Sheaf morphisms commute with the locally constant scalar action. -/
theorem app_smul (φ : F ⟶ G) {U : Opens X} (f : LocallyConstant U ℂ)
    (s : F.presheaf.obj (op U)) :
    φ.hom.app (op U) (f • s) = f • φ.hom.app (op U) s :=
  ext_germ G fun x hx => by
    rw [germ_lc_smul, ← TopCat.Presheaf.stalkFunctor_map_germ_apply,
      ← TopCat.Presheaf.stalkFunctor_map_germ_apply, germ_lc_smul]
    exact ((TopCat.Presheaf.stalkFunctor (ModuleCat.{u} ℂ) x).map φ.hom).hom.map_smul _ _

/-- Each component of a sheaf morphism is linear over the locally constant scalars. -/
def appLinear (φ : F ⟶ G) (U : Opens X) :
    F.presheaf.obj (op U) →ₗ[LocallyConstant U ℂ] G.presheaf.obj (op U) where
  toFun := φ.hom.app (op U)
  map_add' := map_add _
  map_smul' := app_smul φ

@[simp]
theorem appLinear_apply (φ : F ⟶ G) (U : Opens X) (s : F.presheaf.obj (op U)) :
    appLinear φ U s = φ.hom.app (op U) s := rfl

end Morphisms

end Langlands.Sheaf.Renard.VectorSheafScalars
