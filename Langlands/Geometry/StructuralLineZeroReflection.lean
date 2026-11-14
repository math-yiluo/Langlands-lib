import Langlands.Geometry.FormalGroup.DeligneStructuralBaseChange
import Mathlib.AlgebraicGeometry.ResidueField

/-! # Reflection of zero for actual structural line-sheaf maps over fields -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.DeligneFormalSpace

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

section Scalars

variable {S S' : Scheme.{u}}

/-- The global scalar determining an endomorphism of the actual structure module. -/
def structuralUnitEndScalar (e : SheafOfModules.unit S.ringCatSheaf ⟶
    SheafOfModules.unit S.ringCatSheaf) : Γ(S, ⊤) :=
  e.val.app (.op ⊤) (1 : Γ(S, ⊤))

/-- Every endomorphism of the structure module is actual scalar multiplication. -/
theorem structuralUnitEnd_eq_scalar (e : SheafOfModules.unit S.ringCatSheaf ⟶
    SheafOfModules.unit S.ringCatSheaf) :
    e = structuralScalarEnd (SheafOfModules.unit S.ringCatSheaf)
      (structuralUnitEndScalar e) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change S.presheaf.obj U at x
  have hn := PresheafOfModules.naturality_apply e.val
    (homOfLE (show U.unop ≤ ⊤ from le_top)).op (1 : Γ(S, ⊤))
  change e.val.app U
      ((S.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op).hom 1) =
    (S.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op).hom
      (structuralUnitEndScalar e) at hn
  have hr : e.val.app U (1 : S.presheaf.obj U) =
      S.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op
        (structuralUnitEndScalar e) := by
    simpa only [map_one] using hn
  change e.val.app U x =
    (S.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op
      (structuralUnitEndScalar e)) * x
  calc
    _ = e.val.app U (x • (1 : S.presheaf.obj U)) := by
      rw [smul_eq_mul, mul_one]
    _ = x • e.val.app U (1 : S.presheaf.obj U) :=
      (e.val.app U).hom.map_smul x (1 : S.presheaf.obj U)
    _ = _ := by rw [hr, smul_eq_mul, mul_comm]

@[reassoc]
theorem structuralScalarEnd_naturality {M N : S.Modules} (g : M ⟶ N)
    (a : Γ(S, ⊤)) :
    structuralScalarEnd M a ≫ g = g ≫ structuralScalarEnd N a := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  exact (g.val.app U).hom.map_smul ((schemeScalar S a).val U) x

/-- A scalar acting as zero on a globally trivial line is zero. -/
theorem structuralScalarEnd_eq_zero_of_unitIso {M : S.Modules}
    (e : M ≅ SheafOfModules.unit S.ringCatSheaf) (a : Γ(S, ⊤))
    (h : structuralScalarEnd M a = 0) : a = 0 := by
  have hs : structuralScalarEnd (SheafOfModules.unit S.ringCatSheaf) a = 0 := by
    apply (cancel_epi e.hom).mp
    rw [comp_zero, ← structuralScalarEnd_naturality, h, zero_comp]
  have ht := congrArg (fun k => k.val.app (.op ⊤) (1 : Γ(S, ⊤))) hs
  change (structuralScalarEnd (SheafOfModules.unit S.ringCatSheaf) a).val.app
    (.op ⊤) (1 : Γ(S, ⊤)) = (0 : Γ(S, ⊤)) at ht
  simpa [structuralScalarEnd, schemeScalar] using ht

/-- An injective map on actual global scalars makes pullback reflect zero on the unit. -/
theorem structuralPullback_unit_map_eq_zero_iff (f : S' ⟶ S)
    (hf : Function.Injective f.appTop)
    (e : SheafOfModules.unit S.ringCatSheaf ⟶ SheafOfModules.unit S.ringCatSheaf) :
    (Scheme.Modules.pullback f).map e = 0 ↔ e = 0 := by
  constructor
  · intro he
    rw [structuralUnitEnd_eq_scalar e, pullback_structuralScalarEnd] at he
    have ha := structuralScalarEnd_eq_zero_of_unitIso
      (structuralPullbackUnitIso f) (f.appTop (structuralUnitEndScalar e)) he
    have hb : structuralUnitEndScalar e = 0 :=
      hf (ha.trans (map_zero f.appTop.hom).symm)
    rw [structuralUnitEnd_eq_scalar e, hb]
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change S.presheaf.obj U at x
    change (S.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op).hom 0 * x = 0
    rw [map_zero, zero_mul]
  · rintro rfl
    simp only [Functor.map_zero]

end Scalars

section Singleton

variable {S : Scheme.{u}}

/-- Pull a top restriction back along the inverse of the canonical top isomorphism. -/
def structuralTopRestrictionIso (M : S.Modules) :
    (Scheme.Modules.pullback S.topIso.inv).obj
      (M.restrict (⊤ : S.Opens).ι) ≅ M :=
  (Scheme.Modules.pullback S.topIso.inv).mapIso
    ((Scheme.Modules.restrictFunctorIsoPullback (⊤ : S.Opens).ι).app M) ≪≫
    (Scheme.Modules.pullbackComp S.topIso.inv (⊤ : S.Opens).ι).app M ≪≫
    (Scheme.Modules.pullbackCongr (Scheme.toIso_inv_ι S)).app M ≪≫
    (Scheme.Modules.pullbackId S).app M

namespace IsLineSheaf

/-- Local rank one over a nonempty singleton scheme gives an actual global unit isomorphism. -/
theorem nonempty_unitIso [Nonempty S] [Subsingleton S] {M : S.Modules}
    (h : IsLineSheaf S M) :
    Nonempty (M ≅ SheafOfModules.unit S.ringCatSheaf) := by
  obtain ⟨U, hx, ⟨e⟩⟩ := h (Classical.arbitrary S)
  have hU : U = ⊤ := by
    apply le_antisymm le_top
    intro y _
    exact (Subsingleton.elim (Classical.arbitrary S) y) ▸ hx
  subst U
  exact ⟨(structuralTopRestrictionIso M).symm ≪≫
    (Scheme.Modules.pullback S.topIso.inv).mapIso e ≪≫
      structuralPullbackUnitIso S.topIso.inv⟩

end IsLineSheaf

/-- Pullback reflects zero for maps of line sheaves on a singleton base
when its map on global structural scalars is injective. -/
theorem structuralPullback_line_map_eq_zero_iff [Nonempty S] [Subsingleton S]
    {S' : Scheme.{u}} (f : S' ⟶ S) (hf : Function.Injective f.appTop)
    {M N : S.Modules} (hM : IsLineSheaf S M) (hN : IsLineSheaf S N)
    (g : M ⟶ N) :
    (Scheme.Modules.pullback f).map g = 0 ↔ g = 0 := by
  constructor
  · intro hg
    obtain ⟨eM⟩ := hM.nonempty_unitIso
    obtain ⟨eN⟩ := hN.nonempty_unitIso
    have he : (Scheme.Modules.pullback f).map (eM.inv ≫ g ≫ eN.hom) = 0 := by
      rw [Functor.map_comp, Functor.map_comp, hg, zero_comp, comp_zero]
    have hz := (structuralPullback_unit_map_eq_zero_iff f hf _).mp he
    apply (cancel_epi eM.inv).mp
    apply (cancel_mono eN.hom).mp
    simpa only [Category.assoc, zero_comp, comp_zero] using hz
  · rintro rfl
    simp only [Functor.map_zero]

end Singleton

section Fields

variable {K L : Type u} [Field K] [Field L]

/-- The actual global-sections map of a field extension is injective. -/
theorem specField_appTop_injective (r : CommRingCat.of K ⟶ CommRingCat.of L) :
    Function.Injective (Spec.map r).appTop := by
  intro a b hab
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).hom).1
  apply r.hom.injective
  have hn := Scheme.ΓSpecIso_naturality r
  have he := congrArg (fun t => t a) hn
  have he' := congrArg (fun t => t b) hn
  change (Scheme.ΓSpecIso (CommRingCat.of L)).hom ((Spec.map r).appTop a) =
    r ((Scheme.ΓSpecIso (CommRingCat.of K)).hom a) at he
  change (Scheme.ΓSpecIso (CommRingCat.of L)).hom ((Spec.map r).appTop b) =
    r ((Scheme.ΓSpecIso (CommRingCat.of K)).hom b) at he'
  rw [← he, ← he', hab]

/-- Field extension reflects zero on maps between actual line sheaves. -/
theorem specField_pullback_line_map_eq_zero_iff
    (r : CommRingCat.of K ⟶ CommRingCat.of L)
    {M N : (Spec (CommRingCat.of K)).Modules}
    (hM : IsLineSheaf _ M) (hN : IsLineSheaf _ N) (g : M ⟶ N) :
    (Scheme.Modules.pullback (Spec.map r)).map g = 0 ↔ g = 0 :=
  structuralPullback_line_map_eq_zero_iff (Spec.map r)
    (specField_appTop_injective r) hM hN g

end Fields

end Langlands.DeligneFormalSpace
