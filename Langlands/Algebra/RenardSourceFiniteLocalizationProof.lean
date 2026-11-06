import Langlands.Algebra.RenardSourceFiniteLocalizationStatements
import Langlands.Algebra.NonUnitalModuleFinitenessProof
import Langlands.Algebra.RenardAdditiveScalarFiniteLocalization
import Langlands.Algebra.RenardStableIdealFiniteLocalizationProof
import Langlands.Algebra.UnitizationIdealNoetherianProof
import Langlands.Algebra.CompatibleUnitizationSubmodule
import Langlands.CategoryTheory.Renard.FiniteTypeFiniteSubcover
import Mathlib.Algebra.Category.ModuleCat.Subobject

/-!
# Renard C.II under each candidate finiteness reading: proof

The categorical subobjects of an object of `ActionModuleCat k B` are its stable
`k`-subspaces. Through the published unitized comparison they are the subobjects of the
corresponding module over `Unitization k B`, so Renard's finite-type and Noetherian
predicates become ordinary finite generation and Noetherianity. The three readings then
reduce to published finite-localization theorems.
-/

set_option autoImplicit false

open CategoryTheory

namespace Langlands.Renard.SourceFiniteLocalization

open Langlands.Algebra EndomorphismLocalization
open Langlands.LinearAlgebra.StableEndomorphism
open Langlands.Renard.AlgebraActionLocalization

section ActionSubobject

universe u v w

variable {k : Type u} [CommRing k] {B : Type v} [NonUnitalRing B] [Module k B]

/-- The object of a stable subspace, with the restricted action. -/
abbrev subObject (M : ActionModuleCat.{u, v, w} k B) (S : CompatibleSubmodule M.action) :
    ActionModuleCat.{u, v, w} k B :=
  ActionModuleCat.of S.toSubmodule S.restrictAction

/-- The inclusion of a stable subspace. -/
abbrev subArrow (M : ActionModuleCat.{u, v, w} k B) (S : CompatibleSubmodule M.action) :
    subObject M S ⟶ M :=
  ActionModuleCat.ofHom S.subtypeIntertwiner

instance subArrow_mono (M : ActionModuleCat.{u, v, w} k B) (S : CompatibleSubmodule M.action) :
    Mono (subArrow M S) :=
  ⟨fun g h e => by
    ext z
    exact congrArg (fun φ => φ.hom z) e⟩

/-- A monomorphism has injective underlying map: test it against the kernel inclusion
and the zero map out of the kernel object. -/
theorem injective_of_mono {N M : ActionModuleCat.{u, v, w} k B} (f : N ⟶ M) [Mono f] :
    Function.Injective f.hom := by
  let K : CompatibleSubmodule N.action := f.hom.ker
  let z : subObject N K ⟶ N := ActionModuleCat.ofHom
    { toLinearMap := 0
      map_action' := fun b x => by simp }
  have h : subArrow N K ≫ f = z ≫ f := by
    ext x
    change f.hom (x : N) = f.hom 0
    rw [map_zero]
    exact (LinearIntertwiner.mem_ker f.hom).1 x.2
  have h2 : subArrow N K = z := (cancel_mono f).1 h
  refine (injective_iff_map_eq_zero f.hom).2 fun x hx => ?_
  have hx' : x ∈ K := (LinearIntertwiner.mem_ker f.hom).2 hx
  exact congrArg (fun φ : subObject N K ⟶ N => φ.hom ⟨x, hx'⟩) h2

/-- A bijective morphism is an isomorphism, with the inverse linear equivalence. -/
noncomputable def isoOfBijective {N M : ActionModuleCat.{u, v, w} k B} (f : N ⟶ M)
    (hf : Function.Bijective f.hom) : N ≅ M where
  hom := f
  inv := ActionModuleCat.ofHom
    { toLinearMap := (LinearEquiv.ofBijective f.hom.toLinearMap hf).symm.toLinearMap
      map_action' := fun b y => by
        apply hf.1
        change f.hom ((LinearEquiv.ofBijective f.hom.toLinearMap hf).symm (M.action b y)) =
          f.hom (N.action b ((LinearEquiv.ofBijective f.hom.toLinearMap hf).symm y))
        rw [LinearIntertwiner.map_action]
        have e1 := (LinearEquiv.ofBijective f.hom.toLinearMap hf).apply_symm_apply (M.action b y)
        have e2 := (LinearEquiv.ofBijective f.hom.toLinearMap hf).apply_symm_apply y
        simp only [LinearEquiv.ofBijective_apply, LinearIntertwiner.coe_toLinearMap] at e1 e2
        rw [e1, e2] }
  hom_inv_id := by
    ext x
    exact (LinearEquiv.ofBijective f.hom.toLinearMap hf).symm_apply_apply x
  inv_hom_id := by
    ext y
    exact (LinearEquiv.ofBijective f.hom.toLinearMap hf).apply_symm_apply y

/-- Categorical subobjects of an object of `ActionModuleCat k B` are exactly its stable
`k`-subspaces, ordered by inclusion. -/
noncomputable def subobjectOrderIso (M : ActionModuleCat.{u, v, w} k B) :
    Subobject M ≃o CompatibleSubmodule M.action :=
  OrderIso.symm
    { toFun := fun S => Subobject.mk (subArrow M S)
      invFun := fun P => P.arrow.hom.range
      left_inv := fun S => by
        let e := Subobject.underlyingIso (subArrow M S)
        have harrow : (Subobject.mk (subArrow M S)).arrow = e.hom ≫ subArrow M S :=
          (Subobject.underlyingIso_hom_comp_eq_mk (subArrow M S)).symm
        ext m
        rw [LinearIntertwiner.mem_range, harrow]
        constructor
        · rintro ⟨x, rfl⟩
          exact (e.hom.hom x).2
        · intro hm
          refine ⟨e.inv.hom ⟨m, hm⟩, ?_⟩
          have hinv := congrArg (fun φ : subObject M S ⟶ subObject M S => φ.hom ⟨m, hm⟩)
            e.inv_hom_id
          exact congrArg Subtype.val hinv
      right_inv := fun P => by
        symm
        have hinj := injective_of_mono P.arrow
        refine Subobject.eq_mk_of_comm (subArrow M P.arrow.hom.range)
          (isoOfBijective (N := (P : ActionModuleCat.{u, v, w} k B))
            (M := subObject M P.arrow.hom.range)
            (ActionModuleCat.ofHom P.arrow.hom.rangeRestrict) ⟨?_, ?_⟩) ?_
        · intro x y hxy
          exact hinj (congrArg Subtype.val hxy)
        · rintro ⟨m, hm⟩
          obtain ⟨x, rfl⟩ := (LinearIntertwiner.mem_range P.arrow.hom).1 hm
          exact ⟨x, rfl⟩
        · ext x
          rfl
      map_rel_iff' := fun {S T} => by
        constructor
        · intro h m hm
          have hc := congrArg (fun φ : subObject M S ⟶ M => φ.hom ⟨m, hm⟩)
            (Subobject.ofMkLEMk_comp h)
          change ((Subobject.ofMkLEMk (subArrow M S) (subArrow M T) h).hom ⟨m, hm⟩ : M) = m
            at hc
          rw [← hc]
          exact ((Subobject.ofMkLEMk (subArrow M S) (subArrow M T) h).hom ⟨m, hm⟩).2
        · intro h
          exact Subobject.mk_le_mk_of_comm
            (ActionModuleCat.ofHom (S.subtypeIntertwiner.codRestrict T fun x => h x.2))
            (by ext x; rfl) }

variable [IsScalarTower k B B] [SMulCommClass k B B]

/-- The subobjects of `M` are those of the actual module over `Unitization k B` on the same
carrier, acting by `(c, b) • m = c • m + M.action b m`. -/
noncomputable def unitizedSubobjectOrderIso (M : ActionModuleCat.{u, v, w} k B) :
    Subobject M ≃o
      Subobject (letI := CompatibleUnitization.module M.action
        ModuleCat.of (Unitization k B) M) :=
  letI := CompatibleUnitization.module M.action
  ((subobjectOrderIso M).trans (CompatibleUnitization.submoduleOrderIso M.action)).trans
    (ModuleCat.subobjectModule (ModuleCat.of (Unitization k B) M)).symm

/-- Renard's finite type in `ActionModuleCat k B` is finite generation over the unitization. -/
theorem finiteType_iff_finite (M : ActionModuleCat.{u, v, w} k B) :
    IsFiniteTypeObject M ↔
      (letI := CompatibleUnitization.module M.action
       Module.Finite (Unitization k B) M) :=
  letI := CompatibleUnitization.module M.action
  (finiteTypeFiniteSubcover (ActionModuleCat.{u, v, w} k B) M).trans
    ((NonUnitalModuleFiniteness.hasFiniteSubcoverProperty_congr
      (unitizedSubobjectOrderIso M)).trans
      (ModuleFiniteType.finiteSubcover_iff_finite (ModuleCat.of (Unitization k B) M)))

/-- Renard's Noetherian object in `ActionModuleCat k B` is a Noetherian unitized module. -/
theorem noetherianObject_iff_isNoetherian (M : ActionModuleCat.{u, v, w} k B) :
    IsNoetherianObject M ↔
      (letI := CompatibleUnitization.module M.action
       IsNoetherian (Unitization k B) M) :=
  letI := CompatibleUnitization.module M.action
  (NonUnitalModuleFiniteness.isNoetherianObject_congr (unitizedSubobjectOrderIso M)).trans
    (ModuleNoetherian.object_iff (Unitization k B) (ModuleCat.of (Unitization k B) M))

end ActionSubobject

universe uB uV

section Readings

variable {B : Type uB} [NonUnitalRing B] [Module ℂ B]
  [IsScalarTower ℂ B B] [SMulCommClass ℂ B B]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The actual stabilization conclusion gives the source conclusions. -/
theorem sourceConclusion_of_stabilization (ρ : B →ₙₐ[ℂ] Module.End ℂ V)
    (f : LinearIntertwiner ρ ρ) (h : CompatibleLocalizationStabilizationAt ρ f) :
    SourceConclusion ρ f := by
  obtain ⟨-, n, hn, -, hs⟩ := h
  exact ⟨⟨n, hn, hs⟩, fun m hm hs' =>
    CompatibleStableImageProof.compatibleStablePowerImageAt_of_stable ρ f m hm hs'⟩

end Readings

/-- The additive reading, through the published original-action finiteness comparisons
and the additive-ideal finite-localization theorem. -/
theorem additiveReading : AdditiveReadingStatement.{uB, uV} := by
  intro B _ _ _ _ V _ _ ρ f hB hV hL
  let _ : NonUnitalModule B B := NonUnitalModule.ofLinearEndHom (NonUnitalAlgHom.lmul ℂ B)
  let _ : NonUnitalModule B V := NonUnitalModule.ofLinearEndHom ρ
  let _ : NonUnitalModule B (Localized f.toLinearMap) := NonUnitalModule.ofLinearEndHom
    (localizedAction f.toLinearMap ρ (fun b v => f.map_action' b v))
  refine sourceConclusion_of_stabilization ρ f
    (additiveIdealFiniteLocalization B V ρ f ?_ ?_ ?_).1
  · intro P hP
    have hgen := (NonUnitalModuleFiniteness.noetherianObject_iff_original_stable_generators
      _).1 hB
    obtain ⟨S, hSP, hS⟩ := hgen ⟨P, fun b x hx => hP b x hx⟩
    exact ⟨S, hSP, fun Q hQ hSQ => hS ⟨Q, fun b x hx => hQ b x hx⟩ hSQ⟩
  · obtain ⟨S, hS⟩ :=
      (NonUnitalModuleFiniteness.finiteType_iff_original_stable_generators _).1 hV
    refine ⟨S, fun P hP hSP => ?_⟩
    rw [eq_top_iff]
    intro m _
    exact hS ⟨P, fun b x hx => hP b x hx⟩ hSP m
  · obtain ⟨S, hS⟩ :=
      (NonUnitalModuleFiniteness.finiteType_iff_original_stable_generators _).1 hL
    refine ⟨S, fun P hP hSP => ?_⟩
    rw [eq_top_iff]
    intro m _
    exact hS ⟨P, fun b x hx => hP b x hx⟩ hSP m

/-- The compatible reading, through the categorical subobject comparison above and the
regular Noetherian unitization criterion. -/
theorem compatibleReading : CompatibleReadingStatement.{uB, uV} := by
  intro B _ _ _ _ V _ _ ρ f hB hV hL
  let σ := localizedAction f.toLinearMap ρ fun b v => f.map_action' b v
  let _ := CompatibleUnitization.module (NonUnitalAlgHom.lmul ℂ B)
  have hreg : IsNoetherian (Unitization ℂ B) B := (noetherianObject_iff_isNoetherian _).1 hB
  have hR : IsNoetherianRing (Unitization ℂ B) :=
    (UnitizationIdealNoetherian.noetherian_iff_scalar_and_regular ℂ B
      (CompatibleUnitization.smul_eq (NonUnitalAlgHom.lmul ℂ B))).2 ⟨inferInstance, hreg⟩
  exact sourceConclusion_of_stabilization ρ f
    (stabilizationAt_of_finite ρ f hR ((finiteType_iff_finite _).1 hV)
      ((finiteType_iff_finite _).1 hL))

/-- The unitization reading is the published finite stabilization adapter. -/
theorem unitizationReading : UnitizationReadingStatement.{uB, uV} := by
  intro B _ _ _ _ V _ _ ρ f hR hV hL
  exact sourceConclusion_of_stabilization ρ f (stabilizationAt_of_finite ρ f hR hV hL)

/-- The final C.II proposition under all three readings. -/
theorem sourceFiniteLocalizationStatements :
    SourceFiniteLocalizationStatements.{uB, uV} :=
  ⟨additiveReading, compatibleReading, unitizationReading⟩

end Langlands.Renard.SourceFiniteLocalization
