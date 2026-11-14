import Langlands.Geometry.FormalGroup.DeligneLatticeBaseChange
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-! # Structural pullback of Deligne's homogeneous tangent sheaves -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.DeligneFormalSpace

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace DirectSum

section SplitRanges

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}} {N M : SheafOfModules.{u} R}
  (a : N ⟶ M) (p : M ⟶ N) (h : a ≫ p = 𝟙 N)

/-- The sectionwise range of a split inclusion is an actual module subsheaf. -/
def splitRange : M.Submodule where
  toSubmodule := {
    obj U := LinearMap.range (a.val.app U).hom
    map {U V} g := by
      rintro _ ⟨x, rfl⟩
      exact ⟨N.val.map g x, PresheafOfModules.naturality_apply a.val g x⟩ }
  isSheaf {U} s hs := by
    have heq : a.val.app U (p.val.app U s) = s := by
      apply M.isSheaf.isSeparated _ _ hs
      intro V g hg
      obtain ⟨t, ht⟩ := hg
      change a.val.app (.op V) t =
        (show M.val.obj (.op V) from M.val.map g.op s) at ht
      change M.val.map g.op (a.val.app U (p.val.app U s)) = M.val.map g.op s
      have hi := congrArg (fun k : N ⟶ N => k.val.app (.op V) t) h
      change p.val.app (.op V) (a.val.app (.op V) t) = t at hi
      calc
        _ = a.val.app (.op V) (N.val.map g.op (p.val.app U s)) :=
          (PresheafOfModules.naturality_apply a.val g.op (p.val.app U s)).symm
        _ = a.val.app (.op V) (p.val.app (.op V)
            (show M.val.obj (.op V) from M.val.map g.op s)) :=
          congrArg (a.val.app (.op V))
            (PresheafOfModules.naturality_apply p.val g.op s).symm
        _ = a.val.app (.op V) (p.val.app (.op V) (a.val.app (.op V) t)) :=
          congrArg (fun z : M.val.obj (.op V) =>
            a.val.app (.op V) (p.val.app (.op V) z)) ht.symm
        _ = a.val.app (.op V) t := congrArg (a.val.app (.op V)) hi
        _ = _ := ht
    exact ⟨p.val.app U s, heq⟩

/-- The split source identifies with its actual range subsheaf. -/
def splitRangeIso : N ≅ (splitRange a p h).toSheafOfModules where
  hom := {
    val := {
      app U := ModuleCat.ofHom ((a.val.app U).hom.codRestrict _ (fun x => ⟨x, rfl⟩))
      naturality g := by
        ext x
        apply Subtype.ext
        exact PresheafOfModules.naturality_apply a.val g x } }
  inv := {
    val := {
      app U := ModuleCat.ofHom ((p.val.app U).hom.comp (LinearMap.range (a.val.app U).hom).subtype)
      naturality g := by
        ext x
        exact PresheafOfModules.naturality_apply p.val g x.val } }
  hom_inv_id := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    ext x
    exact congrArg (fun k : N ⟶ N => k.val.app U x) h
  inv_hom_id := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    ext x
    apply Subtype.ext
    obtain ⟨t, ht⟩ := x.property
    change a.val.app U (p.val.app U x.val) = x.val
    rw [← ht]
    have hi := congrArg (fun k : N ⟶ N => k.val.app U t) h
    exact congrArg (fun z => a.val.app U z) hi

@[reassoc (attr := simp)]
theorem splitRangeIso_hom_inclusion :
    (splitRangeIso a p h).hom ≫ (splitRange a p h).ι = a := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  rfl

end SplitRanges

section Projections

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  {d : ℕ} [NeZero d] {R : Sheaf J CommRingCat.{u}}
  {b : (R.obj ⋙ CategoryTheory.forget CommRingCat).sections}

namespace GradedPiSheaf

variable (M : GradedPiSheaf d R b)

/-- Canonical projection on homogeneous sections, from the actual internal sum. -/
def sectionProjection (U : Cᵒᵖ) (i : ZMod d) :
    M.module.val.obj U →ₗ[R.obj.obj U] (M.component i).toSubmodule.obj U := by
  classical
  exact (DirectSum.component (R.obj.obj U) (ZMod d)
    (fun j => (M.component j).toSubmodule.obj U) i).comp
    (LinearEquiv.ofBijective
      (DirectSum.coeLinearMap (fun j => (M.component j).toSubmodule.obj U))
      (M.isInternal U)).symm.toLinearMap

@[simp]
theorem sectionProjection_inclusion (U : Cᵒᵖ) (i : ZMod d)
    (x : (M.component i).toSubmodule.obj U) :
    M.sectionProjection U i x.val = x := by
  change (LinearEquiv.ofBijective
    (DirectSum.coeLinearMap (fun j => (M.component j).toSubmodule.obj U))
    (M.isInternal U)).symm x.val i = x
  exact (M.isInternal U).ofBijective_coeLinearMap_of_mem x.property

@[simp]
theorem sectionProjection_inclusion_ne (U : Cᵒᵖ) {i j : ZMod d} (hji : j ≠ i)
    (x : (M.component j).toSubmodule.obj U) :
    M.sectionProjection U i x.val = 0 := by
  change (LinearEquiv.ofBijective
    (DirectSum.coeLinearMap (fun j => (M.component j).toSubmodule.obj U))
    (M.isInternal U)).symm x.val i = 0
  exact (M.isInternal U).ofBijective_coeLinearMap_of_mem_ne hji x.property

/-- The homogeneous projection is a genuine structural module-sheaf map. -/
def projection (i : ZMod d) : M.module ⟶ M.componentSheaf i where
  val := {
    app U := ModuleCat.ofHom (M.sectionProjection U i)
    naturality {U V} g := by
      ext x
      obtain ⟨z, rfl⟩ := (M.isInternal U).surjective x
      induction z using DirectSum.induction_on with
      | zero => simp
      | of j w =>
          simp only [DirectSum.coeAddMonoidHom_of]
          change M.sectionProjection V i (M.module.val.map g w.val) =
            (M.componentSheaf i).val.map g (M.sectionProjection U i w.val)
          change M.sectionProjection V i
            (((M.component j).toSubmodule.toPresheafOfModules.map g w).val) = _
          by_cases hji : j = i
          · subst j
            rw [M.sectionProjection_inclusion, M.sectionProjection_inclusion]
            rfl
          · rw [M.sectionProjection_inclusion_ne V hji,
              M.sectionProjection_inclusion_ne U hji, map_zero]
      | add z w hz hw =>
          simpa only [map_add] using congrArg₂ (· + ·) hz hw }

@[simp]
theorem inclusion_projection (i : ZMod d) :
    M.componentInclusion i ≫ M.projection i = 𝟙 _ := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  exact M.sectionProjection_inclusion U i x

@[simp]
theorem inclusion_projection_ne {i j : ZMod d} (hji : j ≠ i) :
    M.componentInclusion j ≫ M.projection i = 0 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  exact M.sectionProjection_inclusion_ne U hji x

/-- A sectionwise linear map is determined on the homogeneous submodules. -/
theorem section_hom_ext (U : Cᵒᵖ) {N : ModuleCat.{u} (R.obj.obj U)}
    {a c : M.module.val.obj U →ₗ[R.obj.obj U] N}
    (h : ∀ i (x : (M.component i).toSubmodule.obj U), a x.val = c x.val) : a = c := by
  ext x
  obtain ⟨z, rfl⟩ := (M.isInternal U).surjective x
  induction z using DirectSum.induction_on with
  | zero => simp
  | of i w => simpa only [DirectSum.coeAddMonoidHom_of] using h i w
  | add z w hz hw => simp only [map_add, hz, hw]

/-- The finite homogeneous projections resolve the identity. -/
theorem sum_projection_inclusion :
    ∑ i : ZMod d, M.projection i ≫ M.componentInclusion i = 𝟙 _ := by
  classical
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply M.section_hom_ext U
  intro j x
  let E := SheafOfModules.forget (ringSheaf R) ⋙
    PresheafOfModules.evaluation (ringSheaf R).obj U
  change ((E.map
    (∑ i : ZMod d, M.projection i ≫ M.componentInclusion i)).hom x.val) = x.val
  rw [E.map_sum]
  simp only [ModuleCat.hom_sum, LinearMap.sum_apply]
  change (∑ i : ZMod d, (M.sectionProjection U i x.val).val) = x.val
  rw [Finset.sum_eq_single j]
  · rw [M.sectionProjection_inclusion]
  · intro i _ hij
    rw [M.sectionProjection_inclusion_ne U (Ne.symm hij)]
    rfl
  · simp

end GradedPiSheaf

end Projections

section StructuralScalars

variable {S S' : Scheme.{u}} (f : S' ⟶ S)

/-- Multiplication by an actual global structural scalar, on every open. -/
def structuralScalarEnd (M : S.Modules) (a : Γ(S, ⊤)) : M ⟶ M where
  val := {
    app U := ModuleCat.ofHom ((show S.presheaf.obj U from (schemeScalar S a).val U) •
      (LinearMap.id : M.val.obj U →ₗ[S.presheaf.obj U] M.val.obj U))
    naturality {U V} g := by
      ext x
      change (schemeScalar S a).val V •
        (show M.val.obj V from M.val.map g x) =
          M.val.map g ((schemeScalar S a).val U • x)
      rw [M.val.map_smul]
      exact congrArg (fun r : S.presheaf.obj V =>
        r • (show M.val.obj V from M.val.map g x)) ((schemeScalar S a).property g).symm }

@[simp]
theorem structuralScalarEnd_apply (M : S.Modules) (a : Γ(S, ⊤))
    (U : (Opens S)ᵒᵖ) (x : M.val.obj U) :
    (structuralScalarEnd M a).val.app U x = (schemeScalar S a).val U • x := rfl

/-- Structural pullback transports multiplication by the actual pulled scalar. -/
theorem pullback_structuralScalarEnd (M : S.Modules) (a : Γ(S, ⊤)) :
    (Scheme.Modules.pullback f).map (structuralScalarEnd M a) =
      structuralScalarEnd ((Scheme.Modules.pullback f).obj M) (f.appTop a) := by
  let A := Scheme.Modules.pullbackPushforwardAdjunction f
  apply (A.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit]
  have h := A.unit.naturality (structuralScalarEnd M a)
  dsimp only [Functor.comp_map] at h
  rw [← h]
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  change (A.unit.app M).val.app U ((schemeScalar S a).val U • x) =
    (schemeScalar S' (f.appTop a)).val (.op (f ⁻¹ᵁ U.unop)) •
      (show ((Scheme.Modules.pullback f).obj M).val.obj (.op (f ⁻¹ᵁ U.unop)) from
        (A.unit.app M).val.app U x)
  rw [((A.unit.app M).val.app U).hom.map_smul]
  exact congrArg (fun r : S'.presheaf.obj (.op (f ⁻¹ᵁ U.unop)) =>
    r • (show ((Scheme.Modules.pullback f).obj M).val.obj (.op (f ⁻¹ᵁ U.unop)) from
      (A.unit.app M).val.app U x))
        (structuralScalar_pushforward f (RingHom.id _) U.unop a)

end StructuralScalars

section StructuralPullback

variable {S S' : Scheme.{u}} {d : ℕ} [NeZero d] {a : Γ(S, ⊤)}

/-- Evaluation on an open respects the actual endomorphism monoid. -/
def sectionEndHom (M : S.Modules) (U : (Opens S)ᵒᵖ) :
    End M →* Module.End (S.presheaf.obj U) (M.val.obj U) where
  toFun P := (P.val.app U).hom
  map_one' := rfl
  map_mul' _ _ := rfl

namespace PiSheaf

variable (M : PiSheaf d S.sheaf (schemeScalar S a))

omit [NeZero d] in
/-- The sectionwise defining equation is an equality of genuine sheaf maps. -/
theorem pi_pow_sheaf :
    End.asHom ((End.of M.pi) ^ d) = structuralScalarEnd M.module a := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  change sectionEndHom M.module U ((End.of M.pi) ^ d) = _
  rw [map_pow]
  exact M.pi_pow U

/-- Structural pullback of the actual sheaf and its distinguished operator. -/
def pullback (f : S' ⟶ S) :
    PiSheaf d S'.sheaf (schemeScalar S' (f.appTop a)) where
  module := (Scheme.Modules.pullback f).obj M.module
  pi := (Scheme.Modules.pullback f).map M.pi
  pi_pow U := by
    let P := Scheme.Modules.pullback f
    have h : End.asHom ((End.of (P.map M.pi)) ^ d) =
        structuralScalarEnd (P.obj M.module) (f.appTop a) := by
      calc
        _ = P.map (End.asHom ((End.of M.pi) ^ d)) :=
          (map_pow (P.mapEnd M.module) (End.of M.pi) d).symm
        _ = P.map (structuralScalarEnd M.module a) :=
          congrArg P.map M.pi_pow_sheaf
        _ = _ := pullback_structuralScalarEnd f M.module a
    have hU := congrArg (sectionEndHom (P.obj M.module) U) h
    rw [map_pow] at hU
    exact hU

end PiSheaf

namespace GradedPiSheaf

variable (M : GradedPiSheaf d S.sheaf (schemeScalar S a)) (f : S' ⟶ S)

/-- Structural pullback of a homogeneous inclusion. -/
def pullbackInclusion (i : ZMod d) :
    (Scheme.Modules.pullback f).obj (M.componentSheaf i) ⟶
      (Scheme.Modules.pullback f).obj M.module :=
  (Scheme.Modules.pullback f).map (M.componentInclusion i)

/-- Structural pullback of the canonical homogeneous projection. -/
def pullbackProjection (i : ZMod d) :
    (Scheme.Modules.pullback f).obj M.module ⟶
      (Scheme.Modules.pullback f).obj (M.componentSheaf i) :=
  (Scheme.Modules.pullback f).map (M.projection i)

@[simp]
theorem pullbackInclusion_projection (i : ZMod d) :
    M.pullbackInclusion f i ≫ M.pullbackProjection f i = 𝟙 _ := by
  rw [pullbackInclusion, pullbackProjection, ← Functor.map_comp,
    M.inclusion_projection, (Scheme.Modules.pullback f).map_id]

@[simp]
theorem pullbackInclusion_projection_ne {i j : ZMod d} (hji : j ≠ i) :
    M.pullbackInclusion f j ≫ M.pullbackProjection f i = 0 := by
  rw [pullbackInclusion, pullbackProjection, ← Functor.map_comp,
    M.inclusion_projection_ne hji, Functor.map_zero]

/-- The pulled projections and inclusions still resolve the identity. -/
theorem pullback_sum_projection_inclusion :
    ∑ i : ZMod d, M.pullbackProjection f i ≫ M.pullbackInclusion f i = 𝟙 _ := by
  simp only [pullbackInclusion, pullbackProjection, ← Functor.map_comp,
    ← Functor.map_sum, M.sum_projection_inclusion, (Scheme.Modules.pullback f).map_id]

/-- The actual range subsheaf of the pulled homogeneous inclusion. -/
def pullbackComponent (i : ZMod d) :
    ((Scheme.Modules.pullback f).obj M.module).Submodule :=
  splitRange (M.pullbackInclusion f i) (M.pullbackProjection f i)
    (M.pullbackInclusion_projection f i)

/-- Structural pullback of a component identifies with its actual range. -/
def pullbackComponentIso (i : ZMod d) :
    (Scheme.Modules.pullback f).obj (M.componentSheaf i) ≅
      (M.pullbackComponent f i).toSheafOfModules :=
  splitRangeIso (M.pullbackInclusion f i) (M.pullbackProjection f i)
    (M.pullbackInclusion_projection f i)

/-- The pulled homogeneous ranges form the actual internal sum on every open. -/
theorem pullback_isInternal (U : (Opens S')ᵒᵖ) :
    DirectSum.IsInternal (fun i => (M.pullbackComponent f i).toSubmodule.obj U) := by
  classical
  apply isInternal_of_finite_splitting (O := S'.presheaf.obj U)
    (fun i => ((M.pullbackInclusion f i).val.app U).hom)
    (fun i => ((M.pullbackProjection f i).val.app U).hom)
  · intro i x
    exact congrArg (fun g => g.val.app U x) (M.pullbackInclusion_projection f i)
  · intro i j hji x
    exact congrArg (fun g => g.val.app U x) (M.pullbackInclusion_projection_ne f hji)
  · intro x
    let E := SheafOfModules.forget S'.ringCatSheaf ⋙
      PresheafOfModules.evaluation S'.ringCatSheaf.obj U
    have h := congrArg (fun g => (E.map g).hom x)
      (M.pullback_sum_projection_inclusion f)
    rw [E.map_sum, E.map_id] at h
    simp only [ModuleCat.hom_sum, LinearMap.sum_apply, Functor.map_comp,
      ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id,
      LinearMap.id_apply] at h
    exact h

/-- Structural pullback preserves the cyclic grading and its degree-one operator. -/
def pullback : GradedPiSheaf d S'.sheaf (schemeScalar S' (f.appTop a)) where
  toPiSheaf := M.toPiSheaf.pullback f
  component := M.pullbackComponent f
  isInternal := M.pullback_isInternal f
  pi_mem U i x hx := by
    obtain ⟨t, rfl⟩ := hx
    refine ⟨((Scheme.Modules.pullback f).map (M.componentPi i)).val.app U t, ?_⟩
    have h := congrArg ((Scheme.Modules.pullback f).map) (M.componentPi_inclusion i)
    rw [Functor.map_comp, Functor.map_comp] at h
    exact congrArg (fun g => g.val.app U t) h

end GradedPiSheaf

end StructuralPullback

section Lines

variable {S S' : Scheme.{u}} (f : S' ⟶ S)

/-- Actual structural pullback sends the structure module to the structure module. -/
def structuralPullbackUnitIso :
    (Scheme.Modules.pullback f).obj (SheafOfModules.unit S.ringCatSheaf) ≅
      SheafOfModules.unit S'.ringCatSheaf := by
  letI : (Opens.map f.base).Final := inferInstance
  let e := asIso (SheafOfModules.pullbackObjUnitToUnit
    (F := Opens.map f.base) f.toRingCatSheafHom)
  exact e

/-- Restricting a structural pullback agrees with pulling back the restriction
along the actual restricted scheme morphism. -/
def structuralPullbackRestrictIso (M : S.Modules) (U : S.Opens) :
    ((Scheme.Modules.pullback f).obj M).restrict (f ⁻¹ᵁ U).ι ≅
      (Scheme.Modules.pullback (f ∣_ U)).obj (M.restrict U.ι) :=
  (Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι).app _ ≪≫
    (Scheme.Modules.pullbackComp (f ⁻¹ᵁ U).ι f).app M ≪≫
    (Scheme.Modules.pullbackCongr (morphismRestrict_ι f U).symm).app M ≪≫
    ((Scheme.Modules.pullbackComp (f ∣_ U) U.ι).app M).symm ≪≫
    (Scheme.Modules.pullback (f ∣_ U)).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app M).symm

namespace IsLineSheaf

variable {M : S.Modules}

/-- Pull back an actual local trivialization on the inverse-image open. -/
theorem pullback (h : IsLineSheaf S M) :
    IsLineSheaf S' ((Scheme.Modules.pullback f).obj M) := by
  intro x
  obtain ⟨U, hx, ⟨e⟩⟩ := h (f x)
  exact ⟨f ⁻¹ᵁ U, hx, ⟨structuralPullbackRestrictIso f M U ≪≫
    (Scheme.Modules.pullback (f ∣_ U)).mapIso e ≪≫
    structuralPullbackUnitIso (f ∣_ U)⟩⟩

end IsLineSheaf

namespace LinePiSheaf

variable {d : ℕ} [NeZero d] {a : Γ(S, ⊤)}

/-- Structural pullback of Deligne's actual tangent-sheaf data. -/
def pullback (M : LinePiSheaf d S a) : LinePiSheaf d S' (f.appTop a) where
  graded := M.graded.pullback f
  line i := IsLineSheaf.of_iso (M.graded.pullbackComponentIso f i)
    (IsLineSheaf.pullback f (M.line i))

end LinePiSheaf

end Lines

end Langlands.DeligneFormalSpace
