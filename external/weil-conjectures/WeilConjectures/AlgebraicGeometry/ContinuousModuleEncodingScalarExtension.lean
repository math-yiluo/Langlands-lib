/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientModuleEncoding
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed

/-! # Scalar extension under continuous module encodings

Source: Stacks Project, Modules on Sites, Tags 03D7, 03EK, 03EL.
(auxiliary; not a blueprint node)
-/

@[expose] public section

universe u v w
open CategoryTheory
open scoped CategoryTheory.Obj CategoryTheory.Functor ChangeOfRings

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace SheafOfModules

section
variable {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
  {A B : Sheaf J CommRingCat.{u}} (α : A ⟶ B)

local instance scalarExtensionRestrictedModule {U V : Cᵒᵖ} (i : U ⟶ V)
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)) :
    Module (A.obj.obj V)
      ((ModuleCat.restrictScalars
        (((sheafCompose J (forget₂ CommRingCat RingCat)).obj A).obj.map i).hom).obj
          (M.val.obj V)) :=
  inferInstanceAs (Module (A.obj.obj V) (M.val.obj V))

private theorem scalarExtensionMap_tmul {U V : Cᵒᵖ} (i : U ⟶ V)
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A))
    (s : B.obj.obj U) (m : M.val.obj U) :
    changeOfRingsMap α M i (s ⊗ₜ[A.obj.obj U, (α.hom.app U).hom] m) =
      B.obj.map i s ⊗ₜ[A.obj.obj V, (α.hom.app V).hom] M.val.map i m :=
  Classical.choose_spec (exists_changeOfRingsMap α M i) s m

private noncomputable def tensorToRestrict
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A))
    (N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B))
    (f : changeOfRingsPresheaf α M ⟶ N.val) :
    M ⟶ (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map α)).obj N where
  val :=
    { app := fun U ↦ ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.toRestrictScalars
        (α.hom.app U).hom (f.app U)
      naturality := by
        intro U V i
        ext m
        change f.app V ((1 : B.obj.obj V) ⊗ₜ[A.obj.obj V, (α.hom.app V).hom]
            M.val.map i m) =
          N.val.map i (f.app U ((1 : B.obj.obj U) ⊗ₜ[A.obj.obj U, (α.hom.app U).hom] m))
        have h := PresheafOfModules.naturality_apply f i
          ((1 : B.obj.obj U) ⊗ₜ[A.obj.obj U, (α.hom.app U).hom] m)
        change f.app V (changeOfRingsMap α M i _) = N.val.map i (f.app U _) at h
        rw [scalarExtensionMap_tmul, map_one] at h
        exact h }

private noncomputable def tensorFromRestrict
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A))
    (N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B))
    (g : M ⟶ (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map α)).obj N) :
    changeOfRingsPresheaf α M ⟶ N.val where
  app U := ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
    («R» := A.obj.obj U) («S» := B.obj.obj U) (α.hom.app U).hom (g.val.app U)
  naturality := by
    intro U V i
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    change ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
      («R» := A.obj.obj V) («S» := B.obj.obj V) (α.hom.app V).hom (g.val.app V)
        (changeOfRingsMap α M i _) =
      N.val.map i (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
        («R» := A.obj.obj U) («S» := B.obj.obj U) (α.hom.app U).hom (g.val.app U) _)
    rw [scalarExtensionMap_tmul]
    simp only [map_one]
    let : Module (A.obj.obj V) (B.obj.obj V) :=
      Module.compHom (B.obj.obj V) (α.hom.app V).hom
    let : Module (A.obj.obj V) (N.val.obj V) :=
      Module.compHom (N.val.obj V) (α.hom.app V).hom
    let : Module (A.obj.obj U) (B.obj.obj U) :=
      Module.compHom (B.obj.obj U) (α.hom.app U).hom
    let : Module (A.obj.obj U) (N.val.obj U) :=
      Module.compHom (N.val.obj U) (α.hom.app U).hom
    erw [ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_hom_apply
      («R» := A.obj.obj V) («S» := B.obj.obj V), TensorProduct.lift.tmul,
      ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_hom_apply
      («R» := A.obj.obj U) («S» := B.obj.obj U), TensorProduct.lift.tmul]
    change (1 : B.obj.obj V) • (show N.val.obj V from g.val.app V (M.val.map i m)) =
      N.val.map i ((1 : B.obj.obj U) • (show N.val.obj U from g.val.app U m))
    simp only [one_smul]
    exact PresheafOfModules.naturality_apply g.val i m

private noncomputable def scalarExtensionTensorHomEquiv
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A))
    (N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)) :
    (changeOfRings α M ⟶ N) ≃
      (M ⟶ (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map α)).obj N) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 _)).trans
    { toFun := tensorToRestrict α M N
      invFun := tensorFromRestrict α M N
      left_inv := by
        intro f
        ext U x
        exact ConcreteCategory.congr_hom
          ((ModuleCat.ExtendRestrictScalarsAdj.homEquiv
            (α.hom.app U).hom).symm_apply_apply (f.app U)) x
      right_inv := by
        intro g
        ext U x
        exact ConcreteCategory.congr_hom
          ((ModuleCat.ExtendRestrictScalarsAdj.homEquiv
            (α.hom.app U).hom).apply_symm_apply (g.val.app U)) x }

/-- The sheafified sectionwise tensor product is left adjoint to scalar restriction
on any small ringed site. Source: Stacks Project, Modules on Sites, Tag 03D7.
(auxiliary; not a blueprint node)

Proof. The module tensor universal property gives a natural bijection of presheaf
maps with scalar-restricted maps. The sheafification adjunction then gives the
same bijection for sheaf maps. Its naturality constructs the adjunction. -/
theorem exists_siteChangeOfRingsAdjunction :
    ∃ (F : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A) ⥤
        SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)),
      (∀ M, F.obj M = changeOfRings α M) ∧
      Nonempty (F ⊣ restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map α)) := by
  let e := scalarExtensionTensorHomEquiv α
  have he : ∀ M N N' (g : N ⟶ N') (f : changeOfRings α M ⟶ N),
      e M N' (f ≫ g) = e M N f ≫
        (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map α)).map g := by
    intro M N N' g f
    ext U m
    change (PresheafOfModules.sheafificationHomEquiv (𝟙 _)
        (f ≫ g)).app U ((1 : B.obj.obj U) ⊗ₜ[A.obj.obj U, (α.hom.app U).hom] m) =
      g.val.app U ((PresheafOfModules.sheafificationHomEquiv (𝟙 _)
        f).app U ((1 : B.obj.obj U) ⊗ₜ[A.obj.obj U, (α.hom.app U).hom] m))
    have h := (PresheafOfModules.sheafificationAdjunction
      (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B).obj)).homEquiv_naturality_right
        (X := changeOfRingsPresheaf α M) f g
    exact ConcreteCategory.congr_hom (congrArg (fun k ↦ k.app U) h) _
  exact ⟨Adjunction.leftAdjointOfEquiv e he, fun _ ↦ rfl,
    ⟨Adjunction.adjunctionOfEquivLeft e he⟩⟩

end
end SheafOfModules

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Restriction of scalars commutes with the integral and rational continuous encodings.
Source: Stacks Project, Modules on Sites, Tag 03D7.
(auxiliary; not a blueprint node)

Proof. Apply continuousRing_comap_compatibility to the valuation-ring inclusion,
then transport the coefficient square using lisseScalar_square. The latter
transport is identity on underlying module sections. -/
theorem continuousLisse_comap_compatibility
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] (X : Scheme.{u}) :
    Nonempty (Mod.comap (coefficientMap (integralScalarMap ℓ E) X) ⋙
        (continuousIntegerModuleEquivalence ℓ E X).functor ≅
      (continuousFieldModuleEquivalence ℓ E X).functor ⋙
        SheafOfModules.restrictScalars ((sheafCompose (Scheme.ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
            (lisseIntegerToField ℓ E X))) := by
  let : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[ℓ]
  let : TotallySeparatedSpace E :=
    totallySeparatedSpace_iff_exists_isClopen.mpr fun x y h ↦ by
      obtain ⟨r, hr, hr'⟩ := exists_between (dist_pos.mpr h)
      refine ⟨_, IsUltrametricDist.isClopen_ball x r, ?_, ?_⟩
      · simp only [Metric.mem_ball, dist_self, hr]
      · simp only [Set.mem_compl, Metric.mem_ball, dist_comm, not_lt, hr'.le]
  let J := Scheme.ProEt.topology X
  let eI := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso
    (eqToIso (lisseIntegerSheaf_eq ℓ E X))
  let eE := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso
    (eqToIso (lisseFieldSheaf_eq ℓ E X))
  let β := continuousMapRingSheafMap X (continuousIntegers ℓ E).subtype continuous_subtype_val
  let ψ := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
    (lisseIntegerToField ℓ E X)
  have hs : ψ ≫ eE.hom = eI.hom ≫ β := by
    exact congrArg ((sheafCompose J
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map) (lisseScalar_square ℓ E X)
  let q : SheafOfModules.restrictScalars β ⋙
      (ringModuleEquivalenceOfIso X eI).functor ≅
      (ringModuleEquivalenceOfIso X eE).functor ⋙ SheafOfModules.restrictScalars ψ := by
    refine NatIso.ofComponents (fun M ↦ ?_) ?_
    · apply (SheafOfModules.fullyFaithfulForget _).preimageIso
      refine PresheafOfModules.isoMk (fun Z ↦ ?_) ?_
      · refine ModuleCat.isoMk (Iso.refl _) ?_
        intro r
        ext m
        change (eE.hom.hom.app Z (ψ.hom.app Z r)) • (show M.val.obj Z from m) =
          (β.hom.app Z (eI.hom.hom.app Z r)) • (show M.val.obj Z from m)
        exact congrArg (fun a : (continuousMapRingSheaf X E).obj.obj Z ↦
          a • (show M.val.obj Z from m))
          (ConcreteCategory.congr_hom (congr_app (congrArg (fun f ↦ f.hom) hs) Z) r)
      · intro Z W f
        ext
        rfl
    · intro M N f
      ext Z m
      rfl
  obtain ⟨h⟩ := continuousRing_comap_compatibility X (continuousIntegers ℓ E) E
    (continuousIntegers ℓ E).subtype continuous_subtype_val
  exact ⟨Functor.isoWhiskerRight h (ringModuleEquivalenceOfIso X eI).functor ≪≫
    Functor.isoWhiskerLeft (continuousRingModuleEquivalence X E).functor q⟩

/-- Encoding the scalar extension of an inverse integral encoding recovers the
sectionwise sheafified tensor product. Source: Stacks Project, Tag 03D7.
(auxiliary; not a blueprint node)

Proof. Compose the extension-restriction adjunction with the two encoding
equivalences. The preceding scalar-restriction comparison identifies its right
adjoint with sectionwise scalar restriction. The tensor-sheafification
adjunction above has the same right adjoint. Uniqueness of left adjoints gives
the isomorphism on the specified object M. -/
theorem continuousModuleEncoding_scalar_extension
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] (X : Scheme.{u})
    (M : ringedSiteModules.{u + 1} ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (lisseIntegerSheaf ℓ E X))) :
    Nonempty ((continuousFieldModuleEquivalence ℓ E X).functor.obj
        ((Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X)).obj
          ((continuousIntegerModuleEquivalence ℓ E X).inverse.obj M)) ≅
      SheafOfModules.changeOfRings.{u, u + 1, u + 1} (lisseIntegerToField ℓ E X) M) := by
  let FI := continuousIntegerModuleEquivalence ℓ E X
  let FE := continuousFieldModuleEquivalence ℓ E X
  let α := coefficientMap (integralScalarMap ℓ E) X
  let β := (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (lisseIntegerToField ℓ E X)
  obtain ⟨T, hT, ⟨aT⟩⟩ :=
    SheafOfModules.exists_siteChangeOfRingsAdjunction (lisseIntegerToField ℓ E X)
  obtain ⟨ec⟩ := continuousLisse_comap_compatibility ℓ E X
  let a := (FI.symm.toAdjunction.comp (Mod.extendRestrictAdjunction α)).comp FE.toAdjunction
  let er : FE.inverse ⋙ Mod.comap α ⋙ FI.functor ≅
      SheafOfModules.restrictScalars β :=
    Functor.isoWhiskerLeft FE.inverse ec ≪≫
      Functor.isoWhiskerRight FE.counitIso (SheafOfModules.restrictScalars β) ≪≫
        Functor.leftUnitor _
  exact ⟨((a.ofNatIsoRight er).leftAdjointUniq aT).app M ≪≫ eqToIso (hT M)⟩

end AlgebraicGeometry.ProEtale.CondensedRing
