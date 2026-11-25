/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.LocalSystems

/-!
# Transport of stalks of finite locally constant sheaves along paths

Let `s, s'` be geometric points of a scheme `Y` and `τ : F_s ≅ F_{s'}` an isomorphism of the fibre
functors on finite étale `Y`-schemes (a path from `s` to `s'`). Identifying the stalk of a finite
locally constant sheaf of sets with the geometric fibre of the finite étale `Y`-scheme representing
it (`AlgebraicGeometry.Scheme.FiniteLocallyConstant.stalkEquiv`), `τ` transports stalks at `s` to
stalks at `s'` (`AlgebraicGeometry.Scheme.FiniteLocallyConstant.transport`), naturally in the
sheaf. For finite locally constant sheaves of modules over a finite ring the transport, defined
through the underlying sheaf of sets
(`AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.stalkEquiv`), is linear
(`AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.transportLinearEquiv`), since it is
natural with respect to the addition `F ⊞ F ⟶ F` and the scalar multiplications.

We also compute these identifications on germs: the stalk of the sheaf `Hom_Y(-, P)` represented
by a finite étale `Y`-scheme `P` is identified with the geometric fibre `P_s`
(`AlgebraicGeometry.Scheme.FiniteEtale.toFiniteLocallyConstantCompSheafFiberIso`) by sending the
germ at `v` of a section `f : V ⟶ P` to `f(v)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

section Germs

variable {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y)

open GrothendieckTopology.Point in
/-- The identification of the stalk of the sheaf `Hom_Y(-, P)` represented by a finite étale
`Y`-scheme `P` with the geometric fibre `P_s` sends the germ at `v` of a section `f : V ⟶ P` to
`f(v)`. -/
lemma FiniteEtale.toSheafCompSheafFiberIso_hom_app_toPresheafFiber (P : Y.FiniteEtale)
    (V : Y.Etale) (v : (pointSmallEtale s).fiber.obj V) (f : V ⟶ P.obj) :
    (toSheafCompSheafFiberIso s).hom.app P
        ((pointSmallEtale s).toPresheafFiber V v ((toSheaf Y).obj P).obj f) =
      (pointSmallEtale s).fiber.map f v := by
  have h := presheafFiber_map_shrinkYoneda_map_shrinkYonedaCompPresheafFiberIso_inv_app
    (pointSmallEtale s) f v
  have h' := ConcreteCategory.congr_hom
    ((pointSmallEtale s).shrinkYonedaCompPresheafFiberIso.hom.naturality f)
    ((pointSmallEtale s).shrinkYonedaCompPresheafFiberIso.inv.app V v)
  simp only [toSheafCompSheafFiberIso, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, ConcreteCategory.comp_apply, ObjectProperty.ι_obj]
  erw [GrothendieckTopology.Point.toPresheafFiber_naturality_apply,
    GrothendieckTopology.Point.toPresheafFiber_naturality_apply]
  simp only [Functor.comp_map, ConcreteCategory.comp_apply, Iso.inv_hom_id_app_apply] at h'
  exact (congrArg (ConcreteCategory.hom
    ((pointSmallEtale s).shrinkYonedaCompPresheafFiberIso.hom.app P.obj)) h.symm).trans h'

/-- The identification of the stalk of the sheaf `Hom_Y(-, P)` (with values in `Type (u + 1)`)
represented by a finite étale `Y`-scheme `P` with the geometric fibre `P_s` sends the germ at `v`
of a section `f : V ⟶ P` to `f(v)`. -/
lemma FiniteEtale.toFiniteLocallyConstantCompSheafFiberIso_hom_app_toPresheafFiber
    (P : Y.FiniteEtale) (V : Y.Etale) (v : (pointSmallEtale s).fiber.obj V) (f : V ⟶ P.obj) :
    (toFiniteLocallyConstantCompSheafFiberIso s).hom.app P
        ((pointSmallEtale s).toPresheafFiber V v
          ((toFiniteLocallyConstant Y).obj P).obj.obj (ULift.up f)) =
      ULift.up ((pointSmallEtale s).fiber.map f v) := by
  have : PreservesFilteredColimitsOfSize.{u, u} uliftFunctor.{u + 1, u} := inferInstance
  have h := ConcreteCategory.congr_hom
    ((pointSmallEtale s).toPresheafFiber_presheafFiberCompIso_hom_app uliftFunctor.{u + 1} V v
      ((toSheaf Y).obj P).obj) (ULift.up f : ULift.{u + 1} (V ⟶ P.obj))
  rw [ConcreteCategory.comp_apply] at h
  simp only [toFiniteLocallyConstantCompSheafFiberIso, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, ConcreteCategory.comp_apply]
  change uliftFunctor.map _
    ((((pointSmallEtale s).presheafFiberCompIso uliftFunctor.{u + 1}).hom.app
      ((toSheaf Y).obj P).obj) _) = _
  erw [h]
  exact congrArg ULift.up (toSheafCompSheafFiberIso_hom_app_toPresheafFiber s P V v f)

/-- The identification of the stalk of a finite locally constant sheaf of sets `S` with the
geometric fibre of its representing finite étale `Y`-scheme, on germs. -/
lemma FiniteLocallyConstant.stalkEquiv_toPresheafFiber (S : Y.FiniteLocallyConstant) (V : Y.Etale)
    (v : (pointSmallEtale s).fiber.obj V) (z : S.obj.obj.obj (op V)) :
    stalkEquiv s S ((pointSmallEtale s).toPresheafFiber V v S.obj.obj z) =
      ULift.up ((pointSmallEtale s).fiber.map
        (((FiniteEtale.equivalenceFiniteLocallyConstant Y).counitIso.inv.app S).hom.hom.app
          (op V) z).down v) := by
  change (FiniteEtale.toFiniteLocallyConstantCompSheafFiberIso s).hom.app _
    ((pointSmallEtale s).presheafFiber.map
      ((FiniteEtale.equivalenceFiniteLocallyConstant Y).counitIso.inv.app S).hom.hom
      ((pointSmallEtale s).toPresheafFiber V v S.obj.obj z)) = _
  erw [GrothendieckTopology.Point.toPresheafFiber_naturality_apply]
  exact FiniteEtale.toFiniteLocallyConstantCompSheafFiberIso_hom_app_toPresheafFiber s _ V v _

/-- The identification of the stalk of a finite locally constant sheaf of `Λ`-modules with that of
its underlying sheaf of sets, on germs. -/
lemma IsFiniteLocallyConstantSheaf.stalkEquiv_toPresheafFiber {Λ : Type (u + 1)} [CommRing Λ]
    [Finite Λ] {F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (hF : IsFiniteLocallyConstantSheaf F) (V : Y.Etale) (v : (pointSmallEtale s).fiber.obj V)
    (z : F.obj.obj (op V)) :
    hF.stalkEquiv s ((pointSmallEtale s).toPresheafFiber V v F.obj z) =
      (pointSmallEtale s).toPresheafFiber V v hF.toFLC.obj.obj z := by
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  have h := ConcreteCategory.congr_hom
    ((pointSmallEtale s).toPresheafFiber_presheafFiberCompIso_hom_app V v F.obj
      (F := CategoryTheory.forget (ModuleCat.{u + 1} Λ))) z
  have h2 := ((((pointSmallEtale s).presheafFiberCompIso
      (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).app F.obj).toEquiv).symm_apply_apply
    ((pointSmallEtale s).toPresheafFiber V v
      (F.obj ⋙ CategoryTheory.forget (ModuleCat.{u + 1} Λ)) z)
  simp only [Iso.toEquiv_fun, Iso.toEquiv_symm_fun, Iso.app_hom, Iso.app_inv] at h2
  rw [ConcreteCategory.comp_apply] at h
  erw [h] at h2
  exact h2

end Germs


section Transport

variable {Y : Scheme.{u}} {Ω Ω' : Type u} [Field Ω] [IsSepClosed Ω] [Field Ω'] [IsSepClosed Ω']
  (s : Spec (.of Ω) ⟶ Y) (s' : Spec (.of Ω') ⟶ Y)
  (τ : FiniteEtale.fiber s ≅ FiniteEtale.fiber s')

/-- The bijection of geometric fibres given by an isomorphism of fibre functors. -/
noncomputable def FiniteEtale.fiberEquivOfIso (P : Y.FiniteEtale) :
    (fiber s).obj P ≃ (fiber s').obj P where
  toFun := τ.hom.app P
  invFun := τ.inv.app P
  left_inv x := ConcreteCategory.congr_hom (τ.hom_inv_id_app P) x
  right_inv x := ConcreteCategory.congr_hom (τ.inv_hom_id_app P) x

namespace FiniteLocallyConstant

/-- The transport of the stalks of a finite locally constant sheaf of sets along an isomorphism
of fibre functors, through the geometric fibres of the representing finite étale scheme
(`AlgebraicGeometry.Scheme.FiniteLocallyConstant.stalkEquiv`). -/
noncomputable def transport (S : Y.FiniteLocallyConstant) :
    (pointSmallEtale s).sheafFiber.obj S.obj ≃ (pointSmallEtale s').sheafFiber.obj S.obj :=
  ((stalkEquiv s S).trans (Equiv.ulift.trans
    ((FiniteEtale.fiberEquivOfIso s s' τ _).trans Equiv.ulift.symm))).trans
    (stalkEquiv s' S).symm

lemma stalkEquiv_transport (S : Y.FiniteLocallyConstant)
    (x : (pointSmallEtale s).sheafFiber.obj S.obj) :
    stalkEquiv s' S (transport s s' τ S x) =
      ULift.up (τ.hom.app _ (stalkEquiv s S x).down) :=
  Equiv.apply_symm_apply _ _

lemma sheafFiber_map_transport {S S' : Y.FiniteLocallyConstant} (f : S ⟶ S')
    (x : (pointSmallEtale s).sheafFiber.obj S.obj) :
    (pointSmallEtale s').sheafFiber.map f.hom (transport s s' τ S x) =
      transport s s' τ S' ((pointSmallEtale s).sheafFiber.map f.hom x) := by
  apply (stalkEquiv s' S').injective
  rw [stalkEquiv_naturality, stalkEquiv_transport, stalkEquiv_transport, stalkEquiv_naturality]
  exact congrArg ULift.up (ConcreteCategory.congr_hom (τ.hom.naturality _) _).symm

lemma transport_symm_apply_transport (S : Y.FiniteLocallyConstant)
    (x : (pointSmallEtale s).sheafFiber.obj S.obj) :
    transport s' s τ.symm S (transport s s' τ S x) = x := by
  apply (stalkEquiv s S).injective
  rw [stalkEquiv_transport, stalkEquiv_transport]
  exact congrArg ULift.up (ConcreteCategory.congr_hom (τ.hom_inv_id_app _) _)

end FiniteLocallyConstant

namespace IsFiniteLocallyConstantSheaf

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
  {F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (hF : IsFiniteLocallyConstantSheaf F)

/-- The transport of the stalks of a finite locally constant sheaf of `Λ`-modules along an
isomorphism of fibre functors, through the underlying finite locally constant sheaf of sets
(`AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.toFLC`). -/
noncomputable def transport
    (x : ((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj F) :
    ((pointSmallEtale s').sheafFiber (A := ModuleCat.{u + 1} Λ)).obj F :=
  (hF.stalkEquiv s').symm (FiniteLocallyConstant.transport s s' τ hF.toFLC (hF.stalkEquiv s x))

lemma stalkEquiv_transport
    (x : ((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj F) :
    hF.stalkEquiv s' (hF.transport s s' τ x) =
      FiniteLocallyConstant.transport s s' τ hF.toFLC (hF.stalkEquiv s x) :=
  Equiv.apply_symm_apply _ _

lemma sheafFiber_map_transport {F' : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (hF' : IsFiniteLocallyConstantSheaf F') (f : F ⟶ F')
    (x : ((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj F) :
    (pointSmallEtale s').sheafFiber.map f (hF.transport s s' τ x) =
      hF'.transport s s' τ ((pointSmallEtale s).sheafFiber.map f x) := by
  let f' : hF.toFLC ⟶ hF'.toFLC :=
    ObjectProperty.homMk ((sheafCompose _ (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).map f)
  apply (hF'.stalkEquiv s').injective
  rw [← sheafFiber_map_stalkEquiv, stalkEquiv_transport, stalkEquiv_transport,
    ← sheafFiber_map_stalkEquiv]
  exact FiniteLocallyConstant.sheafFiber_map_transport s s' τ f' _

lemma transport_symm_apply_transport
    (x : ((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj F) :
    hF.transport s' s τ.symm (hF.transport s s' τ x) = x := by
  apply (hF.stalkEquiv s).injective
  rw [stalkEquiv_transport, stalkEquiv_transport,
    FiniteLocallyConstant.transport_symm_apply_transport]

lemma transport_add (x y : ((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj F) :
    hF.transport s s' τ (x + y) = hF.transport s s' τ x + hF.transport s s' τ y := by
  have := hF
  have hB : IsFiniteLocallyConstantSheaf (F ⊞ F) := IsFiniteLocallyConstantSheaf.biprod F F
  let St := (pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)
  let St' := (pointSmallEtale s').sheafFiber (A := ModuleCat.{u + 1} Λ)
  let z := St.map biprod.inl x + St.map biprod.inr y
  have hfst : St.map biprod.fst z = x := St.map_biprod_fst_inl_add_inr x y
  have hsnd : St.map biprod.snd z = y := St.map_biprod_snd_inl_add_inr x y
  have h₁ : St.map (biprod.desc (𝟙 F) (𝟙 F)) z = x + y := by
    rw [St.map_biprod_desc_id_id, hfst, hsnd]
  have n₁ := sheafFiber_map_transport s s' τ hB hF (biprod.desc (𝟙 F) (𝟙 F)) z
  have n₂ := sheafFiber_map_transport s s' τ hB hF biprod.fst z
  have n₃ := sheafFiber_map_transport s s' τ hB hF biprod.snd z
  rw [h₁] at n₁
  rw [hfst] at n₂
  rw [hsnd] at n₃
  rw [← n₁, ← n₂, ← n₃]
  exact St'.map_biprod_desc_id_id _

lemma transport_smul (c : Λ)
    (x : ((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj F) :
    hF.transport s s' τ (c • x) = c • hF.transport s s' τ x := by
  have n := sheafFiber_map_transport s s' τ hF hF (c • 𝟙 F) x
  rw [sheafFiber_map_smul_id, sheafFiber_map_smul_id] at n
  exact n.symm

/-- The `Λ`-linear transport of the stalks of a finite locally constant sheaf of `Λ`-modules
along an isomorphism of fibre functors. -/
noncomputable def transportLinearEquiv :
    ((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj F ≃ₗ[Λ]
      ((pointSmallEtale s').sheafFiber (A := ModuleCat.{u + 1} Λ)).obj F where
  toFun := hF.transport s s' τ
  invFun := hF.transport s' s τ.symm
  map_add' := hF.transport_add s s' τ
  map_smul' := hF.transport_smul s s' τ
  left_inv := hF.transport_symm_apply_transport s s' τ
  right_inv x := by
    simpa only [Iso.symm_symm_eq] using hF.transport_symm_apply_transport s' s τ.symm x

lemma transportLinearEquiv_apply
    (x : ((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj F) :
    hF.transportLinearEquiv s s' τ x = hF.transport s s' τ x :=
  rfl

end IsFiniteLocallyConstantSheaf

end Transport

end AlgebraicGeometry.Scheme
