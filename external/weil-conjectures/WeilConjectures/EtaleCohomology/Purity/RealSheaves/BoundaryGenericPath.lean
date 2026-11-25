/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.UniversalCoverLift
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryGenericPoint
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilPathFrobenius
public import WeilConjectures.SixFunctors.ProEtale.GenericPoint

/-!
# Base point data adapted to the generic geometric point

Let `j : U₀ ⟶ C₀` be a nonempty open of a smooth geometrically connected curve over a finite field,
`η : Spec Ω ⟶ Ū` the geometric generic point (`AlgebraicGeometry.WeilGroup.genericGeomPoint`) and
`B₀` base point data of the Weil group of `U₀`, with base point `t` of `Ū`. A lift `ξ` of `η` to
the universal cover `Ỹ_t` defines a path `F_t ≅ F_η`
(`AlgebraicGeometry.Scheme.UniversalCover.liftPath`); pushed down to `U₀` and followed by the path
`F_{η₀} ≅ F_{s_U}` defining the Galois map `Gal(Ω / k(C)) → π₁(U₀)`
(`AlgebraicGeometry.WeilGroup.genericGaloisMap`), it gives new base point data `B`
(`AlgebraicGeometry.WeilGroup.BasePointData.ofLift`). For `B`:

* the loop at `t` defined by the lifts `Spec σ ≫ ξ` and `ξ`, for `σ` acting trivially on `k̄`,
  maps to the image of `σ` in `π₁(U₀)`
  (`AlgebraicGeometry.WeilGroup.BasePointData.geomAut_ofLift`);
* the path `F_t ≅ F_{t ≫ Frⁿ}` defined by the lifts `Spec σ ≫ ξ` and `ξ ≫ (Ỹ_t ⟶ Ỹ_{t ≫ Frⁿ})`,
  for `σ` acting on `k̄` as `Φⁿ`, pushes down to the image of `σ` in `π₁(U₀)`
  (`AlgebraicGeometry.WeilGroup.BasePointData.downAut_ofLift`).

This identifies the inertia groups and residue Frobenius lifts of `lemma-boundary-stalk--1` with
transports of lisse sheaves along lifts of the generic geometric point, as needed for blueprint
`lemma-boundary-stalk--1`.
-/

@[expose] public section

universe u

open CategoryTheory Limits PreGaloisCategory

namespace CategoryTheory

/-- Composites of `eqToIso`, followed by an isomorphism. -/
lemma eqToIso_trans_assoc {𝒞 : Type*} [Category 𝒞] {X Y Z W : 𝒞} (p : X = Y) (q : Y = Z)
    (γ : Z ≅ W) : eqToIso p ≪≫ eqToIso q ≪≫ γ = eqToIso (p.trans q) ≪≫ γ := by
  rw [← Iso.trans_assoc, eqToIso_trans]

end CategoryTheory

namespace AlgebraicGeometry

namespace Scheme.FiniteEtale

variable {X Y Z : Scheme.{u}} {Ω Ω' : Type u} [Field Ω] [IsSepClosed Ω] [Field Ω']
  [IsSepClosed Ω']

/-- The path induced along a composite is the iterated induced path, for paths between geometric
points with values in different fields. -/
lemma pullbackPathIso'_comp (f : X ⟶ Y) (g : Y ⟶ Z) {y : Spec (.of Ω) ⟶ X}
    {z : Spec (.of Ω') ⟶ X} (τ : fiber y ≅ fiber z) :
    pullbackPathIso' (f ≫ g) τ =
      eqToIso (by rw [Category.assoc]) ≪≫ pullbackPathIso' g (pullbackPathIso' f τ) ≪≫
        eqToIso (by rw [Category.assoc]) := by
  ext P x
  apply fiber_ext
  rw [Iso.trans_hom, Iso.trans_hom, NatTrans.comp_app, NatTrans.comp_app, FintypeCat.comp_apply,
    FintypeCat.comp_apply]
  rw [eqToIso_fiber_hom_app_left (Category.assoc z f g), pullbackPathIso'_hom_app_left,
    pullbackPathIso'_hom_app_left, pullbackPathIso'_hom_app_left]
  have hx : ((eqToIso (congrArg fiber (Category.assoc y f g)).symm).hom.app P x).left = x.left :=
    eqToIso_fiber_hom_app_left (Category.assoc y f g).symm _ P x
  have hw : (fiber y).map (pullbackCompHom f g P) ((pullbackFiberIso f y).inv.app _
      ((pullbackFiberIso g (y ≫ f)).inv.app P
        ((eqToIso (congrArg fiber (Category.assoc y f g)).symm).hom.app P x))) =
      (pullbackFiberIso (f ≫ g) y).inv.app P x := by
    apply fiber_ext
    rw [fiber_map_left, pullbackCompHom_hom_left, pullbackFiberIso_inv_app_left f y,
      pullbackFiberIso_inv_app_left (f ≫ g) y]
    apply Limits.pullback.hom_ext
    · rw [Category.assoc, Limits.pullback.lift_fst, Limits.pullback.lift_fst_assoc,
        Limits.pullback.lift_fst, pullbackFiberIso_inv_app_left, Limits.pullback.lift_fst, hx]
    · rw [Category.assoc, Limits.pullback.lift_snd, Limits.pullback.lift_snd,
        Limits.pullback.lift_snd]
  rw [← hw, ← ConcreteCategory.comp_apply, τ.hom.naturality, ConcreteCategory.comp_apply,
    fiber_map_left, pullbackCompHom_hom_left]
  simp only [Category.assoc, Limits.pullback.lift_fst]

/-- Transporting a path along equal morphisms, for different fields. -/
lemma pullbackPathIso'_congr {f f' : X ⟶ Y} (hf : f = f') {y : Spec (.of Ω) ⟶ X}
    {z : Spec (.of Ω') ⟶ X} (τ : fiber y ≅ fiber z) :
    pullbackPathIso' f τ =
      eqToIso (by rw [hf]) ≪≫ pullbackPathIso' f' τ ≪≫ eqToIso (by rw [hf]) := by
  subst hf
  simp

/-- The path induced along `g` by the path induced along an endomorphism `f` over `Y`
(`f ≫ g = g`) is the path induced along `g`, for different fields. -/
lemma pullbackPathIso'_pullbackPathIso'_of_comp_eq {f : X ⟶ X} {g : X ⟶ Y} (hf : f ≫ g = g)
    {y : Spec (.of Ω) ⟶ X} {z : Spec (.of Ω') ⟶ X} (τ : fiber y ≅ fiber z) :
    pullbackPathIso' g (pullbackPathIso' f τ) =
      eqToIso (by rw [Category.assoc, hf]) ≪≫ pullbackPathIso' g τ ≪≫
        eqToIso (by rw [Category.assoc, hf]) := by
  have h := pullbackPathIso'_comp f g τ
  rw [pullbackPathIso'_congr hf] at h
  exact CategoryTheory.eqToIso_trans_trans_eq _ _ _ _ _ _ h

end Scheme.FiniteEtale

/-- A weakly étale surjective morphism has a lift through every geometric point with values in a
separably closed field. -/
lemma exists_comp_eq_of_weaklyEtale_of_surjective {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    {P Y : Scheme.{u}} (p : P ⟶ Y) [WeaklyEtale p] (hp : Function.Surjective p.base)
    (η : Spec (.of Ω) ⟶ Y) : ∃ ξ : Spec (.of Ω) ⟶ P, ξ ≫ p = η := by
  obtain ⟨z⟩ := (inferInstance : Nonempty (Spec (.of Ω)))
  obtain ⟨x, hx⟩ := hp (η.base z)
  obtain ⟨w, -, -⟩ := Scheme.Pullback.exists_preimage_pullback x z hx
  obtain ⟨σ, hσ⟩ := exists_comp_eq_id_of_weaklyEtale_of_isSepClosed (pullback.snd p η) w
  refine ⟨σ ≫ pullback.fst p η, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, hσ, Category.id_comp]

namespace WeilGroup

open Scheme Scheme.FiniteEtale

variable {K : Type u} [Field K] [Finite K] {C U : Scheme.{u}} {pU : U ⟶ Spec (.of K)}
  [IsCurve pU] [GeometricallyConnected pU] [ConnectedSpace U]
  (j : U ⟶ C) [IsOpenImmersion j] [Nonempty U] [IsIntegral C]
  (sU : Spec (.of (AlgebraicClosure K)) ⟶ U)
  (GU : Type u) [Group GU] [TopologicalSpace GU] [IsTopologicalGroup GU] [CompactSpace GU]
  [∀ P, MulAction GU ((fiber sU).obj P)] [IsFundamentalGroup (fiber sU) GU]
  [ConnectedSpace pU.geometricFiber] [CompactSpace pU.geometricFiber]
  [QuasiSeparatedSpace pU.geometricFiber]

local notation "Ω" => SeparableClosure (Scheme.functionField C)

namespace BasePointData

/-- **Base point data adapted to the generic geometric point**: the base point `t` and the path
`β` of `B₀`, and the path from the image of `t` in `U₀` to `s_U` obtained from a lift `ξ` of the
geometric generic point `η` to `Ỹ_t` (`F_t ≅ F_η`), pushed down to `U₀`, followed by the path
`F_{η₀} ≅ F_{s_U}` of the Galois map `Gal(Ω / k(C)) → π₁(U₀)`. -/
noncomputable def ofLift (B₀ : BasePointData (ofFundamentalGroup pU sU GU))
    (ξ : Spec (.of Ω) ⟶ UniversalCover.cover B₀.t)
    (hξ : ξ ≫ UniversalCover.proj B₀.t = genericGeomPoint pU j) :
    BasePointData (ofFundamentalGroup pU sU GU) where
  t := B₀.t
  ht := B₀.ht
  path := pullbackPathIso' pU.geometricFiberProj (UniversalCover.liftPath B₀.t ξ hξ) ≪≫
    eqToIso (congrArg fiber (genericGeomPoint_geometricFiberProj j)) ≪≫ genericPath j sU
  frobPath := B₀.frobPath

variable {j sU GU} (B₀ : BasePointData (ofFundamentalGroup pU sU GU))

/-- The push-down of the path of the lift `Spec σ ≫ ξ` of `Spec σ ≫ η`, for `σ ∈ Gal(Ω / k(C))`,
is the push-down of the path of `ξ` followed by the action of `σ` on the fibre functor at `η₀`. -/
lemma pullbackPathIso'_liftPath_specMap
    (ξ : Spec (.of Ω) ⟶ UniversalCover.cover B₀.t)
    (hξ : ξ ≫ UniversalCover.proj B₀.t = genericGeomPoint pU j) (σ : Gal(Ω/C.functionField))
    {ξ' : Spec (.of Ω) ⟶ UniversalCover.cover B₀.t}
    (hξ' : Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ ξ = ξ')
    {η' : Spec (.of Ω) ⟶ pU.geometricFiber} (h' : ξ' ≫ UniversalCover.proj B₀.t = η')
    (hη' : η' ≫ pU.geometricFiberProj = genericBasePoint j) :
    pullbackPathIso' pU.geometricFiberProj (UniversalCover.liftPath B₀.t ξ' h') =
      pullbackPathIso' pU.geometricFiberProj (UniversalCover.liftPath B₀.t ξ hξ) ≪≫
        eqToIso (congrArg fiber (genericGeomPoint_geometricFiberProj j)) ≪≫
        (galoisToAut (genericPointLift j) σ).asIso ≪≫ eqToIso (congrArg fiber hη'.symm) := by
  subst hξ'
  ext P x
  apply fiber_ext
  simp only [Iso.trans_hom, NatTrans.comp_app, FintypeCat.comp_apply]
  rw [eqToIso_fiber_hom_app_left hη'.symm, galoisToAut_hom_app_left,
    eqToIso_fiber_hom_app_left (genericGeomPoint_geometricFiberProj j),
    pullbackPathIso'_hom_app_left, pullbackPathIso'_hom_app_left,
    UniversalCover.liftPath_hom_app_left, UniversalCover.liftPath_hom_app_left]
  simp only [Category.assoc]

/-- **Inertia-type loops.** For `σ ∈ Gal(Ω / k(C))` fixing `η` (acting trivially on `k̄`), the
loop at `t` defined by the lifts `ξ' = Spec σ ≫ ξ` and `ξ` maps to the image of `σ` in
`π₁(U₀)`. -/
theorem geomAut_ofLift
    (ξ : Spec (.of Ω) ⟶ UniversalCover.cover B₀.t)
    (hξ : ξ ≫ UniversalCover.proj B₀.t = genericGeomPoint pU j) (σ : Gal(Ω/C.functionField))
    {ξ' : Spec (.of Ω) ⟶ UniversalCover.cover B₀.t}
    (hξ' : Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ ξ = ξ')
    (h' : ξ' ≫ UniversalCover.proj B₀.t = genericGeomPoint pU j) :
    (ofLift j sU GU B₀ ξ hξ).geomAut (.of (UniversalCover.liftPath B₀.t ξ' h' ≪≫
      (UniversalCover.liftPath B₀.t ξ hξ).symm)) = genericGaloisMap j sU GU σ := by
  rw [geomAut_apply]
  change (toAutMulEquiv (fiber sU) GU).symm _ = (toAutMulEquiv (fiber sU) GU).symm _
  congr 1
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  apply Aut.ext
  simp only [Aut.autMulEquivOfIso, Equiv.coe_fn_mk, Iso.conjAut_apply]
  rw [← pullbackPathIso'_eq, pullbackPathIso'_trans, pullbackPathIso'_symm,
    pullbackPathIso'_liftPath_specMap B₀ ξ hξ σ hξ' h' (genericGeomPoint_geometricFiberProj j)]
  simp only [ofLift, Iso.trans_symm, Iso.trans_assoc, Iso.symm_self_id_assoc]
  simp only [eqToIso_trans_assoc, eqToIso_refl, Iso.refl_trans]

/-- **Frobenius-type paths.** For `σ ∈ Gal(Ω / k(C))` with `Spec σ ≫ η = η ≫ Frⁿ`, the path
`F_t ≅ F_{t ≫ Frⁿ}` defined by the lifts `ξ' = Spec σ ≫ ξ` and `ξ ≫ (Ỹ_t ⟶ Ỹ_{t ≫ Frⁿ})`
pushes down to the image of `σ` in `π₁(U₀)`. -/
theorem downAut_ofLift
    (ξ : Spec (.of Ω) ⟶ UniversalCover.cover B₀.t)
    (hξ : ξ ≫ UniversalCover.proj B₀.t = genericGeomPoint pU j) (σ : Gal(Ω/C.functionField)) (n : ℕ)
    {ξ' : Spec (.of Ω) ⟶ UniversalCover.cover B₀.t}
    (hξ' : Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ ξ = ξ')
    (h₁ : ξ' ≫ UniversalCover.proj B₀.t =
      genericGeomPoint pU j ≫ (pU.geometricGaloisFrobenius ^ n).asIso.hom)
    (h₂ : (ξ ≫ UniversalCover.map (pU.geometricGaloisFrobenius ^ n).asIso.hom B₀.t) ≫
      UniversalCover.proj (B₀.t ≫ (pU.geometricGaloisFrobenius ^ n).asIso.hom) =
        genericGeomPoint pU j ≫ (pU.geometricGaloisFrobenius ^ n).asIso.hom)
    (hd : (B₀.t ≫ (pU.geometricGaloisFrobenius ^ n).asIso.hom) ≫ pU.geometricFiberProj =
      B₀.t ≫ pU.geometricFiberProj) :
    (ofLift j sU GU B₀ ξ hξ).downAut (UniversalCover.liftPath B₀.t ξ' h₁ ≪≫
      (UniversalCover.liftPath (B₀.t ≫ (pU.geometricGaloisFrobenius ^ n).asIso.hom)
        (ξ ≫ UniversalCover.map (pU.geometricGaloisFrobenius ^ n).asIso.hom B₀.t) h₂).symm) hd =
        genericGaloisMap j sU GU σ := by
  have hF := Scheme.Hom.geometricGaloisFrobenius_pow_hom_comp_geometricFiberProj pU n
  have hη' : (genericGeomPoint pU j ≫ (pU.geometricGaloisFrobenius ^ n).asIso.hom) ≫
      pU.geometricFiberProj = genericBasePoint j := by
    rw [Category.assoc, hF, genericGeomPoint_geometricFiberProj]
  rw [downAut]
  change (toAutMulEquiv (fiber sU) GU).symm _ = (toAutMulEquiv (fiber sU) GU).symm _
  congr 1
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  apply Aut.ext
  simp only [Aut.autMulEquivOfIso, Equiv.coe_fn_mk, Iso.conjAut_apply]
  rw [← pullbackPathIso'_eq, pullbackPathIso'_trans, pullbackPathIso'_symm,
    pullbackPathIso'_liftPath_specMap B₀ ξ hξ σ hξ' h₁ hη', UniversalCover.liftPath_map _ B₀.t ξ hξ,
    pullbackPathIso'_pullbackPathIso'_of_comp_eq hF]
  simp only [ofLift, Iso.trans_symm, Iso.trans_assoc, eqToIso_symm',
    eqToIso_trans, Iso.symm_self_id_assoc, eqToIso_refl, Iso.refl_trans]
  simp only [eqToIso_trans_assoc, eqToIso_refl, Iso.refl_trans]

end BasePointData

end WeilGroup

end AlgebraicGeometry
