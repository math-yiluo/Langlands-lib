/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryGenericPath
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationData
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationStalk
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyLift

/-!
# The Weil fundamental representation at the geometric generic point

Let `j : U₀ ⟶ C₀` be a nonempty open of a smooth geometrically connected curve over `k₀`, `F` a
lisse Weil sheaf on `U₀`, `η : Spec Ω ⟶ Ū` the geometric generic point, and `B` the base point
data adapted to a lift `ξ` of `η` to the universal cover at the base point `t`
(`AlgebraicGeometry.WeilGroup.BasePointData.ofLift`). The restriction along `ξ` identifies the
Weil fundamental representation `V = F_t` with the sections `Γ(Spec Ω, η^* F)` at the generic
point (`AlgebraicGeometry.WeilGroup.genericStalkEquiv`), and for `σ ∈ Gal(Ω / k(C))` whose image
`w = (ρ(σ), n)` lies in the Weil group:

* if `n = 0`, then `ρ(w)` corresponds to the restriction along `Spec σ`
  (`AlgebraicGeometry.WeilGroup.genericStalkEquiv_fundamentalRep_of_deg_zero`);
* in general, `ρ(w)` corresponds to the transport along the square `Spec σ ≫ η = η ≫ Frⁿ` and the
  iterated Weil structure `φ_n` (`AlgebraicGeometry.WeilGroup.genericStalkEquiv_fundamentalRep`).

For `σ` in the inertia group at a boundary point and for a residue Frobenius lift, this is the
action of the inertia group and of the Frobenius on the generic stalk in blueprint
`lemma-boundary-stalk--1`.
-/

@[expose] public section

universe u

open CategoryTheory Limits PreGaloisCategory

namespace AlgebraicGeometry.WeilGroup

open Scheme Scheme.FiniteEtale ProEtale

variable {K : Type u} [Field K] [Finite K] {C U : Scheme.{u}} [U.Over (Spec (.of K))]
  [IsCurve (U ↘ Spec (.of K))] [GeometricallyConnected (U ↘ Spec (.of K))] [ConnectedSpace U]
  {j : U ⟶ C} [IsOpenImmersion j] [Nonempty U] [IsIntegral C]
  {sU : Spec (.of (AlgebraicClosure K)) ⟶ U}
  {GU : Type u} [Group GU] [TopologicalSpace GU] [IsTopologicalGroup GU] [CompactSpace GU]
  [∀ P, MulAction GU ((fiber sU).obj P)] [IsFundamentalGroup (fiber sU) GU]
  [IsLocallyNoetherian (U ↘ Spec (.of K)).geometricFiber]
  [CompactSpace (U ↘ Spec (.of K)).geometricFiber] [IsRegular (U ↘ Spec (.of K)).geometricFiber]
  [ConnectedSpace (U ↘ Spec (.of K)).geometricFiber]
  [QuasiSeparatedSpace (U ↘ Spec (.of K)).geometricFiber]
  {l : ℕ} [Fact l.Prime] [Fact (ringChar K ≠ l)]

local notation "Ω" => SeparableClosure (Scheme.functionField C)

local notation "M" =>
  universalLisseMonodromy l (Scheme.Hom.geometricFiber (U ↘ Spec (CommRingCat.of K))) K

-- the base point data adapted to the lift `ξ` of the geometric generic point
set_option hygiene false in
local notation "Bξ" => BasePointData.ofLift j sU GU B₀ ξ hξ

set_option hygiene false in
local notation "FrU" => Scheme.Hom.geometricGaloisFrobenius (U ↘ Spec (CommRingCat.of K))

/-- The identification `F_t ≅ Γ(Spec Ω, η^* F)` of the Weil fundamental representation with the
sections at the geometric generic point, by restriction along the lift `ξ`. -/
noncomputable def genericStalkEquiv
    (B₀ : BasePointData (ofFundamentalGroup (U ↘ Spec (.of K)) sU GU))
    (ξ : Spec (.of Ω) ⟶ UniversalCover.cover B₀.t)
    (hξ : ξ ≫ UniversalCover.proj B₀.t = genericGeomPoint (U ↘ Spec (.of K)) j)
    (F : WeilSheaf K l U) (hF : F.IsLisse) :
    LisseMonodromy.StalkSpace (Bξ).t (F.toLisse hF)
      ≃ₗ[PadicAlgCl l]
      (WeilCoefficients.toModuleCat l).obj ((Sheaf.Γ _ _).obj
        ((genericGeomPoint (U ↘ Spec (.of K)) j)^*[WeilCoefficients.{u} l].obj F.obj.carrier.X)) :=
  WeilCoefficients.linearEquivOfIso (liftStalkIso B₀.t ξ hξ (F.toLisse hF))

/-- The identification `F_t ≅ Γ(Spec Ω, η^* F)` on elements. -/
lemma genericStalkEquiv_apply
    (B₀ : BasePointData (ofFundamentalGroup (U ↘ Spec (.of K)) sU GU))
    (ξ : Spec (.of Ω) ⟶ UniversalCover.cover B₀.t)
    (hξ : ξ ≫ UniversalCover.proj B₀.t = genericGeomPoint (U ↘ Spec (.of K)) j)
    (F : WeilSheaf K l U) (hF : F.IsLisse)
    (v : LisseMonodromy.StalkSpace (Bξ).t (F.toLisse hF)) :
    genericStalkEquiv B₀ ξ hξ F hF v =
      ((WeilCoefficients.toModuleCat l).map (liftStalkIso B₀.t ξ hξ (F.toLisse hF)).hom).hom v :=
  rfl

/-- **Degree-zero Galois elements act by restriction.** If the image `w = (ρ(σ), 0)` of
`σ ∈ Gal(Ω / k(C))` lies in the Weil group (for instance `σ` in an inertia group at a boundary
point), then `ρ(w)` on `F_t` corresponds to the restriction along `Spec σ` on
`Γ(Spec Ω, η^* F)`. -/
theorem genericStalkEquiv_fundamentalRep_of_deg_zero
    (B₀ : BasePointData (ofFundamentalGroup (U ↘ Spec (.of K)) sU GU))
    (ξ : Spec (.of Ω) ⟶ UniversalCover.cover B₀.t)
    (hξ : ξ ≫ UniversalCover.proj B₀.t = genericGeomPoint (U ↘ Spec (.of K)) j)
    (F : WeilSheaf K l U) (hF : F.IsLisse)
    (σ : Gal(Ω/C.functionField))
    (hw : (genericGaloisMap j sU GU σ, Multiplicative.ofAdd (0 : ℤ)) ∈
      weilGroup (U ↘ Spec (.of K)) sU GU)
    (ha : Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ genericGeomPoint (U ↘ Spec (.of K)) j =
      genericGeomPoint (U ↘ Spec (.of K)) j)
    (v : LisseMonodromy.StalkSpace (Bξ).t (F.toLisse hF)) :
    genericStalkEquiv B₀ ξ hξ F hF (fundamentalRep M
        (Bξ).weilMonodromyData F hF
        (⟨_, hw⟩ : weilGroup (U ↘ Spec (.of K)) sU GU) v) =
      ((WeilCoefficients.toModuleCat l).map ((resOver _ _ ha).app F.obj.carrier.X)).hom
        (genericStalkEquiv B₀ ξ hξ F hF v) := by
  have h' : (Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ ξ) ≫ UniversalCover.proj B₀.t =
      genericGeomPoint (U ↘ Spec (.of K)) j := by
    rw [Category.assoc, hξ, ha]
  set g := Aut.of
    (UniversalCover.liftPath B₀.t _ h' ≪≫ (UniversalCover.liftPath B₀.t ξ hξ).symm)
  have hgw : (⟨_, hw⟩ : weilGroup (U ↘ Spec (.of K)) sU GU) = (Bξ).geomHom g := by
    apply Subtype.ext
    have e := (Bξ).weilGroupEquiv_geomHom g
    rw [BasePointData.geomAut_ofLift B₀ ξ hξ σ rfl h'] at e
    exact e.symm
  have hgeo :=
    fundamentalRep_geometric M (Bξ).weilMonodromyData F hF ⟨(Bξ).geomHom g, (Bξ).geomHom_mem g⟩
  rw [show ((Bξ).weilMonodromyData.geomEquiv.symm ⟨(Bξ).geomHom g, (Bξ).geomHom_mem g⟩) = g from
    (Bξ).geomEquiv.symm_apply_eq.2 (Subtype.ext ((Bξ).geomEquiv_apply g).symm)] at hgeo
  rw [hgw]
  rw [show fundamentalRep M (Bξ).weilMonodromyData F hF ((Bξ).geomHom g) =
    LisseMonodromy.rep M (Bξ).t (F.toLisse hF) g from hgeo]
  have e := congrArg (fun φ ↦ ((WeilCoefficients.toModuleCat l).map φ).hom v)
    (liftStalkIso_resOver B₀.t ξ hξ _ ha h' (F.toLisse hF))
  simp only [CategoryTheory.Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at e
  rw [genericStalkEquiv_apply B₀ ξ hξ, genericStalkEquiv_apply B₀ ξ hξ]
  exact e.symm

-- the anonymous constructor of the Weil group element is checked against the carrier slowly
/-- **Galois elements of degree `n` act through the Weil structure.** If the image
`w = (ρ(σ), n)` of `σ ∈ Gal(Ω / k(C))` lies in the Weil group (for instance a residue Frobenius
lift at a boundary point), so that `Spec σ ≫ η = η ≫ Frⁿ`, then `ρ(w)` on `F_t` corresponds to the
transport of `Γ(Spec Ω, η^* F)` along the square `Spec σ ≫ η = η ≫ Frⁿ` and the iterated Weil
structure `φ_n`. -/
theorem genericStalkEquiv_fundamentalRep
    (B₀ : BasePointData (ofFundamentalGroup (U ↘ Spec (.of K)) sU GU))
    (ξ : Spec (.of Ω) ⟶ UniversalCover.cover B₀.t)
    (hξ : ξ ≫ UniversalCover.proj B₀.t = genericGeomPoint (U ↘ Spec (.of K)) j)
    (F : WeilSheaf K l U) (hF : F.IsLisse)
    (σ : Gal(Ω/C.functionField)) (n : ℕ)
    (hw : (genericGaloisMap j sU GU σ, Multiplicative.ofAdd (n : ℤ)) ∈
      weilGroup (U ↘ Spec (.of K)) sU GU)
    (ha : Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ genericGeomPoint (U ↘ Spec (.of K)) j =
      genericGeomPoint (U ↘ Spec (.of K)) j ≫
        ((U ↘ Spec (.of K)).geometricGaloisFrobenius ^ n).asIso.hom)
    (v : LisseMonodromy.StalkSpace (Bξ).t (F.toLisse hF)) :
    genericStalkEquiv B₀ ξ hξ F hF (fundamentalRep M
        (Bξ).weilMonodromyData F hF
        (⟨_, hw⟩ : weilGroup (U ↘ Spec (.of K)) sU GU) v) =
      ((WeilCoefficients.toModuleCat l).map
        (globalSectionsTransport _ ha (F.frobeniusPowStr n))).hom
        (genericStalkEquiv B₀ ξ hξ F hF v) := by
  have h₁ : (Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ ξ) ≫ UniversalCover.proj B₀.t =
      genericGeomPoint (U ↘ Spec (.of K)) j ≫ (FrU ^ n).asIso.hom := by
    rw [Category.assoc, hξ, ha]
  have h₂ : (ξ ≫ UniversalCover.map (FrU ^ n).asIso.hom B₀.t) ≫
      UniversalCover.proj (B₀.t ≫ (FrU ^ n).asIso.hom) =
        genericGeomPoint (U ↘ Spec (.of K)) j ≫ (FrU ^ n).asIso.hom := by
    rw [Category.assoc, UniversalCover.map_proj, ← Category.assoc, hξ]
  have hd : (B₀.t ≫ (FrU ^ n).asIso.hom) ≫ (U ↘ Spec (.of K)).geometricFiberProj =
      B₀.t ≫ (U ↘ Spec (.of K)).geometricFiberProj := by
    rw [Category.assoc, Scheme.Hom.geometricGaloisFrobenius_pow_hom_comp_geometricFiberProj]
  set δ := UniversalCover.liftPath B₀.t _ h₁ ≪≫
    (UniversalCover.liftPath (B₀.t ≫ (FrU ^ n).asIso.hom) _ h₂).symm
  set g' := Aut.of (δ ≪≫ ((Bξ).frobPathPow n).symm)
  have hwB : (⟨_, hw⟩ : weilGroup (U ↘ Spec (.of K)) sU GU) =
      (Bξ).frobLift ^ n * (Bξ).geomHom g' := by
    have hdown := (Bξ).downAut_eq_mul_geomAut δ ((Bξ).frobPathPow n) hd
    rw [(Bξ).downAut_frobPathPow, BasePointData.downAut_ofLift B₀ ξ hξ σ n rfl h₁ h₂ hd] at hdown
    apply (ofFundamentalGroup (U ↘ Spec (.of K)) sU GU).weilGroupEquiv.injective
    apply Subtype.ext
    rw [map_mul, map_pow, Subgroup.coe_mul, Subgroup.coe_pow, (Bξ).weilGroupEquiv_frobLift,
      (Bξ).weilGroupEquiv_geomHom g']
    ext
    · change genericGaloisMap j sU GU σ = _
      simp only [Prod.fst_mul, Prod.pow_fst]
      exact hdown
    · change Multiplicative.ofAdd (n : ℤ) = _
      rw [Prod.snd_mul, Prod.pow_snd, mul_one, ← ofAdd_nsmul, nsmul_one]
      rfl
  have hfl : (Bξ).weilMonodromyData.frobLift =
      (Bξ).frobLift := rfl
  rw [hwB, map_mul, map_pow, Module.End.mul_apply, ← hfl, fundamentalRep_frobLift]
  have hgeo := fundamentalRep_geometric M (Bξ).weilMonodromyData F hF
    ⟨(Bξ).geomHom g', (Bξ).geomHom_mem g'⟩
  rw [show ((Bξ).weilMonodromyData.geomEquiv.symm ⟨(Bξ).geomHom g', (Bξ).geomHom_mem g'⟩) = g' from
    (Bξ).geomEquiv.symm_apply_eq.2 (Subtype.ext ((Bξ).geomEquiv_apply g').symm)] at hgeo
  change _ = _ at hgeo
  rw [show fundamentalRep M (Bξ).weilMonodromyData F hF ((Bξ).geomHom g') =
    LisseMonodromy.rep M (Bξ).t (F.toLisse hF) g' from hgeo]
  -- the transport along the square is `Ψ_n(δ)`
  have e := liftStalkIso_globalSectionsTransport B₀.t ξ hξ (FrU ^ n).asIso.hom _ ha h₁ h₂
    (F.toLisse hF) (F.frobeniusPowStr n)
  have hΨ : (LisseMonodromy.mono M δ).hom.app (F.toLisse hF) ≫
      (upperStarStalkIso l (FrU ^ n).asIso.hom B₀.t (F.toLisse hF).obj.X).hom ≫
      (stalkFunctor l B₀.t).map (F.frobeniusPowStr n) = frobPowStalk M (Bξ) F hF n δ := by
    rw [frobPowStalk, ← WeilSheaf.lisseFrobPowStr_hom_hom]
    rfl
  erw [reassoc_of% hΨ] at e
  rw [frobPowStalk_eq_mono_comp M (B := Bξ) F hF n δ
    ((Bξ).frobPathPow n)] at e
  have e' := congrArg (fun φ ↦ ((WeilCoefficients.toModuleCat l).map φ).hom v) e
  simp only [CategoryTheory.Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at e'
  rw [genericStalkEquiv_apply B₀ ξ hξ, genericStalkEquiv_apply B₀ ξ hξ]
  refine Eq.trans ?_ e'.symm
  rw [frobPowStalk_frobPathPow M (B := Bξ) F hF n]
  congr 1
  simp only [Module.End.pow_apply]
  erw [LinearEquiv.coe_toLinearMap, LinearEquiv.pow_apply]
  rfl

end AlgebraicGeometry.WeilGroup
