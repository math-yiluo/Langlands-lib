/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import WeilConjectures.AlgebraicGeometry.Tensor.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.CoherentFiniteType
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import WeilConjectures.AlgebraicGeometry.TangentBundle
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import WeilConjectures.AlgebraicGeometry.QuasiCoherentIsoOnAffineCover
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Kaehler.TensorProduct
import WeilConjectures.AlgebraicGeometry.RelativeDifferentialsAffineSections
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine

/-!
# Arbitrary base change of relative differential sheaves

The affine tensor product ring is expressed intrinsically as the section ring of the
open fibre product. The `IsPushout` clause identifies it canonically with `R' ⊗[R] A`.
The three linear equivalences identify the tensor source, the differential target,
and the ring base-change isomorphism, and the final equation identifies their map
with the restriction of the single global sheaf morphism. Consequently the affine
identifications agree on overlaps by the naturality of that morphism.

## References

* Stacks Project, Morphisms, Tags 01UT, 01UV, 01V0 and 01V2
* Stacks, Schemes, Tag 01JR
* Morphisms, Tag 01V0
* Stacks Project, Morphisms, Tag 01UV
* Stacks Project, Morphisms, Tag 01V2
* Algebra, Tag 00RZ
* Stacks Project, Schemes, Tags 01JR and 01JQ
* Stacks Project, Algebra, Tag 00RV
* Stacks Project, Schemes, Tags 01I9 and 01IA
* Stacks Project, Morphisms, Tag 01V0
* Stacks, Morphisms, Tags 01UT, 01UV, 01V0 and 01V2
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Limits Opposite
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme.Hom

/-- The open `U ×_V V'` inside the global fibre product, with `V` implicit in the
conditions that both affine opens map into it. -/
noncomputable abbrev relativeDifferentialsBaseChangeOpen {X S T : Scheme.{u}}
    (f : X ⟶ S) (g : T ⟶ S) (U : X.Opens) (V' : T.Opens) :
    (pullback f g).Opens :=
  (pullback.fst f g) ⁻¹ᵁ U ⊓ (pullback.snd f g) ⁻¹ᵁ V'

/-- The universal derivation and the normalized pullback adjunction construct the global
map and determine it uniquely. -/
private theorem existsUnique_baseChangeMap {X S T : Scheme.{u}}
    (f : X ⟶ S) (g : T ⟶ S) :
    ∃! c : (Modules.tensorPullback (pullback.fst f g)).obj f.relativeDifferentials ⟶
        (pullback.snd f g).relativeDifferentials,
      ∀ (U : X.Opens) (a : Γ(X, U)),
        c.app ((pullback.fst f g) ⁻¹ᵁ U)
          (Modules.tensorPullbackSection (pullback.fst f g) f.relativeDifferentials U
            (f.relativeDifferentialsDerivation.d (X := op U) a)) =
          (pullback.snd f g).relativeDifferentialsDerivation.d
            (X := op ((pullback.fst f g) ⁻¹ᵁ U)) ((pullback.fst f g).app U a) := by
  let p := pullback.fst f g
  let q := pullback.snd f g
  let D : ((Modules.pushforward p).obj q.relativeDifferentials).val.Derivation'
      f.pullbackPresheafToPresheaf :=
    f.derivationMk
      (fun {U} ↦ q.relativeDifferentialsDerivation.d.comp
        (p.app U.unop).hom.toAddMonoidHom)
      (by
        intro U a b
        change q.relativeDifferentialsDerivation.d (p.app U.unop (a * b)) = _
        rw [map_mul, PresheafOfModulesOfCommRing.Derivation.d_mul]
        rfl)
      (by
        intro U V i a
        change q.relativeDifferentialsDerivation.d (p.app V.unop (X.presheaf.map i a)) = _
        rw [← CommRingCat.comp_apply, p.naturality i]
        exact q.relativeDifferentialsDerivation.d_map _ _)
      (by
        intro V a
        change q.relativeDifferentialsDerivation.d
          (p.app (f ⁻¹ᵁ V) (f.app V a)) = 0
        have hw := Scheme.Hom.congr_app (pullback.condition (f := f) (g := g)) V
        have hv := congrArg (fun k ↦ k a) hw
        change (p ≫ f).app V a = _ at hv
        change q.relativeDifferentialsDerivation.d ((p ≫ f).app V a) = 0
        rw [hv]
        erw [q.relativeDifferentialsDerivation.d_map]
        change q.relativeDifferentials.val.map _
          (q.relativeDifferentialsDerivation.d (q.app _ (g.app V a))) = 0
        erw [PresheafOfModules.Derivation'.d_app_app q.relativeDifferentialsDerivation, map_zero])
  obtain ⟨adj, hadj⟩ := Modules.existsUnique_tensorPullbackSectionAdjunction p
  let e := adj.homEquiv f.relativeDifferentials q.relativeDifferentials
  let d := (f.relativeDifferentialsHomEquiv _).symm D
  have he (c : (Modules.tensorPullback p).obj f.relativeDifferentials ⟶
      q.relativeDifferentials) (U : X.Opens) (a : Γ(X, U)) :
      (e c).val.app (op U) (f.relativeDifferentialsDerivation.d a) =
        c.app (p ⁻¹ᵁ U) (Modules.tensorPullbackSection p f.relativeDifferentials U
          (f.relativeDifferentialsDerivation.d a)) := by
    rw [Adjunction.homEquiv_unit]
    change c.app (p ⁻¹ᵁ U) ((adj.unit.app f.relativeDifferentials).app U
      (f.relativeDifferentialsDerivation.d a)) = _
    rw [hadj.1]
  refine ⟨e.symm d, ?_, ?_⟩
  · intro U a
    rw [← he, Equiv.apply_symm_apply]
    exact f.relativeDifferentialsHomEquiv_symm_app_d D a
  · intro c hc
    apply e.injective
    rw [Equiv.apply_symm_apply]
    apply (f.relativeDifferentialsHomEquiv _).injective
    ext U a
    exact (he c U.unop a).trans (hc U.unop a) |>.trans
      (f.relativeDifferentialsHomEquiv_symm_app_d D a).symm

/-- Finite generation on affine-pair charts descends by the affine finite-type criterion. -/
private theorem differentials_finiteType {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] : f.relativeDifferentials.IsFiniteType := by
  choose V hV U hU hxU hUV using f.exists_isAffineOpen_le_preimage
  have hcover : (⨆ x, U x) = ⊤ := eq_top_iff.2 fun x _ ↦
    TopologicalSpace.Opens.mem_iSup.2 ⟨x, hxU x⟩
  have hcriterion := ((Modules.quasicoherent_finite_type_affine X).2
    f.relativeDifferentials inferInstance).2.1
  refine (hcriterion X U hcover hU ?_).1
  intro x
  let φ := f.appLE (V x) (U x) (hUV x)
  let := φ.hom.toAlgebra
  have : Algebra.FiniteType Γ(S, V x) Γ(X, U x) := f.finiteType_appLE (hV x) (hU x) _
  have : Module.Finite Γ(X, U x) (CommRingCat.KaehlerDifferential φ) := by
    dsimp [CommRingCat.KaehlerDifferential]
    infer_instance
  obtain ⟨e, _⟩ := relativeDifferentials_affine_sections f ⟨U x, hU x⟩
    ⟨V x, hV x⟩ (hUV x)
  exact Module.Finite.equiv e

/-- The fibre product of an affine triple is affine and its section rings form a pushout. -/
private theorem affine_baseChange_geometry {X S T : Scheme.{u}}
    (f : X ⟶ S) (g : T ⟶ S) (U : X.affineOpens) (V : S.affineOpens)
    (V' : T.affineOpens) (hU : U.1 ≤ f ⁻¹ᵁ V.1) (hV' : V'.1 ≤ g ⁻¹ᵁ V.1) :
    IsAffineOpen (relativeDifferentialsBaseChangeOpen f g U.1 V'.1) ∧
      IsPushout (f.appLE V.1 U.1 hU) (g.appLE V.1 V'.1 hV')
        ((pullback.fst f g).appLE U.1
          (relativeDifferentialsBaseChangeOpen f g U.1 V'.1) inf_le_left)
        ((pullback.snd f g).appLE V'.1
          (relativeDifferentialsBaseChangeOpen f g U.1 V'.1) inf_le_right) := by
  have : IsAffine U.1.toScheme := U.2
  have : IsAffine V.1.toScheme := V.2
  have : IsAffine V'.1.toScheme := V'.2
  have hsq := Scheme.Hom.isPullback_resLE (IsPullback.of_hasPullback f g) hV' hU rfl
  have hW : IsAffineOpen (relativeDifferentialsBaseChangeOpen f g U.1 V'.1) :=
    .of_isIso hsq.isoPullback.hom
  have hpo := (isIso_pushoutSection_iff (IsPullback.of_hasPullback f g) hV' hU rfl).mp
    (isIso_pushoutSection_of_isAffineOpen (IsPullback.of_hasPullback f g)
      hV' hU rfl V.2 V'.2 U.2)
  exact ⟨hW, hpo⟩

/-- Transport the ring base-change equivalence to ModuleCat scalar extension. -/
private theorem ring_baseChange {R A R' A' : CommRingCat.{u}}
    (r : R ⟶ A) (s : R ⟶ R') (p : A ⟶ A') (q : R' ⟶ A')
    (h : IsPushout r s p q) :
    ∃ β : (ModuleCat.extendScalars p.hom).obj
        (CommRingCat.KaehlerDifferential r) ≃ₗ[A'] CommRingCat.KaehlerDifferential q,
      ∀ (b : A') (a : A),
        β (b ⊗ₜ[A,p.hom] (CommRingCat.KaehlerDifferential.d a)) =
          b • CommRingCat.KaehlerDifferential.d (p a) := by
  let : Algebra R A := r.hom.toAlgebra
  let : Algebra R R' := s.hom.toAlgebra
  let : Algebra A A' := p.hom.toAlgebra
  let : Algebra R' A' := q.hom.toAlgebra
  let : Algebra R A' := (r ≫ p).hom.toAlgebra
  have : IsScalarTower R A A' := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower R R' A' := IsScalarTower.of_algebraMap_eq' (by
    exact congrArg CommRingCat.Hom.hom h.w)
  have : Algebra.IsPushout R R' A A' := CommRingCat.isPushout_iff_isPushout.mp h.flip
  let e := ModuleCat.tensorEquivExtendScalars A A' (CommRingCat.KaehlerDifferential r)
  refine ⟨e.symm ≪≫ₗ KaehlerDifferential.tensorKaehlerEquiv R R' A A', ?_⟩
  intro b a
  change KaehlerDifferential.tensorKaehlerEquiv R R' A A'
    (e.symm (b ⊗ₜ[A,p.hom] (CommRingCat.KaehlerDifferential.d a))) = _
  have he : e (b ⊗ₜ[A] (CommRingCat.KaehlerDifferential.d a)) =
      b ⊗ₜ[A,p.hom] (CommRingCat.KaehlerDifferential.d a) :=
    ModuleCat.tensorEquivExtendScalars_tmul _ _ _ _ _
  rw [← he, e.symm_apply_apply]
  exact KaehlerDifferential.tensorKaehlerEquiv_tmul_D _ _ _ _ b a

/-- Normalize the existing affine pullback-sections equivalence for scalar extension. -/
private theorem affine_tensor_sections {X Y : Scheme.{u}} (p : Y ⟶ X)
    (U : X.affineOpens) (W : Y.affineOpens) (hWU : W.1 ≤ p ⁻¹ᵁ U.1)
    (F : X.Modules) [F.IsQuasicoherent] :
    ∃ α : (ModuleCat.extendScalars (p.appLE U.1 W.1 hWU).hom).obj
        (ModuleCat.of Γ(X, U.1) Γ(F, U.1)) ≃ₗ[Γ(Y, W.1)]
          Γ((Modules.tensorPullback p).obj F, W.1),
      ∀ m : Γ(F, U.1),
        α ((1 : Γ(Y, W.1)) ⊗ₜ[Γ(X, U.1),(p.appLE U.1 W.1 hWU).hom] m) =
          ((Modules.tensorPullback p).obj F).presheaf.map (homOfLE hWU).op
            (Modules.tensorPullbackSection p F U.1 m) := by
  classical
  let ρ := p.appLE U.1 W.1 hWU
  let : Algebra Γ(X, U.1) Γ(Y, W.1) := ρ.hom.toAlgebra
  let : ∀ G : X.Modules, Module Γ(X, U.1) Γ((Modules.tensorPullback p).obj G, W.1) :=
    fun G ↦ Module.compHom _ ρ.hom
  obtain ⟨c, hc, hlin, hp, _⟩ := Modules.exists_tensorPullback_affine_sections p U W hWU
  let e := ModuleCat.tensorEquivExtendScalars Γ(X, U.1) Γ(Y, W.1)
    (ModuleCat.of Γ(X, U.1) Γ(F, U.1))
  let swap := TensorProduct.comm Γ(X, U.1) Γ(F, U.1) Γ(Y, W.1)
  let d : (ModuleCat.extendScalars ρ.hom).obj
      (ModuleCat.of Γ(X, U.1) Γ(F, U.1)) →ₗ[Γ(Y, W.1)]
        Γ((Modules.tensorPullback p).obj F, W.1) :=
    { toFun := fun z ↦ c F inferInstance (swap.symm (e.symm z))
      map_add' := fun a b ↦ by simp only [map_add]
      map_smul' := fun b z ↦ by
        rw [map_smul]
        simpa only [swap, LinearEquiv.apply_symm_apply, RingHom.id_apply] using
          hlin F inferInstance b (swap.symm (e.symm z)) }
  have hd : Function.Bijective d :=
    (hc F inferInstance).comp (swap.symm.bijective.comp e.symm.bijective)
  refine ⟨LinearEquiv.ofBijective d hd, ?_⟩
  intro m
  change c F inferInstance (swap.symm
    (e.symm ((1 : Γ(Y, W.1)) ⊗ₜ[Γ(X, U.1),ρ.hom] m))) = _
  have he : e ((1 : Γ(Y, W.1)) ⊗ₜ[Γ(X, U.1)] m) =
      (1 : Γ(Y, W.1)) ⊗ₜ[Γ(X, U.1),ρ.hom] m :=
    ModuleCat.tensorEquivExtendScalars_tmul _ _ _ _ _
  rw [← he, e.symm_apply_apply]
  change c F inferInstance (m ⊗ₜ[Γ(X, U.1)] (1 : Γ(Y, W.1))) = _
  rw [hp, one_smul]
  congr 1
  exact (Classical.choose_spec (Modules.exists_tensorPullbackAdjunction p)) F (op U.1) m

/-- Identify the global map on affine charts, using the universal properties to check
equality on differential generators. -/
private theorem affine_baseChange_comparison {X S T : Scheme.{u}}
    (f : X ⟶ S) (g : T ⟶ S)
    (c : (Modules.tensorPullback (pullback.fst f g)).obj f.relativeDifferentials ⟶
      (pullback.snd f g).relativeDifferentials)
    (hc : ∀ (U : X.Opens) (a : Γ(X, U)),
      c.app ((pullback.fst f g) ⁻¹ᵁ U)
        (Modules.tensorPullbackSection (pullback.fst f g) f.relativeDifferentials U
          (f.relativeDifferentialsDerivation.d (X := op U) a)) =
        (pullback.snd f g).relativeDifferentialsDerivation.d
          (X := op ((pullback.fst f g) ⁻¹ᵁ U)) ((pullback.fst f g).app U a)) :
    ∀ (U : X.affineOpens) (V : S.affineOpens) (V' : T.affineOpens)
          (hU : U.1 ≤ f ⁻¹ᵁ V.1) (hV' : V'.1 ≤ g ⁻¹ᵁ V.1),
        IsAffineOpen (relativeDifferentialsBaseChangeOpen f g U.1 V'.1) ∧
        IsPushout (f.appLE V.1 U.1 hU) (g.appLE V.1 V'.1 hV')
          ((pullback.fst f g).appLE U.1
            (relativeDifferentialsBaseChangeOpen f g U.1 V'.1) inf_le_left)
          ((pullback.snd f g).appLE V'.1
            (relativeDifferentialsBaseChangeOpen f g U.1 V'.1) inf_le_right) ∧
        ∃ α : (ModuleCat.extendScalars
            ((pullback.fst f g).appLE U.1
              (relativeDifferentialsBaseChangeOpen f g U.1 V'.1) inf_le_left).hom).obj
                (CommRingCat.KaehlerDifferential (f.appLE V.1 U.1 hU)) ≃ₗ[
                  Γ(pullback f g, relativeDifferentialsBaseChangeOpen f g U.1 V'.1)]
                    Γ((Modules.tensorPullback (pullback.fst f g)).obj f.relativeDifferentials,
                      relativeDifferentialsBaseChangeOpen f g U.1 V'.1),
        ∃ δ : CommRingCat.KaehlerDifferential
            ((pullback.snd f g).appLE V'.1
              (relativeDifferentialsBaseChangeOpen f g U.1 V'.1) inf_le_right) ≃ₗ[
                Γ(pullback f g, relativeDifferentialsBaseChangeOpen f g U.1 V'.1)]
                  Γ((pullback.snd f g).relativeDifferentials,
                    relativeDifferentialsBaseChangeOpen f g U.1 V'.1),
        ∃ β : (ModuleCat.extendScalars
            ((pullback.fst f g).appLE U.1
              (relativeDifferentialsBaseChangeOpen f g U.1 V'.1) inf_le_left).hom).obj
                (CommRingCat.KaehlerDifferential (f.appLE V.1 U.1 hU)) ≃ₗ[
                  Γ(pullback f g, relativeDifferentialsBaseChangeOpen f g U.1 V'.1)]
                    CommRingCat.KaehlerDifferential
                      ((pullback.snd f g).appLE V'.1
                        (relativeDifferentialsBaseChangeOpen f g U.1 V'.1) inf_le_right),
          (∀ a : Γ(X, U.1),
            α ((1 : Γ(pullback f g, relativeDifferentialsBaseChangeOpen f g U.1 V'.1))
                ⊗ₜ[Γ(X, U.1),
                ((pullback.fst f g).appLE U.1
                  (relativeDifferentialsBaseChangeOpen f g U.1 V'.1) inf_le_left).hom]
                    (CommRingCat.KaehlerDifferential.d a)) =
              ((Modules.tensorPullback (pullback.fst f g)).obj
                f.relativeDifferentials).presheaf.map (homOfLE inf_le_left).op
                  (Modules.tensorPullbackSection (pullback.fst f g) f.relativeDifferentials U.1
                    (f.relativeDifferentialsDerivation.d (X := op U.1) a))) ∧
          (∀ z : Γ(pullback f g, relativeDifferentialsBaseChangeOpen f g U.1 V'.1),
            δ (CommRingCat.KaehlerDifferential.d z) =
              (pullback.snd f g).relativeDifferentialsDerivation.d
                (X := op (relativeDifferentialsBaseChangeOpen f g U.1 V'.1)) z) ∧
          (∀ (b : Γ(pullback f g, relativeDifferentialsBaseChangeOpen f g U.1 V'.1))
              (a : Γ(X, U.1)),
            β (b ⊗ₜ[Γ(X, U.1),
                ((pullback.fst f g).appLE U.1
                  (relativeDifferentialsBaseChangeOpen f g U.1 V'.1) inf_le_left).hom]
                    (CommRingCat.KaehlerDifferential.d a)) =
              b • CommRingCat.KaehlerDifferential.d
                ((pullback.fst f g).appLE U.1
                  (relativeDifferentialsBaseChangeOpen f g U.1 V'.1) inf_le_left a)) ∧
          (∀ x, c.app (relativeDifferentialsBaseChangeOpen f g U.1 V'.1) (α x) = δ (β x)) := by
  intro U V V' hU hV'
  obtain ⟨hW, hpo⟩ := affine_baseChange_geometry f g U V V' hU hV'
  refine ⟨hW, hpo, ?_⟩
  let W := relativeDifferentialsBaseChangeOpen f g U.1 V'.1
  let p := pullback.fst f g
  let q := pullback.snd f g
  let ρ := p.appLE U.1 W inf_le_left
  obtain ⟨e, he⟩ := relativeDifferentials_affine_sections f U V hU
  obtain ⟨α₀, hα₀⟩ := affine_tensor_sections p U ⟨W, hW⟩ inf_le_left
    f.relativeDifferentials
  let α := ((ModuleCat.extendScalars ρ.hom).mapIso e.toModuleIso).toLinearEquiv ≪≫ₗ α₀
  have hα (a : Γ(X, U.1)) :
      α ((1 : Γ(pullback f g, W)) ⊗ₜ[Γ(X, U.1),ρ.hom]
        (CommRingCat.KaehlerDifferential.d a)) =
      ((Modules.tensorPullback p).obj f.relativeDifferentials).presheaf.map
        (homOfLE inf_le_left).op (Modules.tensorPullbackSection p f.relativeDifferentials U.1
          (f.relativeDifferentialsDerivation.d a)) := by
    change α₀ ((1 : Γ(pullback f g, W)) ⊗ₜ[Γ(X, U.1),ρ.hom]
      (e (CommRingCat.KaehlerDifferential.d a))) = _
    rw [he, hα₀]
  obtain ⟨δ, hδ⟩ := relativeDifferentials_affine_sections q ⟨W, hW⟩ V' inf_le_right
  obtain ⟨β, hβ⟩ := ring_baseChange (f.appLE V.1 U.1 hU) (g.appLE V.1 V'.1 hV')
    ρ (q.appLE V'.1 W inf_le_right) hpo
  refine ⟨α, δ, β, hα, hδ, hβ, ?_⟩
  let L : (ModuleCat.extendScalars ρ.hom).obj
      (CommRingCat.KaehlerDifferential (f.appLE V.1 U.1 hU)) ⟶
      ModuleCat.of Γ(pullback f g, W) Γ(q.relativeDifferentials, W) :=
    ModuleCat.ofHom ((c.appₗ W).comp α.toLinearMap)
  let R : (ModuleCat.extendScalars ρ.hom).obj
      (CommRingCat.KaehlerDifferential (f.appLE V.1 U.1 hU)) ⟶
      ModuleCat.of Γ(pullback f g, W) Γ(q.relativeDifferentials, W) :=
    β.toModuleIso.hom ≫ δ.toModuleIso.hom
  have hLR : L = R := by
    apply ((ModuleCat.extendRestrictScalarsAdj ρ.hom).homEquiv _ _).injective
    apply CommRingCat.KaehlerDifferential.ext
    intro a
    rw [ModuleCat.extendRestrictScalarsAdj_homEquiv_apply,
      ModuleCat.extendRestrictScalarsAdj_homEquiv_apply]
    change c.app W (α ((1 : Γ(pullback f g, W)) ⊗ₜ[Γ(X, U.1),ρ.hom]
        (CommRingCat.KaehlerDifferential.d a))) =
      δ (β ((1 : Γ(pullback f g, W)) ⊗ₜ[Γ(X, U.1),ρ.hom]
        (CommRingCat.KaehlerDifferential.d a)))
    rw [hα, hβ, one_smul, hδ]
    have hn := congrArg (fun k ↦ k
      (Modules.tensorPullbackSection p f.relativeDifferentials U.1
        (f.relativeDifferentialsDerivation.d a)))
      (c.val.naturality (homOfLE (show W ≤ p ⁻¹ᵁ U.1 from inf_le_left)).op)
    change c.app W
      (((Modules.tensorPullback p).obj f.relativeDifferentials).presheaf.map _ _) =
      q.relativeDifferentials.presheaf.map _ (c.app (p ⁻¹ᵁ U.1) _) at hn
    rw [hn, hc]
    exact (q.relativeDifferentialsDerivation.d_map _ (p.app U.1 a)).symm
  intro x
  change L x = R x
  exact congrArg (fun k ↦ k x) hLR

/-- Relative differentials are quasi-coherent, their canonically normalized cartesian
base-change map is an isomorphism, and they have finite type for a locally finite-type
morphism. On every affine triple the map is `b ⊗ da ↦ b d(1 ⊗ a)`. -/
theorem relativeDifferentialSheaf_baseChange {X S T : Scheme.{u}}
    (f : X ⟶ S) (g : T ⟶ S) :
    f.relativeDifferentials.IsQuasicoherent ∧
    (pullback.snd f g).relativeDifferentials.IsQuasicoherent ∧
    ∃ c : (Modules.tensorPullback (pullback.fst f g)).obj f.relativeDifferentials ⟶
        (pullback.snd f g).relativeDifferentials,
      (∀ (U : X.Opens) (a : Γ(X, U)),
        c.app ((pullback.fst f g) ⁻¹ᵁ U)
          (Modules.tensorPullbackSection (pullback.fst f g) f.relativeDifferentials U
            (f.relativeDifferentialsDerivation.d (X := op U) a)) =
          (pullback.snd f g).relativeDifferentialsDerivation.d
            (X := op ((pullback.fst f g) ⁻¹ᵁ U)) ((pullback.fst f g).app U a)) ∧
      (∀ c' : (Modules.tensorPullback (pullback.fst f g)).obj f.relativeDifferentials ⟶
          (pullback.snd f g).relativeDifferentials,
        (∀ (U : X.Opens) (a : Γ(X, U)),
          c'.app ((pullback.fst f g) ⁻¹ᵁ U)
            (Modules.tensorPullbackSection (pullback.fst f g) f.relativeDifferentials U
              (f.relativeDifferentialsDerivation.d (X := op U) a)) =
            (pullback.snd f g).relativeDifferentialsDerivation.d
              (X := op ((pullback.fst f g) ⁻¹ᵁ U)) ((pullback.fst f g).app U a)) →
          c' = c) ∧
      IsIso c ∧
      (∀ (U : X.affineOpens) (V : S.affineOpens) (V' : T.affineOpens)
          (hU : U.1 ≤ f ⁻¹ᵁ V.1) (hV' : V'.1 ≤ g ⁻¹ᵁ V.1),
        IsAffineOpen (relativeDifferentialsBaseChangeOpen f g U.1 V'.1) ∧
        IsPushout (f.appLE V.1 U.1 hU) (g.appLE V.1 V'.1 hV')
          ((pullback.fst f g).appLE U.1
            (relativeDifferentialsBaseChangeOpen f g U.1 V'.1) inf_le_left)
          ((pullback.snd f g).appLE V'.1
            (relativeDifferentialsBaseChangeOpen f g U.1 V'.1) inf_le_right) ∧
        ∃ α : (ModuleCat.extendScalars
            ((pullback.fst f g).appLE U.1
              (relativeDifferentialsBaseChangeOpen f g U.1 V'.1) inf_le_left).hom).obj
                (CommRingCat.KaehlerDifferential (f.appLE V.1 U.1 hU)) ≃ₗ[
                  Γ(pullback f g, relativeDifferentialsBaseChangeOpen f g U.1 V'.1)]
                    Γ((Modules.tensorPullback (pullback.fst f g)).obj f.relativeDifferentials,
                      relativeDifferentialsBaseChangeOpen f g U.1 V'.1),
        ∃ δ : CommRingCat.KaehlerDifferential
            ((pullback.snd f g).appLE V'.1
              (relativeDifferentialsBaseChangeOpen f g U.1 V'.1) inf_le_right) ≃ₗ[
                Γ(pullback f g, relativeDifferentialsBaseChangeOpen f g U.1 V'.1)]
                  Γ((pullback.snd f g).relativeDifferentials,
                    relativeDifferentialsBaseChangeOpen f g U.1 V'.1),
        ∃ β : (ModuleCat.extendScalars
            ((pullback.fst f g).appLE U.1
              (relativeDifferentialsBaseChangeOpen f g U.1 V'.1) inf_le_left).hom).obj
                (CommRingCat.KaehlerDifferential (f.appLE V.1 U.1 hU)) ≃ₗ[
                  Γ(pullback f g, relativeDifferentialsBaseChangeOpen f g U.1 V'.1)]
                    CommRingCat.KaehlerDifferential
                      ((pullback.snd f g).appLE V'.1
                        (relativeDifferentialsBaseChangeOpen f g U.1 V'.1) inf_le_right),
          (∀ a : Γ(X, U.1),
            α ((1 : Γ(pullback f g, relativeDifferentialsBaseChangeOpen f g U.1 V'.1))
                ⊗ₜ[Γ(X, U.1),
                ((pullback.fst f g).appLE U.1
                  (relativeDifferentialsBaseChangeOpen f g U.1 V'.1) inf_le_left).hom]
                    (CommRingCat.KaehlerDifferential.d a)) =
              ((Modules.tensorPullback (pullback.fst f g)).obj
                f.relativeDifferentials).presheaf.map (homOfLE inf_le_left).op
                  (Modules.tensorPullbackSection (pullback.fst f g) f.relativeDifferentials U.1
                    (f.relativeDifferentialsDerivation.d (X := op U.1) a))) ∧
          (∀ z : Γ(pullback f g, relativeDifferentialsBaseChangeOpen f g U.1 V'.1),
            δ (CommRingCat.KaehlerDifferential.d z) =
              (pullback.snd f g).relativeDifferentialsDerivation.d
                (X := op (relativeDifferentialsBaseChangeOpen f g U.1 V'.1)) z) ∧
          (∀ (b : Γ(pullback f g, relativeDifferentialsBaseChangeOpen f g U.1 V'.1))
              (a : Γ(X, U.1)),
            β (b ⊗ₜ[Γ(X, U.1),
                ((pullback.fst f g).appLE U.1
                  (relativeDifferentialsBaseChangeOpen f g U.1 V'.1) inf_le_left).hom]
                    (CommRingCat.KaehlerDifferential.d a)) =
              b • CommRingCat.KaehlerDifferential.d
                ((pullback.fst f g).appLE U.1
                  (relativeDifferentialsBaseChangeOpen f g U.1 V'.1) inf_le_left a)) ∧
          (∀ x, c.app (relativeDifferentialsBaseChangeOpen f g U.1 V'.1) (α x) = δ (β x))) ∧
      (LocallyOfFiniteType f →
        f.relativeDifferentials.IsFiniteType ∧
          (pullback.snd f g).relativeDifferentials.IsFiniteType) := by
  classical
  obtain ⟨c, hc, huniq⟩ := existsUnique_baseChangeMap f g
  refine ⟨inferInstance, inferInstance, c, hc, huniq, ?_,
    affine_baseChange_comparison f g c hc, ?_⟩
  · let p := pullback.fst f g
    let q := pullback.snd f g
    let e := (Modules.tensorPullbackSectionAdjunction p).leftAdjointUniq
      (Modules.pullbackPushforwardAdjunction p)
    have : ((Modules.tensorPullback p).obj f.relativeDifferentials).IsQuasicoherent :=
      (SheafOfModules.isQuasicoherent (pullback f g).ringCatSheaf).prop_of_iso
        (e.app f.relativeDifferentials).symm
        (inferInstance : ((Modules.pullback p).obj f.relativeDifferentials).IsQuasicoherent)
    have charts (z : (pullback f g : Scheme.{u})) :
        ∃ (U : X.affineOpens) (V : S.affineOpens) (V' : T.affineOpens)
          (hU : U.1 ≤ f ⁻¹ᵁ V.1) (hV' : V'.1 ≤ g ⁻¹ᵁ V.1),
          z ∈ relativeDifferentialsBaseChangeOpen f g U.1 V'.1 := by
      obtain ⟨V, hV, U, hU, hzU, hUV⟩ := f.exists_isAffineOpen_le_preimage (p z)
      have hzV : q z ∈ g ⁻¹ᵁ V := by
        have hw := congrArg (fun k : pullback f g ⟶ S ↦ k z)
          (pullback.condition (f := f) (g := g))
        change f (p z) = g (q z) at hw
        change g (q z) ∈ V
        rw [← hw]
        exact hUV hzU
      obtain ⟨_, ⟨V', hV', rfl⟩, hzV', hV'V⟩ :=
        T.isBasis_affineOpens.exists_subset_of_mem_open hzV (g ⁻¹ᵁ V).isOpen
      exact ⟨⟨U, hU⟩, ⟨V, hV⟩, ⟨V', hV'⟩, hUV, hV'V, hzU, hzV'⟩
    choose U V V' hU hV' hz using charts
    let W := fun z ↦ relativeDifferentialsBaseChangeOpen f g (U z).1 (V' z).1
    apply Modules.Hom.isIso_of_bijective_on_affine_open_cover c W
      (eq_top_iff.2 fun z _ ↦ TopologicalSpace.Opens.mem_iSup.2 ⟨z, hz z⟩)
    · intro z
      exact (affine_baseChange_geometry f g (U z) (V z) (V' z) (hU z) (hV' z)).1
    · intro z
      obtain ⟨_, _, α, δ, β, _, _, _, hcomm⟩ :=
        affine_baseChange_comparison f g c hc (U z) (V z) (V' z) (hU z) (hV' z)
      have heq : (fun x ↦ c.app (W z) x) = fun x ↦ δ (β (α.symm x)) := by
        funext x
        simpa only [LinearEquiv.apply_symm_apply] using hcomm (α.symm x)
      change Function.Bijective (fun x ↦ c.app (W z) x)
      rw [heq]
      exact δ.bijective.comp (β.bijective.comp α.symm.bijective)
  · intro hf
    have := hf
    exact ⟨differentials_finiteType f, differentials_finiteType (pullback.snd f g)⟩

end AlgebraicGeometry.Scheme.Hom
