/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.DivisorIdealSheaf
public import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveStructureSheaf
public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsRightExact
public import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
import WeilConjectures.AlgebraicGeometry.EtaleTensorUnitRestrictionEquation
import WeilConjectures.AlgebraicGeometry.FlatModulePullbackExact
import WeilConjectures.AlgebraicGeometry.ClosedSubschemeBaseChangeIdealImage
import Mathlib.Algebra.Category.Grp.Kernels

/-! # The sectionwise kernel of restriction to a closed subscheme
(blueprint: lem-sc-etale-ideal-sections-kernel)
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme

noncomputable section

/-- The unlifted additive structure presheaf. -/
def etaleStructureAdditivePresheaf (X : Scheme.{u}) : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u} :=
  X.etaleStructurePresheaf ⋙ forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat

/-- The canonical structure-module coordinates on tensor sections. -/
def etaleTensorUnitCoordinates (X : Scheme.{u}) :
    Modules.etaleTensorSectionsPresheaf (SheafOfModules.unit X.ringCatSheaf) ⟶
      etaleStructureAdditivePresheaf X where
  app U := (Modules.tensorPullbackObjUnitToUnit U.unop.hom).app ⊤
  naturality {U V} g := by
    apply AddCommGrpCat.ext
    intro x
    exact Modules.etaleTensorUnitRestriction_equation g.unop x

/-- Tensor sections of an ideal included in additive structure functions.
All data are the specified ideal inclusion and the adjoint structure-module map. -/
def etaleIdealSectionsInclusion {X : Scheme.{u}} (I : X.IdealSheafData) :
    (Modules.etaleTensorSectionsPresheaf I.toModules ⋙
      AddCommGrpCat.uliftFunctor.{u + 1, u}) ⟶ X.etaleAdditiveSheaf.obj :=
  Functor.whiskerRight
    ((Modules.etaleTensorSectionsPresheafFunctor X).map I.toModulesι ≫
      etaleTensorUnitCoordinates X) AddCommGrpCat.uliftFunctor.{u + 1, u}

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pulledIdealCoordinates_range {X Y : Scheme.{u}} (g : Y ⟶ X)
    [Flat g] (I : X.IdealSheafData) :
    let φ := (Modules.tensorPullback g).map I.toModulesι ≫
      Modules.tensorPullbackObjUnitToUnit g
    Function.Injective (φ.app ⊤) ∧
      Set.range (φ.app ⊤) =
        {x | (pullback.fst g I.subschemeι).appTop x = 0} := by
  classical
  dsimp only
  let T := Modules.tensorPullback g
  let a := Classical.choice (Modules.nonempty_tensorPullbackAdjunction g)
  let a₀ := Classical.choose (Modules.exists_tensorPullbackAdjunction g)
  let c := a.leftAdjointUniq a₀
  let ε := (a.homEquiv (SheafOfModules.unit X.ringCatSheaf)
    (SheafOfModules.unit Y.ringCatSheaf)).symm
      (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom)
  have hε : ε = (c.app (SheafOfModules.unit X.ringCatSheaf)).hom ≫
      Modules.tensorPullbackObjUnitToUnit g := by
    dsimp [ε, Modules.tensorPullbackObjUnitToUnit]
    rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
    rw [← c.hom.naturality_assoc, Adjunction.leftAdjointUniq_hom_app_counit]
  let q := pullback.fst g I.subschemeι
  have hker : (pullback.snd I.subschemeι g).ker = q.ker := by
    rw [← Scheme.Hom.ker_comp_of_isIso (pullbackSymmetry I.subschemeι g).hom q,
      pullbackSymmetry_hom_comp_fst]
  let φ := T.map I.toModulesι ≫ Modules.tensorPullbackObjUnitToUnit g
  have himg : Subobject.mk q.ker.toModulesι = imageSubobject φ := by
    have h := (closedSubscheme_baseChange_ideal_image I.subschemeι g).2
    rw [hker, I.ker_subschemeι] at h
    change Subobject.mk q.ker.toModulesι = imageSubobject (T.map I.toModulesι ≫ ε) at h
    have hn : T.map I.toModulesι ≫ (c.app _).hom =
        (c.app I.toModules).hom ≫ T.map I.toModulesι :=
      c.hom.naturality I.toModulesι
    rw [hε, ← Category.assoc, hn, Category.assoc, imageSubobject_iso_comp] at h
    exact h
  have : PreservesFiniteLimits T := (flat_module_pullback_exact_pushforward_injective g).1.1
  have : IsIso (Modules.tensorPullbackObjUnitToUnit g) :=
    (Modules.tensorPullbackObjUnitToUnit_isIso g).1
  have : Mono φ := inferInstance
  have hm : Subobject.mk φ = Subobject.mk q.ker.toModulesι := by
    exact (imageSubobject_mono φ).symm.trans himg.symm
  let k := Subobject.isoOfMkEqMk φ q.ker.toModulesι hm
  have hk : k.hom ≫ q.ker.toModulesι = φ := by simp [k]
  have hkapp : (k.hom.app ⊤) ≫ q.ker.toModulesι.app ⊤ = φ.app ⊤ := by
    exact congrArg (fun ψ ↦ ψ.app ⊤) hk
  have hinj : Function.Injective (φ.app ⊤) := by
    rw [← hkapp]
    exact (q.ker.injective_toModulesι_app ⊤).comp
      (ConcreteCategory.bijective_of_isIso (k.hom.app ⊤)).1
  refine ⟨hinj, ?_⟩
  rw [← hkapp]
  change Set.range ((q.ker.toModulesι.app ⊤) ∘ (k.hom.app ⊤)) = _
  rw [Set.range_comp, Set.range_eq_univ.mpr
    (ConcreteCategory.bijective_of_isIso (k.hom.app ⊤)).2, Set.image_univ,
    q.ker.range_toModulesι_app_eq]
  ext x
  change q.ker.subschemeι.app ⊤ x = 0 ↔ q.appTop x = 0
  have hq : q.appTop = q.ker.subschemeι.appTop ≫ q.toImage.appTop := by
    rw [← Scheme.Hom.comp_appTop, q.toImage_imageι]
  rw [hq]
  change _ = 0 ↔ q.toImage.appTop (q.ker.subschemeι.appTop x) = 0
  exact (map_eq_zero_iff q.toImage.appTop.hom
    (ConcreteCategory.bijective_of_isIso q.toImage.appTop).1).symm

/-- On every etale object, the canonical map from pulled-back ideal sections is the
kernel of restriction to the base-changed closed subscheme.
Source: blueprint `lemma-cohomology-multiplicative-group--6`, Proof, Step 1 and its Claim.
(blueprint: lem-sc-etale-ideal-sections-kernel)

Proof: Flat module pullback preserves finite limits, so the pulled-back ideal
inclusion is monic. Compose it with the canonical structure-module isomorphism.
The base-change ideal-image theorem identifies its image subobject with the
kernel ideal of the base-changed closed immersion. Its choice of adjunction is
removed using leftAdjointUniq: naturality makes the alternative composite differ
by precomposition with an isomorphism, which leaves its image unchanged.
Pullback symmetry identifies the two choices of base-change projection.
Since the composite is monic, the image equality gives a unique isomorphism from
the pulled-back ideal module to the specified kernel ideal module, compatible
with inclusion into the structure module. Evaluate at the top open: this gives
an injective map whose range is the kernel of restriction to the kernel ideal's
closed subscheme. The actual closed immersion factors through this subscheme by
toImage, an isomorphism, so its map on global sections is injective and the same
range is the kernel of restriction to the actual fibre product. Corestrict the
section map to this additive kernel; it is bijective and hence gives an additive
isomorphism to the concrete kernel group. Transport the concrete limiting kernel
fork along that isomorphism and apply the limit-preserving additive universe lift.
On the empty object all groups are zero. For I=0 restriction is the identity and
its kernel is zero; for I=top the closed subscheme is empty and the inclusion is
an isomorphism. No finiteness or dimension assumption is used. -/
theorem etaleIdealSectionsInclusion_isKernel {X : Scheme.{u}} (I : X.IdealSheafData)
    (U : X.Etaleᵒᵖ) :
    ∃ h : (etaleIdealSectionsInclusion I).app U ≫
        (etaleAdditiveSheafToLowerStar I.subschemeι).hom.app U = 0,
      Nonempty (IsLimit (KernelFork.ofι (etaleIdealSectionsInclusion I |>.app U) h)) := by
  classical
  let g := U.unop.hom
  let l := ((Modules.tensorPullback g).map I.toModulesι ≫
    Modules.tensorPullbackObjUnitToUnit g).app ⊤
  let f := AddCommGrpCat.ofHom
    (pullback.fst g I.subschemeι).appTop.hom.toAddMonoidHom
  obtain ⟨hinj, hrange⟩ := pulledIdealCoordinates_range g I
  have hz : l ≫ f = 0 := by
    apply AddCommGrpCat.ext
    intro x
    exact hrange.subset ⟨x, rfl⟩
  let a := l.hom.codRestrict f.hom.ker (fun x ↦
    AddMonoidHom.mem_ker.mpr (ConcreteCategory.congr_hom hz x))
  have ha : Function.Bijective a := by
    constructor
    · intro x y h
      exact hinj (congrArg Subtype.val h)
    · intro y
      obtain ⟨x, hx⟩ := hrange.superset y.property
      exact ⟨x, Subtype.ext hx⟩
  let e : (Modules.etaleTensorSectionsPresheaf I.toModules).obj U ≅
      AddCommGrpCat.of f.hom.ker := (AddEquiv.ofBijective a ha).toAddCommGrpIso
  have he : e.hom ≫ (AddCommGrpCat.kernelCone f).ι = l := by
    ext x
    rfl
  let hlim := IsKernel.isoKernel f l (AddCommGrpCat.kernelIsLimit f) e he
  let L := AddCommGrpCat.uliftFunctor.{u + 1, u}
  change ∃ h : L.map l ≫ L.map f = 0,
    Nonempty (IsLimit (KernelFork.ofι (L.map l) h))
  exact ⟨(KernelFork.ofι l hz).map_condition L,
    ⟨(KernelFork.ofι l hz).mapIsLimit hlim L⟩⟩

end
end AlgebraicGeometry.Scheme
