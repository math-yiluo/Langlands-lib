/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.Signed.SignedLinePullbackNormalization
public import WeilConjectures.Algebra.Homology.Finite.FiniteFreeDualPullback
public import WeilConjectures.Algebra.Homology.SmoothPurity.PullbackExistsOfUniverses
public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all WeilConjectures.Algebra.Homology.Signed.SignedLineScalarTensorTower
import WeilConjectures.Algebra.Homology.RingedSitePullback.PullbackLocalizationOfUniverses

/-! # Scalar-square compatibility of normalized signed pullbacks

Source: Stacks Project, Modules on Sites, Tags 03EL, 0GMX and 04J0.
(blueprint: lem-pur-signed-line-scalar-pullback-naturality)
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {U : C ⥤ D} [U.IsContinuous J K]
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  [HasWeakSheafify K AddCommGrpCat.{max u v w}]

attribute [local irreducible] changeOfRingsOfUniverses scalarExtensionSection
  siteSheafTensorRight siteSheafTensorTmul

set_option allowUnsafeReducibility true in
attribute [local reducible] sheafCompose ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj' SheafOfModules.unit PresheafOfModules.unit
  PresheafOfModules.restrictOver Functor.sheafPushforwardContinuous
  SheafOfModules.overFunctor SheafOfModules.pushforward PresheafOfModules.pushforward
  PresheafOfModules.pushforward₀ PresheafOfModules.pushforward₀Obj
  PresheafOfModules.restrictScalars PresheafOfModules.restrictScalarsObj Over.forget
  ringedSitePullbackSection

set_option linter.unusedSectionVars false

private theorem pullback_section_map
    {R : Sheaf J CommRingCat.{max u v w}} {R' : Sheaf K CommRingCat.{max u v w}}
    (a : (sheafCompose J (forget₂ CommRingCat RingCat)).obj R ⟶
      (U.sheafPushforwardContinuous RingCat J K).obj
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R'))
    {M N : ringedSiteModules.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (f : M ⟶ N) (V : C) (x : M.val.obj (op V)) :
    ((ringedSitePullbackFunctor a
      (module_pushforward_isRightAdjoint_of_universes a)).map f).val.app (op (U.obj V))
        (ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a)
          M V x) =
      ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a)
        N V (f.val.app (op V) x) := by
  let := module_pushforward_isRightAdjoint_of_universes a
  exact (congrArg (fun g ↦ g.val.app (op V) x)
    ((pullbackPushforwardAdjunction a).unit.naturality f)).symm

private theorem pullback_section_restrict
    {R : Sheaf J CommRingCat.{max u v w}} {R' : Sheaf K CommRingCat.{max u v w}}
    (a : (sheafCompose J (forget₂ CommRingCat RingCat)).obj R ⟶
      (U.sheafPushforwardContinuous RingCat J K).obj
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R'))
    (M : ringedSiteModules.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    {V W : C} (f : W ⟶ V) (x : M.val.obj (op V)) :
    ((ringedSitePullbackFunctor a
      (module_pushforward_isRightAdjoint_of_universes a)).obj M).val.map (U.map f).op
        (ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a)
          M V x) =
      ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a)
        M W (M.val.map f.op x) := by
  let := module_pushforward_isRightAdjoint_of_universes a
  exact (PresheafOfModules.naturality_apply
    ((pullbackPushforwardAdjunction a).unit.app M).val f.op x).symm

private theorem pullback_section_smul
    {R : Sheaf J CommRingCat.{max u v w}} {R' : Sheaf K CommRingCat.{max u v w}}
    (a : (sheafCompose J (forget₂ CommRingCat RingCat)).obj R ⟶
      (U.sheafPushforwardContinuous RingCat J K).obj
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R'))
    (M : ringedSiteModules.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (V : C) (r : R.obj.obj (op V)) (x : M.val.obj (op V)) :
    ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a)
        M V (r • x) =
      a.hom.app (op V) r •
        ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a)
          M V x := by
  let := module_pushforward_isRightAdjoint_of_universes a
  exact (((pullbackPushforwardAdjunction a).unit.app M).val.app (op V)).hom.map_smul r x

private theorem pullback_basis
    [HasFiniteLimits C] [HasFiniteLimits D] [PreservesFiniteLimits U]
    (hcover : CoverPreserving J K U)
    {R : Sheaf J CommRingCat.{max u v w}} {R' : Sheaf K CommRingCat.{max u v w}}
    (a : (sheafCompose J (forget₂ CommRingCat RingCat)).obj R ⟶
      (U.sheafPushforwardContinuous RingCat J K).obj
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R'))
    (M : ringedSiteModules.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (N : ringedSiteModules.{max u v w}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R'))
    (p : (ringedSitePullbackFunctor a
      (module_pushforward_isRightAdjoint_of_universes a)).obj M ≅ N)
    (V : C) (e : M.val.obj (op V))
    (he : ∀ T : (Over V)ᵒᵖ, Function.Bijective
      (fun r : R.obj.obj (op T.unop.left) ↦ r • M.val.map T.unop.hom.op e)) :
    ∀ T : (Over (U.obj V))ᵒᵖ, Function.Bijective
      (fun r : R'.obj.obj (op T.unop.left) ↦ r • N.val.map T.unop.hom.op
        (p.hom.val.app (op (U.obj V))
          (ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a)
            M V e))) := by
  let := module_pushforward_isRightAdjoint_of_universes a
  let := RingedSitePullback.local_continuous (U := U) hcover V
  let aV := RingedSitePullback.locMap a V
  let := module_pushforward_isRightAdjoint_of_universes.{max u v, v, max u v w}
    (U := Over.post U) aV
  let c := RingedSitePullback.localComparison a V M
  have : IsIso c := RingedSitePullback.localComparison_isIso a V M
  let q := basisChart.{u, v, max u v w} M (op V) e he
  let t : N.over (U.obj V) ≅
      unit (((sheafCompose K (forget₂ CommRingCat RingCat)).obj R').over (U.obj V)) :=
    ((overFunctor _ (U.obj V)).mapIso p).symm ≪≫ (asIso c).symm ≪≫
      (pullback aV).mapIso q.symm ≪≫ asIso (pullbackObjUnitToUnit aV)
  have hq : q.inv.val.app (op (Over.mk (𝟙 V))) e = (1 : R.obj.obj (op V)) := by
    have hh := congrArg (fun f ↦ f.val.app (op (Over.mk (𝟙 V)))
      (1 : R.obj.obj (op V))) q.hom_inv_id
    change q.inv.val.app (op (Over.mk (𝟙 V)))
      (q.hom.val.app (op (Over.mk (𝟙 V))) (1 : R.obj.obj (op V))) =
        (1 : R.obj.obj (op V)) at hh
    rw [basisChart_apply] at hh
    simp only [Over.mk_hom, one_smul] at hh
    erw [signed_map_id.{u, v, w}] at hh
    exact hh
  let Z : Over (U.obj V) := (Over.post U).obj (Over.mk (𝟙 V))
  let ep := p.hom.val.app (op (U.obj V))
    (ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a) M V e)
  have htZ : t.hom.val.app (op Z) ep = (1 : R'.obj.obj (op (U.obj V))) := by
    have hc := RingedSitePullback.localComparison_unit_apply a V M (Over.mk (𝟙 V)) e
    have hn := congrArg (fun f ↦ f.val.app (op (Over.mk (𝟙 V))) e)
      ((pullbackPushforwardAdjunction aV).unit.naturality q.inv)
    have hu := pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit aV
    rw [Adjunction.homEquiv_unit] at hu
    have hu' := congrArg (fun f ↦ f.val.app (op (Over.mk (𝟙 V)))
      (1 : R.obj.obj (op V))) hu
    dsimp only [t, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    change (pullbackObjUnitToUnit aV).val.app (op Z)
      (((pullback aV).map q.inv).val.app (op Z)
        ((inv c).val.app (op Z) (p.inv.val.app (op (U.obj V))
          (p.hom.val.app (op (U.obj V))
            (ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a)
              M V e))))) = _
    have hp := congrArg (fun f ↦ f.val.app (op (U.obj V))
      (ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a)
        M V e)) p.hom_inv_id
    change p.inv.val.app (op (U.obj V))
      (p.hom.val.app (op (U.obj V))
        (ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a)
          M V e)) =
      ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a)
        M V e at hp
    rw [hp]
    change c.val.app (op Z)
      (((pullbackPushforwardAdjunction aV).unit.app (M.over V)).val.app
        (op (Over.mk (𝟙 V))) e) =
      ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a)
        M V e at hc
    rw [← hc]
    have hi := congrArg (fun f ↦ f.val.app (op Z)
      (((pullbackPushforwardAdjunction aV).unit.app (M.over V)).val.app
        (op (Over.mk (𝟙 V))) e)) (IsIso.hom_inv_id c)
    change (inv c).val.app (op Z) (c.val.app (op Z) _) = _ at hi
    rw [hi]
    change (pullbackObjUnitToUnit aV).val.app (op Z)
      (((pullback aV).map q.inv).val.app (op Z)
        (((pullbackPushforwardAdjunction aV).unit.app (M.over V)).val.app
          (op (Over.mk (𝟙 V))) e)) = _
    change ((pullbackPushforwardAdjunction aV).unit.app
      (unit (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over V))).val.app
        (op (Over.mk (𝟙 V))) (q.inv.val.app (op (Over.mk (𝟙 V))) e) =
      ((pullback aV).map q.inv).val.app (op Z)
        (((pullbackPushforwardAdjunction aV).unit.app (M.over V)).val.app
          (op (Over.mk (𝟙 V))) e) at hn
    rw [← hn, hq]
    change (pullbackObjUnitToUnit aV).val.app (op Z)
      (((pullbackPushforwardAdjunction aV).unit.app
        (unit (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over V))).val.app
          (op (Over.mk (𝟙 V))) (1 : R.obj.obj (op V))) =
      a.hom.app (op V) (1 : R.obj.obj (op V)) at hu'
    exact hu'.trans ((a.hom.app (op V)).hom.map_one)
  have ht : t.hom.val.app (op (Over.mk (𝟙 (U.obj V)))) ep =
      (1 : R'.obj.obj (op (U.obj V))) := by
    let f : Over.mk (𝟙 (U.obj V)) ⟶ Z := Over.homMk (𝟙 _) (by
      change 𝟙 (U.obj V) ≫ U.map (𝟙 V) = 𝟙 (U.obj V)
      rw [U.map_id, Category.id_comp])
    have hn := PresheafOfModules.naturality_apply t.hom.val f.op ep
    change t.hom.val.app (op (Over.mk (𝟙 (U.obj V))))
      (N.val.map (𝟙 (U.obj V)).op ep) =
        R'.obj.map (𝟙 (U.obj V)).op (t.hom.val.app (op Z) ep) at hn
    erw [signed_map_id.{u, v, w}] at hn
    rw [htZ, map_one] at hn
    exact hn
  intro T
  apply signedIso_basis_bijective.{max u v, v, max u v w}
    (R := R'.over (U.obj V)) t T
  have hn := PresheafOfModules.naturality_apply t.hom.val
    (Over.homMk T.unop.hom (Category.comp_id _) :
      T.unop ⟶ Over.mk (𝟙 (U.obj V))).op ep
  change t.hom.val.app T (N.val.map T.unop.hom.op ep) =
    R'.obj.map T.unop.hom.op (t.hom.val.app (op (Over.mk (𝟙 (U.obj V)))) ep) at hn
  exact hn.trans (by rw [ht, map_one])

private theorem pullback_signed_basis
    [HasFiniteLimits C] [HasFiniteLimits D] [PreservesFiniteLimits U]
    (hcover : CoverPreserving J K U)
    {R : Sheaf J CommRingCat.{max u v w}} {R' : Sheaf K CommRingCat.{max u v w}}
    (a : (sheafCompose J (forget₂ CommRingCat RingCat)).obj R ⟶
      (U.sheafPushforwardContinuous RingCat J K).obj
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R'))
    (L : ringedSiteModules.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (L' : ringedSiteModules.{max u v w}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R'))
    (p : (ringedSitePullbackFunctor a
      (module_pushforward_isRightAdjoint_of_universes a)).obj L ≅ L')
    (P : ∀ m : ℤ, (ringedSitePullbackFunctor a
      (module_pushforward_isRightAdjoint_of_universes a)).obj
        (signedLinePower.{u, v, w} L m) ≅ signedLinePower.{u, v, w} L' m)
    (hP : SignedLinePullbackNormalized a L L' p P)
    (V : C) (E : ∀ m : ℤ, (signedLinePower.{u, v, w} L m).val.obj (op V))
    (hE : SignedLineBasisPowers.{u, v, w} L (op V) E) :
    SignedLineBasisPowers.{u, v, w} L' (op (U.obj V))
      (fun m ↦ (P m).hom.val.app (op (U.obj V))
        (ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a)
          (signedLinePower.{u, v, w} L m) V (E m))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m
    exact pullback_basis hcover a _ _ (P m) V (E m) (hE.1 m)
  · exact (hP.1 V (E 0)).trans (by rw [hE.2.1, map_one])
  · intro n
    dsimp only
    rw [hE.2.2.1 n]
    have h := hP.2.2.1 n V (E (.ofNat (n + 1))) (E 1)
    rw [hP.2.1]
    exact h
  · intro n W
    let e := (P (.ofNat (n + 1))).hom.val.app (op (U.obj V))
      (ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a)
        (scalarTensorPower R L (n + 1)) V (E (.ofNat (n + 1))))
    let φ := (P (.negSucc n)).hom.val.app (op (U.obj V))
      (ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a)
        (signedLinePower.{u, v, w} L (.negSucc n)) V (E (.negSucc n)))
    have hv : φ.app (op (Over.mk (𝟙 (U.obj V)))) e = 1 := by
      have he := hE.2.2.2 n (op (Over.mk (𝟙 V)))
      simp only [Over.mk_hom] at he
      erw [signed_map_id.{u, v, w}] at he
      exact (hP.2.2.2 n V (E (.negSucc n)) (E (.ofNat (n + 1)))).trans
        (by rw [he, map_one])
    have hn := PresheafOfModules.naturality_apply φ
      (Over.homMk W.unop.hom (Category.comp_id _) :
        W.unop ⟶ Over.mk (𝟙 (U.obj V))).op e
    change φ.app W ((scalarTensorPower R' L' (n + 1)).val.map W.unop.hom.op e) = _
    exact hn.trans (by change R'.obj.map W.unop.hom.op _ = 1; rw [hv, map_one])

/-- A compatible scalar square remains compatible in every signed degree.
Source: Stacks Project, Modules on Sites, Tags 03EL, 0GMX and 04J0;
steps 2 and 6--8 of the signed-line scalar/pullback argument.
(blueprint: lem-pur-signed-line-scalar-pullback-naturality)

Proof: Use the pullback localization comparison to pull a trivializing cover of L
to a cover on the target site. On a member choose a basis e, and let v be its image
under c after insertion of the scalar 1. Let e' and v' be the images under p and q
of their adjunction-unit sections. Localization and the coefficient-unit comparison
show that these are target bases. The assumed degree-one square says that c' sends
e' tensor 1 to v'. Tensor recursion carries all positive basis powers to the
corresponding target powers. The negative evaluation clause carries each dual basis
to its target dual basis, since its value on the positive basis is 1. The scalar
normalizations carry the same signed basis powers to each other. Reassociating
scalar extension and pullback sends (x tensor s) tensor t to (x tensor 1) tensor b(s)t;
balancing uses the commuting coefficient square. On each chart both composites in
the required square therefore take the signed basis generator to the same signed
basis, including degree zero. Linearity gives equality on all local sections and
sheaf uniqueness glues it globally. This theorem asserts compatibility only for
given normalized families, and does not construct either family. -/
theorem signedLineScalarPullbackSquare_of_normalized
    [HasFiniteLimits C] [HasFiniteLimits D] [PreservesFiniteLimits U]
    (_hcover : CoverPreserving J K U)
    [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    [∀ V : D, (K.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    {R S : Sheaf J CommRingCat.{max u v w}}
    {R' S' : Sheaf K CommRingCat.{max u v w}} (ι : R ⟶ S) (ι' : R' ⟶ S')
    (a : (sheafCompose J (forget₂ CommRingCat RingCat)).obj R ⟶
      (U.sheafPushforwardContinuous RingCat J K).obj
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R'))
    (b : (sheafCompose J (forget₂ CommRingCat RingCat)).obj S ⟶
      (U.sheafPushforwardContinuous RingCat J K).obj
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S'))
    (_hab : (sheafCompose J (forget₂ CommRingCat RingCat)).map ι ≫ b =
      a ≫ (U.sheafPushforwardContinuous RingCat J K).map
        ((sheafCompose K (forget₂ CommRingCat RingCat)).map ι'))
    (L : ringedSiteModules.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (N : ringedSiteModules.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
    (L' : ringedSiteModules.{max u v w}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R'))
    (N' : ringedSiteModules.{max u v w}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S'))
    (_hL : ∃ (I : Type u) (V : I → C), J.CoversTop V ∧
      ∀ i : I, Nonempty (L.over (V i) ≅
        unit (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over (V i))))
    (_hN : ∃ (I : Type u) (V : I → C), J.CoversTop V ∧
      ∀ i : I, Nonempty (N.over (V i) ≅
        unit (((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).over (V i))))
    (_hL' : ∃ (I : Type u) (V : I → D), K.CoversTop V ∧
      ∀ i : I, Nonempty (L'.over (V i) ≅
        unit (((sheafCompose K (forget₂ CommRingCat RingCat)).obj R').over (V i))))
    (_hN' : ∃ (I : Type u) (V : I → D), K.CoversTop V ∧
      ∀ i : I, Nonempty (N'.over (V i) ≅
        unit (((sheafCompose K (forget₂ CommRingCat RingCat)).obj S').over (V i))))
    (c : changeOfRingsOfUniverses ι L ≅ N)
    (c' : changeOfRingsOfUniverses ι' L' ≅ N')
    (p : (ringedSitePullbackFunctor a
      (module_pushforward_isRightAdjoint_of_universes a)).obj L ≅ L')
    (q : (ringedSitePullbackFunctor b
      (module_pushforward_isRightAdjoint_of_universes b)).obj N ≅ N')
    (_hc : SignedLineScalarPullbackSquare ι ι' a b L N L' N' c c' p q)
    (B : ∀ m : ℤ, changeOfRingsOfUniverses ι (signedLinePower.{u, v, w} L m) ≅
      signedLinePower.{u, v, w} N m)
    (B' : ∀ m : ℤ, changeOfRingsOfUniverses ι' (signedLinePower.{u, v, w} L' m) ≅
      signedLinePower.{u, v, w} N' m)
    (_hB : SignedLineComparisonNormalized.{u, v, w} ι L N c B)
    (_hB' : SignedLineComparisonNormalized.{u, v, w} ι' L' N' c' B')
    (P : ∀ m : ℤ, (ringedSitePullbackFunctor a
      (module_pushforward_isRightAdjoint_of_universes a)).obj
        (signedLinePower.{u, v, w} L m) ≅ signedLinePower.{u, v, w} L' m)
    (Q : ∀ m : ℤ, (ringedSitePullbackFunctor b
      (module_pushforward_isRightAdjoint_of_universes b)).obj
        (signedLinePower.{u, v, w} N m) ≅ signedLinePower.{u, v, w} N' m)
    (hP : SignedLinePullbackNormalized a L L' p P)
    (hQ : SignedLinePullbackNormalized b N N' q Q) :
    ∀ m : ℤ, SignedLineScalarPullbackSquare ι ι' a b
      (signedLinePower.{u, v, w} L m) (signedLinePower.{u, v, w} N m)
      (signedLinePower.{u, v, w} L' m) (signedLinePower.{u, v, w} N' m)
      (B m) (B' m) (P m) (Q m) := by
  classical
  obtain ⟨I, X, hX, h⟩ := _hL
  choose E hE using fun i ↦ signedBasis_on_chart.{u, v, w} L (X i) (h i).some
  intro m V x s
  let := module_pushforward_isRightAdjoint_of_universes a
  let := module_pushforward_isRightAdjoint_of_universes b
  rw [pullback_section_map]
  apply ((pushforward b).obj (signedLinePower.{u, v, w} N' m)).isSheaf.isSeparated
    _ _ (hX V)
  intro W k hk
  obtain ⟨i, ⟨g⟩⟩ := hk
  change (signedLinePower.{u, v, w} N' m).val.map (U.map k).op _ =
    (signedLinePower.{u, v, w} N' m).val.map (U.map k).op _
  rw [← PresheafOfModules.naturality_apply (Q m).hom.val,
    pullback_section_restrict, ← PresheafOfModules.naturality_apply (B m).hom.val,
    scalarExtensionSection_naturality,
    ← PresheafOfModules.naturality_apply (B' m).hom.val,
    scalarExtensionSection_naturality,
    ← PresheafOfModules.naturality_apply (P m).hom.val, pullback_section_restrict]
  have hb := ConcreteCategory.congr_hom (b.hom.naturality k.op) s
  change b.hom.app (op W) (S.obj.map k.op s) =
    S'.obj.map (U.map k).op (b.hom.app (op V) s) at hb
  rw [← hb]
  let E0 : ∀ n : ℤ, (signedLinePower.{u, v, w} L n).val.obj (op W) :=
    fun n ↦ (signedLinePower.{u, v, w} L n).val.map g.op (E i n)
  have he0 : SignedLineBasisPowers.{u, v, w} L (op W) E0 :=
    signedBasis_restrict.{u, v, w} L _ _ g.op (E i) (hE i)
  obtain ⟨F0, hf0, hc0⟩ := comparison_basis.{u, v, w} ι L N c (op W) E0 he0
  let E1 : ∀ n : ℤ, (signedLinePower.{u, v, w} L' n).val.obj (op (U.obj W)) :=
    fun n ↦ (P n).hom.val.app (op (U.obj W))
      (ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a)
        (signedLinePower.{u, v, w} L n) W (E0 n))
  let F1 : ∀ n : ℤ, (signedLinePower.{u, v, w} N' n).val.obj (op (U.obj W)) :=
    fun n ↦ (Q n).hom.val.app (op (U.obj W))
      (ringedSitePullbackSection b (module_pushforward_isRightAdjoint_of_universes b)
        (signedLinePower.{u, v, w} N n) W (F0 n))
  have he1 : SignedLineBasisPowers.{u, v, w} L' (op (U.obj W)) E1 :=
    pullback_signed_basis _hcover a L L' p P hP W E0 he0
  have hf1 : SignedLineBasisPowers.{u, v, w} N' (op (U.obj W)) F1 :=
    pullback_signed_basis _hcover b N N' q Q hQ W F0 hf0
  have hc1 : c'.hom.val.app (op (U.obj W))
      (scalarExtensionSection ι' L' (op (U.obj W)) 1 (E1 1)) = F1 1 := by
    have hh := _hc W (E0 1) 1
    rw [pullback_section_map, hc0, map_one] at hh
    dsimp only [E1, F1]
    rw [hP.2.1, hQ.2.1]
    exact hh.symm
  have hn0 := normalized_on_basis.{u, v, w} ι L N c B _hB
    (op W) E0 F0 he0 hf0 hc0 m
  have hn1 := normalized_on_basis.{u, v, w} ι' L' N' c' B' _hB'
    (op (U.obj W)) E1 F1 he1 hf1 hc1 m
  obtain ⟨r, hr⟩ := (signedBasis_bijective.{u, v, w} L (op W) E0 he0 m).2
    ((signedLinePower.{u, v, w} L m).val.map k.op x)
  rw [← hr, scalarMap_basis_coeff.{u, v, max u v w}, hn0,
    pullback_section_smul, map_smul, pullback_section_smul, map_smul,
    scalarMap_basis_coeff.{u, v, max u v w}, hn1]
  have habr := congrArg
    (fun f ↦ f.hom.app (op W) (r :
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj.obj (op W))) _hab
  change b.hom.app (op W) (ι.hom.app (op W) r) =
    ι'.hom.app (op (U.obj W)) (a.hom.app (op W) r) at habr
  rw [map_mul, habr]

end SheafOfModules
