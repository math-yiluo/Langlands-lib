/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Exact.ExactCompactificationUnit
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
import WeilConjectures.AlgebraicGeometry.Exact.ExactCompactificationUnitComposition
import WeilConjectures.AlgebraicGeometry.Exact.ExactCompactificationUnitRefinement
import WeilConjectures.SixFunctors.Etale.LowerShriek.Comparison
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-!
# Identity normalization of an exact compact-support unit

Source: Stacks Project, Tags 0F7I, 0F7K and 015F
(blueprint: lem-sfb-exact-compactification-unit-identity).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The normalized exact derived unit at the proper identity compactification has the
canonical identity normalization.
Source: Stacks Project, Tags 0F7I, 0F7K and 015F
(blueprint: lem-sfb-exact-compactification-unit-identity).

Proof: every compactification of the identity has a clopen source open, so its sheaf
inclusion into ordinary direct image is invertible. Normalize the given exact functor
against each such inclusion and descend its compactification unit. The finite proper
identity compactification gives an invertible unit, and refinement compatibility transfers
invertibility to every compactification. Their inverse comparisons therefore form a
compatible family, agreeing with the supplied comparison at the proper identity.
Apply the composition theorem to the identity twice, with the sheaf multiplication
F(F(M)) -> F(M) obtained from the given isomorphism F -> id. Exact-derived composition
naturality identifies its derived multiplication with whiskering by D(F) of the derived
isomorphism D(F) -> id. The existing left unit law for unbounded compact support and
naturality of this latter isomorphism identify the two identity comparisons after applying
the faithful functor R(id)!. Cancel its invertible comparison to conclude equality.
Refinement compatibility transports back to the proper identity compactification. -/
theorem exactCompactificationUnit_identity
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (X : Scheme.{u}) [IsNoetherian X]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤
      Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (ι : F ⟶ lowerStar (ModuleCat.{u + 1} A) (𝟙 X)) [IsIso ι]
    (a : F ≅
      openImmersionLowerShriek (ModuleCat.{u + 1} A)
          (Compactification.ofIsProper (𝟙 X)).i ⋙
        lowerStar (ModuleCat.{u + 1} A) (Compactification.ofIsProper (𝟙 X)).g)
    (na : a.hom ≫ compactificationSheafToDirectImage.{u} A
      (Compactification.ofIsProper (𝟙 X)) = ι)
    (c : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
      (Compactification.ofIsProper (𝟙 X)) ≅ F.mapDerivedCategory)
    (uc : c.inv = exactCompactificationUnit A
      (Compactification.ofIsProper (𝟙 X)) F a) :
    (rightDerivedLowerShriekIso A (Compactification.ofIsProper (𝟙 X))).symm ≪≫
      c ≪≫ Functor.mapDerivedCategoryNatIso
        (asIso ι ≪≫ lowerStarId (ModuleCat.{u + 1} A) X) ≪≫
      Functor.mapDerivedCategoryIdIso _ = unboundedEtaleLowerShriekId A X := by
  classical
  let c₀ : Compactification (𝟙 X) := Compactification.ofIsProper (𝟙 X)
  have hs (d : Compactification (𝟙 X)) :
      IsIso (compactificationSheafToDirectImage.{u} A d) := by
    have := isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range
      (ModuleCat.{u + 1} A) d.i (d.isClopen_range_openImmersion inferInstance).isClosed
    dsimp [compactificationSheafToDirectImage]
    infer_instance
  let b (d : Compactification (𝟙 X)) :
      F ≅ openImmersionLowerShriek (ModuleCat.{u + 1} A) d.i ⋙
        lowerStar (ModuleCat.{u + 1} A) d.g :=
    letI := hs d
    asIso ι ≪≫ (asIso (compactificationSheafToDirectImage.{u} A d)).symm
  have nb (d : Compactification (𝟙 X)) :
      (b d).hom ≫ compactificationSheafToDirectImage.{u} A d = ι := by
    let := hs d
    simp only [b, Iso.trans_hom, Iso.symm_hom, asIso_hom,
      Category.assoc, asIso_inv]
    rw [IsIso.inv_hom_id, Category.comp_id]
  have ba : b c₀ = a := by
    let := hs c₀
    apply Iso.ext
    have hab := (nb c₀).trans na.symm
    change (b c₀).hom ≫ compactificationSheafToDirectImage.{u} A c₀ =
      a.hom ≫ compactificationSheafToDirectImage.{u} A c₀ at hab
    have h := congrArg (fun k => k ≫
      inv (compactificationSheafToDirectImage.{u} A c₀)) hab
    simpa only [Category.assoc, IsIso.hom_inv_id, Category.comp_id] using h
  let μ (d : Compactification (𝟙 X)) : F.mapDerivedCategory ⟶
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d :=
    exactCompactificationUnit A d F (b d)
  have hμ (d r : Compactification (𝟙 X)) :
      μ d ≫ (rightDerivedLowerShriekOfCompactificationIso A d r).hom = μ r :=
    exactCompactificationUnit_refinement A (𝟙 X) F d r (b d) (b r)
      ((nb d).trans (nb r).symm)
  have hμiso (d : Compactification (𝟙 X)) : IsIso (μ d) := by
    have : IsFinite c₀.g := by
      change IsFinite (𝟙 X)
      infer_instance
    have : IsIso (μ c₀) := isIso_exactCompactificationUnit_of_isFinite A c₀ F (b c₀)
    rw [← hμ c₀ d]
    infer_instance
  let C (d : Compactification (𝟙 X)) :
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d ≅
        F.mapDerivedCategory :=
    letI := hμiso d
    (asIso (μ d)).symm
  have hC (d r : Compactification (𝟙 X)) :
      (rightDerivedLowerShriekOfCompactificationIso A d r).hom ≫ (C r).hom =
        (C d).hom := by
    let := hμiso d
    let := hμiso r
    change _ ≫ inv (μ r) = inv (μ d)
    apply (cancel_epi (μ d)).1
    rw [← Category.assoc, hμ, IsIso.hom_inv_id, IsIso.hom_inv_id]
  have hc : C c₀ = c := by
    apply Iso.ext_inv
    change μ c₀ = c.inv
    rw [uc, ← ba]
  let i := asIso ι ≪≫ lowerStarId (ModuleCat.{u + 1} A) X
  let σ := Functor.isoWhiskerLeft F i ≪≫ F.rightUnitor
  have nσ (M) : σ.hom.app M ≫ ι.app M =
      ι.app (F.obj M) ≫ (lowerStar (ModuleCat.{u + 1} A) (𝟙 X)).map (ι.app M) ≫
        (lowerStarComp (ModuleCat.{u + 1} A) (𝟙 X) (𝟙 X) (𝟙 X)
          (by simp)).hom.app M := by
    rw [lowerStarComp_id_right]
    simp only [σ, i, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, NatTrans.comp_app,
      asIso_hom, Category.assoc]
    exact congrArg (ι.app (F.obj M) ≫ ·)
      ((lowerStarId (ModuleCat.{u + 1} A) X).hom.naturality (ι.app M)).symm
  have hcomp := exactCompactificationUnit_composition A (𝟙 X) (𝟙 X)
  have hh := hcomp F F F ι ι ι b b b nb nb nb C C C
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) σ nσ
  let R := rightDerivedLowerShriek (ModuleCat.{u + 1} A) (𝟙 X)
  let D := F.mapDerivedCategory
  let t : R ≅ D :=
    (rightDerivedLowerShriekIso A (HasCompactification.compactification (𝟙 X))).symm ≪≫
      C (HasCompactification.compactification (𝟙 X))
  let j : D ≅ 𝟭 (DerivedCategoryModule A X) :=
    Functor.mapDerivedCategoryNatIso i ≪≫ Functor.mapDerivedCategoryIdIso _
  have hm : (Functor.mapDerivedCategoryCompIso F F).hom ≫
      (Functor.mapDerivedCategoryNatIso σ).hom = Functor.whiskerLeft D j.hom := by
    have hn := Functor.mapDerivedCategoryNatIso_isoWhiskerLeft F i
    change (Functor.mapDerivedCategoryCompIso F F).hom ≫
      (Functor.mapDerivedCategoryNatIso (Functor.isoWhiskerLeft F i)).hom = _
    rw [← cancel_epi (Functor.mapDerivedCategoryCompIso F F).inv,
      Iso.inv_hom_id_assoc]
    dsimp only [j, Iso.trans_hom]
    rw [Functor.whiskerLeft_comp, ← Category.assoc, ← hn, Category.assoc,
      Functor.mapDerivedCategoryCompIso_comp_id]
    exact (Category.comp_id _).symm
  have hh' : (unboundedEtaleLowerShriekCompIso A (𝟙 X) (𝟙 X)).hom ≫ t.hom =
      Functor.whiskerRight t.hom R ≫ Functor.whiskerLeft D t.hom ≫
        Functor.whiskerLeft D j.hom := by
    have hx : HEq (HasCompactification.compactification (𝟙 X ≫ 𝟙 X))
        (HasCompactification.compactification (𝟙 X)) := by rfl
    have h := congrArg Iso.hom hh
    rw [eq_of_heq hx] at h
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, hm] at h
    dsimp only [t, Iso.trans_hom, Iso.symm_hom, D, R]
    simpa only [Category.assoc, D, Category.id_comp] using h
  have hu := (unboundedEtaleLowerShriekCompIso_units A (𝟙 X)).1
  have ht : t ≪≫ j = unboundedEtaleLowerShriekId A X := by
    have : R.Faithful := Functor.Faithful.of_iso (unboundedEtaleLowerShriekId A X).symm
    apply Iso.ext
    apply NatTrans.ext
    funext K
    apply R.map_injective
    apply (cancel_mono (t.hom.app K)).1
    have hk := NatTrans.congr_app hh' K
    rw [hu] at hk
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.leftUnitor_hom_app, unboundedEtaleLowerShriekCongr, Iso.refl_hom,
      Category.comp_id] at hk
    have hj : j.hom.app (D.obj K) = D.map (j.hom.app K) := by
      apply (cancel_mono (j.hom.app K)).1
      exact (j.hom.naturality (j.hom.app K)).symm
    have hid : R(𝟙 X)_![ModuleCat.{u + 1} A].map
        ((unboundedEtaleLowerShriekId A X).hom.app K) ≫
        𝟙 (R(𝟙 X)_![ModuleCat.{u + 1} A].obj K) =
        R.map ((unboundedEtaleLowerShriekId A X).hom.app K) := Category.comp_id _
    rw [hid] at hk
    rw [hj, ← t.hom.naturality] at hk
    dsimp only [Functor.id_obj, Functor.comp_obj, R] at hk ⊢
    simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.map_comp, Category.assoc] using hk.symm
  have ht₀ : (rightDerivedLowerShriekIso A c₀).symm ≪≫ c = t := by
    apply Iso.ext
    dsimp only [t, Iso.trans_hom, Iso.symm_hom]
    rw [← hc, ← hC c₀ (HasCompactification.compactification (𝟙 X))]
    dsimp only [rightDerivedLowerShriekIso]
    rw [Iso.inv_hom_id_assoc,
      (unboundedEtaleCompactSupport_comparison_coherence A (𝟙 X)).1]
    ext K
    simp
  have hfinal := congrArg (fun z => z ≪≫ j) ht₀
  have hresult := hfinal.trans ht
  apply Iso.ext
  simpa only [c₀, j, i, Iso.trans_hom, NatTrans.comp_app, Category.assoc] using
    congrArg Iso.hom hresult

end AlgebraicGeometry.Etale
