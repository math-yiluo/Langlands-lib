/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.LocalizedHomologyStalkComparison
public import Mathlib.AlgebraicGeometry.ResidueField
import WeilConjectures.AlgebraicGeometry.Residue.ResidueHomologyRankOneCoefficient
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-! # The residue calculation for the degree-zero component of a rank-one model

Source: Stacks Project, Tag 0E62, residue-field argument, with Tag 0BCD.
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The degree-zero component of a fixed chain representative is invertible at the
chosen stalk when its derived residue arrow is invertible on degree-zero homology.
Source: Stacks Project, Tag 0E62, residue-field argument, and Tag 0BCD.
(blueprint: lem-sc-rank-one-residue-stalk-component).

Proof: Identify the localized site with the open subscheme. The source is the
structure sheaf in degree zero. The target P is bounded with finite-projective
terms, so the termwise flat-complex comparison computes its residue pullback.
Exact restriction and the composition comparison for derived pullback identify
the residue of Q.map alpha with the residue of a, conjugated by c and e. Both
conjugating arrows are isomorphisms, so the residue homology map of alpha is
invertible. Negative terms of P vanish, hence its residue H^0 is the kernel of
the outgoing degree-zero differential without an incoming quotient. Consequently
the image of the residue source generator under alpha^0 is nonzero: it represents
the nonzero image of the source generator in residue homology. The source and
P^0 stalks are free of rank one over the local ring at s. In these bases alpha^0
is multiplication by a scalar whose residue is nonzero. That scalar is a unit
in the local ring, and multiplication by its inverse gives the two-sided inverse
of the stalk component. Forgetting the scalar action gives the asserted additive
isomorphism. No conclusion about the original homology stalk map is used here.
An empty U cannot contain s. Rank zero is excluded by the fixed rank-one hypothesis;
higher differentials and all other fibres are unrestricted. -/
theorem isIso_localized_stalk_component_of_residue_homology (S : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [∀ U : S.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U))]
    [∀ x : S, HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings (Spec (S.residueField x)).toRingedSpace))]
    (E : schemeDerivedCategory S)
    (a : (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).obj
        (SheafOfModules.unit S.ringCatSheaf) ⟶ E) (s : S)
    (U : S.Opens) (hs : s ∈ U)
    (P : CochainComplex
      (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) ℤ)
    (hP : Scheme.IsStrictlyPerfect S U P)
    (hnegative : ∀ i : ℤ, i < 0 → IsZero (P.X i))
    (hzero : Nonempty (P.X 0 ≅ SheafOfModules.free
      (R := (moduleRings S.toRingedSpace).over U) (ULift.{u} (Fin 1))))
    (e : (SheafOfModules.overFunctor.{u}
      (moduleRings S.toRingedSpace) U).mapDerivedCategory.obj E ≅ DerivedCategory.Q.obj P)
    (ha : IsIso ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (Spec (S.residueField s)).toRingedSpace)) 0).map
        ((derivedPullback (S.fromSpecResidueField s)).map a)))
    (c : (SheafOfModules.overFunctor.{u}
        (moduleRings S.toRingedSpace) U).mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).obj
          (SheafOfModules.unit S.ringCatSheaf)) ≅
      DerivedCategory.Q.obj
        ((CochainComplex.singleFunctor
          (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) 0).obj
            ((SheafOfModules.overFunctor.{u}
              (moduleRings S.toRingedSpace) U).obj (SheafOfModules.unit S.ringCatSheaf))))
    (α : (CochainComplex.singleFunctor
        (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) 0).obj
          ((SheafOfModules.overFunctor.{u}
            (moduleRings S.toRingedSpace) U).obj (SheafOfModules.unit S.ringCatSheaf)) ⟶ P)
    (hα : DerivedCategory.Q.map α = c.inv ≫
      (SheafOfModules.overFunctor.{u} (moduleRings S.toRingedSpace) U).mapDerivedCategory.map a ≫
        e.hom) :
    IsIso ((localizedModuleStalk S U ⟨s, hs⟩).map (α.f 0)) := by
  classical
  have rankOne_unit_stalk_iso (X : Scheme.{u}) (x : X) :
      let S := RingedSpace.moduleStalkFunctor X.toRingedSpace x
      ∃ e : S.obj (SheafOfModules.unit X.ringCatSheaf) ≅
          ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x),
        ∀ (U : X.Opens) (hx : x ∈ U) (r : Γ(X, U)),
          e.hom (TopCat.Presheaf.germ (SheafOfModules.unit X.ringCatSheaf).val.presheaf
            U x hx r) = X.presheaf.germ U x hx r := by
    let D := (TopologicalSpace.OpenNhds.inclusion x).op ⋙ X.presheaf
    let A := forget₂ CommRingCat.{u} RingCat.{u} ⋙
      forget₂ RingCat.{u} AddCommGrpCat.{u}
    let e : ↑(TopCat.Presheaf.stalk (C := Ab.{u})
        (SheafOfModules.unit X.ringCatSheaf).val.presheaf x) ≃+ X.presheaf.stalk x :=
      (preservesColimitIso A D).symm.addCommGroupIsoToAddEquiv
    have hg (U : X.Opens) (hx : x ∈ U) (r : Γ(X, U)) :
        e (TopCat.Presheaf.germ (SheafOfModules.unit X.ringCatSheaf).val.presheaf
          U x hx r) = X.presheaf.germ U x hx r := by
      change (colimit.ι (D ⋙ A) (Opposite.op (⟨U, hx⟩ : TopologicalSpace.OpenNhds x)) ≫
        (preservesColimitIso A D).inv) r = _
      rw [ι_preservesColimitIso_inv]
      rfl
    let f : (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj
        (SheafOfModules.unit X.ringCatSheaf) →ₗ[X.presheaf.stalk x] X.presheaf.stalk x :=
      { e.toAddMonoidHom with
        map_smul' := by
          intro r m
          obtain ⟨U, hxU, r, rfl⟩ := X.presheaf.exists_germ_eq r
          obtain ⟨V, hxV, m, rfl⟩ :=
            TopCat.Presheaf.exists_germ_eq
              (SheafOfModules.unit X.ringCatSheaf).val.presheaf m
          have hx : x ∈ U ⊓ V := ⟨hxU, hxV⟩
          rw [← X.presheaf.germ_res_apply (homOfLE inf_le_left) x hx r,
            ← TopCat.Presheaf.germ_res_apply
              (SheafOfModules.unit X.ringCatSheaf).val.presheaf
              (homOfLE inf_le_right) x hx m,
            ← PresheafOfModules.germ_smul (R := X.presheaf)]
          let r' := X.presheaf.map (homOfLE inf_le_left : U ⊓ V ⟶ U).op r
          let m' : Γ(X, U ⊓ V) :=
            (SheafOfModules.unit X.ringCatSheaf).val.presheaf.map
              (homOfLE inf_le_right : U ⊓ V ⟶ V).op m
          change e (TopCat.Presheaf.germ
            (SheafOfModules.unit X.ringCatSheaf).val.presheaf (U ⊓ V) x hx (r' * m')) =
            X.presheaf.germ (U ⊓ V) x hx r' * (e (TopCat.Presheaf.germ
              (SheafOfModules.unit X.ringCatSheaf).val.presheaf (U ⊓ V) x hx m') :
                X.presheaf.stalk x)
          rw [hg, hg]
          exact map_mul (X.presheaf.germ (U ⊓ V) x hx).hom _ _ }
    refine ⟨(LinearEquiv.ofBijective f e.bijective).toModuleIso, ?_⟩
    exact hg
  let x : U.toScheme := ⟨s, hs⟩
  let T := RingedSpace.moduleStalkFunctor U.toScheme.toRingedSpace x
  let F := (Scheme.Modules.overEquiv U).functor
  obtain ⟨t, ht⟩ := rankOne_unit_stalk_iso U.toScheme x
  let A := (CochainComplex.singleFunctor
    (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) 0).obj
      ((SheafOfModules.overFunctor.{u} (moduleRings S.toRingedSpace) U).obj
        (SheafOfModules.unit S.ringCatSheaf))
  let b : F.obj (A.X 0) ≅ SheafOfModules.unit U.toScheme.ringCatSheaf :=
    F.mapIso (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _) ≪≫
      (Scheme.Modules.overEquivFunctorObjUnitIso U).symm
  obtain ⟨z⟩ := hzero
  let d : F.obj (P.X 0) ≅ SheafOfModules.unit U.toScheme.ringCatSheaf :=
    F.mapIso (z ≪≫ SheafOfModules.freeUniqueIso _) ≪≫
      (Scheme.Modules.overEquivFunctorObjUnitIso U).symm
  let σ := (T.mapIso b ≪≫ t).toLinearEquiv
  let τ := (T.mapIso d ≪≫ t).toLinearEquiv
  have hn := residue_ne_zero_rankOne_stalk_coefficient S E a s U hs P hP
    hnegative e ha c α hα σ τ
  let f := (T.map (F.map (α.f 0))).hom
  let g : U.toScheme.presheaf.stalk x →ₗ[U.toScheme.presheaf.stalk x]
      U.toScheme.presheaf.stalk x := τ.toLinearMap.comp (f.comp σ.symm.toLinearMap)
  have hu : IsUnit (g 1) := (IsLocalRing.residue_ne_zero_iff_isUnit _).mp hn
  have hg (r : U.toScheme.presheaf.stalk x) : g r = r * g 1 := by
    simpa only [smul_eq_mul, mul_one] using g.map_smul r (1 : U.toScheme.presheaf.stalk x)
  have hb : Function.Bijective g := by
    obtain ⟨v, hv⟩ := hu
    rw [show (g : U.toScheme.presheaf.stalk x → U.toScheme.presheaf.stalk x) =
      (fun r ↦ r * (v : U.toScheme.presheaf.stalk x)) by funext r; rw [hg, hv]]
    exact v.mulRight_bijective
  have hf : Function.Bijective f := by
    have heq : (f : _ → _) = τ.symm ∘ g ∘ σ := by
      funext m
      simp only [Function.comp_apply, g, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.symm_apply_apply]
      exact congrArg f (σ.symm_apply_apply m).symm
    rw [heq]
    exact τ.symm.bijective.comp (hb.comp σ.bijective)
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  exact hf

end AlgebraicGeometry
