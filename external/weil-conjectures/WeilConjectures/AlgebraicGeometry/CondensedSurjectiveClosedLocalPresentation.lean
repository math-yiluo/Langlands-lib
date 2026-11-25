/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.CondensedSurjectiveClosedEquivalence
import WeilConjectures.AlgebraicGeometry.ProEtaleSurjectiveClosedCoverRefinement

/-! Local finite presentation under a surjective closed immersion. -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private lemma fp_of_iso {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R]
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (e : M ≅ N) (h : Mod.IsFinitelyPresented R M) : Mod.IsFinitelyPresented R N := by
  obtain ⟨n, m, f, ⟨i⟩⟩ := h
  exact ⟨n, m, f, ⟨e.symm ≪≫ i⟩⟩

private lemma fp_map_family {X Y : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    {S : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}} [MonObj R] [MonObj S]
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R ⥤
      Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) S)
    [F.Additive] [PreservesFiniteColimits F]
    (e : ∀ n : ℕ, F.obj (Mod.finiteFree R n) ≅ Mod.finiteFree S n)
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (h : Mod.IsFinitelyPresented R M) : Mod.IsFinitelyPresented S (F.obj M) := by
  obtain ⟨n, m, f, ⟨i⟩⟩ := h
  let en := e
  let f' : Mod.finiteFree S m ⟶ Mod.finiteFree S n :=
    (en m).inv ≫ F.map f ≫ (en n).hom
  exact ⟨n, m, f', ⟨F.mapIso i ≪≫ PreservesCokernel.iso F f ≪≫
    cokernel.mapIso (F.map f) f' (en m) (en n) (by simp [f'])⟩⟩

private lemma fp_reflect {X Y : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    {S : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}} [MonObj R] [MonObj S]
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R ⥤
      Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) S)
    [F.Additive] [F.IsEquivalence]
    (e : F.obj (Mod.regular R) ≅ Mod.regular S)
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (h : Mod.IsFinitelyPresented S (F.obj M)) : Mod.IsFinitelyPresented R M := by
  let E := F.asEquivalence
  have : E.functor.Additive := by change F.Additive; infer_instance
  have : E.inverse.Additive := E.inverse_additive
  let er := E.inverse.mapIso e.symm ≪≫ E.unitIso.symm.app (Mod.regular R)
  let en : ∀ n : ℕ, E.inverse.obj (Mod.finiteFree S n) ≅ Mod.finiteFree R n :=
    fun n ↦ E.inverse.mapBiproduct (fun _ : Fin n ↦ Mod.regular S) ≪≫
      biproduct.mapIso (fun _ ↦ er)
  exact fp_of_iso (E.unitIso.symm.app M) (fp_map_family E.inverse en h)

private noncomputable def regularExtendIso {X : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] [IsIso φ] :
    (Mod.extendScalars φ).obj (Mod.regular R) ≅ Mod.regular S :=
  (Mod.extendScalarsIsoComapInv φ).app _ ≪≫ Mod.regularIsoOfIsIso φ

private lemma fp_normalize {X : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] [IsIso φ]
    {P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (h : Mod.IsFinitelyPresented R P) :
    Mod.IsFinitelyPresented S ((Mod.extendScalars φ).obj P) :=
  let e : ∀ n : ℕ, (Mod.extendScalars φ).obj (Mod.finiteFree R n) ≅
      Mod.finiteFree S n := fun n ↦
    (Mod.extendScalars φ).mapBiproduct (fun _ : Fin n ↦ Mod.regular R) ≪≫
      biproduct.mapIso (fun _ ↦ regularExtendIso φ)
  fp_map_family (Mod.extendScalars φ) e h

private lemma fp_denormalize {X : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] [IsIso φ]
    {P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (h : Mod.IsFinitelyPresented S ((Mod.extendScalars φ).obj P)) :
    Mod.IsFinitelyPresented R P := by
  have : (Mod.comap (asIso φ).inv).IsEquivalence :=
    (Mod.comapEquivalenceOfIsIso φ).isEquivalence_inverse
  have : (Mod.extendScalars φ).IsEquivalence :=
    Functor.isEquivalence_of_iso (Mod.extendScalarsIsoComapInv φ).symm
  exact fp_reflect (Mod.extendScalars φ) (regularExtendIso φ) h

private noncomputable def regularPullbackIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (CondensedRing.upperStar Λ f).obj (Mod.regular (condensedRingObj Λ X)) ≅
      Mod.regular (condensedRingObj Λ Y) :=
  regularExtendIso (condensedPullbackHom Λ f)

private lemma fp_pullback
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : Y ⟶ X)
    {P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (h : Mod.IsFinitelyPresented (condensedRingObj Λ X) P) :
    Mod.IsFinitelyPresented (condensedRingObj Λ Y)
      ((CondensedRing.upperStar Λ f).obj P) :=
  let e : ∀ n : ℕ, (CondensedRing.upperStar Λ f).obj
      (Mod.finiteFree (condensedRingObj Λ X) n) ≅
      Mod.finiteFree (condensedRingObj Λ Y) n := fun n ↦
    (CondensedRing.upperStar Λ f).mapBiproduct
        (fun _ : Fin n ↦ Mod.regular (condensedRingObj Λ X)) ≪≫
      biproduct.mapIso (fun _ ↦ regularPullbackIso Λ f)
  fp_map_family (CondensedRing.upperStar Λ f) e h

attribute [local irreducible] CondensedRing.upperStarComp
  CondensedRing.upperStarLowerStarAdjunction

/-- Direct image along a surjective closed immersion preserves local finite presentation
for a coefficient ring pulled back from condensed abelian groups.

Source: Stacks Project Tags 09AA and 09AH, empty-complement localization; the support
argument in `ModuleObject/Colimit/TwoColimit.lean`.
Proof: refine a presentation cover of P by a cover obtained from X, using the
affine ind-etale closed-site lift (Tag 09AB). On each lifted member, pull the
finite presentation back along its refinement map. Normalized inverse image
preserves finite free modules and cokernels. The cartesian square and the counit
identify the pullback of the restriction of the direct image with this finitely
presented module. Inverse image along the base-changed surjective closed immersion
is an equivalence preserving the regular module, hence reflects finite presentations.
Undo the coefficient normalization to obtain the presentation on the chosen cover
of X. Rank-zero and empty-cover cases use the same formulas.
(auxiliary; not a blueprint node)
-/
theorem lfp_lowerStar_of_surjective_closed
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [Surjective i]
    (P : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))
    (hP : IsLocallyFinitelyPresented (condensedRingObj Λ Z) P) :
    IsLocallyFinitelyPresented (condensedRingObj Λ X)
      ((CondensedRing.lowerStar Λ i).obj P) := by
  classical
  obtain ⟨C, hC⟩ := hP
  obtain ⟨B, hB⟩ := Scheme.exists_cover_refinement_surjective_closed i C
  let Q := (CondensedRing.lowerStar Λ i).obj P
  have : (CondensedRing.upperStar Λ i).IsEquivalence :=
    condensedSurjectiveClosedPullback_isEquivalence Λ i
  refine ⟨B, fun b ↦ ?_⟩
  obtain ⟨a, W, q, p, r, hsq, hr⟩ := hB b
  have : IsClosedImmersion q :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq.flip inferInstance
  have : Surjective q :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq.flip inferInstance
  have : (CondensedRing.upperStar Λ q).IsEquivalence :=
    condensedSurjectiveClosedPullback_isEquivalence Λ q
  have hp : Mod.IsFinitelyPresented (condensedRingObj Λ _)
      ((CondensedRing.upperStar Λ p).obj P) := by
    let e : (CondensedRing.upperStar Λ r).obj
        ((CondensedRing.upperStar Λ (C.f a)).obj P) ≅
        (CondensedRing.upperStar Λ p).obj P :=
      ((CondensedRing.upperStarComp Λ r (C.f a)).app P).symm ≪≫
        eqToIso (congrArg (fun f ↦ (CondensedRing.upperStar Λ f).obj P) hr)
    exact fp_of_iso e (fp_pullback Λ r
      (fp_normalize (condensedPullbackHom Λ (C.f a)) (hC a)))
  let e : (CondensedRing.upperStar Λ q).obj
      ((CondensedRing.upperStar Λ (B.f b)).obj Q) ≅
      (CondensedRing.upperStar Λ p).obj P :=
    ((CondensedRing.upperStarComp Λ q (B.f b)).app Q).symm ≪≫
      eqToIso (congrArg (fun f ↦ (CondensedRing.upperStar Λ f).obj Q)
        hsq.w) ≪≫
      (CondensedRing.upperStarComp Λ p i).app Q ≪≫
      (CondensedRing.upperStar Λ p).mapIso
        (asIso ((CondensedRing.upperStarLowerStarAdjunction Λ i).counit.app P))
  exact fp_denormalize (condensedPullbackHom Λ (B.f b))
    (fp_reflect (CondensedRing.upperStar Λ q) (regularPullbackIso Λ q)
      (fp_of_iso e.symm hp))

end AlgebraicGeometry.ProEtale
