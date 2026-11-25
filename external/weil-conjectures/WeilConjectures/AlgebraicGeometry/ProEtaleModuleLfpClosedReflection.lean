/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs

import WeilConjectures.AlgebraicGeometry.ProEtaleSurjectiveClosedCoverRefinement
import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedSupport
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.AlgebraicGeometry.LocallyFinitelyPresentedExtendScalars

/-! # Reflection of local finite presentations across a surjective closed immersion -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

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
  exact (fp_iff_of_iso (E.unitIso.symm.app M)).1 (fp_map_family E.inverse en h)

private lemma fp_pullback_comp_iff {X Y Z : Scheme.{u}} (f : Z ⟶ Y) (g : Y ⟶ X)
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) :
    Mod.IsFinitelyPresented ((upperStar Ab.{u + 1} (f ≫ g)).obj R)
      (((upperStar Ab.{u + 1} (f ≫ g)).mapMod R).obj M) ↔
    Mod.IsFinitelyPresented ((upperStar Ab.{u + 1} f).obj
      ((upperStar Ab.{u + 1} g).obj R))
      (((upperStar Ab.{u + 1} f).mapMod _).obj
        (((upperStar Ab.{u + 1} g).mapMod R).obj M)) := by
  let F := upperStar Ab.{u + 1} g
  let G := upperStar Ab.{u + 1} f
  let e := upperStarComp Ab.{u + 1} f g
  let φ := Functor.compAlgHom F G e.inv R
  let i := (Functor.mapModCompIso F G e.inv R).app M
  exact ⟨fun h ↦ finitePresentation_of_iso i.symm (finitePresentation_comap φ h),
    fun h ↦ finitePresentation_of_comap φ (finitePresentation_of_iso i h)⟩

private theorem closed_mapMod_isEquivalence {X Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] [Surjective i]
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] :
    ((upperStar Ab.{u + 1} i).mapMod R).IsEquivalence := by
  let j := (⊥ : X.Opens).ι
  have hU : IsEmpty (⊥ : X.Opens).toScheme := ⟨fun x ↦ x.property⟩
  let := hU
  have hij : Set.range j = (Set.range i)ᶜ := by
    rw [Set.range_eq_univ.mpr i.surjective, Set.compl_univ]
    exact Set.range_eq_empty j
  have hunitAb (F : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :
      IsIso ((upperStarLowerStarAdjunction Ab.{u + 1} i).unit.app F) := by
    apply abelian_closed_support i j hij F
    refine Sheaf.isZero_of_isZero_obj _ ?_
    rintro ⟨V⟩
    have : IsEmpty V.left := ⟨fun v ↦ by
      have x : (⊥ : X.Opens).toScheme := V.hom.base v
      exact x.property⟩
    exact (Scheme.ProEt.isTerminalSectionsOfIsEmpty
      ((upperStar Ab.{u + 1} j).obj F) V).isZero
  let adj := (upperStarLowerStarAdjunction Ab.{u + 1} i).mapModAdjunction R
  have hunit (M) : IsIso (adj.unit.app M) := by
    have hh : IsIso ((Mod.forget _).map (adj.unit.app M)) := by
      change IsIso (adj.unit.app M).hom
      dsimp only [adj]
      rw [Adjunction.mapModAdjunction_unit_app_hom]
      infer_instance
    exact isIso_of_reflects_iso _ (Mod.forget _)
  have hcounit (N) : IsIso (adj.counit.app N) := by
    have hh : IsIso ((Mod.forget _).map (adj.counit.app N)) := by
      change IsIso (adj.counit.app N).hom
      dsimp only [adj]
      rw [Adjunction.mapModAdjunction_counit_app_hom]
      infer_instance
    exact isIso_of_reflects_iso _ (Mod.forget _)
  exact adj.toEquivalence.isEquivalence_functor

/-- Surjective closed inverse image reflects pro-etale local finite presentation.
Source: Bhatt--Scholze, Lemma 5.4.2, Theorem 2.3.4 and Definition 6.8.10.
(auxiliary; not a blueprint node)

Proof: a surjective closed immersion is a universal homeomorphism. Topological
invariance is computed on the affine ind-etale basis of Theorem 2.3.4. On this basis
base change is an equivalence preserving the faithfully flat and Zariski covering
criteria. Refine the covering presentations of p^*M to basis objects and lift them
along this basis equivalence and its induced monoidal sheaf equivalence. The coefficient
ring identifies with p^*R, regular modules correspond,
and the equivalence preserves finite sums and cokernels. Thus the lifted finite matrices
present M on the corresponding covering of U. Compatibility with the adjunction unit
identifies the presented module with the original M, rather than an unspecified object.
For empty U, use the empty covering and rank-zero presentations. Neither reduction of U
nor a uniform nilpotence bound on the defining ideal is required. -/
theorem localFinitePresentation_of_surjective_closed_pullback
    {U V : Scheme.{u}} (p : V ⟶ U) [IsClosedImmersion p]
    (hp : Function.Surjective p)
    (R : Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) [MonObj R]
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) R)
    (hM : IsLocallyFinitelyPresented ((upperStar Ab.{u + 1} p).obj R)
      (((upperStar Ab.{u + 1} p).mapMod R).obj M)) :
    IsLocallyFinitelyPresented R M := by
  classical
  let : Surjective p := ⟨hp⟩
  obtain ⟨C, hC⟩ := hM
  obtain ⟨B, hB⟩ := Scheme.exists_cover_refinement_surjective_closed p C
  refine ⟨B, fun b ↦ ?_⟩
  obtain ⟨a, W, q, s, r, hsq, hr⟩ := hB b
  have : IsClosedImmersion q :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq.flip inferInstance
  have : Surjective q :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq.flip inferInstance
  have : ((upperStar Ab.{u + 1} q).mapMod
      ((upperStar Ab.{u + 1} (B.f b)).obj R)).IsEquivalence :=
    closed_mapMod_isEquivalence q _
  apply fp_reflect ((upperStar Ab.{u + 1} q).mapMod _)
    (Mod.isoMk (Iso.refl _) (by simp [Mod.act]))
  apply (fp_pullback_comp_iff q (B.f b) M).mp
  rw [hsq.w]
  apply (fp_pullback_comp_iff s p M).mpr
  rw [← hr]
  apply (fp_pullback_comp_iff r (C.f a) _).mpr
  exact finitePresentation_mapMod (upperStar Ab.{u + 1} r) (hC a)

end AlgebraicGeometry.ProEtale
