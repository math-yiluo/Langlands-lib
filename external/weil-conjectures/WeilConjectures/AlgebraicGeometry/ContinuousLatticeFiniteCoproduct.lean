/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficients
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.LocallyFree
public import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
import WeilConjectures.AlgebraicGeometry.ContinuousLocallyFreePullback
import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import all WeilConjectures.AlgebraicGeometry.CondensedFieldLfpLocalTriviality
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionEssImage

/-! # Integral lattices on finite disjoint unions

Source: Stacks Project, Tag 04TR, sheaf gluing; Bhatt--Scholze, Lemma 6.8.13.
(auxiliary; not a blueprint node)
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

private lemma locallyFree_of_extendScalars {X : Scheme.{u}}
    {R T : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj T] [IsCommMonObj R]
    (φ : R ⟶ T) [IsMonHom φ] [IsIso φ]
    {P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (hP : IsLocallyFree T ((Mod.extendScalars φ).obj P)) : IsLocallyFree R P := by
  exact IsLocallyFree.of_iso ((Mod.comapEquivalenceOfIsIso φ).counitIso.app P)
    (IsLocallyFree.comap φ
      (IsLocallyFree.of_iso ((Mod.extendScalarsIsoComapInv φ).app P) hP))

private lemma module_isZero_of_underlying
    {X : Scheme.{u}} {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) (h : IsZero M.X) :
    IsZero M := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply (Mod.forget R).map_injective
  exact h.eq_of_src _ _

set_option backward.isDefEq.respectTransparency false in
private lemma pull_push_zero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U V : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (g : V ⟶ X)
    (h : Set.range g.base ∩ Set.range j.base = ∅)
    (M : Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1}) (condensedRingObj Λ V)) :
    IsZero ((upperStar Λ j).obj ((lowerStar Λ g).obj M)) := by
  apply module_isZero_of_underlying
  apply IsZero.of_iso _ ((profinitePointModuleForgetPullbackIso Λ j).app _)
  apply IsZero.of_iso _ ((ProEtale.upperStarIsoOpenImmersionRestriction Ab.{u + 1} j).app _)
  apply Sheaf.isZero_of_isZero_obj
  rintro ⟨T⟩
  let W := (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj
    ((MorphismProperty.Over.map ⊤ (inferInstance : @WeaklyEtale _ _ j)).obj T)
  have : IsEmpty W.left := by
    refine ⟨fun w ↦ ?_⟩
    have hw : (pullback.fst (T.hom ≫ j) g ≫ T.hom ≫ j).base w ∈
        Set.range g.base ∩ Set.range j.base := by
      refine ⟨?_, ⟨T.hom.base (pullback.fst (T.hom ≫ j) g w), rfl⟩⟩
      rw [pullback.condition]
      exact ⟨_, rfl⟩
    rw [h] at hw
    exact hw
  exact (isZero_zero Ab.{u + 1}).of_iso
    ((Scheme.ProEt.isTerminalSectionsOfIsEmpty M.X W).uniqueUpToIso
      HasZeroObject.zeroIsTerminal)

private lemma pull_shriek_zero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U V : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (g : V ⟶ X)
    (h : Set.range j.base ∩ Set.range g.base = ∅)
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)) :
    IsZero ((upperStar Λ g).obj ((openImmersionLowerShriek Λ j).obj M)) := by
  have hinit : IsInitial ((upperStar Λ g).obj ((openImmersionLowerShriek Λ j).obj M)) := by
    refine IsInitial.ofUnique (h := fun N ↦ ?_)
    have hz := pull_push_zero Λ j g (by rw [Set.inter_comm]; exact h) N
    letI : Unique (M ⟶ (upperStar Λ j).obj ((lowerStar Λ g).obj N)) :=
      ⟨⟨hz.isTerminal.from M⟩, fun f ↦ hz.isTerminal.hom_ext f _⟩
    exact Equiv.unique
      (((upperStarLowerStarAdjunction Λ g).homEquiv _ N).trans
        ((openImmersionLowerShriekUpperStarAdjunction Λ j).homEquiv M _))
  exact (isZero_zero _).of_iso (hinit.uniqueUpToIso HasZeroObject.zeroIsInitial)

private lemma module_iso_of_cover
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    {I : Type u} (Y : I → Scheme.{u}) (j : ∀ i, Y i ⟶ X)
    [∀ i, IsOpenImmersion (j i)]
    (hj : ∀ x : X, ∃ (i : I) (y : Y i), j i y = x)
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (f : M ⟶ N) (hf : ∀ i, IsIso ((upperStar Λ (j i)).map f)) : IsIso f := by
  have hsheaf : IsIso f.hom := by
    apply ProEtale.isIso_of_isIso_localizationRestriction Ab.{u + 1} f.hom j
    · apply Scheme.zariskiPrecoverage_le_proetalePrecoverage
      exact (Scheme.ofArrows_mem_precoverage_iff _).mpr ⟨hj, fun _ ↦ inferInstance⟩
    · intro i
      have : IsIso ((ProEtale.upperStar Ab.{u + 1} (j i)).map f.hom) := by
        have : IsIso ((upperStar Λ (j i)).map f) := hf i
        have : IsIso ((Mod.forget _).map ((upperStar Λ (j i)).map f)) := inferInstance
        exact (NatIso.isIso_map_iff (profinitePointModuleForgetPullbackIso Λ (j i)) f).mp
          (show IsIso ((Mod.forget _).map ((upperStar Λ (j i)).map f)) from
            inferInstance)
      exact (NatIso.isIso_map_iff
        (ProEtale.upperStarIsoOpenImmersionRestriction Ab.{u + 1} (j i)) f.hom).mp
          (by infer_instance)
  have : IsIso ((Mod.forget _).map f) := hsheaf
  exact isIso_of_reflects_iso f (Mod.forget _)

attribute [local instance] Abelian.hasFiniteBiproducts

private lemma sigma_disjoint {I : Type u} (Y : I → Scheme.{u}) {s t : I} (hst : s ≠ t) :
    Set.range (Sigma.ι Y s).base ∩ Set.range (Sigma.ι Y t).base = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun x ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ↦ hst ?_
  exact congrArg Sigma.fst ((sigmaι_eq_iff Y s t a b).mp (ha.trans hb.symm))

private lemma pull_biproduct_shriek_inclusion_isIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {I : Type u} [Finite I]
    (Y : I → Scheme.{u})
    (M : ∀ i, Mod (Sheaf (Scheme.ProEt.topology (Y i)) Ab.{u + 1})
      (condensedRingObj Λ (Y i))) (t : I) :
    IsIso ((upperStar Λ (Sigma.ι Y t)).map
      (biproduct.ι (fun i ↦ (openImmersionLowerShriek Λ (Sigma.ι Y i)).obj (M i)) t)) := by
  classical
  let := Fintype.ofFinite I
  let G := fun i ↦ (openImmersionLowerShriek Λ (Sigma.ι Y i)).obj (M i)
  let F := upperStar Λ (Sigma.ι Y t)
  have hz (s : I) (hst : s ≠ t) : IsZero (F.obj (G s)) :=
    pull_shriek_zero Λ _ _ (sigma_disjoint Y hst) (M s)
  refine ⟨F.map (biproduct.π G t), ?_, ?_⟩
  · rw [← F.map_comp, biproduct.ι_π_self, F.map_id]
  · rw [← F.map_comp, ← F.map_id, ← IsBilimit.total (biproduct.isBilimit G),
      F.map_sum, Finset.sum_eq_single t (fun s _ hst ↦ ?_) (by simp)]
    rw [F.map_comp, (hz s hst).eq_zero_of_tgt (F.map (biproduct.π G s)), zero_comp]

private theorem nonempty_pull_biproduct_shriek_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {I : Type u} [Finite I]
    (Y : I → Scheme.{u})
    (M : ∀ i, Mod (Sheaf (Scheme.ProEt.topology (Y i)) Ab.{u + 1})
      (condensedRingObj Λ (Y i))) (t : I) :
    Nonempty ((upperStar Λ (Sigma.ι Y t)).obj
      (⨁ fun i ↦ (openImmersionLowerShriek Λ (Sigma.ι Y i)).obj (M i)) ≅ M t) := by
  have := pull_biproduct_shriek_inclusion_isIso Λ Y M t
  have : IsIso (openImmersionLowerShriekUpperStarAdjunction Λ (Sigma.ι Y t)).unit :=
    Adjunction.unit_isIso_of_L_fully_faithful _
  exact ⟨(asIso ((upperStar Λ (Sigma.ι Y t)).map (biproduct.ι _ t))).symm ≪≫
    (asIso ((openImmersionLowerShriekUpperStarAdjunction Λ (Sigma.ι Y t)).unit.app
      (M t))).symm⟩

private lemma biproduct_shriek_counit_isIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {I : Type u} [Finite I]
    (Y : I → Scheme.{u})
    (G : Mod (Sheaf (Scheme.ProEt.topology (∐ Y)) Ab.{u + 1})
      (condensedRingObj Λ (∐ Y))) :
    IsIso (biproduct.desc (fun i ↦
      (openImmersionLowerShriekUpperStarAdjunction Λ (Sigma.ι Y i)).counit.app G)) := by
  apply module_iso_of_cover Λ Y (Sigma.ι Y)
    (fun x ↦ (sigmaOpenCover Y).exists_eq x)
  intro t
  let F := upperStar Λ (Sigma.ι Y t)
  have := pull_biproduct_shriek_inclusion_isIso Λ Y (fun i ↦
    (upperStar Λ (Sigma.ι Y i)).obj G) t
  have : IsIso (openImmersionLowerShriekUpperStarAdjunction Λ (Sigma.ι Y t)).unit :=
    Adjunction.unit_isIso_of_L_fully_faithful _
  have hε : IsIso (F.map
      ((openImmersionLowerShriekUpperStarAdjunction Λ (Sigma.ι Y t)).counit.app G)) := by
    let adj := openImmersionLowerShriekUpperStarAdjunction Λ (Sigma.ι Y t)
    have ht := adj.right_triangle_components G
    have : IsIso (adj.unit.app (F.obj G) ≫ F.map (adj.counit.app G)) := by
      rw [ht]
      exact IsIso.id _
    exact IsIso.of_isIso_comp_left (adj.unit.app (F.obj G)) _
  have : IsIso (F.map (biproduct.ι _ t) ≫ F.map (biproduct.desc (fun i ↦
      (openImmersionLowerShriekUpperStarAdjunction Λ (Sigma.ι Y i)).counit.app G))) := by
    rw [← F.map_comp, biproduct.ι_desc]
    exact hε
  have hι : IsIso (F.map (biproduct.ι (fun i ↦
      ((upperStar Λ (Sigma.ι Y i)) ⋙
        (openImmersionLowerShriek Λ (Sigma.ι Y i))).obj G) t)) :=
    pull_biproduct_shriek_inclusion_isIso Λ Y (fun i ↦
      (upperStar Λ (Sigma.ι Y i)).obj G) t
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ hι ‹_›

/-- The finite-disjoint-union lattice calculation for an arbitrary coefficient morphism. -/
theorem continuousLattice_finite_coproduct_of_coefficients
    (Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (φ : Λ ⟶ Λ') [IsMonHom φ]
    (X : Scheme.{u})
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Λ') X))
    {I : Type u} [Finite I] (Y : I → Scheme.{u}) (p : ∀ i, Y i ⟶ X)
    (M : ∀ i, Mod (Sheaf (Scheme.ProEt.topology (Y i)) Ab.{u + 1})
      (condensedRingObj (Λ) (Y i)))
    (hM : ∀ i, IsLocallyFree (condensedRingObj (Λ) (Y i)) (M i))
    (e : ∀ i, Nonempty
      ((Mod.extendScalars (coefficientMap (φ) (Y i))).obj (M i) ≅
        (CondensedRing.upperStar (Λ') (p i)).obj P)) :
    ∃ M : Mod (Sheaf (Scheme.ProEt.topology (∐ Y)) Ab.{u + 1})
        (condensedRingObj (Λ) (∐ Y)),
      (IsLocallyFree (condensedRingObj (Λ) (∐ Y)) M) ∧
      Nonempty ((Mod.extendScalars (coefficientMap (φ) (∐ Y))).obj M ≅
        (CondensedRing.upperStar (Λ') (Sigma.desc p)).obj P) := by
  classical
  let G := fun i ↦ (openImmersionLowerShriek Λ (Sigma.ι Y i)).obj (M i)
  let N := ⨁ G
  refine ⟨N, ?_, ?_⟩
  · have hlocal (i : I) : IsLocallyFree
        ((ProEtale.upperStar Ab.{u + 1} (Sigma.ι Y i)).obj (condensedRingObj Λ (∐ Y)))
        (((ProEtale.upperStar Ab.{u + 1} (Sigma.ι Y i)).mapMod _).obj N) := by
      apply locallyFree_of_extendScalars (condensedPullbackHom Λ (Sigma.ι Y i))
      exact IsLocallyFree.of_iso (nonempty_pull_biproduct_shriek_iso Λ Y M i).some.symm (hM i)
    choose D hD using hlocal
    let C : Scheme.Cover.{u} Scheme.proetalePrecoverage (∐ Y) :=
      { I₀ := I
        X := Y
        f := Sigma.ι Y
        mem₀ := Scheme.zariskiPrecoverage_le_proetalePrecoverage _
          (sigmaOpenCover Y).mem₀ }
    refine ⟨C.bind D, fun ij ↦ ?_⟩
    rcases ij with ⟨i, j⟩
    exact (ProEtale.free_pullback_comp_iff ((D i).f j) (Sigma.ι Y i) N).mpr (hD i j)
  · let Q := (upperStar Λ' (Sigma.desc p)).obj P
    have hcomp (i : I) :
        (upperStar Λ' (p i)).obj P ≅ (upperStar Λ' (Sigma.ι Y i)).obj Q :=
      (eqToIso (congrArg (fun f ↦ (upperStar Λ' f).obj P)
        (Sigma.ι_comp_desc p i).symm)) ≪≫ (upperStarComp Λ' (Sigma.ι Y i) (Sigma.desc p)).app P
    have ec (i : I) :
        (Mod.extendScalars (coefficientMap (φ) (∐ Y))).obj (G i) ≅
          (openImmersionLowerShriek Λ' (Sigma.ι Y i)).obj
            ((upperStar Λ' (Sigma.ι Y i)).obj Q) :=
      (openImmersionShriekIso (φ) (Sigma.ι Y i)).app (M i) ≪≫
        (openImmersionLowerShriek Λ' (Sigma.ι Y i)).mapIso ((e i).some ≪≫ hcomp i)
    let : PreservesBiproduct G
        (Mod.extendScalars (coefficientMap (φ) (∐ Y))) :=
      preservesBiproduct_of_preservesCoproduct _
    let eout : (⨁ fun i ↦ (openImmersionLowerShriek Λ' (Sigma.ι Y i)).obj
        ((upperStar Λ' (Sigma.ι Y i)).obj Q)) ≅ Q :=
      @asIso _ _ _ _ (biproduct.desc (fun i ↦
        (openImmersionLowerShriekUpperStarAdjunction Λ' (Sigma.ι Y i)).counit.app Q))
          (biproduct_shriek_counit_isIso Λ' Y Q)
    exact ⟨(Mod.extendScalars (coefficientMap (φ) (∐ Y))).mapBiproduct G ≪≫
      biproduct.mapIso ec ≪≫ eout⟩

end AlgebraicGeometry.ProEtale.CondensedRing
