/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Fiber
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage

public import WeilConjectures.AlgebraicGeometry.DerivedFiberBetti
import WeilConjectures.AlgebraicGeometry.Proper.Flat.ProperFlatSingleDerivedDirectImagePerfect
import WeilConjectures.AlgebraicGeometry.Perfect.PerfectFiniteFreeResidueModel
import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import WeilConjectures.AlgebraicGeometry.DescendedInvertibleNeighbourhood
import WeilConjectures.AlgebraicGeometry.Picard.Direct.PicardDirectImageFibreBetti
import WeilConjectures.AlgebraicGeometry.Residue.ResidueRankModelDifferential

/-! # Common trivializations and a minimal source model

## References

* Stacks Project, Tag 0BF2, through the first displayed source complex
* Stacks Project, Tag 0BF2, first two proof paragraphs
* Tags 0B91 and 0BCD
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Perfectness follows directly from proper relatively flat base change. -/
private theorem invertible_directImage_isPerfect
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    {Y T : Scheme.{v}} (p : Y ⟶ T)
    [Flat p] [IsProper p] [LocallyOfFinitePresentation p]
    (M : Y.Modules) [M.IsInvertible] :
    IsPerfect T ((schemeDerivedDirectImage p).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings Y.toRingedSpace)) 0).obj M)) := by
  have := Modules.IsInvertible.sheafOfModules_isInvertible M
  exact properFlat_single_derivedDirectImage_perfect p M
    (Modules.isFlatOver_of_isInvertible p M)

/-- Restrict a bounded free model inside a prescribed neighbourhood. -/
private theorem refine_residue_model
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    (W : Scheme.{v}) (E : schemeDerivedCategory W) (w : W)
    (V : W.Opens) (hwV : w ∈ V) (U : W.Opens) (hwU : w ∈ U)
    (K : CochainComplex (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hb : ∃ a b : ℤ, ∀ j : ℤ, j < a ∨ b < j → IsZero (K.X j))
    (hrank : ∀ j : ℤ, Nonempty (K.X j ≅ SheafOfModules.free
      (R := (moduleRings W.toRingedSpace).over U)
      (ULift.{v} (Fin (derivedFiberBetti W E j w)))))
    (he : Nonempty ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj E ≅
        DerivedCategory.Q.obj K)) :
    ∃ (U' : W.Opens) (_ : w ∈ U'), IsAffineOpen U' ∧ U' ≤ V ∧
      ∃ K' : CochainComplex
          (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U')) ℤ,
        (∃ a b : ℤ, ∀ j : ℤ, j < a ∨ b < j → IsZero (K'.X j)) ∧
        (∀ j : ℤ, Nonempty (K'.X j ≅ SheafOfModules.free
          (R := (moduleRings W.toRingedSpace).over U')
          (ULift.{v} (Fin (derivedFiberBetti W E j w))))) ∧
        Nonempty ((SheafOfModules.overFunctor.{v}
          (moduleRings W.toRingedSpace) U').mapDerivedCategory.obj E ≅
            DerivedCategory.Q.obj K') := by
  classical
  obtain ⟨U', hU'aff, hwU', hsub⟩ :=
    exists_isAffineOpen_mem_and_subset (U := U ⊓ V) ⟨hwU, hwV⟩
  have hU'U : U' ≤ U := hsub.trans inf_le_left
  let F := SheafOfModules.overMap.{v} (moduleRings W.toRingedSpace) (homOfLE hU'U)
  let G := SheafOfModules.overFunctor.{v} (moduleRings W.toRingedSpace) U
  let G' := SheafOfModules.overFunctor.{v} (moduleRings W.toRingedSpace) U'
  let K' := (F.mapHomologicalComplex (.up ℤ)).obj K
  have : PreservesFiniteLimits (G ⋙ F) := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (G ⋙ F) := comp_preservesFiniteColimits _ _
  let e' : G'.mapDerivedCategory.obj E ≅ DerivedCategory.Q.obj K' :=
    (Functor.mapDerivedCategoryNatIso
      (SheafOfModules.overFunctorMap.{v} (moduleRings W.toRingedSpace)
        (homOfLE hU'U))).symm.app E ≪≫
      (Functor.mapDerivedCategoryCompIso G F).symm.app E ≪≫
      F.mapDerivedCategory.mapIso he.some ≪≫ F.mapDerivedCategoryFactors.app K
  refine ⟨U', hwU', hU'aff, hsub.trans inf_le_right, K', ?_, ?_, ⟨e'⟩⟩
  · obtain ⟨a, b, hab⟩ := hb
    exact ⟨a, b, fun j hj ↦ F.map_isZero (hab j hj)⟩
  · intro j
    refine ⟨F.mapIso (hrank j).some ≪≫ ?_⟩
    exact (SheafOfModules.mapFreeIso F
      (ULift.{v} (Fin (derivedFiberBetti W E j w)))
      (SheafOfModules.overMapUnitIso (homOfLE hU'U)).symm).symm

set_option linter.unusedVariables false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Choose a common affine neighbourhood with trivial target bundles and a minimal
finite-free representative of the source direct image. -/
theorem picard_h1_common_minimal_model
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    {X S : Scheme.{v}} (f : X ⟶ S) {n : ℕ}
    (Xi : Fin n → Scheme.{v}) (fi : ∀ i, Xi i ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    [∀ i, Flat (fi i)] [∀ i, IsProper (fi i)] [∀ i, LocallyOfFinitePresentation (fi i)]
    (ui : ∀ i, Xi i ⟶ X) (hui : ∀ i, ui i ≫ f = fi i)
    (hO : ∀ {T : Scheme.{v}} (g : T ⟶ S),
      IsIso ((Classical.choose
        (Scheme.Modules.exists_tensorPullbackAdjunction (pullback.snd f g))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)))
    (hOi : ∀ i, ∀ {T : Scheme.{v}} (g : T ⟶ S),
      IsIso ((Classical.choose
        (Scheme.Modules.exists_tensorPullbackAdjunction (pullback.snd (fi i) g))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)))
    (L : X.Modules) [L.IsInvertible]
    (W : Scheme.{v}) (k : W ⟶ S) [IsImmersion k]
    (w : W) (s : S) (hw : k w = s)
    (hLi : ∀ i, ∃ (N : W.Modules) (_ : N.IsFiniteLocallyFree),
      Nonempty ((Modules.tensorPullback (pullback.fst (fi i) k)).obj
        ((Modules.tensorPullback (ui i)).obj L) ≅
        (Modules.tensorPullback (pullback.snd (fi i) k)).obj N))
    (hLs : ∃ (N : (Spec (S.residueField s)).Modules) (_ : N.IsFiniteLocallyFree),
      Nonempty ((Modules.tensorPullback (pullback.fst f (S.fromSpecResidueField s))).obj L ≅
        (Modules.tensorPullback (pullback.snd f (S.fromSpecResidueField s))).obj N)) :
    let E := ((schemeDerivedDirectImage (pullback.snd f k)).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst f k)).obj L)))
    ∃ (U : W.Opens) (hwU : w ∈ U), IsAffineOpen U ∧
      (∀ i, Nonempty
        ((Modules.tensorPullback (pullback.fst (fi i) (U.ι ≫ k))).obj
          ((Modules.tensorPullback (ui i)).obj L) ≅
          SheafOfModules.unit (pullback (fi i) (U.ι ≫ k)).ringCatSheaf)) ∧
      ∃ (m : ℕ) (K : CochainComplex
          (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ),
        (∃ a b : ℤ, ∀ j : ℤ, j < a ∨ b < j → IsZero (K.X j)) ∧
        (∀ j : ℤ, j < 0 → derivedFiberBetti W E j w = 0) ∧
        (∀ j : ℤ, Nonempty (K.X j ≅ SheafOfModules.free
          (R := (moduleRings W.toRingedSpace).over U)
          (ULift.{v} (Fin (derivedFiberBetti W E j w))))) ∧
        ∃ (e0 : (K.X 0).val.obj (.op (Over.mk (𝟙 U))) ≃ₗ[Γ(W, U)] Γ(W, U))
          (e1 : (K.X 1).val.obj (.op (Over.mk (𝟙 U))) ≃ₗ[Γ(W, U)] (Fin m → Γ(W, U))),
          Nonempty ((SheafOfModules.overFunctor.{v}
            (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj E ≅
              DerivedCategory.Q.obj K) ∧
          ∀ i, W.evaluation U w hwU
            (e1 ((K.d 0 1).val.app (.op (Over.mk (𝟙 U))) (e0.symm 1)) i) = 0 := by
  classical
  intro E
  have target_local (i : Fin n) : ∃ V : W.Opens, w ∈ V ∧ ∀ U : W.Opens, U ≤ V →
      Nonempty ((Modules.tensorPullback (pullback.fst (fi i) (U.ι ≫ k))).obj
        ((Modules.tensorPullback (ui i)).obj L) ≅
        SheafOfModules.unit (pullback (fi i) (U.ι ≫ k)).ringCatSheaf) := by
    let e := (Classical.choose (Modules.exists_tensorPullbackAdjunction (ui i))).leftAdjointUniq
      (Modules.pullbackPushforwardAdjunction (ui i))
    have : ((Modules.tensorPullback (ui i)).obj L).IsInvertible :=
      Modules.IsInvertible.of_iso (e.app L).symm
    exact exists_descendedInvertible_neighbourhood (fi i) (hOi i)
      ((Modules.tensorPullback (ui i)).obj L) W k w (hLi i)
  choose V hwV hV using target_local
  let Vcommon : W.Opens := ⨅ i, V i
  have hwcommon : w ∈ Vcommon := by
    change w ∈ ((⨅ i, V i : W.Opens) : Set W)
    rw [TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
    exact hwV
  let Y := pullback f k
  let G : Y.Modules := (Modules.tensorPullback (pullback.fst f k)).obj L
  let eg := (Classical.choose
    (Modules.exists_tensorPullbackAdjunction (pullback.fst f k))).leftAdjointUniq
      (Modules.pullbackPushforwardAdjunction (pullback.fst f k))
  have : G.IsInvertible := Modules.IsInvertible.of_iso (eg.app L).symm
  have hperfect : IsPerfect W E := invertible_directImage_isPerfect (pullback.snd f k) G
  obtain ⟨hnegative, hzero⟩ := picard_directImage_fibre_betti f hO L W k w s hw hLs
  obtain ⟨hfin, _, U0, hw0, _, K0, hb0, hrank0, he0⟩ :=
    exists_finiteFreeResidueModel W E hperfect w
  obtain ⟨U, hwU, hU, hUV, K, hb, hrank, he⟩ :=
    refine_residue_model W E w Vcommon hwcommon U0 hw0 K0 hb0 hrank0 he0
  obtain ⟨eK0⟩ := hrank 0
  rw [hzero] at eK0
  let e0 : (K.X 0).val.obj (.op (Over.mk (𝟙 U))) ≃ₗ[Γ(W, U)] Γ(W, U) :=
    (SheafOfModules.sectionsLinearEquivOfIsoFree eK0 (.op (Over.mk (𝟙 U)))) ≪≫ₗ
      (LinearEquiv.piUnique Γ(W, U) (fun _ : ULift.{v} (Fin 1) ↦ Γ(W, U)))
  let m := derivedFiberBetti W E 1 w
  let e1 : (K.X 1).val.obj (.op (Over.mk (𝟙 U))) ≃ₗ[Γ(W, U)] (Fin m → Γ(W, U)) :=
    (SheafOfModules.sectionsLinearEquivOfIsoFree (hrank 1).some
      (.op (Over.mk (𝟙 U)))) ≪≫ₗ
        (LinearEquiv.piCongrLeft Γ(W, U) (fun _ : Fin m ↦ Γ(W, U)) Equiv.ulift)
  refine ⟨U, hwU, hU, ?_, m, K, hb, hnegative, hrank, e0, e1, he, ?_⟩
  · intro i
    exact hV i U (hUV.trans (iInf_le V i))
  · exact residueRankModel_differential_eval_eq_zero W E w hfin U hwU hU K
      hb hrank he m e1 (e0.symm 1)

end AlgebraicGeometry.Scheme
