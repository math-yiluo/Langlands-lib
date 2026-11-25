/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Fiber
import WeilConjectures.AlgebraicGeometry.Proper.Flat.ProperFlatSingleDerivedDirectImagePerfect
import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula

/-! Simultaneous affine strictly-perfect residue model data for a finite family.

## Implementation details

Restrict the finitely many proper flat direct images to affine
neighbourhoods of the marked point and intersect those neighbourhoods.  Apply
perfectness and the finite-free residue-model construction to the source and
each target, transporting the derived localization isomorphisms along the
restriction.  The residue ideal is the kernel of evaluation at the marked
point.  The construction is simultaneous in `Fin n`, including the empty
family. The comparison equations are not part of this data.

## References

* Stacks Project, Tags 01IB, 064K, 06YJ and 0B91
-/

@[expose] public section
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private theorem tensorPullback_invertible_local {X Y : Scheme.{v}} (g : X ⟶ Y)
    (M : Y.Modules) [M.IsInvertible] : ((Modules.tensorPullback g).obj M).IsInvertible := by
  obtain ⟨adj⟩ := Modules.nonempty_tensorPullbackAdjunction g
  exact Modules.IsInvertible.of_iso
    ((adj.leftAdjointUniq (Modules.pullbackPushforwardAdjunction g)).app M).symm

private theorem perfect_of_invertible_directImage
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    {Y T : Scheme.{v}} (p : Y ⟶ T)
    [Flat p] [IsProper p] [LocallyOfFinitePresentation p]
    (M : Y.Modules) [Modules.IsInvertible M] :
    IsPerfect T ((schemeDerivedDirectImage p).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings Y.toRingedSpace)) 0).obj M)) := by
  have := Modules.IsInvertible.sheafOfModules_isInvertible M
  exact properFlat_single_derivedDirectImage_perfect p M
    (Modules.isFlatOver_of_isInvertible p M)

private theorem restrict_strictlyPerfect_local (X : Scheme.{v}) (U V : X.Opens)
    (h : V ≤ U)
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hK : IsStrictlyPerfect X U K) :
    IsStrictlyPerfect X V
      (((SheafOfModules.overMap
        (moduleRings X.toRingedSpace) (homOfLE h)).mapHomologicalComplex (.up ℤ)).obj K) := by
  let F := SheafOfModules.overMap (moduleRings X.toRingedSpace) (homOfLE h)
  obtain ⟨⟨a, b, hb⟩, hp⟩ := hK
  constructor
  · exact ⟨a, b, fun n hn ↦ F.map_isZero (hb n hn)⟩
  · intro n
    obtain ⟨m, i, r, hir⟩ := hp n
    let e : F.obj (SheafOfModules.free
        (R := (moduleRings X.toRingedSpace).over U) (ULift.{v} (Fin m))) ≅
        SheafOfModules.free
          (R := (moduleRings X.toRingedSpace).over V) (ULift.{v} (Fin m)) :=
      (asIso (sigmaComparison F (fun _ : ULift.{v} (Fin m) ↦
        SheafOfModules.unit ((moduleRings X.toRingedSpace).over U)))).symm ≪≫
        Sigma.mapIso (fun _ ↦ SheafOfModules.overMapUnitIso (homOfLE h))
    refine ⟨m, F.map i ≫ e.hom, e.inv ≫ F.map r, ?_⟩
    change (F.map i ≫ e.hom) ≫ e.inv ≫ F.map r = 𝟙 (F.obj (K.X n))
    simp only [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp, hir]
    exact F.map_id _

private theorem restrict_model_local
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    (X : Scheme.{v}) (U V : X.Opens) (h : V ≤ U)
    (E : schemeDerivedCategory X)
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (e : (SheafOfModules.overFunctor.{v}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj E ≅ DerivedCategory.Q.obj K) :
    Nonempty ((SheafOfModules.overFunctor.{v}
      (moduleRings X.toRingedSpace) V).mapDerivedCategory.obj E ≅ DerivedCategory.Q.obj
        (((SheafOfModules.overMap
          (moduleRings X.toRingedSpace) (homOfLE h)).mapHomologicalComplex (.up ℤ)).obj K)) := by
  let F := SheafOfModules.overMap (moduleRings X.toRingedSpace) (homOfLE h)
  let G := SheafOfModules.overFunctor.{v} (moduleRings X.toRingedSpace) U
  have : PreservesFiniteLimits (G ⋙ F) := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (G ⋙ F) := comp_preservesFiniteColimits _ _
  exact ⟨(Functor.mapDerivedCategoryNatIso
    (SheafOfModules.overFunctorMap (moduleRings X.toRingedSpace) (homOfLE h))).symm.app E ≪≫
      (Functor.mapDerivedCategoryCompIso G F).symm.app E ≪≫ F.mapDerivedCategory.mapIso e ≪≫
        F.mapDerivedCategoryFactors.app K⟩

/-- The common affine and strictly-perfect model data needed by the residue bridge. -/
theorem picard_derived_fibre_residue_model_data
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    {X S : Scheme.{v}} (f : X ⟶ S) {n : ℕ}
    (Xi : Fin n → Scheme.{v}) (fi : ∀ i, Xi i ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    [∀ i, Flat (fi i)] [∀ i, IsProper (fi i)]
    [∀ i, LocallyOfFinitePresentation (fi i)]
    (ui : ∀ i, Xi i ⟶ X) (hui : ∀ i, ui i ≫ f = fi i)
    (L : X.Modules) [L.IsInvertible]
    (W : Scheme.{v}) (k : W ⟶ S) [IsImmersion k]
    (w : W) (s : S) (hw : k w = s)
    (τ : (Modules.tensorPullback (pullback.fst f (S.fromSpecResidueField s))).obj L ≅
      SheafOfModules.unit (pullback f (S.fromSpecResidueField s)).ringCatSheaf) :
    let E := (schemeDerivedDirectImage (pullback.snd f k)).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst f k)).obj L))
    let Ei := fun i ↦ (schemeDerivedDirectImage (pullback.snd (fi i) k)).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback (fi i) k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst (fi i) k)).obj
            ((Modules.tensorPullback (ui i)).obj L)))
    ∃ (U : W.Opens) (hwU : w ∈ U), IsAffineOpen U ∧
      ∃ (p : Ideal Γ(W, U)) (_ : p.IsPrime)
        (hp : p = RingHom.ker (W.evaluation U w hwU).hom)
        (K : CochainComplex
          (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
        (C : Fin n → CochainComplex
          (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ),
        IsStrictlyPerfect W U K ∧ (∀ i, IsStrictlyPerfect W U (C i)) ∧
        Nonempty ((SheafOfModules.overFunctor.{v}
          (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj E ≅
            DerivedCategory.Q.obj K) ∧
        (∀ i, Nonempty ((SheafOfModules.overFunctor.{v}
          (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj (Ei i) ≅
            DerivedCategory.Q.obj (C i)) ) := by
  classical
  dsimp only
  let E := (schemeDerivedDirectImage (pullback.snd f k)).obj
    ((DerivedCategory.singleFunctor
      (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
        ((Modules.tensorPullback (pullback.fst f k)).obj L))
  let Ei := fun i ↦ (schemeDerivedDirectImage (pullback.snd (fi i) k)).obj
    ((DerivedCategory.singleFunctor
      (SheafOfModules.{v} (moduleRings (pullback (fi i) k).toRingedSpace)) 0).obj
        ((Modules.tensorPullback (pullback.fst (fi i) k)).obj
          ((Modules.tensorPullback (ui i)).obj L)))
  have hEperf : IsPerfect W E := by
    let G := (Modules.tensorPullback (pullback.fst f k)).obj L
    letI : Modules.IsInvertible G := tensorPullback_invertible_local _ _
    dsimp [E]
    exact perfect_of_invertible_directImage (pullback.snd f k)
      G
  have hEiperf : ∀ i, IsPerfect W (Ei i) := by
    intro i
    let M := (Modules.tensorPullback (pullback.fst (fi i) k)).obj
      ((Modules.tensorPullback (ui i)).obj L)
    letI : Modules.IsInvertible ((Modules.tensorPullback (ui i)).obj L) :=
      tensorPullback_invertible_local _ _
    letI : Modules.IsInvertible M := tensorPullback_invertible_local _ _
    dsimp [Ei, M]
    exact perfect_of_invertible_directImage (pullback.snd (fi i) k) M
  obtain ⟨U₀, hw₀, K₀, hK₀, eK₀⟩ := hEperf w
  choose Ui hwUi Ki hKi ei using fun i ↦ hEiperf i w
  let V : W.Opens := U₀ ⊓ ⨅ i, Ui i
  have hwV : w ∈ V := by
    change w ∈ ((U₀ ⊓ ⨅ i, Ui i : W.Opens) : Set W)
    rw [TopologicalSpace.Opens.coe_inf, TopologicalSpace.Opens.coe_iInf,
      Set.mem_inter_iff, Set.mem_iInter]
    exact ⟨hw₀, hwUi⟩
  obtain ⟨U, hUaff, hwU, hsub⟩ :=
    exists_isAffineOpen_mem_and_subset (U := V) hwV
  have hU₀ : U ≤ U₀ := hsub.trans inf_le_left
  have hUi : ∀ i, U ≤ Ui i := fun i ↦
    hsub.trans (inf_le_right.trans (iInf_le (fun i : Fin n ↦ Ui i) i))
  let R (A : W.Opens)
      (B : CochainComplex
        (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over A)) ℤ)
      (h : U ≤ A) :=
    let F := SheafOfModules.overMap (moduleRings W.toRingedSpace) (homOfLE h)
    (F.mapHomologicalComplex (.up ℤ)).obj B
  let K := R U₀ K₀ hU₀
  let C := fun i ↦ R (Ui i) (Ki i) (hUi i)
  have hK : IsStrictlyPerfect W U K :=
    restrict_strictlyPerfect_local W U₀ U hU₀ K₀ hK₀
  have hC : ∀ i, IsStrictlyPerfect W U (C i) := fun i ↦
    restrict_strictlyPerfect_local W (Ui i) U (hUi i) (Ki i) (hKi i)
  have hE : Nonempty ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj E ≅
        DerivedCategory.Q.obj K) :=
    restrict_model_local W U₀ U hU₀ E K₀ eK₀.some
  have hCi : ∀ i, Nonempty ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj (Ei i) ≅
        DerivedCategory.Q.obj (C i)) := fun i ↦
    restrict_model_local W (Ui i) U (hUi i) (Ei i) (Ki i) (ei i).some
  let p : Ideal Γ(W, U) := RingHom.ker (W.evaluation U w hwU).hom
  have hpEq : p = RingHom.ker (W.evaluation U w hwU).hom := rfl
  have hp : p.IsPrime := RingHom.ker_isPrime (W.evaluation U w hwU).hom
  exact ⟨U, hwU, hUaff, p, hp, hpEq, K, C, hK, hC, hE, hCi⟩

end AlgebraicGeometry.Scheme
