/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PicardTermwiseModels
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
import WeilConjectures.AlgebraicGeometry.PicardTermwiseCompositeCounit
import WeilConjectures.AlgebraicGeometry.FlatComplexDerivedPullback
import WeilConjectures.AlgebraicGeometry.SingleComplexOpenRestrictionData
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed

/-! # Coherence of the local perfect target model

## References

* Stacks Project, Tags 06YJ, 0D5S and 08DW
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
noncomputable section

variable [d : ∀ Y : Scheme.{v},
  HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]

variable [dO : ∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
  (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]

attribute [local instance] Functor.additive_of_preserves_binary_products

omit d dO in
private theorem flat_retract (Y : Scheme.{v})
    (M : SheafOfModules.{v} (moduleRings Y.toRingedSpace)) (m : ℕ)
    (i : M ⟶ SheafOfModules.free (R := moduleRings Y.toRingedSpace) (ULift.{v} (Fin m)))
    (r : SheafOfModules.free (R := moduleRings Y.toRingedSpace) (ULift.{v} (Fin m)) ⟶ M)
    (h : i ≫ r = 𝟙 M) : SheafOfModules.IsFlat M := by
  let := SheafOfModules.monoidalCategory Y.sheaf
  let := SheafOfModules.symmetricCategory Y.sheaf
  obtain ⟨⟨mp⟩, ⟨mc⟩, _⟩ := SheafOfModules.tensorClosed Y.sheaf
  let := mp
  let := mc
  have := SheafOfModules.isGrothendieckAbelian (moduleRings Y.toRingedSpace)
  have hf : ObjectProperty.flat
      (SheafOfModules.free (R := moduleRings Y.toRingedSpace) (ULift.{v} (Fin m))) :=
    ObjectProperty.flat_coproduct _ (fun _ ↦ ObjectProperty.prop_unit _)
  exact (ObjectProperty.flat_of_retract ⟨i, r, h⟩ hf).2

omit d dO in
private def targetComplex (W : Scheme.{v}) (U : W.Opens)
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ) :
    CochainComplex (SheafOfModules.{v} (moduleRings U.toScheme.toRingedSpace)) ℤ :=
  let A : SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U) ⥤
      SheafOfModules.{v} (moduleRings U.toScheme.toRingedSpace) :=
    (Modules.overEquiv U).functor
  (A.mapHomologicalComplex (.up ℤ)).obj K

omit d dO in
private theorem transported_model_flat (W : Scheme.{v}) (U : W.Opens)
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hK : IsStrictlyPerfect W U K) :
    let P := targetComplex W U K
    (∃ b : ℤ, ∀ n : ℤ, b < n → IsZero (P.X n)) ∧
      ∀ n : ℤ, SheafOfModules.IsFlat (P.X n) := by
  dsimp only [targetComplex]
  let A : SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U) ⥤
      SheafOfModules.{v} (moduleRings U.toScheme.toRingedSpace) :=
      (Modules.overEquiv U).functor
  let P := (A.mapHomologicalComplex (.up ℤ)).obj K
  obtain ⟨⟨a, b, hb⟩, hp⟩ := hK
  refine ⟨⟨b, fun n hn ↦ A.map_isZero (hb n (Or.inr hn))⟩, ?_⟩
  intro n
  obtain ⟨m, i, r, hir⟩ := hp n
  let ei : A.obj (SheafOfModules.free
      (R := (moduleRings W.toRingedSpace).over U) (ULift.{v} (Fin m))) ≅
      SheafOfModules.free (R := moduleRings U.toScheme.toRingedSpace)
        (ULift.{v} (Fin m)) :=
    (asIso (sigmaComparison A (fun _ : ULift.{v} (Fin m) ↦
      SheafOfModules.unit ((moduleRings W.toRingedSpace).over U)))).symm ≪≫
    Sigma.mapIso (fun _ ↦ U.sheafOfModulesEquivOverUnit (moduleRings W.toRingedSpace))
  apply flat_retract U.toScheme (P.X n) m (A.map i ≫ ei.hom) (ei.inv ≫ A.map r)
  change (A.map i ≫ ei.hom) ≫ ei.inv ≫ A.map r = 𝟙 (A.obj (K.X n))
  simp only [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp, hir]
  exact A.map_id _

omit dO in
private theorem pinned_counit_isIso {X Y : Scheme.{v}} (f : X ⟶ Y)
    (P : CochainComplex (SheafOfModules.{v} (moduleRings Y.toRingedSpace)) ℤ)
    (hb : ∃ b : ℤ, ∀ n : ℤ, b < n → IsZero (P.X n))
    (hp : ∀ n : ℤ, SheafOfModules.IsFlat (P.X n)) :
    IsIso ((picardTermwiseCounit f).app P) := by
  let a : ∀ {X Y : Scheme.{v}} (f : X ⟶ Y), (Modules.tensorPullback f).Additive :=
    fun f ↦ Classical.choose exists_derivedPullbackComposition f
  let ε : ∀ {X Y : Scheme.{v}} (f : X ⟶ Y),
      DerivedCategory.Qh ⋙ derivedPullback f ⟶
        (Modules.tensorPullback f).mapHomotopyCategory (.up ℤ) ⋙
          DerivedCategory.Qh (C := SheafOfModules.{v} (moduleRings X.toRingedSpace)) :=
    fun f ↦ Classical.choose (Classical.choose_spec exists_derivedPullbackComposition) f
  let : (Modules.tensorPullback f).Additive := a f
  let A := SheafOfModules.{v} (moduleRings Y.toRingedSpace)
  let q := HomotopyCategory.quotient A (.up ℤ)
  let Wq := HomotopyCategory.quasiIso A (.up ℤ)
  obtain ⟨F, hF, hFmap, hFadd, ε₀, hε₀, ⟨e, he⟩⟩ :=
    flatComplexDerivedPullback f P hb hp
  have h : F = Modules.tensorPullback f :=
    CategoryTheory.Functor.ext hF (fun M N g ↦ hFmap g)
  subst F
  have : (derivedPullback f).IsLeftDerivedFunctor ε₀ Wq := hε₀
  have hε : (derivedPullback f).IsLeftDerivedFunctor (ε f) Wq :=
    (Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition))) f
  have hi : IsIso (ε₀.app (q.obj P)) := by
    rw [← he]
    infer_instance
  have hfac := Functor.leftDerived_fac_app (derivedPullback f) ε₀ Wq
    (derivedPullback f) (ε f) (q.obj P)
  have hlift : IsIso ((derivedPullback f).leftDerivedLift ε₀ Wq
      (derivedPullback f) (ε f)) :=
    (Functor.isLeftDerivedFunctor_iff_isIso_leftDerivedLift
      (derivedPullback f) ε₀ Wq (derivedPullback f) (ε f)).mp hε
  have hi' : IsIso ((ε f).app (q.obj P)) := by
    rw [← hfac]
    infer_instance
  dsimp only [picardTermwiseCounit, NatTrans.comp_app, Functor.whiskerLeft_app]
  infer_instance

private theorem open_model_iso (W : Scheme.{v}) (E : schemeDerivedCategory W)
    (U : W.Opens)
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hE : Nonempty ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj E ≅
        DerivedCategory.Q.obj K)) :
    Nonempty ((derivedPullback U.ι).obj E ≅
      DerivedCategory.Q.obj (targetComplex W U K)) := by
  let A : SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U) ⥤
      SheafOfModules.{v} (moduleRings U.toScheme.toRingedSpace) :=
      (Modules.overEquiv U).functor
  let R := SheafOfModules.overFunctor.{v} (moduleRings W.toRingedSpace) U
  obtain ⟨e⟩ := hE
  let : HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} (moduleRings U.toScheme.toRingedSpace)) := d U.toScheme
  exact ⟨(singleComplexOpenPullbackIso W U).app E ≪≫
    (Functor.mapDerivedCategoryCompIso R A).symm.app E ≪≫
    A.mapDerivedCategory.{v + 1, v + 1}.mapIso e ≪≫
      A.mapDerivedCategoryFactors.{v + 1, v + 1}.app K⟩

/-- The perfect target model has object comparisons compatible with the canonical
composition counit. This assertion involves no morphism out of a source single. -/
theorem picard_termwise_target_coherence
    (W : Scheme.{v}) (E : schemeDerivedCategory W) (U : W.Opens)
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hK : IsStrictlyPerfect W U K)
    (hE : Nonempty ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj E ≅
        DerivedCategory.Q.obj K)) :
    ∃ b : ∀ {T : Scheme.{v}} (t : T ⟶ W) (s : T ⟶ U.toScheme),
        s ≫ U.ι = t → ((derivedPullback t).obj E ≅
          DerivedCategory.Q.obj (picardTermwiseModel W U K s)),
      ∀ {T T' : Scheme.{v}} (i : T' ⟶ T) (t : T ⟶ W) (t' : T' ⟶ W)
        (s : T ⟶ U.toScheme) (s' : T' ⟶ U.toScheme)
        (ht : i ≫ t = t') (hs : i ≫ s = s')
        (hf : s ≫ U.ι = t) (hf' : s' ≫ U.ι = t'),
      let c := (Classical.choose (Classical.choose_spec (Classical.choose_spec
        (Classical.choose_spec exists_derivedPullbackComposition)))) i t ≪≫
          eqToIso (congrArg (fun g : T' ⟶ W ↦ derivedPullback g) ht)
      (b t' s' hf').hom ≫
          DerivedCategory.Q.map (picardTermwiseModelRestrictionIso W U K i s s' hs).hom =
        c.inv.app E ≫ (derivedPullback i).map (b t s hf).hom ≫
          (picardTermwiseCounit i).app (picardTermwiseModel W U K s) := by
  classical
  let P := targetComplex W U K
  let e : (derivedPullback U.ι).obj E ≅ DerivedCategory.Q.obj P :=
    Classical.choice (open_model_iso (d := d) (dO := dO) W E U K hE)
  have hP : (∃ b : ℤ, ∀ n : ℤ, b < n → IsZero (P.X n)) ∧
      (∀ n : ℤ, SheafOfModules.IsFlat (P.X n)) := transported_model_flat W U K hK
  have hε {T : Scheme.{v}} (s : T ⟶ U.toScheme) :
      IsIso ((picardTermwiseCounit s).app P) := pinned_counit_isIso (d := d) s P hP.1 hP.2
  let c : ∀ {X Y Z : Scheme.{v}} (f : X ⟶ Y) (g : Y ⟶ Z),
      derivedPullback g ⋙ derivedPullback f ≅ derivedPullback (f ≫ g) :=
    fun f g ↦ Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition))) f g
  let b : ∀ {T : Scheme.{v}} (t : T ⟶ W) (s : T ⟶ U.toScheme),
      s ≫ U.ι = t → ((derivedPullback t).obj E ≅
        DerivedCategory.Q.obj (picardTermwiseModel W U K s)) :=
    fun {T} t s hf ↦ by
      have := hε s
      exact asIso (((c s U.ι ≪≫ eqToIso
        (congrArg (fun g : T ⟶ W ↦ derivedPullback g) hf)).inv.app E) ≫
        (derivedPullback s).map e.hom ≫ (picardTermwiseCounit s).app P)
  refine ⟨b, ?_⟩
  intro T T' i t t' s s' ht hs hf hf'
  exact picard_termwise_composite_counit W E U K e.hom i t t' s s' ht hs hf hf'

end
end AlgebraicGeometry.Scheme
