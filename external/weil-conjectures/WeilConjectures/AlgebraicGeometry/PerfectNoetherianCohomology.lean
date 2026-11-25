/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel

/-! # Bounded coherent cohomology of perfect complexes

Source: Stacks Project, Derived Categories of Schemes, Tag 0FXU, part (1).
(blueprint: lem-pc-perfect-noetherian-cohomology).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem finitePresentation_overEquiv_inverse (X : Scheme.{u}) (U : X.Opens)
    (M : U.toScheme.Modules) [M.IsFinitePresentation] :
    ((Modules.overEquiv (X := X) U).inverse.obj M).IsFinitePresentation := by
  have (V : CategoryTheory.Over U) :
      (Over.post (X := V) U.overEquivalence.symm.inverse).IsContinuous
        ((Opens.grothendieckTopology ↥X).over U |>.over V)
        ((Opens.grothendieckTopology ↥U).over
          (U.overEquivalence.functor.obj V)) :=
    Functor.isContinuous_of_coverPreserving
      (compatiblePreservingOfFlat _ _)
      (((U.overEquivalence.symm.toAdjunction.isCocontinuous_iff_coverPreserving _ _).mp
        inferInstance).overPost V)
  exact @SheafOfModules.isFinitePresentation_pushforward_of_isLeftAdjoint.{u}
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf) _ _ (fun V ↦ this V) _ _ M _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem finitePresentation_free (X : Scheme.{u}) (n : ℕ) :
    (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin n))).IsFinitePresentation := by
  let P := SheafOfModules.presentationOfIsCokernelFree
    (0 : SheafOfModules.free (PEmpty.{u + 1}) ⟶
      SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin n)))
    (𝟙 _) (by simp) (CokernelCofork.IsColimit.ofId _ rfl)
  have : P.IsFinite := ⟨⟨inferInstanceAs (Finite (ULift.{u} (Fin n)))⟩,
    ⟨inferInstanceAs (Finite (PEmpty.{u + 1}))⟩⟩
  exact P.isFinitePresentation

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem finitePresentation_retract (X : Scheme.{u}) [IsLocallyNoetherian X]
    (M N : X.Modules) [N.IsFinitePresentation]
    (ι : M ⟶ N) (π : N ⟶ M) (h : ι ≫ π = 𝟙 M) : M.IsFinitePresentation := by
  let f : N ⟶ N := 𝟙 N - π ≫ ι
  have hf : ι ≫ f = 0 := by simp [f, Preadditive.comp_sub, ← Category.assoc, h]
  have hk := Modules.isFinitePresentation_kernel f
  let e : M ≅ kernel f :=
    { hom := kernel.lift f ι hf
      inv := kernel.ι f ≫ π
      hom_inv_id := by simp [← Category.assoc, h]
      inv_hom_id := by
        apply (cancel_mono (kernel.ι f)).1
        simp only [Category.assoc, kernel.lift_ι, Category.id_comp]
        have hc := kernel.condition f
        change kernel.ι f ≫ (𝟙 N - π ≫ ι) = 0 at hc
        exact (sub_eq_zero.mp (by simpa only
          [Preadditive.comp_sub, Category.comp_id] using hc)).symm }
  exact (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso e.symm hk

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem finitePresentation_homology (X : Scheme.{u}) [IsLocallyNoetherian X]
    (K : CochainComplex X.Modules ℤ) (hK : ∀ n, (K.X n).IsFinitePresentation) (i : ℤ) :
    (K.homology i).IsFinitePresentation := by
  have (n : ℤ) : (K.X n).IsFinitePresentation := hK n
  let S := K.sc i
  have : S.X₁.IsFinitePresentation := hK _
  have : S.X₂.IsFinitePresentation := hK _
  have : S.X₃.IsFinitePresentation := hK _
  have := Modules.isFinitePresentation_kernel S.g
  have hc := Modules.isFinitePresentation_cokernel (kernel.lift S.g S.f S.zero)
  exact (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso
    S.homologyIsoCokernelLift.symm hc

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem local_model_homology (X : Scheme.{u}) [IsLocallyNoetherian X]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (E : schemeDerivedCategory X) (U : X.Opens)
    (K : CochainComplex (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hK : IsStrictlyPerfect X U K)
    (e : (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj E ≅ DerivedCategory.Q.obj K) :
    (∀ i : ℤ, ((Modules.restrictFunctor U.ι).obj
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj E)).IsFinitePresentation) ∧
    (∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i →
      IsZero ((Modules.restrictFunctor U.ι).obj
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj E))) := by
  let F := (Modules.overEquiv (X := X) U).functor
  have : F.Additive := Functor.additive_of_preserves_binary_products F
  let O := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U
  let L := (F.mapHomologicalComplex (.up ℤ)).obj K
  have hterms (n : ℤ) : (L.X n).IsFinitePresentation := by
    change (F.obj (K.X n)).IsFinitePresentation
    obtain ⟨m, ι, π, h⟩ := hK.2 n
    have hfree := finitePresentation_free U.toScheme m
    have hfree' : (F.obj (SheafOfModules.free
        (R := (moduleRings X.toRingedSpace).over U)
        (ULift.{u} (Fin m)))).IsFinitePresentation :=
      (SheafOfModules.isFinitePresentation U.toScheme.ringCatSheaf).prop_of_iso
        (SheafOfModules.mapFreeIso F (ULift.{u} (Fin m))
          (U.sheafOfModulesEquivOverUnit X.ringCatSheaf).symm) hfree
    exact finitePresentation_retract U.toScheme _ _ (F.map ι) (F.map π)
      (by rw [← F.map_comp, h, F.map_id])
  let cmp (i : ℤ) : (Modules.restrictFunctor U.ι).obj
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj E) ≅ L.homology i :=
    ((Modules.overFunctorEquiv U).symm.app _) ≪≫
      F.mapIso ((O.mapDerivedCategoryHomologyFunctorIso i).app E ≪≫
        (DerivedCategory.homologyFunctor _ i).mapIso e ≪≫
        (DerivedCategory.homologyFunctorFactors _ i).app K) ≪≫
      ((F.mapHomologicalComplexHomologyIso (.up ℤ) i).app K).symm
  constructor
  · intro i
    exact (SheafOfModules.isFinitePresentation U.toScheme.ringCatSheaf).prop_of_iso
      (cmp i).symm (finitePresentation_homology U.toScheme L hterms i)
  · obtain ⟨a, b, hab⟩ := hK.1
    refine ⟨a, b, fun i hi ↦ ?_⟩
    have hz : IsZero (L.X i) := F.map_isZero (hab i hi)
    have hh : IsZero (L.homology i) := (L.sc i).isZero_homology_of_isZero_X₂ hz
    exact hh.of_iso (cmp i)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A perfect complex on a Noetherian scheme has bounded coherent cohomology.
Source: Stacks Project, Derived Categories of Schemes, Lemma
`perfect-lemma-perfect-on-noetherian`, Tag 0FXU, part (1).

Proof: choose strictly perfect neighbourhoods from `IsPerfect`. Refine them by affine
opens and then by opens where the finite projective terms become finite free. On these
opens the kernels and images of the matrices are finite modules over Noetherian rings;
their quotients are finite as well. Their associated sheaves are therefore coherent,
and exact restriction identifies them with the restrictions of the cohomology of E.
Coherence is local, so all cohomology sheaves of E are coherent. Each bounded local
model has zero cohomology outside its term bounds. Quasi-compactness selects a finite
subcover; take the minimum of its lower bounds and maximum of its upper bounds.
Outside that interval every restriction of the cohomology sheaf is zero, so the sheaf
itself is zero. On the empty scheme all sheaves are zero; use bounds 0 and 0.
(blueprint: lem-pc-perfect-noetherian-cohomology). -/
theorem perfect_bounded_coherent_cohomology (X : Scheme.{u}) [IsNoetherian X]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (E : schemeDerivedCategory X) (hE : IsPerfect X E) :
    (∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i →
      IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj E)) ∧
    (∀ i : ℤ, RingedSpace.IsCoherent X.toRingedSpace
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj E)) := by
  classical
  choose U hx K hK he using hE
  have hlocal (x : X) := local_model_homology X E (U x) (K x) (hK x) (he x).some
  have hcover : ⨆ x, U x = ⊤ :=
    eq_top_iff.mpr fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx x⟩
  constructor
  · choose a b hab using fun x ↦ (hlocal x).2
    obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ (U x : Set X))
      (fun x ↦ (U x).isOpen) (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hx x⟩)
    let N := t.sup (fun x ↦ (a x).natAbs + (b x).natAbs)
    refine ⟨-(N : ℤ), (N : ℤ), fun i hi ↦ ?_⟩
    have hfiniteCover : ⨆ x : t, U x = ⊤ := by
      apply eq_top_iff.mpr
      intro x _
      obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hxy⟩
    apply Modules.isZero_of_iSup_eq_top _ (fun x : t ↦ U x) hfiniteCover
    intro x
    have hbound : (a x).natAbs + (b x).natAbs ≤ N :=
      Finset.le_sup (f := fun x ↦ (a x).natAbs + (b x).natAbs) x.property
    have ha : -(N : ℤ) ≤ a x := by
      have := Int.le_natAbs (a := -(a x))
      rw [Int.natAbs_neg] at this
      have : ((a x).natAbs : ℤ) ≤ (N : ℤ) := by exact_mod_cast (by omega : (a x).natAbs ≤ N)
      omega
    have hb : b x ≤ (N : ℤ) := by
      have := Int.le_natAbs (a := b x)
      have : ((b x).natAbs : ℤ) ≤ (N : ℤ) := by exact_mod_cast (by omega : (b x).natAbs ≤ N)
      omega
    exact hab x i (hi.elim (fun h ↦ Or.inl (h.trans_le ha))
      (fun h ↦ Or.inr (hb.trans_lt h)))
  · intro i
    have hfp : ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj E).IsFinitePresentation := by
      let M := (DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj E
      have hrest (x : X) : (M.over (U x)).IsFinitePresentation := by
        have := (hlocal x).1 i
        have hinv := finitePresentation_overEquiv_inverse X (U x)
          ((Modules.restrictFunctor (U x).ι).obj M)
        let F := Modules.overEquiv (X := X) (U x)
        let e := F.unitIso.app (M.over (U x)) ≪≫
          F.inverse.mapIso ((Modules.overFunctorEquiv (U x)).app M)
        exact (SheafOfModules.isFinitePresentation (X.ringCatSheaf.over (U x))).prop_of_iso
          e.symm hinv
      exact @SheafOfModules.IsFinitePresentation.of_coversTop _ _ _ _ _ _ _ _
        M X U (by
          rw [Opens.coversTop_iff]
          exact hcover) hrest
    exact (Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X _).2
      ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry.Scheme
