/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientModuleEncoding
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.LocallyFree
import WeilConjectures.AlgebraicGeometry.LisseLatticeCoefficientNormalization
import WeilConjectures.AlgebraicGeometry.ContinuousModuleEncodingSliceFreeness
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoversTop.Basic

/-! # Local freeness under continuous module encodings

Source: Stacks Project, Modules on Sites, Tags 03DM and 03DO.
(auxiliary; not a blueprint node)
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The continuous module encoding preserves and reflects local finite freeness.
Source: Stacks Project, Modules on Sites, Tags 03DM and 03DO;
Bhatt--Scholze, Section 6.8.
(auxiliary; not a blueprint node)

Proof. On a weakly etale chart, the small pro-etale site of the source is the
slice of the base site. The chart-pullback square identifies restriction of the
sectionwise encoding with encoding of canonical inverse image. On these slices,
continuousRingFreeIso identifies each finite biproduct of the internal regular
module with the finite free sectionwise module, including rank zero. Conversely
full faithfulness and the counit of the encoding take any finite free
sectionwise presentation back to that internal biproduct. The local generators
criterion for IsFiniteLocallyFree therefore transports trivializations in both
directions. A scheme pro-etale precover gives a covering family on the small
site. In the converse direction, evaluate the covering family at the terminal
object, refine the resulting covering sieve by a pro-etale precover, and pull
back the finite free presentations along the refinement arrows. The resulting
scheme cover is the cover appearing on the left. No uniform rank, nonempty
cover, quasi-compactness, or finite indexing set is required. -/
theorem continuousRing_locallyFree_iff
    (X : Scheme.{u}) (T : Type)
    [CommRing T] [TopologicalSpace T] [IsTopologicalRing T] [TotallyDisconnectedSpace T]
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X)) :
    (IsLocallyFree (condensedRingObj (Profinite.continuousMapRingObj T) X) P) ↔
      ((continuousRingModuleEquivalence X T).functor.obj P).IsFiniteLocallyFree := by
  classical
  let R := continuousMapRingSheaf X T
  let M := (continuousRingModuleEquivalence X T).functor.obj P
  constructor
  · rintro ⟨C, hC⟩
    let (s : C.I₀) : WeaklyEtale (C.f s) :=
      Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ C.mem₀ (.mk s)
    let U (s : C.I₀) : X.ProEt := Scheme.ProEt.mk (C.f s)
    have hU : (Scheme.ProEt.topology X).CoversTop U := by
      rw [GrothendieckTopology.coversTop_iff_of_isTerminal _
        (Scheme.ProEt.mk (𝟙 X)) (MorphismProperty.Over.mkIdTerminal (@WeaklyEtale) X)]
      let a (s : C.I₀) : U s ⟶ Scheme.ProEt.mk (𝟙 X) :=
        MorphismProperty.Over.homMk (C.f s) (by
          change C.f s ≫ 𝟙 X = C.f s
          exact Category.comp_id _)
      apply Scheme.ProEt.mem_topology_iff.mpr
      refine ⟨Presieve.ofArrows U a, ?_, ?_⟩
      · rw [Scheme.ProEt.mem_precoverage_iff, Presieve.map_ofArrows]
        exact C.mem₀
      · intro W f hf
        obtain ⟨s⟩ := hf
        exact ⟨s, ⟨𝟙 _⟩⟩
    have hfree (s : C.I₀) : ∃ n : ℕ, Nonempty (M.over (U s) ≅
        SheafOfModules.free (ULift.{u + 1} (Fin n))) :=
      (continuousRing_slice_free_iff X T P (U s)).mpr (hC s)
    choose n hn using hfree
    have hU' : (Scheme.ProEt.topology X).CoversTop
        (fun s : ULift.{u + 1} C.I₀ ↦ U s.down) := by
      intro V
      apply (Scheme.ProEt.topology X).superset_covering _ (hU V)
      rintro W f ⟨s, ⟨a⟩⟩
      exact ⟨ULift.up s, ⟨a⟩⟩
    exact SheafOfModules.isFiniteLocallyFree_of_exists_over_iso_free (M := M)
      (fun s : ULift.{u + 1} C.I₀ ↦ U s.down) hU'
      (fun s ↦ ULift.{u + 1} (Fin (n s.down))) (fun s ↦ hn s.down)
  · intro hM
    let : M.IsFiniteLocallyFree := hM
    obtain ⟨q, hq, hf⟩ := hM.exists_localGeneratorsData
    let : q.IsLocallyFreeData := hq
    have hfree (i : q.I) : ∃ n : ℕ, Nonempty (M.over (q.X i) ≅
        SheafOfModules.free (ULift.{u + 1} (Fin n))) := by
      let : (q.generators i).IsFiniteType := hf.isFiniteType i
      obtain ⟨n, ⟨en⟩⟩ := Finite.exists_equiv_fin (q.generators i).I
      exact ⟨n, ⟨(asIso (q.generators i).π).symm ≪≫
        SheafOfModules.freeFunctor.mapIso (en.trans Equiv.ulift.symm).toIso⟩⟩
    let V : X.ProEt := Scheme.ProEt.mk (𝟙 X)
    obtain ⟨S, hS, hle⟩ := Scheme.ProEt.mem_topology_iff.mp (q.coversTop V)
    obtain ⟨C, rfl⟩ := Precoverage.mem_iff_exists_zeroHypercover.mp hS
    have hw (i : C.I₀) : (C.f i).left = (C.X i).hom := by
      have h := MorphismProperty.Over.w (C.f i)
      change (C.f i).left ≫ 𝟙 X = (C.X i).hom at h
      exact (Category.comp_id _).symm.trans h
    let D : Scheme.Cover.{u + 1} Scheme.proetalePrecoverage X :=
      { I₀ := C.I₀
        X := fun i ↦ (C.X i).left
        f := fun i ↦ (C.X i).hom
        mem₀ := by
          have hm := Scheme.ProEt.mem_precoverage_iff.mp C.mem₀
          rw [Presieve.map_ofArrows] at hm
          change (Presieve.ofArrows (fun i ↦ (C.X i).left)
            (fun i ↦ (C.f i).left)) ∈ Scheme.proetalePrecoverage X at hm
          simpa only [hw] using hm }
    let : Precoverage.Small.{u} Scheme.proetalePrecoverage :=
      inferInstanceAs (Precoverage.Small.{u} (Scheme.propQCPrecoverage (@WeaklyEtale)))
    let D' := D.restrictIndexOfSmall.{u}
    refine ⟨D', fun s ↦ ?_⟩
    let j := Precoverage.ZeroHypercover.Small.restrictFun.{u} D s
    obtain ⟨i, ⟨a⟩⟩ := hle _ _ (.mk j)
    obtain ⟨n, ⟨en⟩⟩ := hfree i
    have en' : Nonempty (M.over (C.X j) ≅
        SheafOfModules.free (ULift.{u + 1} (Fin n))) := by
      let F := SheafOfModules.overMap R a
      let e : F.obj (SheafOfModules.unit (R.over (q.X i))) ≅
          SheafOfModules.unit (R.over (C.X j)) := SheafOfModules.overMapUnitIso a
      exact ⟨((SheafOfModules.overFunctorMap R a).app M).symm ≪≫ F.mapIso en ≪≫
        (SheafOfModules.mapFreeIso F _ e.symm).symm⟩
    exact (continuousRing_slice_free_iff X T P (C.X j)).mp ⟨n, en'⟩

set_option backward.isDefEq.respectTransparency false

/-- Local finite freeness transports to the normalized rational encoding.
Source: Stacks Project, Tag 03DM.
(auxiliary; not a blueprint node)

Apply the continuous-ring criterion, then restrict along the coefficient
isomorphism supplied by lisseFieldSheaf_eq. -/
theorem continuousField_locallyFree
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (X : Scheme.{u})
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))
    (hP : IsLocallyFree (condensedRingObj (Profinite.continuousMapRingObj E) X) P) :
    ((continuousFieldModuleEquivalence ℓ E X).functor.obj P).IsFiniteLocallyFree := by
  let : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[ℓ]
  let : TotallySeparatedSpace E :=
    totallySeparatedSpace_iff_exists_isClopen.mpr fun x y h ↦ by
      obtain ⟨r, hr, hr'⟩ := exists_between (dist_pos.mpr h)
      refine ⟨_, IsUltrametricDist.isClopen_ball x r, ?_, ?_⟩
      · simp only [Metric.mem_ball, dist_self, hr]
      · simp only [Set.mem_compl, Metric.mem_ball, dist_comm, not_lt, hr'.le]
  let : ((continuousRingModuleEquivalence X E).functor.obj P).IsFiniteLocallyFree :=
    (continuousRing_locallyFree_iff X E P).mp hP
  exact finiteLocallyFree_restrict (Scheme.ProEt.topology X) _ _
    ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso
        (eqToIso (lisseFieldSheaf_eq ℓ E X))) _

/-- A finite locally free integral module has locally free inverse encoding.
Source: Stacks Project, Tag 03DM.
(auxiliary; not a blueprint node)

First transport the given module along the inverse integral coefficient
isomorphism. Apply the counit of the continuous-ring encoding, then the reverse
direction of continuousRing_locallyFree_iff. -/
theorem continuousInteger_inverse_locallyFree
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (X : Scheme.{u})
    (M : ringedSiteModules.{u + 1} ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (lisseIntegerSheaf ℓ E X)))
    [M.IsFiniteLocallyFree] :
    IsLocallyFree (condensedRingObj (integralCoeff ℓ E) X)
      ((continuousIntegerModuleEquivalence ℓ E X).inverse.obj M) := by
  let : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[ℓ]
  let : TotallySeparatedSpace E :=
    totallySeparatedSpace_iff_exists_isClopen.mpr fun x y h ↦ by
      obtain ⟨r, hr, hr'⟩ := exists_between (dist_pos.mpr h)
      refine ⟨_, IsUltrametricDist.isClopen_ball x r, ?_, ?_⟩
      · simp only [Metric.mem_ball, dist_self, hr]
      · simp only [Set.mem_compl, Metric.mem_ball, dist_comm, not_lt, hr'.le]
  let F := continuousRingModuleEquivalence X (continuousIntegers ℓ E)
  let e := (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso
      (eqToIso (lisseIntegerSheaf_eq ℓ E X))
  let H := ringModuleEquivalenceOfIso X e
  let : (H.inverse.obj M).IsFiniteLocallyFree :=
    finiteLocallyFree_restrict (Scheme.ProEt.topology X) _ _ e.symm M
  let e' : H.inverse.obj M ≅ F.functor.obj (F.inverse.obj (H.inverse.obj M)) :=
    (F.counitIso.app _).symm
  let : (F.functor.obj (F.inverse.obj (H.inverse.obj M))).IsFiniteLocallyFree :=
    SheafOfModules.IsFiniteLocallyFree.of_iso.{u + 1, u, u + 1} e'
  exact (continuousRing_locallyFree_iff X (continuousIntegers ℓ E)
    (F.inverse.obj (H.inverse.obj M))).mpr inferInstance

end AlgebraicGeometry.ProEtale.CondensedRing
