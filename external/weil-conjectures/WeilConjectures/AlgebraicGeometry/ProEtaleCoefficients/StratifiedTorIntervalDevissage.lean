/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import WeilConjectures.SixFunctors.ConstructibleOpenClosedRefinement
import WeilConjectures.AlgebraicGeometry.PullbackFiniteConstantLocalModel
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
import WeilConjectures.AlgebraicGeometry.CondensedPullbackTensorComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Order.CompletePartialOrder
public import WeilConjectures.AlgebraicGeometry.StratifiedTorIntervalDevissage

/-!
# A fixed Tor interval across constructible strata

The coefficient list uses the finite-subextension-valued algebraic closure.
All modules in the Tor conditions are placed in degree zero. Constructibility uses
finite constructible locally closed scheme strata, without a reducedness condition.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open CategoryTheory.MonoidalCategory

attribute [local instance] DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

section GenericTensor

universe w₁ w₂
variable {C : Type w₁} {D : Type w₂}
  [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C]
  [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  [Abelian.HasFunctorialFlatResolution D]

private noncomputable def transportTensorFamily
    (F G : C ⥤ D) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (e : F ≅ G) (T : ExactDerivedTensorComparisonFamily F) :
    ExactDerivedTensorComparisonFamily G :=
  fun K L ↦ ((Functor.mapDerivedCategoryNatIso e).app _).symm ≪≫ T K L ≪≫
    tensorIso ((Functor.mapDerivedCategoryNatIso e).app K)
      ((Functor.mapDerivedCategoryNatIso e).app L)

private theorem concentration_of_pullback_tor
    (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (T : ExactDerivedTensorComparisonFamily F) (c d : ℤ) (K : DerivedCategory C)
    (hK : _root_.DerivedCategory.torAmplitudeIn _ c d (F.mapDerivedCategory.obj K)) (M : C) :
    DerivedCategory.homologyConcentratedIn c d
      (F.mapDerivedCategory.obj (K ⊗ (DerivedCategory.singleFunctor _ 0).obj M)) :=
  (DerivedCategory.homologyConcentratedIn c d).prop_of_iso
    (T K _ ≪≫ tensorIso (Iso.refl _)
      ((F.mapDerivedCategorySingleFunctor 0).app M)).symm (hK _)

end GenericTensor

private noncomputable def pullbackTensorIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : Y ⟶ X) :
    ExactDerivedTensorComparisonFamily (CondensedRing.upperStar Λ f) :=
  transportTensorFamily _ _ (CondensedRing.supportPullbackIsoUpperStar Λ f)
    (CondensedRing.supportDerivedTensorComparison Λ f)

private theorem torInterval_of_open_closed
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Z U : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j]
    (hij : IsCompl (Set.range i.base) (Set.range j.base))
    (c d : ℤ)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (hi : _root_.DerivedCategory.torAmplitudeIn _ c d
      ((CondensedRing.upperStar Λ i).mapDerivedCategory.obj K))
    (hj : _root_.DerivedCategory.torAmplitudeIn _ c d
      ((CondensedRing.upperStar Λ j).mapDerivedCategory.obj K)) :
    _root_.DerivedCategory.torAmplitudeIn _ c d K := by
  intro M
  let E := K ⊗ (DerivedCategory.singleFunctor _ 0).obj M
  have hlocal {Y : Scheme.{u}} (f : Y ⟶ X)
      (hf : _root_.DerivedCategory.torAmplitudeIn _ c d
        ((CondensedRing.upperStar Λ f).mapDerivedCategory.obj K)) :
      DerivedCategory.homologyConcentratedIn c d
        ((CondensedRing.upperStar Λ f).mapDerivedCategory.obj E) :=
    concentration_of_pullback_tor _ (pullbackTensorIso Λ f) c d K hf M
  have hvan {Y : Scheme.{u}} (f : Y ⟶ X)
      (hf : _root_.DerivedCategory.torAmplitudeIn _ c d
        ((CondensedRing.upperStar Λ f).mapDerivedCategory.obj K))
      (q : ℤ) (hq : q < c ∨ d < q) :
      IsZero ((CondensedRing.upperStar Λ f).obj
        ((DerivedCategory.homologyFunctor _ q).obj E)) := by
    have hz : IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((CondensedRing.upperStar Λ f).mapDerivedCategory.obj E)) := by
      rcases hq with hq | hq
      · exact (DerivedCategory.isGE_iff _ c).1 (hlocal f hf).1 q hq
      · exact (DerivedCategory.isLE_iff _ d).1 (hlocal f hf).2 q hq
    exact hz.of_iso (((CondensedRing.upperStar Λ f).mapDerivedCategoryHomologyFunctorIso q).app E)
  have hzero (q : ℤ) (hq : q < c ∨ d < q) :
      IsZero ((DerivedCategory.homologyFunctor _ q).obj E) :=
    CondensedRing.isZero_of_isZero_upperStar_of_isCompl Λ i j hij _
      (hvan i hi q hq) (hvan j hj q hq)
  exact ⟨(DerivedCategory.isGE_iff E c).2 (fun q hq ↦ hzero q (.inl hq)),
    (DerivedCategory.isLE_iff E d).2 (fun q hq ↦ hzero q (.inr hq))⟩

private theorem finiteModel_of_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) (hM : HasFiniteConstantLocalModel Λ X M) :
    HasFiniteConstantLocalModel Λ X N := by
  obtain ⟨U, hU⟩ := hM
  refine ⟨U, fun i ↦ ?_⟩
  obtain ⟨P, hP, ⟨eP⟩⟩ := hU i
  exact ⟨P, hP, ⟨(CondensedRing.upperStar Λ (U.f i)).mapIso e.symm ≪≫ eP⟩⟩

private theorem finiteModel_empty
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) [IsEmpty X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    HasFiniteConstantLocalModel Λ X M := by
  let U : Scheme.Cover.{u} Scheme.proetalePrecoverage X :=
    { I₀ := PEmpty
      X := PEmpty.elim
      f := fun i ↦ PEmpty.elim i
      mem₀ := by
        change Presieve.ofArrows _ _ ∈ Scheme.proetalePrecoverage X
        rw [Presieve.ofArrows_of_isEmpty]
        exact Scheme.bot_mem_propQCPrecoverage X }
  exact ⟨U, fun i ↦ PEmpty.elim i⟩

private theorem torInterval_of_iso_pullback
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (e : Y ≅ X)
    (c d : ℤ)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (ht : _root_.DerivedCategory.torAmplitudeIn _ c d
      ((CondensedRing.upperStar Λ e.hom).mapDerivedCategory.obj K)) :
    _root_.DerivedCategory.torAmplitudeIn _ c d K := by
  let F := CondensedRing.upperStar Λ e.hom
  intro A
  let T := K ⊗ (DerivedCategory.singleFunctor _ 0).obj A
  have hT : DerivedCategory.homologyConcentratedIn c d (F.mapDerivedCategory.obj T) :=
    concentration_of_pullback_tor _ (pullbackTensorIso Λ e.hom) c d K ht A
  have hreflect (B : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) (hB : IsZero (F.obj B)) : IsZero B := by
    let G := CondensedRing.upperStar Λ e.inv
    let hcomp : e.inv ≫ e.hom = 𝟙 X := e.inv_hom_id
    exact (G.map_isZero hB).of_iso
      (((CondensedRing.upperStarId Λ X).app B).symm ≪≫
        ((CondensedRing.upperStarCongr Λ hcomp).app B).symm ≪≫
        (CondensedRing.upperStarComp Λ e.inv e.hom).app B)
  constructor
  · apply (DerivedCategory.isGE_iff T c).2
    intro q hq
    exact hreflect _ (((DerivedCategory.isGE_iff _ c).1 hT.1 q hq).of_iso
      ((F.mapDerivedCategoryHomologyFunctorIso q).app T))
  · apply (DerivedCategory.isLE_iff T d).2
    intro q hq
    exact hreflect _ (((DerivedCategory.isLE_iff _ d).1 hT.2 q hq).of_iso
      ((F.mapDerivedCategoryHomologyFunctorIso q).app T))

private theorem reverseIndex_lt {N a b : ℕ} (hb : b < N) (hab : a < b) :
    N - b < N - a := by omega

private theorem torInterval_of_stratified
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (c d : ℤ)
    (hlocal : ∀ (S : Scheme.{u})
      (N : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)),
      HasFiniteConstantLocalModel Λ S N →
        _root_.DerivedCategory.torAmplitudeIn _ c d ((DerivedCategory.singleFunctor _ 0).obj N))
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsConstantModelConstructible Λ X M) :
    _root_.DerivedCategory.torAmplitudeIn _ c d ((DerivedCategory.singleFunctor _ 0).obj M) := by
  classical
  have hX : CompactSpace X ∧ QuasiSeparatedSpace X := ⟨inferInstance, inferInstance⟩
  obtain ⟨S, hS⟩ : IsFiniteConstantStratified Λ X M := by
    simpa only [IsConstantModelConstructible, ite_eq_left hX] using hM
  obtain ⟨O, Q, Z, o, a, q, z, ho, ha, hq, hz, hao, hqc, hqqc, hr, hzr,
    N, V, t, root, parent, left, right, le, re, leaf,
    hroot, hparent, hparent_lt, hl, hright, hcompact, hqs, himm, hchild,
    hleaf, hbranch, hpullback, hcover, hdisj, hfactor⟩ :=
    Scheme.exists_finite_open_closed_refinement 1 (fun _ ↦ S.n)
      (fun _ ↦ S.domain) (fun _ ↦ S.immersion) (fun _ ↦ S.isImmersion)
      (fun _ k ↦ by rw [S.range_immersion]; exact S.isConstructible_stratum k)
      (fun _ ↦ by simpa only [S.range_immersion] using S.iUnion_stratum_eq_univ)
      (fun _ ↦ by simpa only [S.range_immersion] using S.pairwise_disjoint_stratum)
  clear ho ha hq hz hao hqc hqqc hr hzr hpullback
  clear o a q z O Q Z
  clear hparent hparent_lt hcompact hqs himm hchild hleaf hcover hdisj
  let R (v : Fin N) := (CondensedRing.upperStar Λ (t v)).obj M
  have hleaf_model (v : Fin N) (hv : leaf v) :
      HasFiniteConstantLocalModel Λ (V v) (R v) := by
    cases isEmpty_or_nonempty (V v) with
    | inl he =>
      let := he
      exact finiteModel_empty Λ (V v) (R v)
    | inr he =>
      obtain ⟨k, f, hf⟩ := hfactor v hv he 0
      have hm := pullback_finiteConstantLocalModel Λ f _ (hS k)
      apply finiteModel_of_iso Λ
        ((CondensedRing.upperStarComp Λ f (S.immersion k)).app M).symm at hm
      simpa only [hf] using hm
  have htor_aux (n : ℕ) : ∀ v : Fin N, N - v.val = n →
      _root_.DerivedCategory.torAmplitudeIn _ c d
        ((DerivedCategory.singleFunctor _ 0).obj (R v)) := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hv
      by_cases hvleaf : leaf v
      · exact hlocal (V v) (R v) (hleaf_model v hvleaf)
      · obtain ⟨hne, hlt, hrt, hpl, hpr, hopen, hclosed, hqcl, hqcr, hcov, hdis⟩ :=
          hbranch v hvleaf
        let := hopen
        let := hclosed
        let := hqcl
        have hlTor := ih (N - (left v).val)
          ((reverseIndex_lt (left v).isLt hlt).trans_eq hv) (left v) rfl
        have hrTor := ih (N - (right v).val)
          ((reverseIndex_lt (right v).isLt hrt).trans_eq hv) (right v) rfl
        have hpull {w : Fin N} (f : V w ⟶ V v) (hf : f ≫ t v = t w)
            (ht : _root_.DerivedCategory.torAmplitudeIn _ c d
              ((DerivedCategory.singleFunctor _ 0).obj (R w))) :
            _root_.DerivedCategory.torAmplitudeIn _ c d
              ((CondensedRing.upperStar Λ f).mapDerivedCategory.obj
                ((DerivedCategory.singleFunctor _ 0).obj (R v))) := by
          let e : (CondensedRing.upperStar Λ f).obj (R v) ≅ R w :=
            ((CondensedRing.upperStarComp Λ f (t v)).app M).symm ≪≫
              (CondensedRing.upperStarCongr Λ hf).app M
          exact (_root_.DerivedCategory.torAmplitudeIn _ c d).prop_of_iso
            (((DerivedCategory.singleFunctor _ 0).mapIso e).symm ≪≫
              (((CondensedRing.upperStar Λ f).mapDerivedCategorySingleFunctor 0).app
                (R v)).symm) ht
        exact torInterval_of_open_closed Λ (re v) (le v)
          ⟨hdis.symm, codisjoint_iff.mpr (by
            change Set.range (re v) ∪ Set.range (le v) = Set.univ
            exact (Set.union_comm _ _).trans hcov)⟩ c d _
          (hpull (re v) (hright v hvleaf) hrTor) (hpull (le v) (hl v hvleaf) hlTor)
  have htor (v : Fin N) := htor_aux (N - v.val) v rfl
  obtain ⟨e, he⟩ := hroot
  have ht : _root_.DerivedCategory.torAmplitudeIn _ c d
      ((CondensedRing.upperStar Λ e.hom).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor _ 0).obj M)) := by
    rw [he]
    exact (_root_.DerivedCategory.torAmplitudeIn _ c d).prop_of_iso
      (((CondensedRing.upperStar Λ (t root)).mapDerivedCategorySingleFunctor 0).app M).symm
      (htor root)
  exact torInterval_of_iso_pullback Λ e c d _ ht

/-- A uniform Tor interval for all finite constant local models is also a uniform
Tor interval for all constructible modules on qcqs schemes. The six coefficient cases
are finite discrete rings killed by a power of `ℓ`, `ℤ_ℓ`, `𝒪_E`, `ℚ_ℓ`, `E`, and
finite-subextension-valued `ℚ̄_ℓ`, with `E` a finite subextension of the fixed `PadicAlgCl ℓ`. -/
theorem torAmplitudeIn_of_constructible_of_uniform_local_model
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (_hΛ :
      (∃ (A : Type) (_ : CommRing A) (_ : TopologicalSpace A)
          (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
        Finite A ∧ (∃ n : ℕ, ∀ a : A, (ℓ ^ n) • a = 0) ∧
          Nonempty (Λ ≅ Mon.mk (Profinite.continuousMapRingObj A))) ∨
      Nonempty (Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E))) ∨
      Nonempty (Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
      Nonempty (Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ)))
    (c d : ℤ) (_hcd : c ≤ d)
    (hlocal : ∀ (S : Scheme.{u})
      (N : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ.X S)),
      HasFiniteConstantLocalModel Λ.X S N →
        _root_.DerivedCategory.torAmplitudeIn _ c d ((DerivedCategory.singleFunctor _ 0).obj N))
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X))
    (hM : IsConstantModelConstructible Λ.X X M) :
    _root_.DerivedCategory.torAmplitudeIn _ c d ((DerivedCategory.singleFunctor _ 0).obj M) := by
  exact torInterval_of_stratified Λ.X c d hlocal X M hM

end AlgebraicGeometry.ProEtale
