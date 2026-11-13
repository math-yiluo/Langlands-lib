import Langlands.AlgebraicGeometry.Picard.VersalAlgebraizationStatement
import Langlands.AlgebraicGeometry.Picard.ArtinianChartVersalityLevels
import Langlands.AlgebraicGeometry.Picard.AffineFamilyDescent
import Langlands.AlgebraicGeometry.Picard.AffineQuotientTests
import Langlands.CommutativeAlgebra.CompleteLocalAlgebraicChart
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Langlands.CategoryTheory.Sites.PseudofunctorPointFiberAtlasRestriction

/-! # Algebraization of formally versal Picard families from etale approximation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite IsLocalRing

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.AlgebraicGeometry.Deformation Langlands.CategoryTheory
open PicardGroupoid PicardGroupoid.ArtinianChartVersality AffineQuotientTests

namespace VersalAlgebraizationReduction

variable {k K : Type u} [CommRing k] [Field K] [Algebra k K]

/-- The base arrow of a test arrow is the affine-base arrow of its algebra map. -/
lemma baseMap_eq_affineBaseMap {A B : ArtinianTest k K} (q : A ⟶ B) :
    ArtinianTest.baseMap q = affineBaseMap (ArtinianTest.toAlgHom q) := rfl

/-- The residue point of a test is the affine-base arrow of its augmentation. -/
lemma reduction_eq_affineBaseMap (A : ArtinianTest k K) :
    ArtinianTest.reduction A = affineBaseMap A.augmentation := rfl

/-- A test arrow from a pointed affine base map: pointed maps into an affine base are the
affine-base arrows of augmentation-compatible algebra maps. -/
lemma augmentation_comp_of_reduction {T : Type u} [CommRing T] [Algebra k T]
    (A : ArtinianTest k K) (ψ : T →ₐ[k] A.algebra) (εT : T →ₐ[k] K)
    (h : ArtinianTest.reduction A ≫ affineBaseMap ψ = affineBaseMap εT) :
    A.augmentation.comp ψ = εT := by
  apply AffineQuotientTests.affineBaseMap_injective
  rw [affineBaseMap_comp]
  exact h

/-- Maps from a ring to an Artinian test that are compatible with the augmentations kill
all large powers of the kernel of the given augmentation. -/
lemma exists_pow_le_ker {T : Type u} [CommRing T] [Algebra k T] (A : ArtinianTest k K)
    (εT : T →ₐ[k] K) : ∃ N : ℕ, ∀ (ψ : T →ₐ[k] A.algebra), A.augmentation.comp ψ = εT →
      ∀ n ≥ N, RingHom.ker εT ^ n ≤ RingHom.ker ψ := by
  obtain ⟨N, hN⟩ := A.maximalIdeal_isNilpotent
  refine ⟨N, fun ψ hψ n hn => ?_⟩
  have hmap : (RingHom.ker εT).map ψ.toRingHom ≤ maximalIdeal A.algebra := by
    rw [← ArtinianTest.ker_augmentation A, Ideal.map_le_iff_le_comap]
    intro t ht
    change A.augmentation (ψ t) = 0
    rw [← AlgHom.comp_apply, hψ]
    exact ht
  have hbot : (RingHom.ker εT ^ n).map ψ.toRingHom ≤ ⊥ := by
    rw [Ideal.map_pow]
    calc ((RingHom.ker εT).map ψ.toRingHom) ^ n ≤ maximalIdeal A.algebra ^ n :=
          pow_le_pow_left' hmap n
      _ ≤ maximalIdeal A.algebra ^ N := Ideal.pow_le_pow_right hn
      _ = ⊥ := hN
  intro x hx
  have := hbot (Ideal.mem_map_of_mem ψ.toRingHom hx)
  rw [Ideal.mem_bot] at this
  exact this

/-- Composites of affine-base arrows are affine-base arrows of composites. -/
lemma affineBaseMap_comp_eq {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra k A] [Algebra k B] [Algebra k C] (a : A →ₐ[k] B) (b : B →ₐ[k] C)
    (c : A →ₐ[k] C) (h : ∀ x, b (a x) = c x) :
    affineBaseMap b ≫ affineBaseMap a = affineBaseMap c := by
  rw [← affineBaseMap_comp]
  congr 1
  ext x
  exact h x

end VersalAlgebraizationReduction

open VersalAlgebraizationReduction in
/-- **Algebraization from etale approximation.** Etale approximation for maximal
localizations of finite-type `ℤ`-algebras implies the algebraization of formally versal
Picard families over complete local bases (Stacks, Tag 07XH, for the Picard stack). -/
theorem versalAlgebraization_of_etaleApproximation
    (happrox : CommutativeAlgebra.FiniteTypeIntEtaleCompletionApproximationStatement.{u}) :
    VersalAlgebraizationStatement.{u} := by
  intro R _ _ X hprop hflat K _ _ _ A _ _ _ _ _ ε hε L p hp hL
  classical
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  -- spread the family to a finitely generated subalgebra
  obtain ⟨B, hBfg, -, LB, ⟨eB⟩⟩ := exists_affineFamily_subalgebra X.hom L ∅
  have : Algebra.FiniteType R B := (Subalgebra.fg_iff_finiteType B).mp hBfg
  -- the algebraic chart
  obtain ⟨T, _, _, hTft, εT, mT, hεTs, hker, βT, φ₂, hcompat, hres, hrig⟩ :=
    CommutativeAlgebra.CompleteLocalAlgebraicChart.exists_algebraicChart happrox ε hε B.val
  subst hker
  have : IsNoetherianRing T := Algebra.FiniteType.isNoetherianRing R T
  let F := PicardGroupoid.relative X.hom
  let aβ : affineBase R T ⟶ affineBase R B := affineBaseMap βT
  let L' : LineBundle ((relativeSpace X.hom).obj (affineBase R T)) :=
    ((F.map aβ.op.toLoc).toFunctor.obj (Core.mk LB)).of
  -- the truncations of the chart
  let Tt : ℕ → ArtinianTest R K := fun n => test εT hεTs (n + 1)
  let πt : ∀ n, Tt (n + 1) ⟶ Tt n := fun n => transition εT hεTs (n + 1)
  let c : ∀ n, ArtinianTest.base (Tt n) ⟶ affineBase R T := fun n => level εT hεTs (n + 1)
  have hc : ∀ n, ArtinianTest.baseMap (πt n) ≫ c (n + 1) = c n :=
    fun n => baseMap_transition_level εT hεTs (n + 1)
  let p' : ArtinianTest.residueBase R K ⟶ affineBase R T := affineBaseMap εT
  have hred : ∀ n, ArtinianTest.reduction (Tt n) ≫ c n = p' := fun n =>
    affineBaseMap_comp_eq (Ideal.Quotient.mkₐ R (RingHom.ker εT ^ (n + 1 + 1)))
      (Tt n).augmentation εT (fun x => rfl)
  have hp' : p = affineBaseMap ε := Over.OverMorphism.ext hp
  -- the initial fibre point, from the identification modulo squares
  let ιB : affineBase R A ⟶ affineBase R B := affineSubalgebraMap B
  let a₀ : ArtinianTest.base (Tt 0) ⟶ affineBase R A := affineBaseMap φ₂
  have hsq : a₀ ≫ ιB = c 0 ≫ aβ := by
    have h1 : a₀ ≫ ιB = affineBaseMap (φ₂.comp B.val) :=
      affineBaseMap_comp_eq B.val φ₂ _ (fun x => rfl)
    have h2 : c 0 ≫ aβ = affineBaseMap ((Ideal.Quotient.mkₐ R _).comp βT) :=
      affineBaseMap_comp_eq βT (Ideal.Quotient.mkₐ R (RingHom.ker εT ^ (0 + 1 + 1))) _
        (fun x => rfl)
    rw [h1, h2, hcompat]
  let e₀ : (F.map a₀.op.toLoc).toFunctor.obj (Core.mk L) ≅
      (F.map (c 0).op.toLoc).toFunctor.obj (Core.mk L') :=
    (F.map a₀.op.toLoc).toFunctor.mapIso eB.symm ≪≫
      (PseudofunctorPointFiberAtlasRestriction.atlasComparison F ιB (Core.mk LB) a₀).symm ≪≫
      eqToIso (by rw [hsq]) ≪≫
      PseudofunctorPointFiberAtlasRestriction.atlasComparison F aβ (Core.mk LB) (c 0)
  have hx₀ : ArtinianTest.reduction (Tt 0) ≫ a₀ = p := by
    rw [hp']
    refine affineBaseMap_comp_eq φ₂ (Tt 0).augmentation ε (fun a => ?_)
    obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (φ₂ a)
    rw [← ht]
    exact hres a t ht.symm
  -- lift through the whole tower by versality
  have htow := exists_tower_points X.hom L p hL L' Tt πt
    (fun n => transition_surjective εT hεTs (n + 1)) c hc ⟨a₀, e₀⟩ hx₀
  choose xs hxs1 hxs2 using htow
  have hφex : ∀ n, ∃ φ : A →ₐ[R] (Tt n).algebra, affineBaseMap φ = (xs n).1 :=
    fun n => exists_affineBaseMap_eq (xs n).1
  choose φs hφs using hφex
  have hdown : ∀ n (t : T), ArtinianTest.toAlgHom (towerDown Tt πt n)
      (Ideal.Quotient.mk _ t) = Ideal.Quotient.mk _ t := by
    intro n t
    induction n with
    | zero => rfl
    | succ n ih =>
      change ArtinianTest.toAlgHom (towerDown Tt πt n)
        (ArtinianTest.toAlgHom (πt n) (Ideal.Quotient.mk _ t)) = _
      exact ih
  have hfac : ∀ n, (Ideal.Quotient.factorₐ R
      (Ideal.pow_le_pow_right (show 2 ≤ n + 1 + 1 by omega))).comp (φs n) = φ₂ := by
    intro n
    have h1 : affineBaseMap ((ArtinianTest.toAlgHom (towerDown Tt πt n)).comp (φs n)) =
        affineBaseMap φ₂ := by
      rw [affineBaseMap_comp, hφs n]
      exact hxs2 n
    have h2 := affineBaseMap_injective h1
    rw [← h2]
    congr 1
    apply Ideal.Quotient.algHom_ext
    ext t
    exact (hdown n t).symm
  have hrig' : ∀ n, Function.Surjective (φs n) ∧
      RingHom.ker (φs n) = maximalIdeal A ^ (n + 1 + 1) :=
    fun n => hrig (n + 1 + 1) (by omega) (φs n) (hfac n)
  have hkerε : RingHom.ker ε = maximalIdeal A := IsLocalRing.ker_eq_maximalIdeal _ hε
  -- versality at the closed point of the chart
  have hversal : IsFormallyVersalAt X.hom L' p' := by
    refine isFormallyVersalAt_of_levels X.hom L p hL L' p'
      (fun n => ArtinianTest.base (Tt n)) c xs (fun n => ?_) (fun n r hr => ?_)
      (fun B' => ?_) (fun A' => ?_)
    · rw [← hφs n]
      exact mono_affineBaseMap (hrig' n).1
    · have : Mono (c n) := mono_affineBaseMap Ideal.Quotient.mk_surjective
      have hr' : r = ArtinianTest.reduction (Tt n) := by
        rw [← cancel_mono (c n), hr, hred n]
      rw [hr']
      exact hxs1 n
    · obtain ⟨N, hN⟩ := exists_pow_le_ker B' εT
      refine ⟨N, fun n hn y hy => ?_⟩
      obtain ⟨ψ, rfl⟩ := exists_affineBaseMap_eq
        (show affineBase R B'.algebra ⟶ affineBase R T from y)
      have hψ := augmentation_comp_of_reduction B' ψ εT hy
      have hk : RingHom.ker εT ^ (n + 1 + 1) ≤ RingHom.ker ψ := hN ψ hψ _ (by omega)
      refine ⟨affineBaseMap (Ideal.Quotient.liftₐ _ ψ (fun x hx => RingHom.mem_ker.mp (hk hx))),
        ?_⟩
      exact affineBaseMap_comp_eq (Ideal.Quotient.mkₐ R (RingHom.ker εT ^ (n + 1 + 1))) _ ψ
        (fun x => rfl)
    · obtain ⟨N, hN⟩ := exists_pow_le_ker A' ε
      refine ⟨N, fun n hn z hz => ?_⟩
      obtain ⟨ζ, rfl⟩ := exists_affineBaseMap_eq
        (show affineBase R A'.algebra ⟶ affineBase R A from z)
      have hζ := augmentation_comp_of_reduction A' ζ ε (by rw [hz, hp'])
      have hk : RingHom.ker (φs n) ≤ RingHom.ker ζ := by
        rw [(hrig' n).2, ← hkerε]
        exact hN ζ hζ _ (by omega)
      have hk' : ∀ x ∈ RingHom.ker (φs n), ζ x = 0 := fun x hx => RingHom.mem_ker.mp (hk hx)
      let ψ : (Tt n).algebra →ₐ[R] A'.algebra :=
        (Ideal.Quotient.liftₐ _ ζ hk').comp
          (Ideal.quotientKerAlgEquivOfSurjective (hrig' n).1).symm.toAlgHom
      refine ⟨affineBaseMap ψ, ?_⟩
      rw [← hφs n]
      refine affineBaseMap_comp_eq (φs n) ψ ζ (fun a => ?_)
      change Ideal.Quotient.liftₐ _ ζ hk'
        ((Ideal.quotientKerAlgEquivOfSurjective (hrig' n).1).symm (φs n a)) = ζ a
      rw [Ideal.quotientKerAlgEquivOfSurjective_symm_apply]
      rfl
  -- the residue point and the comparison of residue bundles
  obtain ⟨u₀, e, he⟩ := exists_residueField_iso εT hεTs
  refine ⟨affineBase R T, L', u₀, e, p', he, ?_, hversal, ?_⟩
  · change LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap R T)))
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr hTft
  · exact ⟨(PseudofunctorPointFiber.pullIso e₀ (ArtinianTest.reduction (Tt 0)) p p'
      hx₀ (hred 0)).symm.hom.iso⟩

set_option linter.defProp false in
/-- The implication proved by `versalAlgebraization_of_etaleApproximation`, as a single
term from etale approximation to the algebraization statement. -/
def versalAlgebraizationOfEtaleApproximation :
    CommutativeAlgebra.FiniteTypeIntEtaleCompletionApproximationStatement.{u} →
      VersalAlgebraizationStatement.{u} :=
  versalAlgebraization_of_etaleApproximation

end Langlands.AlgebraicGeometry.Picard
