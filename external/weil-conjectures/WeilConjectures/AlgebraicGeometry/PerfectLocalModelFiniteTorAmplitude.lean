/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import Mathlib.AlgebraicGeometry.Sites.QuasiCompact
import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeMapDerivedCategory
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralLisseDerivedAux
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalLeftDerived

/-! # Descent of finite Tor amplitude along a pro-etale cover

Source: blueprint latest, scalar-six-ctf proof (2), local models.
(blueprint: lem-sfb-perfect-local-model-finite-tor-amplitude).
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Finite Tor amplitude descends from a pro-etale cover of a Noetherian scheme.
No scalar model or admissibility assumption is needed for this descent step.

Source: blueprint latest, sec-six-functors-basics/sk-prop-scalar-six,
det-prop-scalar-six-ctf.proof.md (2), local models.
(blueprint: lem-sfb-perfect-local-model-finite-tor-amplitude).

Proof in words:
1. Choose a Tor interval on each cover member. Cover S by finitely many affine
   opens. The finite-refinement condition of the pro-etale precoverage refines the
   given cover over each affine open by finitely many affine opens. Since the base
   affine opens are open in S, each refined member is also open in an original
   cover member. Exact coefficient pullback preserves flat modules, so
   the existing derived Tor-amplitude preservation theorem transports the original
   interval to every refined member. Composition identifies this with restriction
   from S. Taking the minimum lower endpoint and maximum upper endpoint
   gives one interval for the finite covering. For empty S choose [0,0].
2. For every module N on S, exact monoidal pullback identifies the restriction of
   Q tensor-derived N[0] with the tensor of the restrictions. Exact pullback also
   preserves the single-functor embedding. Thus all restricted tensors have the
   common interval independently of N.
3. Exact restriction commutes with homology. A sheaf that is zero on the covering
   is zero: pull the covering back over every test object and apply the uniqueness
   clause of the sheaf condition to its sections. The same holds for internal
   modules because the forgetful functor detects zero objects. Consequently every
   global tensor has homology in the common interval, which is finite Tor amplitude. -/
theorem finiteTorAmplitude_of_proetale_cover
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (S : Scheme.{u}) [IsLocallyNoetherian S] [CompactSpace S]
    (Q : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj Λ S)))
    (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage S)
    (hQ : ∀ i : 𝒰.I₀, DerivedCategory.finiteTorAmplitude _
      ((CondensedRing.upperStar Λ (𝒰.f i)).mapDerivedCategory.obj Q)) :
    DerivedCategory.finiteTorAmplitude _ Q := by
  classical
  obtain ⟨𝒱, e, hfin, hopen⟩ :=
    AlgebraicGeometry.QuasiCompactCover.exists_hom 𝒰.forgetQc
  let : Finite 𝒱.I₀ := hfin
  let (j : 𝒱.I₀) : AlgebraicGeometry.QuasiCompact (𝒱.cover.f j) := by
    infer_instance
  let : Finite 𝒱.cover.I₀ := hfin
  let : QuasiCompactCover 𝒱.cover.toPreZeroHypercover := .of_finite
  let V := Scheme.Cover.ofQuasiCompactCover 𝒱.cover
  have hlocal (j : 𝒱.I₀) : ∃ a b : ℤ, a ≤ b ∧
      DerivedCategory.torAmplitudeIn _ a b
        ((CondensedRing.upperStar Λ (𝒱.cover.f j)).mapDerivedCategory.obj Q) := by
    let i : 𝒰.I₀ := e.s₀ j
    obtain ⟨a, b, ht⟩ := hQ i
    have hta := DerivedCategory.torAmplitudeIn_mapDerivedCategory_obj
      (CondensedRing.upperStar Λ (e.h₀ j)) ht
    let c := Functor.mapDerivedCategoryNatIso
        (CondensedRing.upperStarComp Λ (e.h₀ j) (𝒰.f i))
    let d := Functor.mapDerivedCategoryCompIso
        (CondensedRing.upperStar Λ (𝒰.f i)) (CondensedRing.upperStar Λ (e.h₀ j))
    have heq : (𝒱.cover.f j) = e.h₀ j ≫ 𝒰.f i := by
      exact (e.w₀ j).symm
    rw [heq]
    refine ⟨min a b, max a b, min_le_max, ?_⟩
    apply (DerivedCategory.torAmplitudeIn _ (min a b) (max a b)).prop_of_iso
      ((c ≪≫ d.symm).app Q).symm
    exact hta.mono (min_le_left _ _) (le_max_right _ _)
  choose A B hAB hT using hlocal
  by_cases hne : Nonempty 𝒱.I₀
  · let : Nonempty 𝒱.I₀ := hne
    let : Fintype 𝒱.I₀ := Fintype.ofFinite 𝒱.I₀
    let a : ℤ := Finset.univ.inf' Finset.univ_nonempty A
    let b : ℤ := Finset.univ.sup' Finset.univ_nonempty B
    have ha (j : 𝒱.I₀) : a ≤ A j := Finset.inf'_le _ (Finset.mem_univ j)
    have hb (j : 𝒱.I₀) : B j ≤ b := Finset.le_sup' _ (Finset.mem_univ j)
    have hab : a ≤ b := by
      obtain ⟨j⟩ := hne
      exact (ha j).trans ((hAB j).trans (hb j))
    refine ⟨a, b, ?_⟩
    intro N
    refine ⟨?_, ?_⟩
    · apply (DerivedCategory.isGE_iff _ a).2
      intro q hq
      apply CondensedRing.isZero_homology_of_cover V
        (Q ⊗ (DerivedCategory.singleFunctor _ 0).obj N) q
      intro j
      let v := V.f j
      have hlocal' := (hT j).mono (ha j) (hb j)
      have hLv : DerivedCategory.torAmplitudeIn _ a b
          ((CondensedRing.upperStar Λ v).leftDerivedFunctor.obj Q) :=
        (DerivedCategory.torAmplitudeIn _ a b).prop_of_iso
          ((CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ v).app Q).symm hlocal'
      have hN := hLv ((CondensedRing.upperStar Λ v).obj N)
      let eT : (CondensedRing.upperStar Λ v).leftDerivedFunctor.obj
          (Q ⊗ (DerivedCategory.singleFunctor _ 0).obj N) ≅
          (CondensedRing.upperStar Λ v).leftDerivedFunctor.obj Q ⊗
            (CondensedRing.upperStar Λ v).leftDerivedFunctor.obj
              ((DerivedCategory.singleFunctor _ 0).obj N) := by
        simpa [CondensedRing.leftDerivedUpperStarTensorLeft,
          CondensedRing.leftDerivedUpperStarTensorRight] using
          ((CondensedRing.leftDerivedUpperStarTensorIso Λ v).app Q).app
            ((DerivedCategory.singleFunctor _ 0).obj N)
      let eN := CondensedRing.leftDerivedUpperStarSingleFunctorIso Λ v N 0
      let e := eT ≪≫ tensorIso (Iso.refl _) eN
      have hz : IsZero ((DerivedCategory.homologyFunctor _ q).obj
          (((CondensedRing.upperStar Λ v).leftDerivedFunctor.obj Q) ⊗
            (DerivedCategory.singleFunctor _ 0).obj
              ((CondensedRing.upperStar Λ v).obj N))) := by
        exact ((DerivedCategory.isGE_iff _ a).1 hN.1 q hq)
      have he : (DerivedCategory.homologyFunctor _ q).obj
          ((CondensedRing.upperStar Λ (V.f j)).leftDerivedFunctor.obj
            (Q ⊗ (DerivedCategory.singleFunctor _ 0).obj N)) ≅
          (DerivedCategory.homologyFunctor _ q).obj
            ((CondensedRing.upperStar Λ v).leftDerivedFunctor.obj Q ⊗
              (DerivedCategory.singleFunctor _ 0).obj
                ((CondensedRing.upperStar Λ v).obj N)) := by
        simpa [v] using (DerivedCategory.homologyFunctor _ q).mapIso e
      exact hz.of_iso he
    · apply (DerivedCategory.isLE_iff _ b).2
      intro q hq
      apply CondensedRing.isZero_homology_of_cover V
        (Q ⊗ (DerivedCategory.singleFunctor _ 0).obj N) q
      intro j
      let v := V.f j
      have hlocal' := (hT j).mono (ha j) (hb j)
      have hLv : DerivedCategory.torAmplitudeIn _ a b
          ((CondensedRing.upperStar Λ v).leftDerivedFunctor.obj Q) :=
        (DerivedCategory.torAmplitudeIn _ a b).prop_of_iso
          ((CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ v).app Q).symm hlocal'
      have hN := hLv ((CondensedRing.upperStar Λ v).obj N)
      let eT : (CondensedRing.upperStar Λ v).leftDerivedFunctor.obj
          (Q ⊗ (DerivedCategory.singleFunctor _ 0).obj N) ≅
          (CondensedRing.upperStar Λ v).leftDerivedFunctor.obj Q ⊗
            (CondensedRing.upperStar Λ v).leftDerivedFunctor.obj
              ((DerivedCategory.singleFunctor _ 0).obj N) := by
        simpa [CondensedRing.leftDerivedUpperStarTensorLeft,
          CondensedRing.leftDerivedUpperStarTensorRight] using
          ((CondensedRing.leftDerivedUpperStarTensorIso Λ v).app Q).app
            ((DerivedCategory.singleFunctor _ 0).obj N)
      let eN := CondensedRing.leftDerivedUpperStarSingleFunctorIso Λ v N 0
      let e := eT ≪≫ tensorIso (Iso.refl _) eN
      have hz : IsZero ((DerivedCategory.homologyFunctor _ q).obj
          (((CondensedRing.upperStar Λ v).leftDerivedFunctor.obj Q) ⊗
            (DerivedCategory.singleFunctor _ 0).obj
              ((CondensedRing.upperStar Λ v).obj N))) := by
        exact ((DerivedCategory.isLE_iff _ b).1 hN.2 q hq)
      have he : (DerivedCategory.homologyFunctor _ q).obj
          ((CondensedRing.upperStar Λ (V.f j)).leftDerivedFunctor.obj
            (Q ⊗ (DerivedCategory.singleFunctor _ 0).obj N)) ≅
          (DerivedCategory.homologyFunctor _ q).obj
            ((CondensedRing.upperStar Λ v).leftDerivedFunctor.obj Q ⊗
              (DerivedCategory.singleFunctor _ 0).obj
                ((CondensedRing.upperStar Λ v).obj N)) := by
        simpa [v] using (DerivedCategory.homologyFunctor _ q).mapIso e
      exact hz.of_iso he
  · let : IsEmpty 𝒱.I₀ := not_nonempty_iff.mp hne
    let : IsEmpty V.I₀ := by
      change IsEmpty 𝒱.I₀
      exact not_nonempty_iff.mp hne
    refine ⟨0, 0, ?_⟩
    intro N
    refine ⟨?_, ?_⟩
    · apply (DerivedCategory.isGE_iff _ 0).2
      intro q hq
      exact CondensedRing.isZero_homology_of_cover V
        (Q ⊗ (DerivedCategory.singleFunctor _ 0).obj N) q (fun j ↦ isEmptyElim j)
    · apply (DerivedCategory.isLE_iff _ 0).2
      intro q hq
      exact CondensedRing.isZero_homology_of_cover V
        (Q ⊗ (DerivedCategory.singleFunctor _ 0).obj N) q (fun j ↦ isEmptyElim j)

end AlgebraicGeometry.ProEtale
