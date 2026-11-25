/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedCompleteIntegralDetailed
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import WeilConjectures.SmoothPurity.Supporting.Coefficient.ConstantCoefficientObjectsConstructible
import WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisons
import all WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
import WeilConjectures.CategoryTheory.Ringed.Site.RingedSitePerfectDuality

/-! # Completeness of a locally free completed-coefficient line

Source: coefficient-twist blueprint, proof step 11; Bhatt--Scholze, Section 6.5.
(blueprint: lem-pur-completed-line-complete)
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u d
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace AlgebraicGeometry.Scheme

private theorem regular_package
    {S : Scheme.{u}} (U : S.ProEt)
    (R : Sheaf ((ProEt.topology S).over U) RingCat.{u + 1}) :
    Nonempty (SheafOfModules.StrictPerfectCoefficientPackageOnSite R
      ((HomologicalComplex.single _ (.up ℤ) 0).obj (SheafOfModules.unit R))) := by
  classical
  let F := (HomologicalComplex.single _ (.up ℤ) 0).obj (SheafOfModules.unit R)
  have h (n : ℤ) : ∃ k : ℕ, Nonempty (F.X n ≅
      ∏ᶜ fun _ : Fin k ↦ SheafOfModules.unit R) := by
    by_cases hn : n = 0
    · subst n
      exact ⟨1, ⟨HomologicalComplex.singleObjXSelf (.up ℤ) 0 _ ≪≫
        (productUniqueIso (fun _ : Fin 1 ↦ SheafOfModules.unit R)).symm⟩⟩
    · refine ⟨0, ⟨?_⟩⟩
      have hz : IsZero (∏ᶜ fun _ : Fin 0 ↦ SheafOfModules.unit R) :=
        (IsZero.iff_id_eq_zero _).mpr (by
          apply Pi.hom_ext
          intro i
          exact Fin.elim0 i)
      exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ n hn).isoZero ≪≫
        hz.isoZero.symm
  choose N e using h
  exact ⟨{ N := N
           i := fun n ↦ (e n).some.hom
           p := fun n ↦ (e n).some.inv
           splitting := fun n ↦ (e n).some.hom_inv_id }⟩

private theorem line_perfect (S : Scheme.{u})
    (R : Sheaf (ProEt.topology S) CommRingCat.{u + 1})
    (L : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology S)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    (hL : L.IsFiniteLocallyFreeOfRank 1) :
    SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u + 1, u, u, u + 2} R
      ((DerivedCategory.singleFunctor _ 0).obj L) := by
  classical
  let A := (sheafCompose (ProEt.topology S)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  let K := (HomologicalComplex.single _ (.up ℤ) 0).obj L
  refine ⟨K, ?_, ⟨(DerivedCategory.singleFunctorIsoCompQ _ 0).app L⟩⟩
  obtain ⟨I, X, hX, he⟩ :=
    (SheafOfModules.isFiniteLocallyFreeOfRank_iff_exists_over_iso_free
      (M := L) (r := 1)).mp hL
  intro V
  refine ⟨Sieve.ofObjects X V, hX V, ?_⟩
  rintro U f ⟨i, ⟨g⟩⟩
  let e : L.over U ≅ SheafOfModules.unit (A.over U) :=
    ((SheafOfModules.overFunctorMap A g).app L).symm ≪≫
      (SheafOfModules.overMap A g).mapIso ((he i).some ≪≫
        SheafOfModules.freeUniqueIso _) ≪≫ SheafOfModules.overMapUnitIso (R := A) g
  let F := (HomologicalComplex.single _ (.up ℤ) 0).obj
    (SheafOfModules.unit (A.over U))
  refine ⟨F, ⟨0, 0, ?_⟩, regular_package U (A.over U), ?_⟩
  · intro n hn
    exact HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ n (by omega)
  · let a := (HomologicalComplex.single _ (.up ℤ) 0).mapIso e.symm ≪≫
      ((HomologicalComplex.singleMapHomologicalComplex
        (SheafOfModules.overFunctor A U) (.up ℤ) 0).app L).symm
    exact ⟨a.hom, inferInstance⟩

private theorem sf_complete_iso (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (S : Scheme.{u}) {K L : DerivedCategory (WeilConjectures.scalarReductionSource l E S)}
    (e : K ≅ L) (h : WeilConjectures.IsSfDerivedComplete l E S K) :
    WeilConjectures.IsSfDerivedComplete l E S L := by
  let a (n : ℕ) := (WeilConjectures.sfDerivedReductionRestricted l E S n).mapIso e
  unfold WeilConjectures.IsSfDerivedComplete at h ⊢
  exact WeilConjectures.roos_transport
    (fun n ↦ (WeilConjectures.sfDerivedReductionTransition l E S n).app K)
    (fun n ↦ (WeilConjectures.sfDerivedReductionTransition l E S n).app L)
    e a (fun n ↦ (WeilConjectures.sfDerivedReductionUnit l E S n).app K)
    (fun n ↦ (WeilConjectures.sfDerivedReductionUnit l E S n).app L)
    (fun n ↦ ((WeilConjectures.sfDerivedReductionTransition l E S n).naturality e.hom).symm)
    (fun n ↦ ((WeilConjectures.sfDerivedReductionUnit l E S n).naturality e.hom).symm) h

/-- A locally free completed-coefficient line in degree zero is derived complete.

Source: coefficient-twist blueprint, proof step 11; Bhatt--Scholze, Sections 3.4
and 6.5; Stacks Project, Tag 08JJ.
(blueprint: lem-pur-completed-line-complete)

Proof: use a local rank-one trivialization to represent the line by a bounded
single complex of regular modules on a covering sieve. In degree zero the
regular module is the product indexed by Fin 1; in every other degree both the
term and the product indexed by Fin 0 are zero. These splittings give a strict
perfect coefficient package. Perfect duality identifies the line with its
bidual relative to the regular coefficient object. That regular object is
complete by the constant-coefficient theorem. Internal Hom into a complete
object is complete, so the bidual is complete. Transport its actual augmented
reduction triangle along the bidual isomorphism, using naturality of the
reduction transitions and units. Finally the proved comparison of the intrinsic
and finite-field presentations gives exactly IsDerivedComplete for any supplied
datum. This uses no invertibility or nonemptiness assumption on the base. -/
theorem completedLine_complete (S : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : SheafOfModules.{u + 1}
      (WeilConjectures.completedIntegralCoefficientSheafUnrestricted.{u, u} l E S))
    (hL : L.IsFiniteLocallyFreeOfRank 1)
    (D : WeilConjectures.FiniteFieldDatum.{d}) (hl : l ≠ D.p) :
    letI := WeilConjectures.integralCoefficientAbLocallyBijective.{u, u} S
    WeilConjectures.IsDerivedComplete.{d, u, u} l E S D hl
      ((DerivedCategory.singleFunctor _ 0).obj L) := by
  classical
  let := WeilConjectures.integralCoefficientAbLocallyBijective.{u, u} S
  let R := WeilConjectures.completedIntegralCommRingSheafUnrestricted.{u, u} l E S
  let P := (DerivedCategory.singleFunctor _ 0).obj L
  let O := ringedSiteDualityUnit.{u + 1, u, u, u + 2} (ProEt.topology S) R
  let H := WeilConjectures.integralDerivedInternalHom l E S
  have hO : WeilConjectures.IsSfDerivedComplete l E S O := by
    obtain ⟨D', hl', hc⟩ :=
      (WeilConjectures.integralConstantCoefficient_constructible l E S D hl).2.2.1
    have hs := (WeilConjectures.sfDerivedComplete_iff_legacy l E S D' hl' _).mpr hc
    exact sf_complete_iso l E S
      ((DerivedCategory.singleFunctorIsoCompQ _ 0).app (SheafOfModules.unit _)) hs
  obtain ⟨M, _, hbidual, _⟩ := ringedSitePerfectDuality.{u + 1, u, u, u + 2}
    (ProEt.topology S) R P (line_perfect S R L hL)
  have hc := WeilConjectures.scalarInternalHom_complete l E S
    (H.obj (op P, O)) O hO
  exact (WeilConjectures.sfDerivedComplete_iff_legacy l E S D hl P).mp
    (sf_complete_iso l E S (@Iso.symm _ _ _ _ (@asIso _ _ _ _ _ hbidual)) hc)

end AlgebraicGeometry.Scheme
