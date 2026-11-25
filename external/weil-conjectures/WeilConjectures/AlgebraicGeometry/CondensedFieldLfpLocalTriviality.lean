/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
public import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
public import Mathlib.Topology.NoetherianSpace

import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationCorank
import WeilConjectures.AlgebraicGeometry.CondensedFieldRankDescent
import WeilConjectures.AlgebraicGeometry.ContinuousFieldCokernelLocalFree

/-!
# Local triviality over continuous p-adic field coefficients

Source: Hemo--Richarz--Scholbach, Example 3.1, and the agent rank/descent argument
recorded in (auxiliary; not a blueprint node).
-/

@[expose] public section

universe u v w

open CategoryTheory MonoidalCategory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private lemma fp_map {X Y : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
    (T : Sheaf (Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1}) [MonObj R] [MonObj T]
    (F : Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) R ⥤
      Mod (Sheaf (Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1}) T)
    [F.Additive] [Limits.PreservesFiniteColimits F]
    (e : F.obj (Mod.regular R) ≅ Mod.regular T)
    {M : Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) R}
    (h : Mod.IsFinitelyPresented R M) : Mod.IsFinitelyPresented T (F.obj M) := by
  open Limits in
  rcases h with ⟨n, m, f, ⟨i⟩⟩
  let en (n : ℕ) : F.obj (Mod.finiteFree R n) ≅ Mod.finiteFree T n :=
    F.mapBiproduct (fun _ : Fin n ↦ Mod.regular R) ≪≫
      Limits.biproduct.mapIso (fun _ ↦ e)
  let f' : Mod.finiteFree T m ⟶ Mod.finiteFree T n :=
    (en m).inv ≫ F.map f ≫ (en n).hom
  exact ⟨n, m, f', ⟨F.mapIso i ≪≫ Limits.PreservesCokernel.iso F f ≪≫
    Limits.cokernel.mapIso (F.map f) f' (en m) (en n) (by simp [f'])⟩⟩

private lemma fp_comap {X : Scheme.{u}}
    {R T : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}}
    [MonObj R] [MonObj T]
    (φ : R ⟶ T) [IsMonHom φ] [IsIso φ]
    {M : Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) T}
    (h : Mod.IsFinitelyPresented T M) :
    Mod.IsFinitelyPresented R ((Mod.comap φ).obj M) := by
  let eqv : Mod _ T ≌ Mod _ R :=
    CategoryTheory.Equivalence.mk (Mod.comap φ) (Mod.comap (inv φ))
      ((Mod.comapId T).symm ≪≫ Mod.comapCongr (by simp) ≪≫ Mod.comapComp (inv φ) φ)
      ((Mod.comapComp φ (inv φ)).symm ≪≫ Mod.comapCongr (by simp) ≪≫ Mod.comapId R)
  have : (Mod.comap φ).IsEquivalence := eqv.isEquivalence_functor
  exact fp_map T R (Mod.comap φ) (by
    simpa using (Mod.regularIsoOfIsIso (inv φ))) h

private lemma lfp_comap {X : Scheme.{u}}
    {R T : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}}
    [MonObj R] [MonObj T]
    (φ : R ⟶ T) [IsMonHom φ] [IsIso φ]
    {M : Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) T}
    (h : IsLocallyFinitelyPresented T M) :
    IsLocallyFinitelyPresented R ((Mod.comap φ).obj M) := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C, fun i ↦ ?_⟩
  let F := upperStar AddCommGrpCat.{u + 1} (C.f i)
  obtain ⟨n, m, f, ⟨e⟩⟩ := fp_comap (F.map φ) (hC i)
  exact ⟨n, m, f, ⟨(F.mapModComapIso φ).app M ≪≫ e⟩⟩

private lemma free_comap {X : Scheme.{u}}
    {R T : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}}
    [MonObj R] [MonObj T]
    (φ : R ⟶ T) [IsMonHom φ] [IsIso φ]
    {M : Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) T}
    (h : Mod.IsFree T M) : Mod.IsFree R ((Mod.comap φ).obj M) := by
  let eqv : Mod _ T ≌ Mod _ R :=
    CategoryTheory.Equivalence.mk (Mod.comap φ) (Mod.comap (inv φ))
      ((Mod.comapId T).symm ≪≫ Mod.comapCongr (by simp) ≪≫ Mod.comapComp (inv φ) φ)
      ((Mod.comapComp φ (inv φ)).symm ≪≫ Mod.comapCongr (by simp) ≪≫ Mod.comapId R)
  have : (Mod.comap φ).IsEquivalence := eqv.isEquivalence_functor
  obtain ⟨n, ⟨e⟩⟩ := h
  refine ⟨n, ⟨(Mod.comap φ).mapIso e ≪≫ ?_⟩⟩
  exact (Mod.comap φ).mapBiproduct (fun _ : Fin n ↦ Mod.regular T) ≪≫
    Limits.biproduct.mapIso (fun _ ↦ by simpa using Mod.regularIsoOfIsIso (inv φ))

private lemma free_of_iso {V : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology V) AddCommGrpCat.{u + 1}} [MonObj R]
    {M N : Mod (Sheaf (Scheme.ProEt.topology V) AddCommGrpCat.{u + 1}) R}
    (h : Mod.IsFree R M) (e : M ≅ N) : Mod.IsFree R N := by
  obtain ⟨n, ⟨i⟩⟩ := h
  exact ⟨n, ⟨e.symm ≪≫ i⟩⟩

private lemma free_of_comap {V : Scheme.{u}}
    {R T : Sheaf (Scheme.ProEt.topology V) AddCommGrpCat.{u + 1}}
    [MonObj R] [MonObj T] (φ : R ⟶ T) [IsMonHom φ] [IsIso φ]
    {M : Mod (Sheaf (Scheme.ProEt.topology V) AddCommGrpCat.{u + 1}) T}
    (h : Mod.IsFree R ((Mod.comap φ).obj M)) : Mod.IsFree T M := by
  let e : (Mod.comap (inv φ)).obj ((Mod.comap φ).obj M) ≅ M :=
    ((Mod.comapComp (inv φ) φ).symm ≪≫ Mod.comapCongr (by simp) ≪≫ Mod.comapId T).app M
  exact free_of_iso (free_comap (inv φ) h) e

private lemma free_pullback_comp_iff {X Y Z : Scheme.{u}} (f : Z ⟶ Y) (g : Y ⟶ X)
    {R : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}} [MonObj R]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) R) :
    Mod.IsFree ((upperStar AddCommGrpCat.{u + 1} (f ≫ g)).obj R)
      (((upperStar AddCommGrpCat.{u + 1} (f ≫ g)).mapMod R).obj M) ↔
    Mod.IsFree ((upperStar AddCommGrpCat.{u + 1} f).obj
      ((upperStar AddCommGrpCat.{u + 1} g).obj R))
      (((upperStar AddCommGrpCat.{u + 1} f).mapMod _).obj
        (((upperStar AddCommGrpCat.{u + 1} g).mapMod R).obj M)) := by
  let F := upperStar AddCommGrpCat.{u + 1} g
  let G := upperStar AddCommGrpCat.{u + 1} f
  let e := upperStarComp AddCommGrpCat.{u + 1} f g
  let φ := Functor.compAlgHom F G e.inv R
  let i := (Functor.mapModCompIso F G e.inv R).app M
  exact ⟨fun h ↦ free_of_iso (free_comap φ h) i.symm,
    fun h ↦ free_of_comap φ (free_of_iso h i)⟩

/-- Local finite presentations over continuous field coefficients are locally finite free.
Source: Hemo--Richarz--Scholbach, Example 3.1, with the agent rank/descent argument
(auxiliary; not a blueprint node).
Proof: use the preceding continuous-function realization. Pull a finite presentation to a
geometric point; inverse image and evaluation preserve cokernels, and covers of a geometric
point split. Its dimension is independent of the algebraically closed representative.
The presentation matrix consists of continuous functions, so the dimension is n minus its
pointwise rank. Flat going-down lifts generalizations through presentation covers.
Continuous functions to the Hausdorff field E agree at comparable points, hence the rank
descends and is constant on specializations. Noetherianity gives finitely many irreducible
components and sobriety gives their generic points. Rank levels are therefore clopen.
Restrict presentations to these levels. Nonvanishing loci of maximal-rank minors cover;
Gaussian elimination using the continuous inverse of each invertible minor reduces the
matrix to an identity block and a Schur complement. The latter vanishes pointwise, hence
is zero as a matrix of functions. Its cokernel is finite free. For rank zero use the zero
matrix directly. Composing the covers proves the assertion, including the empty scheme.
All cokernels are ordinary sheaf cokernels; no completeness hypothesis is used. -/
theorem exists_finiteFree_cover_of_condensedField_lfp
    (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
    [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (P : Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj E) X))
    (hP : IsLocallyFinitelyPresented
      (condensedRingObj (Profinite.continuousCoefficientRingObj E) X) P) :
    ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : C.I₀,
      Mod.IsFree
        ((upperStar AddCommGrpCat.{u + 1} (C.f i)).obj
          (condensedRingObj (Profinite.continuousCoefficientRingObj E) X))
        (((upperStar AddCommGrpCat.{u + 1} (C.f i)).mapMod
          (condensedRingObj (Profinite.continuousCoefficientRingObj E) X)).obj P) := by
  classical
  let e₀ := (Module.finBasis ℚ_[l] E).equivFunL.toHomeomorph
  have : TotallyDisconnectedSpace E :=
    e₀.isEmbedding.isTotallyDisconnected_range.mp
      (isTotallyDisconnected_of_totallyDisconnectedSpace _)
  let R := condensedRingObj (Profinite.continuousCoefficientRingObj E) X
  obtain ⟨C, hC⟩ := hP
  choose n m f e using hC
  let A (i : C.I₀) := continuousFieldPresentationMatrix E (C.X i)
    (condensedFieldPullbackRealization E (C.f i)) (f i)
  let corank (i : C.I₀) (v : C.X i) : ℕ := n i - ((A i).map (fun a ↦ a v)).rank
  have hcompat (i j : C.I₀) (v : C.X i) (w : C.X j) (h : C.f i v = C.f j w) :
      corank i v = corank j w :=
    condensedField_presentation_corank_eq E X P C n m f (fun i ↦ (e i).some) i j v w h
  have hspec (i : C.I₀) {v w : C.X i} (h : v ⤳ w) : corank i v = corank i w := by
    have hA : (A i).map (fun a ↦ a v) = (A i).map (fun a ↦ a w) := by
      ext j k
      exact (h.map ((A i) j k).continuous).eq
    simp only [corank, hA]
  obtain ⟨d, hd, hdc⟩ := exists_locallyConstant_descent_of_specializes C.X C.f
    (fun i ↦ by
      have : WeaklyEtale (C.f i) :=
        Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ C.mem₀ (.mk i)
      infer_instance)
    (fun x ↦ by
      have hsurj := ((Scheme.ofArrows_mem_precoverage_iff (P := @WeaklyEtale)).1
        (Scheme.propQCPrecoverage_le_precoverage _ C.mem₀)).1
      exact hsurj x)
    corank hcompat (fun i _ _ h ↦ hspec i h)
  have hr (i : C.I₀) : IsLocallyConstant (fun v : C.X i ↦
      ((A i).map (fun a ↦ a v)).rank) := by
    have hc : IsLocallyConstant (corank i) := by
      have he : corank i = d ∘ (C.f i) := funext fun v ↦ (hdc i v).symm
      rw [he]
      exact hd.comp_continuous (C.f i).continuous
    have he : (fun v : C.X i ↦ ((A i).map (fun a ↦ a v)).rank) =
        (fun r ↦ n i - r) ∘ corank i := by
      funext v
      exact (Nat.sub_sub_self (Matrix.rank_le_height _)).symm
    rw [he]
    exact hc.comp _
  have hlocal (i : C.I₀) : ∃ D : Scheme.Cover.{u} Scheme.proetalePrecoverage (C.X i),
      ∀ j : D.I₀, Mod.IsFree
        ((upperStar AddCommGrpCat.{u + 1} (D.f j)).obj
          ((upperStar AddCommGrpCat.{u + 1} (C.f i)).obj R))
        (((upperStar AddCommGrpCat.{u + 1} (D.f j)).mapMod _).obj
          (((upperStar AddCommGrpCat.{u + 1} (C.f i)).mapMod R).obj P)) := by
    obtain ⟨D, hD⟩ := exists_finiteFree_cover_cokernel_of_locallyConstant_rank E (C.X i)
      _ (condensedFieldPullbackRealization E (C.f i)) (f i) (hr i)
    refine ⟨D, fun j ↦ free_of_iso (hD j) ?_⟩
    exact ((upperStar AddCommGrpCat.{u + 1} (D.f j)).mapMod _).mapIso (e i).some.symm
  choose D hD using hlocal
  refine ⟨C.bind D, fun ij ↦ ?_⟩
  rcases ij with ⟨i, j⟩
  exact (free_pullback_comp_iff ((D i).f j) (C.f i) P).mpr (hD i j)

/-- The local triviality assertion applies on every noetherian locally closed stratum.
Source: the concluding application in the agent rank/descent argument accompanying
Hemo--Richarz--Scholbach, Example 3.1
(auxiliary; not a blueprint node).
Proof: restrict the module to a stratum of its finite locally closed stratification.
The coefficient composition comparison identifies the restricted ring with the condensed
coefficient ring of the stratum. Apply the local triviality theorem there, to the finite
presentations in the stratified constructibility hypothesis. Pullback preserves the
coefficient comparison, so its finite free modules give exactly the displayed ones.
This includes empty strata, rank zero, and presentations with zero rows or columns. -/
theorem exists_finiteFree_cover_on_condensedField_strata
    (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
    [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (S : Scheme.Stratification X)
    (P : Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj E) X))
    (hP : ∀ a : Fin S.n,
      IsLocallyFinitelyPresented
        ((upperStar AddCommGrpCat.{u + 1} (S.immersion a)).obj
          (condensedRingObj (Profinite.continuousCoefficientRingObj E) X))
        (((upperStar AddCommGrpCat.{u + 1} (S.immersion a)).mapMod
          (condensedRingObj (Profinite.continuousCoefficientRingObj E) X)).obj P)) :
    ∀ (a : Fin S.n), TopologicalSpace.NoetherianSpace (S.domain a) →
      ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage (S.domain a), ∀ i : C.I₀,
        Mod.IsFree
          ((upperStar AddCommGrpCat.{u + 1} (C.f i)).obj
            ((upperStar AddCommGrpCat.{u + 1} (S.immersion a)).obj
              (condensedRingObj (Profinite.continuousCoefficientRingObj E) X)))
          (((upperStar AddCommGrpCat.{u + 1} (C.f i)).mapMod
            ((upperStar AddCommGrpCat.{u + 1} (S.immersion a)).obj
              (condensedRingObj (Profinite.continuousCoefficientRingObj E) X))).obj
            (((upperStar AddCommGrpCat.{u + 1} (S.immersion a)).mapMod
              (condensedRingObj (Profinite.continuousCoefficientRingObj E) X)).obj P)) := by
  intro a ha
  let Λ := Profinite.continuousCoefficientRingObj E
  let R := (upperStar AddCommGrpCat.{u + 1} (S.immersion a)).obj (condensedRingObj Λ X)
  let M := ((upperStar AddCommGrpCat.{u + 1} (S.immersion a)).mapMod
    (condensedRingObj Λ X)).obj P
  let φ := condensedPullbackHom Λ (S.immersion a)
  let Q := (Mod.comap (inv φ)).obj M
  have hQ : IsLocallyFinitelyPresented (condensedRingObj Λ (S.domain a)) Q :=
    lfp_comap (inv φ) (hP a)
  obtain ⟨C, hC⟩ := exists_finiteFree_cover_of_condensedField_lfp l E (S.domain a) Q hQ
  refine ⟨C, fun i ↦ ?_⟩
  let F := upperStar AddCommGrpCat.{u + 1} (C.f i)
  let e : (Mod.comap φ).obj Q ≅ M :=
    ((Mod.comapComp φ (inv φ)).symm ≪≫
      Mod.comapCongr (IsIso.hom_inv_id φ) ≪≫ Mod.comapId R).app M
  obtain ⟨n, ⟨f⟩⟩ := free_comap (F.map φ) (hC i)
  exact ⟨n, ⟨(F.mapMod R).mapIso e.symm ≪≫ (F.mapModComapIso φ).app Q ≪≫ f⟩⟩


end AlgebraicGeometry.ProEtale
