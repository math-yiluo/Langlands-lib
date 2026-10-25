import Langlands.AlgebraicGeometry.FiniteLocalBasisStatements
import Langlands.AlgebraicGeometry.RelativeDifferentialsAffineChart
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.CategoryTheory.Sites.Spaces

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

namespace Langlands.Scheme

private def localFreeIsoOfRestrict {X : AlgebraicGeometry.Scheme.{u}}
    (M : X.Modules) (U : X.Opens) (I : Type u)
    (e : M.restrict U.ι ≅ SheafOfModules.free (R := U.toScheme.ringCatSheaf) I) :
    SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U :=
  SheafOfModules.mapFreeIso (overEquiv U).inverse I
      (U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf).symm ≪≫
    (overEquiv U).inverse.mapIso e.symm ≪≫
    (overEquiv U).inverse.mapIso ((overFunctorEquiv U).app M).symm ≪≫
    ((overEquiv U).unitIso.app (M.over U)).symm

private def generatorsOfRestrict {X : AlgebraicGeometry.Scheme.{u}}
    (M : X.Modules) (U : X.Opens) (I : Type u)
    (e : M.restrict U.ι ≅ SheafOfModules.free (R := U.toScheme.ringCatSheaf) I) :
    (M.over U).GeneratingSections :=
  (SheafOfModules.free.generatingSections I).ofEpi (localFreeIsoOfRestrict M U I e).hom

private lemma generatorsOfRestrict_isIso {X : AlgebraicGeometry.Scheme.{u}}
    (M : X.Modules) (U : X.Opens) (I : Type u)
    (e : M.restrict U.ι ≅ SheafOfModules.free (R := U.toScheme.ringCatSheaf) I) :
    IsIso (generatorsOfRestrict M U I e).π := by
  dsimp [generatorsOfRestrict]
  rw [SheafOfModules.GeneratingSections.ofEpi_π]
  infer_instance

private def generatorsOnCover {X : AlgebraicGeometry.Scheme.{u}}
    (M : X.Modules) (U : X → X.Opens) (hx : ∀ x, x ∈ U x) (I : X → Type u)
    (e : ∀ x, M.restrict (U x).ι ≅
      SheafOfModules.free (R := (U x).toScheme.ringCatSheaf) (I x)) :
    SheafOfModules.LocalGeneratorsData.{u} M where
  I := X
  X := U
  coversTop := (_root_.Opens.coversTop_iff X U).mpr (by
    apply top_le_iff.mp
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx x⟩)
  generators x := generatorsOfRestrict M (U x) (I x) (e x)

private lemma generatorsOnCover_free {X : AlgebraicGeometry.Scheme.{u}}
    (M : X.Modules) (U : X → X.Opens) (hx : ∀ x, x ∈ U x) (I : X → Type u)
    (e : ∀ x, M.restrict (U x).ι ≅
      SheafOfModules.free (R := (U x).toScheme.ringCatSheaf) (I x)) :
    (generatorsOnCover M U hx I e).IsLocallyFreeData where
  isIso x := generatorsOfRestrict_isIso M (U x) (I x) (e x)

private lemma generatorsOnCover_finite {X : AlgebraicGeometry.Scheme.{u}}
    (M : X.Modules) (U : X → X.Opens) (hx : ∀ x, x ∈ U x) (I : X → Type u)
    (e : ∀ x, M.restrict (U x).ι ≅
      SheafOfModules.free (R := (U x).toScheme.ringCatSheaf) (I x)) (hI : ∀ x, Finite (I x)) :
    (generatorsOnCover M U hx I e).IsFiniteType where
  isFiniteType x := ⟨hI x⟩

private lemma finiteLocalBases_of_neighborhoods {X : AlgebraicGeometry.Scheme.{u}}
    (M : X.Modules)
    (h : ∀ x : X, ∃ (U : X.Opens), x ∈ U ∧ ∃ (I : Type u),
      Finite I ∧ Nonempty (M.restrict U.ι ≅
        SheafOfModules.free (R := U.toScheme.ringCatSheaf) I)) :
    ∃ q : SheafOfModules.LocalGeneratorsData.{u} M,
      q.IsLocallyFreeData ∧ q.IsFiniteType := by
  classical
  choose U hx I hI e using h
  exact ⟨generatorsOnCover M U hx I (fun x => (e x).some),
    generatorsOnCover_free M U hx I (fun x => (e x).some),
    generatorsOnCover_finite M U hx I (fun x => (e x).some) hI⟩

private lemma fixedRank_of_neighborhoods {X : AlgebraicGeometry.Scheme.{u}}
    (M : X.Modules) (n : ℕ)
    (h : ∀ x : X, ∃ (U : X.Opens), x ∈ U ∧ Nonempty (M.restrict U.ι ≅
      SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin n)))) :
    Modules.IsLocallyFreeOfRank M n := by
  classical
  choose U hx e using h
  refine ⟨generatorsOnCover M U hx (fun _ => ULift.{u} (Fin n)) (fun x => (e x).some),
    generatorsOnCover_free M U hx (fun _ => ULift.{u} (Fin n)) (fun x => (e x).some), ?_⟩
  intro x
  exact ⟨Equiv.ulift⟩

private lemma standardSmooth_basis {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] [Algebra.IsStandardSmooth R A] :
    ∃ I : Type u, Finite I ∧ Nonempty (Module.Basis I A (KaehlerDifferential R A)) := by
  classical
  obtain ⟨ι, σ, hσ, hι, ⟨P⟩⟩ := (inferInstance : Algebra.IsStandardSmooth R A).out
  let := hσ
  let := hι
  exact ⟨ULift.{u} ((Set.range P.map)ᶜ : Set ι), inferInstance,
    ⟨P.basisKaehler.reindex Equiv.ulift.symm⟩⟩

private lemma standardSmooth_basis_rank {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] (n : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension n R A] :
    Nonempty (Module.Basis (ULift.{u} (Fin n)) A (KaehlerDifferential R A)) := by
  classical
  obtain ⟨ι, σ, hσ, hι, P, hP⟩ :=
    (inferInstance : Algebra.IsStandardSmoothOfRelativeDimension n R A).out
  let := hσ
  let := hι
  let := Fintype.ofFinite ι
  let := Fintype.ofFinite σ
  have hc : Fintype.card ((Set.range P.map)ᶜ : Set ι) = n := by
    rw [Fintype.card_compl_set, Set.card_range_of_injective P.map_inj]
    simpa only [Algebra.Presentation.dimension, Nat.card_eq_fintype_card] using hP
  exact ⟨P.basisKaehler.reindex
    ((Fintype.equivFinOfCardEq hc).trans Equiv.ulift.symm)⟩

/-- Smooth differentials have finite local bases and the prescribed geometric rank. -/
theorem smoothDifferentialsFiniteLocalBasisRank :
    SmoothDifferentialsFiniteLocalBasisRankStatement.{u} := by
  intro X S f
  constructor
  · intro hf
    let := hf
    apply finiteLocalBases_of_neighborhoods
    intro x
    obtain ⟨U, hU, V, hV, hx, e, hstandard⟩ := Smooth.exists_isStandardSmooth f x
    let := (f.appLE U V e).hom.toAlgebra
    let : Algebra.IsStandardSmooth Γ(S, U) Γ(X, V) := hstandard
    obtain ⟨I, hI, ⟨b⟩⟩ := standardSmooth_basis (R := Γ(S, U)) (A := Γ(X, V))
    exact ⟨V, hx, I, hI, ⟨relativeDifferentialsAffineChartBasisIso f hU hV e I b⟩⟩
  · intro n hf
    let := hf
    apply fixedRank_of_neighborhoods
    intro x
    obtain ⟨U, hU, V, hV, hx, e, hstandard⟩ :=
      SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := n) (f := f) x
    let := (f.appLE U V e).hom.toAlgebra
    let : Algebra.IsStandardSmoothOfRelativeDimension n Γ(S, U) Γ(X, V) := hstandard
    obtain ⟨b⟩ := standardSmooth_basis_rank (R := Γ(S, U)) (A := Γ(X, V)) n
    exact ⟨V, hx,
      ⟨relativeDifferentialsAffineChartBasisIso f hU hV e (ULift.{u} (Fin n)) b⟩⟩

end Langlands.Scheme
