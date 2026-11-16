import Langlands.AlgebraicGeometry.Picard.DeterminantVariableCoverPullback
import Langlands.AlgebraicGeometry.PullbackFiniteLocalBasisRankProof

/-! # Determinant lines of actual finite locally free module sheaves -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Scheme.Modules

/-- One covering family of actual local generators is simultaneously finite
and a family of bases. Its finite rank may depend on the chart. -/
def HasFiniteLocalBasis {X : AlgebraicGeometry.Scheme.{u}} (M : X.Modules) : Prop :=
  ∃ q : SheafOfModules.LocalGeneratorsData.{u} M,
    q.IsLocallyFreeData ∧ q.IsFiniteType

lemma HasFiniteLocalBasis.pullback {X Y : AlgebraicGeometry.Scheme.{u}}
    {M : X.Modules} (h : HasFiniteLocalBasis M) (f : Y ⟶ X) :
    HasFiniteLocalBasis ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M) :=
  (pullbackFiniteLocalBasisRank Y X f M).1 h

end Langlands.Scheme.Modules

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.Scheme.Modules

/-- A covering of actual free charts, with a separate finite rank on each chart. -/
structure FiniteLocalFrames {X : Scheme.{u}} (M : X.Modules) where
  I : Type u
  opens : I → X.Opens
  covers : (⨆ i, opens i) = ⊤
  rank : I → ℕ
  frame : ∀ i, SheafOfModules.free (R := X.ringCatSheaf.over (opens i))
    (ULift.{u} (Fin (rank i))) ≅ M.over (opens i)

namespace FiniteLocalFrames

variable {X Y : Scheme.{u}} {M N P : X.Modules}

/-- Enumerate each certified finite local basis, without choosing a common rank. -/
def ofLocalBasis (q : SheafOfModules.LocalGeneratorsData.{u} M)
    [hfree : q.IsLocallyFreeData] [hfinite : q.IsFiniteType] :
    FiniteLocalFrames M where
  I := q.I
  opens := q.X
  covers := (_root_.Opens.coversTop_iff X q.X).mp q.coversTop
  rank i := @Fintype.card (q.generators i).I
    (@Fintype.ofFinite _ (hfinite.isFiniteType i).finite)
  frame i := by
    letI : Finite (q.generators i).I := (hfinite.isFiniteType i).finite
    letI : Fintype (q.generators i).I := Fintype.ofFinite _
    exact (SheafOfModules.freeFunctor (R := X.ringCatSheaf.over (q.X i))).mapIso
      (Equiv.ulift.trans (Fintype.equivFin (q.generators i).I).symm).toIso ≪≫
        asIso (q.generators i).π

/-- Actual finite free charts give a finite local basis witness. -/
def localGeneratorsData (a : FiniteLocalFrames M) :
    SheafOfModules.LocalGeneratorsData.{u} M where
  I := a.I
  X := a.opens
  coversTop := (_root_.Opens.coversTop_iff X a.opens).mpr a.covers
  generators i := (SheafOfModules.free.generatingSections
    (ULift.{u} (Fin (a.rank i)))).ofEpi (a.frame i).hom

instance (a : FiniteLocalFrames M) :
    a.localGeneratorsData.IsLocallyFreeData where
  isIso i := by
    change IsIso ((SheafOfModules.free.generatingSections
      (ULift.{u} (Fin (a.rank i)))).ofEpi (a.frame i).hom).π
    rw [SheafOfModules.GeneratingSections.ofEpi_π]
    infer_instance

instance (a : FiniteLocalFrames M) : a.localGeneratorsData.IsFiniteType where
  isFiniteType i := by
    refine ⟨?_⟩
    change Finite (ULift.{u} (Fin (a.rank i)))
    infer_instance

lemma hasFiniteLocalBasis (a : FiniteLocalFrames M) : HasFiniteLocalBasis M :=
  ⟨a.localGeneratorsData, inferInstance, inferInstance⟩

/-- Choose charts only from the proved finite local basis condition. -/
def choose (h : HasFiniteLocalBasis M) : FiniteLocalFrames M :=
  letI := h.choose_spec.1
  letI := h.choose_spec.2
  ofLocalBasis h.choose

/-- The actual line bundle glued from the determinant transition functions. -/
def lineBundle (a : FiniteLocalFrames M) : LineBundle X :=
  VariableDeterminantFrames.lineBundle a.frame a.covers

/-- The determinant isomorphism between two arbitrary frame presentations. -/
def isoMap (a : FiniteLocalFrames M) (b : FiniteLocalFrames N) (φ : M ≅ N) :
    a.lineBundle ≅ b.lineBundle :=
  VariableDeterminantFrames.lineBundleIsoMap a.frame b.frame φ a.covers b.covers

@[simp]
lemma isoMap_refl (a : FiniteLocalFrames M) :
    a.isoMap a (Iso.refl M) = Iso.refl _ :=
  VariableDeterminantFrames.lineBundleIsoMap_refl a.frame a.covers

lemma isoMap_comp (a : FiniteLocalFrames M) (b : FiniteLocalFrames N)
    (c : FiniteLocalFrames P) (φ : M ≅ N) (ψ : N ≅ P) :
    a.isoMap b φ ≪≫ b.isoMap c ψ = a.isoMap c (φ ≪≫ ψ) :=
  VariableDeterminantFrames.lineBundleIsoMap_comp a.frame b.frame c.frame φ ψ
    a.covers b.covers c.covers

/-- Compare any two choices of covering finite frames of the same module. -/
def changeIso (a b : FiniteLocalFrames M) : a.lineBundle ≅ b.lineBundle :=
  a.isoMap b (Iso.refl M)

@[simp]
lemma changeIso_self (a : FiniteLocalFrames M) :
    a.changeIso a = Iso.refl _ := a.isoMap_refl

lemma changeIso_trans (a b c : FiniteLocalFrames M) :
    a.changeIso b ≪≫ b.changeIso c = a.changeIso c := by
  simpa only [changeIso, Iso.refl_trans] using
    a.isoMap_comp b c (Iso.refl M) (Iso.refl M)

lemma changeIso_isoMap (a b : FiniteLocalFrames M) (c : FiniteLocalFrames N)
    (φ : M ≅ N) :
    a.changeIso b ≪≫ b.isoMap c φ = a.isoMap c φ := by
  simpa only [changeIso, Iso.refl_trans] using
    a.isoMap_comp b c (Iso.refl M) φ

lemma isoMap_changeIso (a : FiniteLocalFrames M) (b c : FiniteLocalFrames N)
    (φ : M ≅ N) :
    a.isoMap b φ ≪≫ b.changeIso c = a.isoMap c φ := by
  simpa only [changeIso, Iso.trans_refl] using
    a.isoMap_comp b c φ (Iso.refl N)

/-- Pull back every actual free chart along an arbitrary scheme morphism. -/
def pullback (a : FiniteLocalFrames M) (f : Y ⟶ X) :
    FiniteLocalFrames ((Scheme.Modules.pullback f).obj M) where
  I := a.I
  opens i := f ⁻¹ᵁ a.opens i
  covers := f.iSup_preimage_eq_top a.covers
  rank := a.rank
  frame := VariableDeterminantFrames.pullbackFrames a.frame f

/-- Pullback of the determinant compared with the pulled-back actual charts. -/
def pullbackIso (a : FiniteLocalFrames M) (f : Y ⟶ X) :
    (LineBundle.pullback f).obj a.lineBundle ≅ (a.pullback f).lineBundle :=
  VariableDeterminantFrames.lineBundlePullbackIso a.frame f a.covers

lemma pullbackIso_naturality (a : FiniteLocalFrames M) (b : FiniteLocalFrames N)
    (f : Y ⟶ X) (φ : M ≅ N) :
    (LineBundle.pullback f).mapIso (a.isoMap b φ) ≪≫ b.pullbackIso f =
      a.pullbackIso f ≪≫
        (a.pullback f).isoMap (b.pullback f) ((Scheme.Modules.pullback f).mapIso φ) :=
  VariableDeterminantFrames.lineBundlePullbackIso_naturality a.frame b.frame f φ
    a.covers b.covers

end FiniteLocalFrames

/-- The determinant line of an actual finite locally free module sheaf. -/
def finiteLocallyFreeDeterminant {X : Scheme.{u}} {M : X.Modules}
    (h : HasFiniteLocalBasis M) : LineBundle X :=
  (FiniteLocalFrames.choose h).lineBundle

/-- Determinant of an actual isomorphism, using the chosen finite local frames. -/
def finiteLocallyFreeDeterminantIso {X : Scheme.{u}} {M N : X.Modules}
    (hM : HasFiniteLocalBasis M) (hN : HasFiniteLocalBasis N) (φ : M ≅ N) :
    finiteLocallyFreeDeterminant hM ≅ finiteLocallyFreeDeterminant hN :=
  (FiniteLocalFrames.choose hM).isoMap (FiniteLocalFrames.choose hN) φ

@[simp]
lemma finiteLocallyFreeDeterminantIso_refl {X : Scheme.{u}} {M : X.Modules}
    (hM : HasFiniteLocalBasis M) :
    finiteLocallyFreeDeterminantIso hM hM (Iso.refl M) = Iso.refl _ :=
  (FiniteLocalFrames.choose hM).isoMap_refl

lemma finiteLocallyFreeDeterminantIso_comp {X : Scheme.{u}} {M N P : X.Modules}
    (hM : HasFiniteLocalBasis M) (hN : HasFiniteLocalBasis N)
    (hP : HasFiniteLocalBasis P) (φ : M ≅ N) (ψ : N ≅ P) :
    finiteLocallyFreeDeterminantIso hM hN φ ≪≫
      finiteLocallyFreeDeterminantIso hN hP ψ =
        finiteLocallyFreeDeterminantIso hM hP (φ ≪≫ ψ) :=
  (FiniteLocalFrames.choose hM).isoMap_comp
    (FiniteLocalFrames.choose hN) (FiniteLocalFrames.choose hP) φ ψ

/-- Comparison with any supplied finite covering frame system. -/
def finiteLocallyFreeDeterminantPresentationIso {X : Scheme.{u}} {M : X.Modules}
    (a : FiniteLocalFrames M) (hM : HasFiniteLocalBasis M) :
    a.lineBundle ≅ finiteLocallyFreeDeterminant hM :=
  a.changeIso (FiniteLocalFrames.choose hM)

/-- Presentation comparisons intertwine every actual module isomorphism. -/
lemma finiteLocallyFreeDeterminantPresentationIso_naturality
    {X : Scheme.{u}} {M N : X.Modules}
    (a : FiniteLocalFrames M) (b : FiniteLocalFrames N)
    (hM : HasFiniteLocalBasis M) (hN : HasFiniteLocalBasis N) (φ : M ≅ N) :
    finiteLocallyFreeDeterminantPresentationIso a hM ≪≫
        finiteLocallyFreeDeterminantIso hM hN φ =
      a.isoMap b φ ≪≫ finiteLocallyFreeDeterminantPresentationIso b hN := by
  exact (a.changeIso_isoMap _ _ φ).trans (a.isoMap_changeIso _ _ φ).symm

end Langlands.AlgebraicGeometry.Picard
