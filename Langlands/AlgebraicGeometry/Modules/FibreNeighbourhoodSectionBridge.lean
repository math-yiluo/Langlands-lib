import Langlands.AlgebraicGeometry.Modules.FibreNeighbourhoodSections
import Langlands.AlgebraicGeometry.ProjectiveBundle.EvaluationRestriction
import Langlands.AlgebraicGeometry.Picard.ClosedImmersionPullbackAmpleProof

/-! # Comparing open-subscheme and fibre restrictions of sections -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.AlgebraicGeometry.ProjectiveBundle
open Langlands.AlgebraicGeometry.Picard

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Modules

variable {X Y S : Scheme.{u}}

/-- Pulling back through an open factorization agrees with direct pullback. -/
def openFactorPullbackIso (M : X.Modules) (A : X.Opens)
    (k : Y ⟶ A.toScheme) (g : Y ⟶ X) (hk : k ≫ A.ι = g) :
    (Scheme.Modules.pullback k).obj ((Scheme.Modules.pullback A.ι).obj M) ≅
      (Scheme.Modules.pullback g).obj M :=
  (Scheme.Modules.pullbackComp k A.ι).app M ≪≫
    (Scheme.Modules.pullbackCongr hk).app M

/-- The canonical factorization comparison preserves the actual restricted section. -/
lemma openFactorPullbackIso_hom_openSection (M : X.Modules) (A : X.Opens)
    (k : Y ⟶ A.toScheme) (g : Y ⟶ X) (hk : k ≫ A.ι = g)
    (hA : ⊤ ≤ g ⁻¹ᵁ A) (t : Γ(M, A)) :
    (openFactorPullbackIso M A k g hk).hom.app ⊤
        (pullbackSection k ((Scheme.Modules.pullback A.ι).obj M)
          (openSection M A t)) =
      sectionPullbackLE g M hA t := by
  rw [pullbackSection_eq_sectionPullbackLE, openSection_eq_sectionPullbackLE]
  simp only [openFactorPullbackIso, Iso.trans_hom, Iso.app_hom,
    Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
  have hkg : ⊤ ≤ (k ≫ A.ι) ⁻¹ᵁ A := by
    rw [hk]
    exact hA
  erw [pullbackComp_hom_sectionPullbackLE k A.ι M
    (show ⊤ ≤ A.ι ⁻¹ᵁ A by simp) (show ⊤ ≤ k ⁻¹ᵁ ⊤ by simp) hkg,
    pullbackCongr_hom_sectionPullbackLE hk M hkg hA]

/-- The same comparison specializes to the canonical neighbourhood-to-fibre section. -/
lemma openFactorPullbackIso_hom_fibreNeighbourhoodSection
    (f : X ⟶ S) (s : S) (M : X.Modules) {V : S.Opens} (hs : s ∈ V)
    (k : f.fiber s ⟶ (f ⁻¹ᵁ V).toScheme)
    (hk : k ≫ (f ⁻¹ᵁ V).ι = f.fiberι s) (t : Γ(M, f ⁻¹ᵁ V)) :
    (openFactorPullbackIso M (f ⁻¹ᵁ V) k (f.fiberι s) hk).hom.app ⊤
        (pullbackSection k ((Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj M)
          (openSection M (f ⁻¹ᵁ V) t)) =
      fibreNeighbourhoodSection f s M hs t :=
  openFactorPullbackIso_hom_openSection M (f ⁻¹ᵁ V) k (f.fiberι s) hk
    (fibre_preimage_neighbourhood f s hs) t

/-- The entire generation open is preserved by the factorization comparison. -/
lemma openFactor_sectionOpen (L : LineBundle X) (A : X.Opens)
    (k : Y ⟶ A.toScheme) (g : Y ⟶ X) (hk : k ≫ A.ι = g)
    (hA : ⊤ ≤ g ⁻¹ᵁ A) (t : Γ(L.obj, A)) :
    k ⁻¹ᵁ trivializationOpen ((Scheme.Modules.pullback A.ι).obj L.obj)
        (openSection L.obj A t) =
      trivializationOpen ((Scheme.Modules.pullback g).obj L.obj)
        (sectionPullbackLE g L.obj hA t) := by
  rw [← openFactorPullbackIso_hom_openSection L.obj A k g hk hA t,
    trivializationOpen_mapIso]
  exact (lineBundlePullbackSectionOpen A.toScheme Y k
    ((LineBundle.pullback A.ι).obj L) (openSection L.obj A t)).symm

/-- Generation opens of neighbourhood sections restrict to their actual fibre
generation opens. -/
lemma fibreNeighbourhoodSection_generationOpen
    (f : X ⟶ S) (s : S) (L : LineBundle X) {V : S.Opens} (hs : s ∈ V)
    (k : f.fiber s ⟶ (f ⁻¹ᵁ V).toScheme)
    (hk : k ≫ (f ⁻¹ᵁ V).ι = f.fiberι s) (t : Γ(L.obj, f ⁻¹ᵁ V)) :
    k ⁻¹ᵁ trivializationOpen ((Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj L.obj)
        (openSection L.obj (f ⁻¹ᵁ V) t) =
      trivializationOpen ((Scheme.Modules.pullback (f.fiberι s)).obj L.obj)
        (fibreNeighbourhoodSection f s L.obj hs t) :=
  openFactor_sectionOpen L (f ⁻¹ᵁ V) k (f.fiberι s) hk
    (fibre_preimage_neighbourhood f s hs) t

end Langlands.AlgebraicGeometry.Modules

namespace Langlands.AlgebraicGeometry.Picard.LineBundle

open Langlands.AlgebraicGeometry.Modules

variable {X S : Scheme.{u}}

/-- A section of a tensor power on an open, regarded as a power section of the
actually restricted line bundle. -/
def openPowSection (L : LineBundle X) (A : X.Opens) {n : ℕ}
    (t : Γ(tensorPow L.obj n, A)) :
    ((LineBundle.pullback A.ι).obj L).powSections n :=
  (actualPullbackTensorPowIso A.ι L.obj n).hom.app ⊤
    (openSection (tensorPow L.obj n) A t)

/-- The whole generation open of an actual restricted power section pulls back
to the generation open of its actual fibre restriction. -/
lemma sectionOpen_openPowSection_fibre
    (f : X ⟶ S) (s : S) (L : LineBundle X) {V : S.Opens} (hs : s ∈ V)
    (k : f.fiber s ⟶ (f ⁻¹ᵁ V).toScheme)
    (hk : k ≫ (f ⁻¹ᵁ V).ι = f.fiberι s) {n : ℕ}
    (t : Γ(tensorPow L.obj n, f ⁻¹ᵁ V)) :
    k ⁻¹ᵁ ((LineBundle.pullback (f ⁻¹ᵁ V).ι).obj L).sectionOpen
        (L.openPowSection (f ⁻¹ᵁ V) t) =
      ((LineBundle.pullback (f.fiberι s)).obj L).sectionOpen
        ((actualPullbackTensorPowIso (f.fiberι s) L.obj n).hom.app ⊤
          (fibreNeighbourhoodSection f s (tensorPow L.obj n) hs t)) := by
  change k ⁻¹ᵁ trivializationOpen _
      ((actualPullbackTensorPowIso (f ⁻¹ᵁ V).ι L.obj n).hom.app ⊤
        (openSection (tensorPow L.obj n) (f ⁻¹ᵁ V) t)) =
    trivializationOpen _
      ((actualPullbackTensorPowIso (f.fiberι s) L.obj n).hom.app ⊤
        (fibreNeighbourhoodSection f s (tensorPow L.obj n) hs t))
  rw [trivializationOpen_mapIso, trivializationOpen_mapIso]
  exact fibreNeighbourhoodSection_generationOpen f s
    ⟨tensorPow L.obj n, tensorPow_isLocallyFreeRankOne X L n⟩ hs k hk t

end Langlands.AlgebraicGeometry.Picard.LineBundle
