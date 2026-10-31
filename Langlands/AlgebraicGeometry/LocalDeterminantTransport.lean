import Langlands.AlgebraicGeometry.LocalChartDeterminantPullback
import Langlands.AlgebraicGeometry.LocalSectionIso
import Langlands.AlgebraicGeometry.ModuleDualPullbackLocalFree

/-! # Actual pullback charts transported through local sheaf isomorphisms -/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v

namespace Langlands.Scheme.Modules

variable {X Y : AlgebraicGeometry.Scheme.{u}}

/-- Local pullback of a restricted global morphism is its actual pulled-back restriction. -/
lemma localHomPullback_over (f : X ⟶ Y) {M N : Y.Modules} (a : M ⟶ N)
    (U : Y.Opens) :
    localHomPullback f U (a.over U) =
      ((AlgebraicGeometry.Scheme.Modules.pullback f).map a).over (f ⁻¹ᵁ U) := by
  have h := localHomPullback_naturality f (𝟙 M) a U (𝟙 (M.over U))
  simpa only [SheafOfModules.Hom.over, CategoryTheory.Functor.map_id, Category.id_comp,
    Category.comp_id, localHomPullback_id] using h

variable {I : Type u} [Fintype I] {M : Y.Modules} {U : Y.Opens}
    {N : X.Modules}

local instance localDeterminantTransportDecidableEq : DecidableEq I := Classical.decEq I

/-- The finite chart on a target sheaf obtained by actual pullback and a local isomorphism. -/
def chartFreePullbackTransportIso (f : X ⟶ Y)
    (e : SheafOfModules.free (R := Y.ringCatSheaf.over U) I ≅ M.over U)
    (h : ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M).over (f ⁻¹ᵁ U) ≅
      N.over (f ⁻¹ᵁ U)) :
    SheafOfModules.free (R := X.ringCatSheaf.over (f ⁻¹ᵁ U)) I ≅ N.over (f ⁻¹ᵁ U) :=
  chartFreePullbackIso f U e ≪≫ h

set_option maxRecDepth 2048 in
/-- In the constructed transported chart, actual section matrices are coefficient pullbacks. -/
theorem localSectionEndomorphism_toMatrix_pullback_transport (f : X ⟶ Y)
    (e : SheafOfModules.free (R := Y.ringCatSheaf.over U) I ≅ M.over U)
    (h : ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M).over (f ⁻¹ᵁ U) ≅
      N.over (f ⁻¹ᵁ U))
    (a : End (M.over U)) (b : End (N.over (f ⁻¹ᵁ U)))
    (hab : localHomPullback f U a ≫ h.hom = h.hom ≫ b) (V : Over U) :
    LinearMap.toMatrix
        (localSectionBasis (chartFreePullbackTransportIso f e h)
          (Over.mk ((TopologicalSpace.Opens.map f.base).map V.hom)))
        (localSectionBasis (chartFreePullbackTransportIso f e h)
          (Over.mk ((TopologicalSpace.Opens.map f.base).map V.hom)))
        (localSectionEndomorphism N
          (Over.mk ((TopologicalSpace.Opens.map f.base).map V.hom)) b) =
      (LinearMap.toMatrix (localSectionBasis e V) (localSectionBasis e V)
        (localSectionEndomorphism M V a)).map (f.app V.left) := by
  unfold chartFreePullbackTransportIso
  rw [← localSectionEndomorphism_toMatrix_iso (chartFreePullbackIso f U e) h
    (localHomPullback f U a) b hab]
  exact localSectionEndomorphism_toMatrix_pullback f e a V

variable {ι : Type v} [Fintype ι]

/-- Actual pullback followed by local transport preserves the universal determinant polynomial. -/
theorem localSectionDeterminant_pullback_transport (f : X ⟶ Y)
    (e : SheafOfModules.free (R := Y.ringCatSheaf.over U) I ≅ M.over U)
    (h : ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M).over (f ⁻¹ᵁ U) ≅
      N.over (f ⁻¹ᵁ U))
    (a : ι → End (M.over U)) (b : ι → End (N.over (f ⁻¹ᵁ U)))
    (hab : ∀ i, localHomPullback f U (a i) ≫ h.hom = h.hom ≫ b i) (V : Over U) :
    MvPolynomial.map (f.app V.left).hom (localSectionDeterminant e a V) =
      localSectionDeterminant (chartFreePullbackTransportIso f e h) b
        (Over.mk ((TopologicalSpace.Opens.map f.base).map V.hom)) := by
  rw [localSectionDeterminant_pullback f e a V]
  exact localSectionDeterminant_iso (chartFreePullbackIso f U e) h
    (fun i => localHomPullback f U (a i)) b hab _

/-- Every finite target chart on the same inverse-image chart open gives this polynomial. -/
theorem localSectionDeterminant_pullback_transport_any_chart (f : X ⟶ Y)
    (e : SheafOfModules.free (R := Y.ringCatSheaf.over U) I ≅ M.over U)
    (h : ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M).over (f ⁻¹ᵁ U) ≅
      N.over (f ⁻¹ᵁ U))
    {J : Type u} [Fintype J]
    (e' : SheafOfModules.free (R := X.ringCatSheaf.over (f ⁻¹ᵁ U)) J ≅
      N.over (f ⁻¹ᵁ U))
    (a : ι → End (M.over U)) (b : ι → End (N.over (f ⁻¹ᵁ U)))
    (hab : ∀ i, localHomPullback f U (a i) ≫ h.hom = h.hom ≫ b i) (V : Over U) :
    MvPolynomial.map (f.app V.left).hom (localSectionDeterminant e a V) =
      localSectionDeterminant e' b
        (Over.mk ((TopologicalSpace.Opens.map f.base).map V.hom)) := by
  rw [localSectionDeterminant_pullback f e a V]
  exact localSectionDeterminant_iso_any_chart (chartFreePullbackIso f U e) h e'
    (fun i => localHomPullback f U (a i)) b hab _

/-- Every determinant coefficient transports as an actual section of the structure sheaf. -/
theorem coeff_localSectionDeterminant_pullback_transport (f : X ⟶ Y)
    (e : SheafOfModules.free (R := Y.ringCatSheaf.over U) I ≅ M.over U)
    (h : ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M).over (f ⁻¹ᵁ U) ≅
      N.over (f ⁻¹ᵁ U))
    (a : ι → End (M.over U)) (b : ι → End (N.over (f ⁻¹ᵁ U)))
    (hab : ∀ i, localHomPullback f U (a i) ≫ h.hom = h.hom ≫ b i)
    (V : Over U) (d : ι →₀ ℕ) :
    f.app V.left ((localSectionDeterminant e a V).coeff d) =
      (localSectionDeterminant (chartFreePullbackTransportIso f e h) b
        (Over.mk ((TopologicalSpace.Opens.map f.base).map V.hom))).coeff d := by
  rw [← localSectionDeterminant_pullback_transport f e h a b hab V]
  exact (MvPolynomial.coeff_map _ _ _).symm

/-- A global intertwining equation restricts to the one required by local determinant transport. -/
lemma localHomPullback_over_intertwine (f : X ⟶ Y) {M : Y.Modules} {N : X.Modules}
    (h : (AlgebraicGeometry.Scheme.Modules.pullback f).obj M ≅ N)
    (a : End M) (b : End N)
    (hab : (AlgebraicGeometry.Scheme.Modules.pullback f).map a ≫ h.hom = h.hom ≫ b)
    (U : Y.Opens) :
    localHomPullback f U (a.over U) ≫ h.hom.over (f ⁻¹ᵁ U) =
      h.hom.over (f ⁻¹ᵁ U) ≫ b.over (f ⁻¹ᵁ U) := by
  rw [localHomPullback_over]
  exact congrArg ((SheafOfModules.overFunctor X.ringCatSheaf (f ⁻¹ᵁ U)).map) hab

end Langlands.Scheme.Modules
