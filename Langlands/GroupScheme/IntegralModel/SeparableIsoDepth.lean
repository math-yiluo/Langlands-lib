import Langlands.GroupScheme.IntegralModel.SeparableDepthVector
import Langlands.GroupScheme.IntegralModel.SemilinearExtension

/-! # Separable additive depth models under an actual generic isomorphism -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u w

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.FieldTheory

namespace Langlands.GroupScheme.IntegralModel

variable {K : Type u} [Field K]
  (v : Valuation K (WithZero (Multiplicative ℤ)))
  (hH : HenselianLocalRing v.valuationSubring)
  (E : Type w) [Field E] [Algebra K E] [Algebra.IsSeparable K E]
  (hv : Function.Surjective v) [FiniteDimensional K E]
  (b : Module.Basis (Fin (Module.finrank K E)) K E)
  {U : GroupScheme (Spec (CommRingCat.of K))}
  (e : U ≅ VectorGroup.groupScheme (CommRingCat.of K) (Module.finrank K E))

/-- Retarget the actual separable depth lattice along a generic group-scheme
isomorphism, retaining the polynomial integral group. -/
def separableIsoDepthModel (r : ℝ) : IntegralModel v.valuationSubring K U :=
  (separableDepthVector v hH E hv b r).retarget e.symm

/-- The transported integral-point image is exactly the actual depth lattice
in the extension field, evaluated through the generic isomorphism. -/
theorem separableIsoDepthModel_mem_integralPoints (r : ℝ) (g : rationalPoints U) :
    g ∈ (separableIsoDepthModel v hH E hv b e r).integralPoints ↔
      separableDepthVectorPoint E b (rationalPoints.map e.hom g) ∈
        henselianSeparableDepthLattice v hH E r := by
  rw [separableIsoDepthModel, retarget_integralPoints]
  have hmem :
      g ∈ (separableDepthVector v hH E hv b r).integralPoints.map
          (rationalPoints.map e.inv) ↔
        rationalPoints.map e.hom g ∈
          (separableDepthVector v hH E hv b r).integralPoints := by
    constructor
    · rintro ⟨z, hz, rfl⟩
      have he : rationalPoints.map e.hom (rationalPoints.map e.inv z) = z := by
        simp only [rationalPoints.map_apply, Category.assoc,
          ← Grp.comp_hom_hom, Iso.inv_hom_id, Grp.id_hom_hom, Category.comp_id]
      exact he.symm ▸ hz
    · intro hg
      refine ⟨rationalPoints.map e.hom g, hg, ?_⟩
      simp only [rationalPoints.map_apply, Category.assoc,
        ← Grp.comp_hom_hom, Iso.hom_inv_id, Grp.id_hom_hom, Category.comp_id]
  exact hmem.trans (separableDepthVector_mem_integralPoints v hH E hv b r _)

theorem separableIsoDepthModel_isSmooth (r : ℝ) :
    (separableIsoDepthModel v hH E hv b e r).IsSmooth := by
  change Smooth (VectorGroup.groupScheme (CommRingCat.of v.valuationSubring)
    (Module.finrank K E)).X.hom
  exact VectorGroup.smooth _ _

theorem separableIsoDepthModel_hasGeometricallyConnectedFibres (r : ℝ) :
    (separableIsoDepthModel v hH E hv b e r).HasGeometricallyConnectedFibres := by
  change GeometricallyConnected
    (VectorGroup.groupScheme (CommRingCat.of v.valuationSubring) (Module.finrank K E)).X.hom
  exact VectorGroup.geometricallyConnected _ _

/-- The actual inclusion of depth lattices extends the generic identity
after transporting both generic identifications. -/
def separableIsoDepthTransition (r s : ℝ) (hrs : r ≤ s) :
    (separableIsoDepthModel v hH E hv b e s).Hom
      (separableIsoDepthModel v hH E hv b e r) (𝟙 _) where
  hom := (separableDepthVectorTransition v hH E hv b r s hrs).hom
  generic_comm := by
    have hc := (separableDepthVectorTransition v hH E hv b r s hrs).generic_comm
    change _ ≫ ((separableDepthVector v hH E hv b r).genericIso.hom ≫ e.inv) =
      ((separableDepthVector v hH E hv b s).genericIso.hom ≫ e.inv) ≫ 𝟙 _
    rw [Category.comp_id, ← Category.assoc, hc, Category.comp_id]

/-- Every generic-identity extension between the transported models has a
smooth, connected and unipotent actual scheme-theoretic residue kernel. -/
theorem separableIsoDepthModel_kernel_properties (r s : ℝ) (hrs : r ≤ s)
    (φ : (separableIsoDepthModel v hH E hv b e s).Hom
      (separableIsoDepthModel v hH E hv b e r) (𝟙 _)) :
    Smooth (kernel φ.specialFibreMap).X.hom ∧
      ConnectedSpace (kernel φ.specialFibreMap).X.left ∧
        IsUnipotent (kernel φ.specialFibreMap) := by
  have hφ := φ.hom_eq (separableIsoDepthTransition v hH E hv b e r s hrs)
  change Smooth (kernel ((GroupScheme.baseChange
      (residueBaseMap v.valuationSubring)).map φ.hom)).X.hom ∧
    ConnectedSpace (kernel ((GroupScheme.baseChange
      (residueBaseMap v.valuationSubring)).map φ.hom)).X.left ∧
      IsUnipotent (kernel ((GroupScheme.baseChange
        (residueBaseMap v.valuationSubring)).map φ.hom))
  rw [hφ]
  exact separableDepthVector_kernel_properties v hH E hv b r s hrs
    (separableDepthVectorTransition v hH E hv b r s hrs)

end Langlands.GroupScheme.IntegralModel
