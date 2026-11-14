import Langlands.GroupScheme.VectorScalarKernel
import Langlands.GroupScheme.CorepresentedSmooth
import Langlands.GroupScheme.IntegralModel.GenericRigidity
import Mathlib.AlgebraicGeometry.AffineSpace

/-! # Scaled integral vector-group models and their actual transition kernels -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace VectorGroup

variable (R : CommRingCat.{u}) (n : ℕ)

/-- The standard vector group is smooth over every coefficient ring. -/
theorem smooth : Smooth (groupScheme R n).X.hom :=
  Corepresented.smooth_groupScheme_iff.mpr inferInstance

/-- Every fibre of the polynomial vector group is geometrically connected. -/
theorem geometricallyConnected : GeometricallyConnected (groupScheme R n).X.hom := by
  change GeometricallyConnected
    (Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial (Fin n) R))))
  let e : Spec (CommRingCat.of (MvPolynomial (Fin n) R)) ≅
      AffineSpace (ULift.{u} (Fin n)) (Spec R) :=
    Scheme.Spec.mapIso
      (MvPolynomial.renameEquiv R Equiv.ulift).toRingEquiv.toCommRingCatIso.op ≪≫
        (AffineSpace.SpecIso (ULift.{u} (Fin n)) R).symm
  have he : e.hom ≫ (AffineSpace (ULift.{u} (Fin n)) (Spec R) ↘ Spec R) =
      Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial (Fin n) R))) := by
    dsimp only [e, Iso.trans_hom, Iso.symm_hom]
    rw [Category.assoc, AffineSpace.SpecIso_inv_over]
    simp only [Functor.mapIso_hom, Iso.op_hom, Scheme.Spec_map, Quiver.Hom.unop_op]
    rw [← Spec.map_comp]
    congr 1
    ext x
    simp
  rw [← he]
  apply MorphismProperty.RespectsIso.precomp (P := @GeometricallyConnected)
  constructor
  intro L _ a T fst snd hp
  let : IrreducibleSpace T :=
    GeometricallyIrreducible.geometrically_irreducibleSpace a fst snd hp
  infer_instance

/-- Coordinates of sections over the coefficient ring itself. -/
def sectionCoordinates :
    rationalPoints (groupScheme R n) ≃* Multiplicative (Fin n → R) :=
  (coordinates R n (Over.mk (𝟙 _))).trans
    (AddEquiv.piCongrRight fun _ =>
      (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.toAddEquiv).toMultiplicative

@[simp]
theorem sectionCoordinates_apply (x : rationalPoints (groupScheme R n)) (j : Fin n) :
    (sectionCoordinates R n x).toAdd j =
      (Scheme.ΓSpecIso R).hom.hom ((coordinates R n (Over.mk (𝟙 _)) x).toAdd j) := rfl

end VectorGroup

namespace IntegralModel

variable (R K : Type u) [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] (n : ℕ)

/-- The polynomial vector model whose generic identification scales by `t`. -/
def scaledVector (t : Kˣ) :
    IntegralModel R K (VectorGroup.groupScheme (CommRingCat.of K) n) where
  group := VectorGroup.groupScheme (CommRingCat.of R) n
  affine := by
    change IsAffineHom
      (Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial (Fin n) R))))
    infer_instance
  flat := by
    have := VectorGroup.smooth (CommRingCat.of R) n
    infer_instance
  finiteType := by
    have := VectorGroup.smooth (CommRingCat.of R) n
    infer_instance
  genericIso := VectorGroup.baseChangeIso
    (CommRingCat.ofHom (algebraMap R K)) ≪≫ VectorGroup.scalarIso t

theorem scaledVector_isSmooth (t : Kˣ) :
    (scaledVector R K n t).IsSmooth :=
  VectorGroup.smooth (CommRingCat.of R) n

theorem scaledVector_hasGeometricallyConnectedFibres (t : Kˣ) :
    (scaledVector R K n t).HasGeometricallyConnectedFibres :=
  VectorGroup.geometricallyConnected (CommRingCat.of R) n

variable {R K n}

/-- A scalar on the integral vector group gives the generic identity exactly
when the scaling factors satisfy the stated coefficient equation. -/
def scaledVectorTransition (s t : Kˣ) (c : R)
    (h : algebraMap R K c * (t : K) = s) :
    (scaledVector R K n s).Hom (scaledVector R K n t) (𝟙 _) where
  hom := VectorGroup.scalar c
  generic_comm := by
    change (GroupScheme.baseChange (Spec.algebraMap R K)).map (VectorGroup.scalar c) ≫
        ((VectorGroup.baseChangeIso _).hom ≫ VectorGroup.scalar (t : K)) =
      ((VectorGroup.baseChangeIso _).hom ≫ VectorGroup.scalar (s : K)) ≫ 𝟙 _
    rw [Category.comp_id, ← Category.assoc, ← VectorGroup.scalar_baseChange,
      Category.assoc, VectorGroup.scalar_comp]
    have hc : (CommRingCat.ofHom (algebraMap R K)).hom c * (t : K) = (s : K) := h
    rw [hc]

variable [IsLocalRing R]

/-- Every extension of the generic identity between these scaled models has
the scalar map's actual special-fibre kernel geometry. -/
theorem scaledVector_kernel_properties (s t : Kˣ) (c : R)
    (h : algebraMap R K c * (t : K) = s)
    (φ : (scaledVector R K n s).Hom (scaledVector R K n t) (𝟙 _)) :
    Smooth (kernel φ.specialFibreMap).X.hom ∧
      ConnectedSpace (kernel φ.specialFibreMap).X.left ∧
        IsUnipotent (kernel φ.specialFibreMap) := by
  have hφ := φ.hom_eq (scaledVectorTransition s t c h)
  change Smooth (kernel ((GroupScheme.baseChange (residueBaseMap R)).map φ.hom)).X.hom ∧
    ConnectedSpace (kernel ((GroupScheme.baseChange (residueBaseMap R)).map φ.hom)).X.left ∧
      IsUnipotent (kernel ((GroupScheme.baseChange (residueBaseMap R)).map φ.hom))
  rw [hφ]
  exact VectorGroup.scalar_baseChange_kernel_properties n
    (CommRingCat.ofHom (IsLocalRing.residue R)) c

end IntegralModel
end Langlands.GroupScheme
