import Langlands.Global.PositiveRealTorusTopology
import Langlands.GroupScheme.Torus.SplitPointTopology

/-! # Closed embeddings of positive-real parameters into actual adelic split tori -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite Topology
open scoped CategoryTheory.MonObj NNReal Topology

namespace Langlands.Global.PositiveRealTorus

open Langlands.GroupScheme

variable (F : Type u) [Field F]
variable (I : Type u) [Fintype I]
variable (T : CommGroupScheme (Spec (CommRingCat.of F)))
variable (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)

local instance (G : GroupScheme (Spec (CommRingCat.of F)))
    (A : Type u) [CommRing A] [Algebra F A] [TopologicalSpace A] :
    TopologicalSpace (Lie.AffinePoints G A) :=
  GroupScheme.affinePointsTopologicalSpace G (CommAlgCat.of F A)

variable (A : Type u) [CommRing A] [Algebra F A] [TopologicalSpace A]

/-- Coordinates of the supplied actual splitting are continuous. -/
theorem continuous_coordinates : Continuous (coordinates F I T e A) := by
  change Continuous (fun x : Lie.AffinePoints T.toGrp A =>
    splitTorus.affineUnitsEquiv I (CommRingCat.of F) (CommAlgCat.of F A)
      (x ≫ e.hom.hom.hom))
  exact (splitTorus.continuous_affinePointsEquiv I (CommRingCat.of F)
    (CommAlgCat.of F A)).comp
      (GroupScheme.continuous_affinePointPostcomp T.toGrp (CommAlgCat.of F A)
        e.hom.hom.hom)

omit [TopologicalSpace A] in
/-- The inverse uses the genuine inverse splitting on actual points. -/
theorem coordinates_symm_apply (x : I → Aˣ) :
    (coordinates F I T e A).symm x =
      (splitTorus.affineUnitsEquiv I (CommRingCat.of F) (CommAlgCat.of F A)).symm x ≫
        e.inv.hom.hom := by
  apply (coordinates F I T e A).injective
  rw [MulEquiv.apply_symm_apply]
  change x = splitTorus.affineUnitsEquiv I (CommRingCat.of F) (CommAlgCat.of F A)
    (((splitTorus.affineUnitsEquiv I (CommRingCat.of F) (CommAlgCat.of F A)).symm x ≫
      e.inv.hom.hom) ≫ e.hom.hom.hom)
  simp only [Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id,
    Grp.id_hom_hom, Category.comp_id, MulEquiv.apply_symm_apply]

variable [IsTopologicalRing A]

/-- Inverse coordinates are continuous for the existing regular-evaluation topology. -/
theorem continuous_coordinates_symm : Continuous (coordinates F I T e A).symm := by
  change Continuous (fun x : I → Aˣ => (coordinates F I T e A).symm x)
  simp_rw [coordinates_symm_apply]
  exact (GroupScheme.continuous_affinePointPostcomp (splitTorus (Spec (CommRingCat.of F)) I)
    (CommAlgCat.of F A) e.inv.hom.hom).comp
      (splitTorus.continuous_affinePointsEquiv_symm I (CommRingCat.of F) (CommAlgCat.of F A))

/-- The supplied splitting identifies the existing topologies on actual coefficient points. -/
def coordinatesHomeomorph : Lie.AffinePoints T.toGrp A ≃ₜ* (I → Aˣ) where
  toMulEquiv := coordinates F I T e A
  continuous_toFun := continuous_coordinates F I T e A
  continuous_invFun := continuous_coordinates_symm F I T e A

@[simp] theorem coordinatesHomeomorph_apply (x : Lie.AffinePoints T.toGrp A) :
    coordinatesHomeomorph F I T e A x = coordinates F I T e A x := rfl

variable [NumberField F]

/-- The actual positive-real torus map is a closed topological embedding. -/
theorem isClosedEmbedding_full : IsClosedEmbedding (full F I T e) := by
  change IsClosedEmbedding (fun x : I → ℝ≥0ˣ =>
    (coordinatesHomeomorph F I T e (Adeles F)).symm
      (fun i => PositiveRealIdeles.full F (x i)))
  exact (coordinatesHomeomorph F I T e (Adeles F)).symm.toHomeomorph.isClosedEmbedding.comp
    (PositiveRealIdeles.isClosedEmbedding_full_pi F I)

/-- The original positive-real homomorphism, now bundled with its proved continuity. -/
def continuousFull : (I → ℝ≥0ˣ) →ₜ* Lie.AffinePoints T.toGrp (Adeles F) where
  toMonoidHom := full F I T e
  continuous_toFun := (isClosedEmbedding_full F I T e).continuous

@[simp] theorem continuousFull_apply (x : I → ℝ≥0ˣ) :
    continuousFull F I T e x = full F I T e x := rfl

end Langlands.Global.PositiveRealTorus
