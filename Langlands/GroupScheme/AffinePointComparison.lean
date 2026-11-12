import Langlands.GroupScheme.AffineLinearEmbeddingCorepresentedProof
import Langlands.AlgebraicGeometry.PointTopology.AffineScheme

/-! # Reconstruction from actual affine group-valued points -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AffinePointComparison

open Langlands.AlgebraicGeometry.PointTopology

variable {R : CommRingCat.{u}} (G : GroupScheme (Spec R)) [IsAffine G.X.left]

/-- The canonical affine presentation, with the original relative structure. -/
def presentation :
    (algSpec R).obj (op (CommAlgCat.of R (AffineCoordinateRing R G.X))) ≅ G.X :=
  (affineSchemeOverIso R G.X).symm

/-- Recovery of the actual group, including all its group laws. -/
def modelIso : AffineCorepresentation.model G (presentation G) ≅ G :=
  Grp.mkIso' (AffineCorepresentation.iso G (presentation G))

@[simp] theorem modelIso_hom : (modelIso G).hom.hom.hom = (presentation G).hom := rfl
@[simp] theorem modelIso_inv : (modelIso G).inv.hom.hom = (presentation G).inv := rfl

/-- Affine tests detect morphisms with affine source. -/
theorem hom_ext {H : GroupScheme (Spec R)} (f g : G ⟶ H)
    (h : ∀ (A : CommAlgCat.{u} R) (p : G.affinePoints A),
      p ≫ f.hom.hom = p ≫ g.hom.hom) : f = g := by
  apply Grp.hom_ext
  apply (cancel_epi (presentation G).hom).mp
  exact h _ (presentation G).hom

variable {G} {H : GroupScheme (Spec R)} [IsAffine H.X.left]

/-- An affine-point natural transformation gives an actual group-scheme map. -/
def map (α : G.affinePointFunctor ⟶ H.affinePointFunctor) : G ⟶ H :=
  (modelIso G).inv ≫
    Corepresented.groupSchemeMap
      (AffineCorepresentation.corep G (presentation G))
      (AffineCorepresentation.corep H (presentation H)) α ≫
    (modelIso H).hom

/-- The reconstructed map induces exactly the specified transformation. -/
theorem map_points (α : G.affinePointFunctor ⟶ H.affinePointFunctor)
    (A : CommAlgCat.{u} R) (p : G.affinePoints A) :
    p ≫ (map α).hom.hom = α.app A p := by
  have h := Corepresented.groupSchemeMap_affinePoints
    (AffineCorepresentation.corep G (presentation G))
    (AffineCorepresentation.corep H (presentation H)) α
    (p ≫ (presentation G).inv)
  rw [AffineCorepresentation.affinePointsEquiv_eq,
    AffineCorepresentation.affinePointsEquiv_eq] at h
  change ((p ≫ (presentation G).inv) ≫
      (Corepresented.groupSchemeMap
        (AffineCorepresentation.corep G (presentation G))
        (AffineCorepresentation.corep H (presentation H)) α).hom.hom) ≫
      (presentation H).hom =
    α.app A ((p ≫ (presentation G).inv) ≫ (presentation G).hom) at h
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at h
  exact h

/-- A natural isomorphism of actual affine points reconstructs an actual group isomorphism. -/
def iso (e : G.affinePointFunctor ≅ H.affinePointFunctor) : G ≅ H where
  hom := map e.hom
  inv := map e.inv
  hom_inv_id := by
    apply hom_ext G
    intro A p
    change (p ≫ (map e.hom).hom.hom) ≫ (map e.inv).hom.hom = p ≫ 𝟙 G.X
    rw [map_points, map_points, Category.comp_id]
    exact ConcreteCategory.congr_hom (e.hom_inv_id_app A) p
  inv_hom_id := by
    apply hom_ext H
    intro A p
    change (p ≫ (map e.inv).hom.hom) ≫ (map e.hom).hom.hom = p ≫ 𝟙 H.X
    rw [map_points, map_points, Category.comp_id]
    exact ConcreteCategory.congr_hom (e.inv_hom_id_app A) p

/-- Reconstruction preserves the original affine-point formula. -/
theorem iso_hom_points (e : G.affinePointFunctor ≅ H.affinePointFunctor)
    (A : CommAlgCat.{u} R) (p : G.affinePoints A) :
    p ≫ (iso e).hom.hom.hom = e.hom.app A p :=
  map_points e.hom A p

end Langlands.GroupScheme.AffinePointComparison
