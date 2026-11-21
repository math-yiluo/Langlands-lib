import Langlands.GroupScheme.AffineHopfMorphism
import Langlands.GroupScheme.Cartier.FiniteDualGeometry
import Langlands.GroupScheme.Cartier.FiniteDualMorphism
import Langlands.GroupScheme.Cartier.FiniteDualSpectrum

/-! # Spectrum of the finite Hopf-algebra dual and its morphisms -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Cartier.FiniteDual

variable {R : CommRingCat.{u}}

section Affine

variable {G H J : GroupScheme (Spec R)} [IsAffine G.X.left] [IsAffine H.X.left] [IsAffine J.X.left]

@[simp]
theorem coordinatePullback_id : Langlands.GroupScheme.AffineHopfMorphism.pullback (𝟙 G) = 𝟙 _ := by
  apply Quiver.Hom.op_inj
  apply (hopfSpec R).map_injective
  simp only [Langlands.GroupScheme.AffineHopfMorphism.pullback_map, Category.id_comp, Iso.hom_inv_id, op_id]
  exact ((hopfSpec R).map_id _).symm

@[simp]
theorem coordinatePullback_comp (f : G ⟶ H) (g : H ⟶ J) :
    Langlands.GroupScheme.AffineHopfMorphism.pullback (f ≫ g) = Langlands.GroupScheme.AffineHopfMorphism.pullback g ≫ Langlands.GroupScheme.AffineHopfMorphism.pullback f := by
  apply Quiver.Hom.op_inj
  apply (hopfSpec R).map_injective
  rw [op_comp, Functor.map_comp, Langlands.GroupScheme.AffineHopfMorphism.pullback_map, Langlands.GroupScheme.AffineHopfMorphism.pullback_map, Langlands.GroupScheme.AffineHopfMorphism.pullback_map]
  simp [Category.assoc]

end Affine

section Finite

local instance finiteScheme_isAffine (G : CommGroupScheme (Spec R)) [IsFinite G.X.hom] : IsAffine G.X.left :=
  isAffine_of_isFinite G.toGrp

variable (G : CommGroupScheme (Spec R)) [IsFinite G.X.hom] [Flat G.X.hom]
  [LocallyOfFinitePresentation G.X.hom]

local instance finiteScheme_cocomm : Coalgebra.IsCocomm R (AffineCoordinates.hopfAlgebra G.toGrp) :=
  affineCoordinates_isCocomm G

local instance finiteScheme_finite : Module.Finite R (AffineCoordinates.hopfAlgebra G.toGrp) :=
  hopfAlgebra_finite G.toGrp

local instance finiteScheme_projective : Module.Projective R (AffineCoordinates.hopfAlgebra G.toGrp) :=
  hopfAlgebra_projective G.toGrp

/-- The finite spectrum of the actual dual of the chosen coordinate Hopf algebra. -/
def schemeDual : CommGroupScheme (Spec R) :=
  specGroup R (Dual R (AffineCoordinates.hopfAlgebra G.toGrp))

/-- The dual spectrum is finite locally free. -/
theorem schemeDual_finiteLocallyFree :
    IsFinite (schemeDual G).X.hom ∧ Flat (schemeDual G).X.hom ∧
      LocallyOfFinitePresentation (schemeDual G).X.hom :=
  algSpec_finiteLocallyFree (R := R) (Dual R (AffineCoordinates.hopfAlgebra G.toGrp))

variable {G} {H J : CommGroupScheme (Spec R)} [IsFinite H.X.hom] [Flat H.X.hom]
  [LocallyOfFinitePresentation H.X.hom] [IsFinite J.X.hom] [Flat J.X.hom]
  [LocallyOfFinitePresentation J.X.hom]

/-- The actual map of the dual spectra induced by transposing coordinate pullback. -/
def schemeDualMap (f : G ⟶ H) : schemeDual H ⟶ schemeDual G :=
  Additive.ofMul ((hopfSpec R).map
    (CommHopfAlgCat.ofHom (dualBialgHom (Langlands.GroupScheme.AffineHopfMorphism.pullback f.toMul).hom)).op)

@[simp]
theorem schemeDualMap_id : schemeDualMap (𝟙 G) = 𝟙 _ := by
  change Additive.ofMul ((hopfSpec R).map
    (CommHopfAlgCat.ofHom (dualBialgHom (Langlands.GroupScheme.AffineHopfMorphism.pullback (𝟙 G.toGrp)).hom)).op) =
    Additive.ofMul (𝟙 (schemeDual G).toGrp)
  apply congrArg Additive.ofMul
  rw [coordinatePullback_id]
  change (hopfSpec R).map (CommHopfAlgCat.ofHom
    (dualBialgHom (BialgHom.id R (AffineCoordinates.hopfAlgebra G.toGrp)))).op = _
  rw [dualBialgHom_id, CommHopfAlgCat.ofHom_id, op_id]
  exact (hopfSpec R).map_id _

@[simp]
theorem schemeDualMap_comp (f : G ⟶ H) (g : H ⟶ J) :
    schemeDualMap (f ≫ g) = schemeDualMap g ≫ schemeDualMap f := by
  change Additive.ofMul ((hopfSpec R).map
    (CommHopfAlgCat.ofHom (dualBialgHom (Langlands.GroupScheme.AffineHopfMorphism.pullback (f.toMul ≫ g.toMul)).hom)).op) =
    Additive.ofMul ((schemeDualMap g).toMul ≫ (schemeDualMap f).toMul)
  apply congrArg Additive.ofMul
  rw [coordinatePullback_comp, CommHopfAlgCat.hom_comp, dualBialgHom_comp, CommHopfAlgCat.ofHom_comp,
    op_comp, Functor.map_comp]
  rfl

end Finite
end Langlands.GroupScheme.Cartier.FiniteDual
