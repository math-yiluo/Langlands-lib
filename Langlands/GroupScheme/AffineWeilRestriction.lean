import Langlands.AlgebraicGeometry.PointTopology.AffineWeilRestriction
import Langlands.GroupScheme.AffinePoints
import Langlands.GroupScheme.CorepresentedPoints

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj CategoryTheory.Obj TensorProduct

namespace Langlands.GroupScheme.AffineWeil

open Langlands.Algebra Langlands.AlgebraicGeometry.PointTopology

section CoordinateNaturality

variable (R : Type u) [CommRing R]
  (X : Over (Spec (CommRingCat.of R))) [IsAffine X.left]
  {T T' : Type u} [CommRing T] [CommRing T'] [Algebra R T] [Algebra R T']

/-- Global-section coordinates respect change of the actual test algebra. -/
theorem coordinatePoint_changeRing (a : T →ₐ[R] T') (p : RingPoint R X T) :
    (affineSchemePointEquiv R X T' (ringTestMap R a ≫ p)).toAlgHom =
      a.comp (affineSchemePointEquiv R X T p).toAlgHom := by
  dsimp only [RingPoint, ringTest] at p
  apply AlgHom.coe_ringHom_injective
  change (Spec.preimage
    ((Spec.map (CommRingCat.ofHom a.toRingHom) ≫ p.left) ≫ X.left.isoSpec.hom)).hom =
      a.toRingHom.comp (Spec.preimage (p.left ≫ X.left.isoSpec.hom)).hom
  rw [Category.assoc, Spec.preimage_comp, Spec.preimage_map]
  rfl

/-- The direct spectrum coordinate map is the inverse of the affine spectrum functor. -/
theorem spectrumPoint_preimage (D T : CommAlgCat.{u} (CommRingCat.of R))
    (p : (algSpec (CommRingCat.of R)).obj (op T) ⟶
      (algSpec (CommRingCat.of R)).obj (op D)) :
    (algSpec.fullyFaithful.preimage p).unop.hom = affineRingPointEquiv R D T p := by
  apply AlgHom.coe_ringHom_injective
  have h := congrArg (fun q => q.left) (algSpec.fullyFaithful.map_preimage p)
  change Spec.map (CommRingCat.ofHom
      (algSpec.fullyFaithful.preimage p).unop.hom.toRingHom) = p.left at h
  have h' := Spec.preimage_map (CommRingCat.ofHom
    (algSpec.fullyFaithful.preimage p).unop.hom.toRingHom)
  rw [h] at h'
  exact (congrArg (fun f => f.hom) h').symm

end CoordinateNaturality

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

/-- Actual tensor extension on commutative algebras. -/
def tensorFunctor : CommAlgCat.{u} (CommRingCat.of A) ⥤
    CommAlgCat.{u} (CommRingCat.of B) where
  obj T := CommAlgCat.of (CommRingCat.of B) (B ⊗[A] T)
  map a := CommAlgCat.ofHom (Algebra.TensorProduct.lTensor (S := B) B a.hom)
  map_id T := by
    apply CommAlgCat.hom_ext
    ext; simp
  map_comp a b := by
    apply CommAlgCat.hom_ext
    exact Algebra.TensorProduct.map_id_comp _ _

variable (G : GroupScheme (Spec (CommRingCat.of B)))

/-- Restriction of the original actual group-valued affine-point functor. -/
abbrev pointFunctor : CommAlgCat.{u} (CommRingCat.of A) ⥤ GrpCat.{u} :=
  tensorFunctor A B ⋙ G.affinePointFunctor

variable [Module.Finite A B] [Module.Projective A B]
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

/-- The same representing algebra as the published affine scheme restriction. -/
abbrev coordinateAlgebra : CommAlgCat.{u} (CommRingCat.of A) :=
  CommAlgCat.of (CommRingCat.of A)
    (WeilRestrictionFiniteType A B (AffineCoordinateRing B G.X))

/-- The canonical representing bijection, with values in the original actual point groups. -/
def classifyingEquiv (T : CommAlgCat.{u} (CommRingCat.of A)) :
    (coordinateAlgebra A B G ⟶ T) ≃ (pointFunctor A B G).obj T :=
  ConcreteCategory.homEquiv.trans <|
    (WeilRestrictionFiniteType.homEquiv A B (AffineCoordinateRing B G.X) T).trans <|
      AlgPoint.algHomEquiv.symm.trans (affineSchemePointEquiv B G.X (B ⊗[A] T)).symm

/-- The classification is exactly `homEquiv` in global-section coordinates. -/
theorem classifyingEquiv_coordinates (T : CommAlgCat.{u} (CommRingCat.of A))
    (f : coordinateAlgebra A B G ⟶ T) :
    (affineSchemePointEquiv B G.X (B ⊗[A] T)
      (classifyingEquiv A B G T f)).toAlgHom =
        WeilRestrictionFiniteType.homEquiv A B (AffineCoordinateRing B G.X) T f.hom := by
  exact congrArg AlgPoint.toAlgHom
    ((affineSchemePointEquiv B G.X (B ⊗[A] T)).apply_symm_apply _)

/-- The finite-type algebra corepresents the original tensor-valued group functor. -/
def corepresentableBy :
    (pointFunctor A B G ⋙ forget GrpCat).CorepresentableBy (coordinateAlgebra A B G) where
  homEquiv := fun {T} => classifyingEquiv A B G T
  homEquiv_comp := by
    intro T T' a f
    apply (affineSchemePointEquiv B G.X (B ⊗[A] T')).injective
    apply AlgPoint.ext
    intro c
    have h := coordinatePoint_changeRing B G.X
      (Algebra.TensorProduct.lTensor (S := B) B a.hom) (classifyingEquiv A B G _ f)
    change (affineSchemePointEquiv B G.X (B ⊗[A] T')
      (classifyingEquiv A B G T' (f ≫ a))).toAlgHom c =
      (affineSchemePointEquiv B G.X (B ⊗[A] T')
        (ringTestMap B (Algebra.TensorProduct.lTensor (S := B) B a.hom) ≫
          classifyingEquiv A B G _ f)).toAlgHom c
    rw [h]
    rw [classifyingEquiv_coordinates, classifyingEquiv_coordinates]
    exact congrArg (fun q => q c)
      (WeilRestrictionFiniteType.homEquiv_comp f.hom a.hom)

/-- Actual affine group-scheme Weil restriction, carrying the original group laws. -/
abbrev groupScheme : GroupScheme (Spec (CommRingCat.of A)) :=
  Corepresented.groupScheme (pointFunctor A B G) (corepresentableBy A B G)

/-- Its underlying relative scheme is exactly the existing affine Weil restriction. -/
theorem groupScheme_X : (groupScheme A B G).X = affineWeilRestriction A B G.X := rfl

instance : IsAffine (groupScheme A B G).X.left :=
  affineWeilRestriction_isAffine A B G.X

instance : LocallyOfFiniteType (groupScheme A B G).X.hom :=
  affineWeilRestriction_locallyOfFiniteType A B G.X

/-- Multiplicative recovery of the original group's actual tensor-valued points. -/
def pointsEquiv (T : Type u) [CommRing T] [Algebra A T] :
    (groupScheme A B G).affinePoints (CommAlgCat.of (CommRingCat.of A) T) ≃*
      G.affinePoints (CommAlgCat.of (CommRingCat.of B) (B ⊗[A] T)) :=
  Corepresented.affinePointsEquiv (pointFunctor A B G) (corepresentableBy A B G)
    (CommAlgCat.of (CommRingCat.of A) T)

/-- Multiplicative recovery has precisely the previously published underlying bijection. -/
theorem pointsEquiv_eq (T : Type u) [CommRing T] [Algebra A T] :
    (pointsEquiv A B G T).toEquiv = affineWeilRestrictionPointEquiv A B G.X T := by
  apply Equiv.ext
  intro p
  change classifyingEquiv A B G _ (algSpec.fullyFaithful.preimage p).unop = _
  change (affineSchemePointEquiv B G.X (B ⊗[A] T)).symm
      (AlgPoint.ofAlgHom (WeilRestrictionFiniteType.homEquiv A B
        (AffineCoordinateRing B G.X) T (algSpec.fullyFaithful.preimage p).unop.hom)) =
    (affineSchemePointEquiv B G.X (B ⊗[A] T)).symm
      (AlgPoint.ofAlgHom (WeilRestrictionFiniteType.homEquiv A B
        (AffineCoordinateRing B G.X) T (affineRingPointEquiv A
          (WeilRestrictionFiniteType A B (AffineCoordinateRing B G.X)) T p)))
  congr 3
  exact spectrumPoint_preimage A (coordinateAlgebra A B G)
    (CommAlgCat.of (CommRingCat.of A) T) p

/-- The multiplicative comparison retains the canonical tensor-valued classification map. -/
theorem pointsEquiv_coordinates (T : Type u) [CommRing T] [Algebra A T]
    (p : (groupScheme A B G).affinePoints (CommAlgCat.of (CommRingCat.of A) T)) :
    (affineSchemePointEquiv B G.X (B ⊗[A] T) (pointsEquiv A B G T p)).toAlgHom =
      WeilRestrictionFiniteType.homEquiv A B (AffineCoordinateRing B G.X) T
        (affineRingPointEquiv A
          (WeilRestrictionFiniteType A B (AffineCoordinateRing B G.X)) T p) := by
  change (affineSchemePointEquiv B G.X (B ⊗[A] T)
    (classifyingEquiv A B G _ (algSpec.fullyFaithful.preimage p).unop)).toAlgHom = _
  exact (classifyingEquiv_coordinates A B G
    (CommAlgCat.of (CommRingCat.of A) T) (algSpec.fullyFaithful.preimage p).unop).trans
      (congrArg (WeilRestrictionFiniteType.homEquiv A B (AffineCoordinateRing B G.X) T)
        (spectrumPoint_preimage A (coordinateAlgebra A B G)
          (CommAlgCat.of (CommRingCat.of A) T) p))

/-- Coefficient maps act by the actual tensor-product spectrum pullback. -/
theorem pointsEquiv_naturality {T T' : Type u} [CommRing T] [CommRing T']
    [Algebra A T] [Algebra A T'] (a : T →ₐ[A] T')
    (p : (groupScheme A B G).affinePoints (CommAlgCat.of (CommRingCat.of A) T)) :
    pointsEquiv A B G T' ((groupScheme A B G).affinePointMap (CommAlgCat.ofHom a) p) =
      G.affinePointMap (CommAlgCat.ofHom (Algebra.TensorProduct.lTensor (S := B) B a))
        (pointsEquiv A B G T p) :=
  Corepresented.affinePointsEquiv_naturality (pointFunctor A B G)
    (corepresentableBy A B G) (CommAlgCat.ofHom a) p

end Langlands.GroupScheme.AffineWeil
