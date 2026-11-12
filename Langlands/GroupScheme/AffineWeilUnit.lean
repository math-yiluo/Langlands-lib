import Langlands.GroupScheme.AffineWeilRestrictionMaps
import Langlands.GroupScheme.AffinePointBaseChangeSmooth
import Langlands.GroupScheme.AffineLinearEmbeddingCorepresentedProof
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # The actual unit into Weil restriction after scalar extension -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry CategoryTheory.Limits
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Langlands.AlgebraicGeometry.PointTopology

section Naturality

variable (R S A A' : Type u) [CommRing R] [CommRing S]
  [CommRing A] [CommRing A'] [Algebra R S] [Algebra R A] [Algebra R A']
  [Algebra S A] [Algebra S A'] [IsScalarTower R S A] [IsScalarTower R S A']
  (G : GroupScheme (Spec (CommRingCat.of R)))

/-- The actual multiplicative base-change comparison respects coefficient maps. -/
theorem affinePointsBaseChangeMulEquiv_naturality (a : A →ₐ[S] A')
    (p : G.affinePoints (CommAlgCat.of R A)) :
    ((GroupScheme.baseChange (Spec.algebraMap R S)).obj G).affinePointMap
        (CommAlgCat.ofHom a) (affinePointsBaseChangeMulEquiv R S A G p) =
      affinePointsBaseChangeMulEquiv R S A' G
        (G.affinePointMap (CommAlgCat.ofHom (a.restrictScalars R)) p) := by
  apply (affinePointsBaseChangeMulEquiv R S A' G).symm.injective
  rw [MulEquiv.symm_apply_apply]
  apply Over.OverMorphism.ext
  rw [affinePointsBaseChangeMulEquiv_symm_left]
  change (Spec.map (CommRingCat.ofHom a.toRingHom) ≫
    (affinePointsBaseChangeMulEquiv R S A G p).left) ≫
      pullback.fst G.X.hom (Spec.algebraMap R S) =
    Spec.map (CommRingCat.ofHom a.toRingHom) ≫ p.left
  rw [Category.assoc, affinePointsBaseChangeMulEquiv_eq_ringPoint,
    ringPointBaseChangeEquiv_left_fst]

end Naturality

section TensorUniversal

variable (R S B : Type u) [CommRing R] [CommRing S] [CommRing B]
  [Algebra R S] [Algebra R B]

/-- The universal tensor-valued point of a base-changed spectrum is its canonical
tensor-coordinate isomorphism. -/
theorem ringPointBaseChangeEquiv_tensorUniversal :
    ringPointBaseChangeEquiv R S (S ⊗[R] B) (ringTest R B)
        (ringTestMap R (Algebra.TensorProduct.includeRight : B →ₐ[R] S ⊗[R] B)) =
      (ringBaseChangeSpectrumIso R S B).inv := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · rw [ringPointBaseChangeEquiv_left_fst]
    change Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : B →ₐ[R] S ⊗[R] B).toRingHom) =
      ((pullbackSpecIso R S B).inv ≫
        (pullbackSymmetry (Spec.algebraMap R B) (Spec.algebraMap R S)).inv) ≫
          pullback.fst _ _
    rw [Category.assoc, pullbackSymmetry_inv_comp_fst, pullbackSpecIso_inv_snd]
    rfl
  · rw [ringPointBaseChangeEquiv_left_snd]
    exact (Over.w (ringBaseChangeSpectrumIso R S B).inv).symm

end TensorUniversal

section IsoCoordinates

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  (X : Over (Spec (CommRingCat.of R))) [IsAffine X.left]
  (p : RingPoint R X A) [IsIso p]

/-- Coordinates of an actual affine-scheme isomorphism are a surjective algebra map. -/
theorem affineSchemePointEquiv_surjective_of_isIso :
    Function.Surjective (affineSchemePointEquiv R X A p).toAlgHom := by
  let f := (affineSchemePointEquiv R X A p).toAlgHom
  have hp : IsIso p.left :=
    inferInstanceAs (IsIso ((Over.forget _).map p))
  have hspec : IsIso (Spec.map (CommRingCat.ofHom f.toRingHom)) := by
    rw [affineSchemePointEquiv_spec]
    infer_instance
  let : IsIso (Scheme.Spec.map (CommRingCat.ofHom f.toRingHom).op) := hspec
  let : IsIso (CommRingCat.ofHom f.toRingHom).op :=
    isIso_of_reflects_iso _ Scheme.Spec
  let : IsIso (CommRingCat.ofHom f.toRingHom) := isIso_of_op _
  exact (ConcreteCategory.bijective_of_isIso (CommRingCat.ofHom f.toRingHom)).2

end IsoCoordinates

namespace AffineWeil

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  [Module.Finite R S] [Module.Projective R S]
  (G : GroupScheme (Spec (CommRingCat.of R)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

/-- The exact existing group-scheme base change. -/
abbrev unitBaseChange : GroupScheme (Spec (CommRingCat.of S)) :=
  (GroupScheme.baseChange (Spec.algebraMap R S)).obj G

instance unitBaseChange_isAffine : IsAffine (unitBaseChange R S G).X.left := by
  change IsAffine (pullback G.X.hom (Spec.algebraMap R S))
  infer_instance

instance unitBaseChange_locallyOfFiniteType :
    LocallyOfFiniteType (unitBaseChange R S G).X.hom := by
  change LocallyOfFiniteType (pullback.snd G.X.hom (Spec.algebraMap R S))
  infer_instance

/-- The unit formula on each actual affine test algebra. -/
def unitPointHom (A : CommAlgCat.{u} (CommRingCat.of R)) :
    G.affinePoints A →* (pointFunctor R S (unitBaseChange R S G)).obj A :=
  (affinePointsBaseChangeMulEquiv R S (S ⊗[R] A) G).toMonoidHom.comp
    (G.affinePointMap (CommAlgCat.ofHom
      (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A)))

omit [Module.Finite R S] [Module.Projective R S]
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
theorem unitPointHom_naturality
    {A A' : CommAlgCat.{u} (CommRingCat.of R)} (a : A ⟶ A')
    (p : G.affinePoints A) :
    (pointFunctor R S (unitBaseChange R S G)).map a (unitPointHom R S G A p) =
      unitPointHom R S G A' (G.affinePointMap a p) := by
  change (unitBaseChange R S G).affinePointMap
    (CommAlgCat.ofHom (Algebra.TensorProduct.lTensor (S := S) S a.hom))
      (affinePointsBaseChangeMulEquiv R S (S ⊗[R] A) G
        (G.affinePointMap (CommAlgCat.ofHom Algebra.TensorProduct.includeRight) p)) = _
  rw [affinePointsBaseChangeMulEquiv_naturality]
  change affinePointsBaseChangeMulEquiv R S (S ⊗[R] A') G
      (G.affinePointMap
        (CommAlgCat.ofHom
          ((Algebra.TensorProduct.lTensor (S := S) S a.hom).restrictScalars R))
        (G.affinePointMap (CommAlgCat.ofHom Algebra.TensorProduct.includeRight) p)) =
    affinePointsBaseChangeMulEquiv R S (S ⊗[R] A') G
      (G.affinePointMap (CommAlgCat.ofHom Algebra.TensorProduct.includeRight)
        (G.affinePointMap a p))
  apply congrArg (affinePointsBaseChangeMulEquiv R S (S ⊗[R] A') G)
  apply Over.OverMorphism.ext
  change
    Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.lTensor (S := S) S a.hom).toRingHom) ≫
        (Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).toRingHom) ≫ p.left) =
    Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : A' →ₐ[R] S ⊗[R] A').toRingHom) ≫
        (Spec.map (CommRingCat.ofHom a.hom.toRingHom) ≫ p.left)
  rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 2

/-- Scalar extension on actual points as a natural group-valued transformation. -/
def unitTransformation :
    G.affinePointFunctor ⟶ pointFunctor R S (unitBaseChange R S G) where
  app A := GrpCat.ofHom (unitPointHom R S G A)
  naturality A A' a := by
    ext p
    exact (unitPointHom_naturality R S G a p).symm

private abbrev unitSourceIso :
    (algSpec (CommRingCat.of R)).obj
        (op (CommAlgCat.of R (AffineCoordinateRing R G.X))) ≅ G.X :=
  (affineSchemeOverIso R G.X).symm

/-- The canonical unit is an actual homomorphism to restriction of the existing base change. -/
def unit : G ⟶ groupScheme R S (unitBaseChange R S G) :=
  AffineCorepresentation.toModel G (unitSourceIso R G) ≫
    Corepresented.groupSchemeMap
      (AffineCorepresentation.corep G (unitSourceIso R G))
      (corepresentableBy R S (unitBaseChange R S G))
      (unitTransformation R S G)

/-- The actual unit has exactly coefficient extension `a ↦ 1 ⊗ a` on all affine tests. -/
theorem unit_affinePoints (A : CommAlgCat.{u} (CommRingCat.of R)) (p : G.affinePoints A) :
    pointsEquiv R S (unitBaseChange R S G) A
        (G.affinePointsTarget (unit R S G) A p) =
      unitPointHom R S G A p := by
  change Corepresented.affinePointsEquiv _ _
      A (p ≫ (AffineCorepresentation.toModel G (unitSourceIso R G)).hom.hom ≫
        (Corepresented.groupSchemeMap
          (AffineCorepresentation.corep G (unitSourceIso R G))
          (corepresentableBy R S (unitBaseChange R S G))
          (unitTransformation R S G)).hom.hom) = _
  rw [← Category.assoc, Corepresented.groupSchemeMap_affinePoints]
  change unitPointHom R S G A
    (Corepresented.affinePointsEquiv _ (AffineCorepresentation.corep G (unitSourceIso R G))
      A (p ≫ (unitSourceIso R G).inv)) = _
  rw [AffineCorepresentation.affinePointsEquiv_eq]
  simp only [AffineCorepresentation.iso_hom, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

omit [Module.Finite R S] [Module.Projective R S] [LocallyOfFiniteType G.X.hom] in
/-- Extending an affine presentation point is the base change of that presentation. -/
theorem unitPointHom_universal :
    unitPointHom R S G (CommAlgCat.of R (AffineCoordinateRing R G.X))
        (unitSourceIso R G).hom =
      (ringBaseChangeSpectrumIso R S (AffineCoordinateRing R G.X)).inv ≫
        (Over.pullback (Spec.algebraMap R S)).map (unitSourceIso R G).hom := by
  change affinePointsBaseChangeMulEquiv R S (S ⊗[R] AffineCoordinateRing R G.X) G
    (ringTestMap R Algebra.TensorProduct.includeRight ≫ (unitSourceIso R G).hom) = _
  rw [affinePointsBaseChangeMulEquiv_eq_ringPoint, ringPointBaseChangeEquiv_natural,
    ringPointBaseChangeEquiv_tensorUniversal]

/-- The classifying algebra map of the actual unit in canonical global-section coordinates. -/
def unitCoordinateMap :
    Langlands.Algebra.WeilRestrictionFiniteType R S
        (AffineCoordinateRing S (unitBaseChange R S G).X) →ₐ[R]
      AffineCoordinateRing R G.X :=
  ((corepresentableBy R S (unitBaseChange R S G)).homEquiv.symm
    ((unitTransformation R S G).app (CommAlgCat.of R (AffineCoordinateRing R G.X))
      ((AffineCorepresentation.corep G (unitSourceIso R G)).homEquiv (𝟙 _)))).hom

/-- The coordinate map classifies precisely the scalar extension of the original
affine presentation point. -/
theorem unitCoordinateMap_classifies :
    (corepresentableBy R S (unitBaseChange R S G)).homEquiv
        (CommAlgCat.ofHom (unitCoordinateMap R S G)) =
      unitPointHom R S G (CommAlgCat.of R (AffineCoordinateRing R G.X))
        (unitSourceIso R G).hom := by
  change (corepresentableBy R S (unitBaseChange R S G)).homEquiv
    ((corepresentableBy R S (unitBaseChange R S G)).homEquiv.symm _) = _
  rw [Equiv.apply_symm_apply]
  change unitPointHom R S G (CommAlgCat.of R (AffineCoordinateRing R G.X))
    ((algSpec (CommRingCat.of R)).map (𝟙 _).op ≫ (unitSourceIso R G).hom) = _
  rw [op_id]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]

/-- The represented upper-field point is an isomorphism, hence its coordinates are surjective. -/
theorem unitCoordinateMap_homEquiv_surjective :
    Function.Surjective
      (Langlands.Algebra.WeilRestrictionFiniteType.homEquiv R S
        (AffineCoordinateRing S (unitBaseChange R S G).X) (AffineCoordinateRing R G.X)
        (unitCoordinateMap R S G)) := by
  have hc := classifyingEquiv_coordinates R S (unitBaseChange R S G)
    (CommAlgCat.of R (AffineCoordinateRing R G.X))
    (CommAlgCat.ofHom (unitCoordinateMap R S G))
  change (affineSchemePointEquiv S (unitBaseChange R S G).X
    (S ⊗[R] AffineCoordinateRing R G.X)
    ((corepresentableBy R S (unitBaseChange R S G)).homEquiv
      (CommAlgCat.ofHom (unitCoordinateMap R S G)))).toAlgHom = _ at hc
  rw [unitCoordinateMap_classifies] at hc
  change _ = Langlands.Algebra.WeilRestrictionFiniteType.homEquiv R S
    (AffineCoordinateRing S (unitBaseChange R S G).X) (AffineCoordinateRing R G.X)
    (unitCoordinateMap R S G) at hc
  rw [← hc]
  have hi : IsIso (unitPointHom R S G (CommAlgCat.of R (AffineCoordinateRing R G.X))
      (unitSourceIso R G).hom) := by
    rw [unitPointHom_universal]
    infer_instance
  exact affineSchemePointEquiv_surjective_of_isIso S _ _ _

/-- Faithful flatness descends surjectivity of the actual unit's classifying algebra map. -/
theorem unitCoordinateMap_surjective [Module.FaithfullyFlat R S] :
    Function.Surjective (unitCoordinateMap R S G) := by
  apply (Module.FaithfullyFlat.lTensor_surjective_iff_surjective R S
    (unitCoordinateMap R S G).toLinearMap).mp
  intro y
  obtain ⟨x, hx⟩ := unitCoordinateMap_homEquiv_surjective R S G y
  refine ⟨Langlands.Algebra.WeilRestrictionFiniteType.universalPoint R S
    (AffineCoordinateRing S (unitBaseChange R S G).X) x, ?_⟩
  exact hx

/-- The actual unit is the spectrum of its canonical classifying algebra map,
preceded by the original group's canonical affine presentation. -/
theorem unit_hom_left :
    (unit R S G).hom.hom.left =
      (unitSourceIso R G).inv.left ≫
        Spec.map (CommRingCat.ofHom (unitCoordinateMap R S G).toRingHom) := rfl

/-- The canonical actual unit is a closed immersion whenever the finite projective
coefficient extension is faithfully flat. In particular this holds for finite field extensions. -/
theorem isClosedImmersion_unit [Module.FaithfullyFlat R S] :
    IsClosedImmersion (unit R S G).hom.hom.left := by
  rw [unit_hom_left]
  have hi : IsIso (unitSourceIso R G).inv.left :=
    inferInstanceAs (IsIso ((Over.forget _).map (unitSourceIso R G).inv))
  have hc : IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (unitCoordinateMap R S G).toRingHom)) :=
    IsClosedImmersion.spec_of_surjective _ (unitCoordinateMap_surjective R S G)
  infer_instance

end AffineWeil

namespace AffineWeil

variable (F L : Type u) [Field F] [Field L] [Algebra F L] [FiniteDimensional F L]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

/-- Every finite field extension satisfies the closed-immersion conclusion, including
inseparable extensions. Faithful flatness is provided by the field-module instances. -/
theorem isClosedImmersion_unit_of_field :
    IsClosedImmersion (unit F L G).hom.hom.left :=
  isClosedImmersion_unit F L G

end AffineWeil

end Langlands.GroupScheme
