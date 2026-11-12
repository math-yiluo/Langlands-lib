import Langlands.GroupScheme.AffineWeilRestrictionMaps
import Langlands.GroupScheme.CorepresentedAffineComparison
import Langlands.GroupScheme.MultiplicativePointTopology
import Langlands.GroupScheme.MultiplicativeGeometry
import Langlands.Algebra.TensorNorm

/-! # Norm characters on the actual affine Weil restriction -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.AffineWeil

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance multiplicative_isAffine (A : CommRingCat.{u}) :
    IsAffine (Gm (Spec A)).X.left := by
  change IsAffine (CategoryTheory.Limits.pullback
    (Spec.map (CommRingCat.ofHom (LaurentPolynomial.C (R := ULift.{u} ℤ))))
    (Gm.toSpecZ (Spec A)))
  infer_instance

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  [Module.Finite R S] [Module.Projective R S]

/-- Full test-scheme points of the actual affine restriction of the multiplicative group
are precisely tensor units over relative global sections. -/
def multiplicativeUnitsEquiv (T : Over (Spec (CommRingCat.of R))) :
    (T ⟶ (groupScheme R S (Gm (Spec (CommRingCat.of S))).toGrp).X) ≃*
      (S ⊗[R] ((algΓ (CommRingCat.of R)).obj T).unop)ˣ :=
  (Corepresented.pointsEquiv
    (pointFunctor R S (Gm (Spec (CommRingCat.of S))).toGrp)
    (corepresentableBy R S (Gm (Spec (CommRingCat.of S))).toGrp) T).trans
      (Gm.affineUnitsEquiv (CommRingCat.of S)
        ((tensorFunctor R S).obj ((algΓ (CommRingCat.of R)).obj T).unop))

theorem multiplicativeUnitsEquiv_naturality
    {T T' : Over (Spec (CommRingCat.of R))} (a : T' ⟶ T)
    (p : T ⟶ (groupScheme R S (Gm (Spec (CommRingCat.of S))).toGrp).X) :
    multiplicativeUnitsEquiv R S T' (a ≫ p) =
      Units.map
        (Algebra.TensorProduct.lTensor (S := S) S
          ((algΓ (CommRingCat.of R)).map a).unop.hom).toMonoidHom
        (multiplicativeUnitsEquiv R S T p) := by
  simp only [multiplicativeUnitsEquiv, MulEquiv.trans_apply,
    Corepresented.pointsEquiv_naturality]
  exact Gm.affineUnitsEquiv_naturality (CommRingCat.of S)
    ((tensorFunctor R S).map ((algΓ (CommRingCat.of R)).map a).unop) _

/-- On affine tests, normalization of relative global sections recovers the fixed
affine representing comparison followed by the original Gm unit map. -/
theorem multiplicativeUnitsEquiv_affine_normalized
    (A : CommAlgCat.{u} (CommRingCat.of R))
    (p : (groupScheme R S (Gm (Spec (CommRingCat.of S))).toGrp).affinePoints A) :
    Units.map
        (Algebra.TensorProduct.lTensor (S := S) S
          (Corepresented.affineSectionsIso A).hom.hom).toMonoidHom
        (multiplicativeUnitsEquiv R S ((algSpec (CommRingCat.of R)).obj (op A)) p) =
      Gm.affineUnitsEquiv (CommRingCat.of S) ((tensorFunctor R S).obj A)
        (pointsEquiv R S (Gm (Spec (CommRingCat.of S))).toGrp A p) := by
  have h := Corepresented.map_affineSectionsIso_pointsEquiv
    (pointFunctor R S (Gm (Spec (CommRingCat.of S))).toGrp)
    (corepresentableBy R S (Gm (Spec (CommRingCat.of S))).toGrp) A p
  have h' := congrArg (Gm.affineUnitsEquiv (CommRingCat.of S)
    ((tensorFunctor R S).obj A)) h
  change Gm.affineUnitsEquiv (CommRingCat.of S) ((tensorFunctor R S).obj A)
    (GroupScheme.affinePointMap (Gm (Spec (CommRingCat.of S))).toGrp
      ((tensorFunctor R S).map (Corepresented.affineSectionsIso A).hom) _) = _ at h'
  rw [Gm.affineUnitsEquiv_naturality] at h'
  exact h'

variable [Module.Free R S]

/-- The determinant norm on every actual test scheme. -/
def multiplicativeNormPoints (T : Over (Spec (CommRingCat.of R))) :
    (T ⟶ (groupScheme R S (Gm (Spec (CommRingCat.of S))).toGrp).X) →*
      (T ⟶ (Gm (Spec (CommRingCat.of R))).X) :=
  (Gm.pointsEquiv (Spec (CommRingCat.of R)) T).symm.toMonoidHom.comp
    ((Langlands.Algebra.tensorNormUnits R S
      ((algΓ (CommRingCat.of R)).obj T).unop).comp
        (multiplicativeUnitsEquiv R S T).toMonoidHom)

omit [Module.Free R S] in
@[simp] theorem multiplicativeNormPoints_units
    (T : Over (Spec (CommRingCat.of R)))
    (p : T ⟶ (groupScheme R S (Gm (Spec (CommRingCat.of S))).toGrp).X) :
    Gm.pointsEquiv (Spec (CommRingCat.of R)) T (multiplicativeNormPoints R S T p) =
      Langlands.Algebra.tensorNormUnits R S
        ((algΓ (CommRingCat.of R)).obj T).unop
          (multiplicativeUnitsEquiv R S T p) :=
  (Gm.pointsEquiv (Spec (CommRingCat.of R)) T).apply_symm_apply _

theorem multiplicativeNormPoints_naturality
    {T T' : Over (Spec (CommRingCat.of R))} (a : T' ⟶ T)
    (p : T ⟶ (groupScheme R S (Gm (Spec (CommRingCat.of S))).toGrp).X) :
    multiplicativeNormPoints R S T' (a ≫ p) = a ≫ multiplicativeNormPoints R S T p := by
  apply (Gm.pointsEquiv (Spec (CommRingCat.of R)) T').injective
  rw [multiplicativeNormPoints_units, Gm.pointsEquiv_naturality,
    multiplicativeNormPoints_units, multiplicativeUnitsEquiv_naturality]
  exact Langlands.Algebra.tensorNormUnits_naturality
    ((algΓ (CommRingCat.of R)).map a).unop.hom _

/-- The determinant norm on the exact affine restriction carrier used by adelic comparison. -/
def multiplicativeNorm :
    groupScheme R S (Gm (Spec (CommRingCat.of S))).toGrp ⟶
      (Gm (Spec (CommRingCat.of R))).toGrp :=
  homOfPoints (multiplicativeNormPoints R S) (multiplicativeNormPoints_naturality R S)

theorem multiplicativeNorm_units
    (T : Over (Spec (CommRingCat.of R)))
    (p : T ⟶ (groupScheme R S (Gm (Spec (CommRingCat.of S))).toGrp).X) :
    Gm.pointsEquiv (Spec (CommRingCat.of R)) T (p ≫ (multiplicativeNorm R S).hom.hom) =
      Langlands.Algebra.tensorNormUnits R S
        ((algΓ (CommRingCat.of R)).obj T).unop (multiplicativeUnitsEquiv R S T p) := by
  rw [multiplicativeNorm, comp_homOfPoints, multiplicativeNormPoints_units]

/-- On every affine coefficient algebra, the actual norm is exactly its determinant tensor norm. -/
theorem multiplicativeNorm_affineUnits
    (A : CommAlgCat.{u} (CommRingCat.of R))
    (p : (groupScheme R S (Gm (Spec (CommRingCat.of S))).toGrp).affinePoints A) :
    Gm.affineUnitsEquiv (CommRingCat.of R) A (p ≫ (multiplicativeNorm R S).hom.hom) =
      Langlands.Algebra.tensorNormUnits R S A
        (Gm.affineUnitsEquiv (CommRingCat.of S) ((tensorFunctor R S).obj A)
          (pointsEquiv R S (Gm (Spec (CommRingCat.of S))).toGrp A p)) := by
  change Units.map
    (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.toMonoidHom
      (Gm.pointsEquiv (Spec (CommRingCat.of R))
        ((algSpec (CommRingCat.of R)).obj (op A))
          (p ≫ (multiplicativeNorm R S).hom.hom)) = _
  rw [multiplicativeNorm_units]
  have hsections := Corepresented.affineSectionsIso_hom_ringHom A
  change (Corepresented.affineSectionsIso A).hom.hom.toRingHom =
    (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom at hsections
  rw [← hsections]
  change Units.map (Corepresented.affineSectionsIso A).hom.hom.toMonoidHom
    (Langlands.Algebra.tensorNormUnits R S
      ((algΓ (CommRingCat.of R)).obj ((algSpec (CommRingCat.of R)).obj (op A))).unop
        (multiplicativeUnitsEquiv R S ((algSpec (CommRingCat.of R)).obj (op A)) p)) = _
  calc
    _ = Langlands.Algebra.tensorNormUnits R S A
        (Units.map
          (Algebra.TensorProduct.lTensor (S := S) S
            (Corepresented.affineSectionsIso A).hom.hom).toMonoidHom
          (multiplicativeUnitsEquiv R S ((algSpec (CommRingCat.of R)).obj (op A)) p)) :=
      (Langlands.Algebra.tensorNormUnits_naturality
        (Corepresented.affineSectionsIso A).hom.hom _).symm
    _ = _ := congrArg (Langlands.Algebra.tensorNormUnits R S A)
      (multiplicativeUnitsEquiv_affine_normalized R S A p)

variable (G : GroupScheme (Spec (CommRingCat.of S)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

/-- The canonical ground-base norm character associated to an upper-base character. -/
def normCharacter (χ : G ⟶ (Gm (Spec (CommRingCat.of S))).toGrp) :
    groupScheme R S G ⟶ (Gm (Spec (CommRingCat.of R))).toGrp :=
  map R S χ ≫ multiplicativeNorm R S

/-- Exact coefficient evaluation of the norm character, on every actual affine test. -/
theorem normCharacter_affineUnits
    (χ : G ⟶ (Gm (Spec (CommRingCat.of S))).toGrp)
    (A : CommAlgCat.{u} (CommRingCat.of R))
    (p : (groupScheme R S G).affinePoints A) :
    Gm.affineUnitsEquiv (CommRingCat.of R) A (p ≫ (normCharacter R S G χ).hom.hom) =
      Langlands.Algebra.tensorNormUnits R S A
        (Gm.affineUnitsEquiv (CommRingCat.of S) ((tensorFunctor R S).obj A)
          (G.affinePointsTarget χ ((tensorFunctor R S).obj A)
            (pointsEquiv R S G A p))) := by
  change Gm.affineUnitsEquiv (CommRingCat.of R) A
    ((p ≫ (map R S χ).hom.hom) ≫ (multiplicativeNorm R S).hom.hom) = _
  rw [multiplicativeNorm_affineUnits]
  exact congrArg (fun q => Langlands.Algebra.tensorNormUnits R S A
    (Gm.affineUnitsEquiv (CommRingCat.of S) ((tensorFunctor R S).obj A) q))
      (map_affinePoints R S χ A p)

end Langlands.GroupScheme.AffineWeil
