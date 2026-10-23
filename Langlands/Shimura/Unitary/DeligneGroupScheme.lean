import Langlands.GroupScheme.Corepresented
import Langlands.Shimura.Unitary.DeligneAffine

noncomputable section

namespace Langlands.Shimura

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace DeligneTorus

/-- The quadratic unit groups are commutative over every real algebra. -/
def commFunctor : CommAlgCat ℝ ⥤ CommGrpCat where
  obj S := CommGrpCat.of (Points S)
  map f := CommGrpCat.ofHom (functor.map f).hom
  map_id S := by
    apply CommGrpCat.hom_ext
    exact congrArg GrpCat.Hom.hom (functor.map_id S)
  map_comp f g := by
    apply CommGrpCat.hom_ext
    exact congrArg GrpCat.Hom.hom (functor.map_comp f g)

/-- The actual affine Deligne group scheme on its explicit coordinate algebra. -/
abbrev groupScheme : GroupScheme (Spec (CommRingCat.of ℝ)) :=
  GroupScheme.Corepresented.groupScheme (R := CommRingCat.of ℝ) functor corepresentableBy

/-- The same affine group scheme with its commutativity certificate. -/
def commGroupScheme : CommGroupScheme (Spec (CommRingCat.of ℝ)) :=
  GroupScheme.Corepresented.commGroupScheme (R := CommRingCat.of ℝ) commFunctor corepresentableBy

@[simp] theorem groupScheme_scheme : groupScheme.X.left = scheme := rfl
@[simp] theorem groupScheme_structureMap : groupScheme.X.hom = structureMap := rfl
@[simp] theorem commGroupScheme_toGrp : commGroupScheme.toGrp = groupScheme := rfl

/-- Points on affine real test schemes recover the actual quadratic units multiplicatively. -/
def affinePointsEquiv (S : CommAlgCat ℝ) :
    ((algSpec (CommRingCat.of ℝ)).obj (op S) ⟶ groupScheme.X) ≃* Points S :=
  GroupScheme.Corepresented.affinePointsEquiv (R := CommRingCat.of ℝ) functor corepresentableBy S

@[simp] theorem affinePointsEquiv_map (S : CommAlgCat ℝ) (f : coordinateAlgebra ⟶ S) :
    affinePointsEquiv S ((algSpec (CommRingCat.of ℝ)).map f.op) = point f.hom :=
  GroupScheme.Corepresented.affinePointsEquiv_map (R := CommRingCat.of ℝ) functor corepresentableBy S f

/-- The natural pointwise inversion is an actual group-scheme homomorphism. -/
def inversionGroupSchemeMap : groupScheme ⟶ groupScheme :=
  GroupScheme.Corepresented.groupSchemeMap (R := CommRingCat.of ℝ) corepresentableBy corepresentableBy inversion

@[simp] theorem inversionGroupSchemeMap_hom :
    inversionGroupSchemeMap.hom.hom.left = inversionSchemeMap := rfl

end DeligneTorus

namespace AlgebraInvolution

variable {A : Type} [Ring A] [Algebra ℝ A]
variable {κ : Type} [Fintype κ] (b : Module.Basis κ ℝ A) (σ : AlgebraInvolution ℝ A)

/-- The actual affine similitude group scheme from its explicit coordinate algebra. -/
abbrev similitudeGroupScheme : GroupScheme (Spec (CommRingCat.of ℝ)) :=
  GroupScheme.Corepresented.groupScheme (R := CommRingCat.of ℝ) σ.similitudeFunctor (σ.similitudeCorepresentableBy b)

@[simp] theorem similitudeGroupScheme_scheme :
    (σ.similitudeGroupScheme b).X.left = σ.similitudeScheme b := rfl

@[simp] theorem similitudeGroupScheme_structureMap :
    (σ.similitudeGroupScheme b).X.hom = σ.similitudeStructureMap b := rfl

/-- The group scheme's affine points are the original scalar-extended similitudes. -/
def similitudeAffinePointsEquiv (S : CommAlgCat ℝ) :
    ((algSpec (CommRingCat.of ℝ)).obj (op S) ⟶ (σ.similitudeGroupScheme b).X) ≃*
      (σ.baseChange S).similitudes :=
  GroupScheme.Corepresented.affinePointsEquiv (R := CommRingCat.of ℝ) σ.similitudeFunctor
    (σ.similitudeCorepresentableBy b) S

namespace ComplexHom

variable {σ} (h : ComplexHom σ)

/-- The direct Deligne map with its actual group-scheme homomorphism structure. -/
def deligneGroupSchemeMap : DeligneTorus.groupScheme ⟶ σ.similitudeGroupScheme b :=
  GroupScheme.Corepresented.groupSchemeMap (R := CommRingCat.of ℝ) DeligneTorus.corepresentableBy
    (σ.similitudeCorepresentableBy b) h.deligneHom

@[simp] theorem deligneGroupSchemeMap_hom :
    (h.deligneGroupSchemeMap b).hom.hom.left = h.deligneSchemeMap b := rfl

/-- On every affine test scheme, the constructed group-scheme map recovers scalar extension. -/
theorem deligneGroupSchemeMap_affinePoints {S : CommAlgCat ℝ}
    (f : (algSpec (CommRingCat.of ℝ)).obj (op S) ⟶ DeligneTorus.groupScheme.X) :
    σ.similitudeAffinePointsEquiv b S (f ≫ (h.deligneGroupSchemeMap b).hom.hom) =
      h.delignePoints S (DeligneTorus.affinePointsEquiv S f) :=
  GroupScheme.Corepresented.groupSchemeMap_affinePoints (R := CommRingCat.of ℝ) DeligneTorus.corepresentableBy
    (σ.similitudeCorepresentableBy b) h.deligneHom f

/-- The inverse convention is also an actual homomorphism of group schemes. -/
def inverseDeligneGroupSchemeMap : DeligneTorus.groupScheme ⟶ σ.similitudeGroupScheme b :=
  GroupScheme.Corepresented.groupSchemeMap (R := CommRingCat.of ℝ) DeligneTorus.corepresentableBy
    (σ.similitudeCorepresentableBy b) h.inverseDeligneHom

/-- The inverse-convention group homomorphism has the previously constructed spectrum map. -/
@[simp] theorem inverseDeligneGroupSchemeMap_hom :
    (h.inverseDeligneGroupSchemeMap b).hom.hom.left = h.inverseDeligneSchemeMap b := by
  have hc : σ.similitudeHom b
      (h.delignePoints DeligneTorus.CoordinateRing DeligneTorus.universalPoint⁻¹) =
      h.inverseDeligneComorphism b := by
    apply (σ.similitudeHomEquiv b).injective
    change σ.similitudePoint b (σ.similitudeHom b _) =
      σ.similitudePoint b (h.inverseDeligneComorphism b)
    rw [similitudePoint_similitudeHom]
    have hd := h.inverseDeligneComorphism_point b (AlgHom.id ℝ DeligneTorus.CoordinateRing)
    rw [AlgHom.id_comp, DeligneTorus.point_id] at hd
    exact hd.symm
  change Spec.map (CommRingCat.ofHom (σ.similitudeHom b
      (h.delignePoints DeligneTorus.CoordinateRing DeligneTorus.universalPoint⁻¹)).toRingHom) =
    Spec.map (CommRingCat.ofHom (h.inverseDeligneComorphism b).toRingHom)
  rw [hc]

/-- The inverse-convention map recovers scalar extension at the inverse point. -/
theorem inverseDeligneGroupSchemeMap_affinePoints {S : CommAlgCat ℝ}
    (f : (algSpec (CommRingCat.of ℝ)).obj (op S) ⟶ DeligneTorus.groupScheme.X) :
    σ.similitudeAffinePointsEquiv b S (f ≫ (h.inverseDeligneGroupSchemeMap b).hom.hom) =
      h.delignePoints S (DeligneTorus.affinePointsEquiv S f)⁻¹ :=
  GroupScheme.Corepresented.groupSchemeMap_affinePoints (R := CommRingCat.of ℝ) DeligneTorus.corepresentableBy
    (σ.similitudeCorepresentableBy b) h.inverseDeligneHom f

end ComplexHom
end AlgebraInvolution

/-- The corrected Harris homomorphism as an actual homomorphism of real group schemes. -/
def harrisDeligneGroupSchemeMap (n : ℕ) (I : Type) [Fintype I] [DecidableEq I]
    (distinguished : I) :=
  (harrisArchimedeanHom n I distinguished).deligneGroupSchemeMap (harrisArchimedeanBasis n I)

/-- Kottwitz's inverse convention as an actual homomorphism of real group schemes. -/
def kottwitzDeligneGroupSchemeMap (n : ℕ) (I : Type) [Fintype I] [DecidableEq I]
    (distinguished : I) :=
  (kottwitzHom n I distinguished).inverseDeligneGroupSchemeMap (harrisArchimedeanBasis n I)

@[simp] theorem harrisDeligneGroupSchemeMap_hom (n : ℕ) (I : Type)
    [Fintype I] [DecidableEq I] (distinguished : I) :
    (harrisDeligneGroupSchemeMap n I distinguished).hom.hom.left =
      harrisDeligneSchemeMap n I distinguished := rfl

@[simp] theorem kottwitzDeligneGroupSchemeMap_hom (n : ℕ) (I : Type)
    [Fintype I] [DecidableEq I] (distinguished : I) :
    (kottwitzDeligneGroupSchemeMap n I distinguished).hom.hom.left =
      kottwitzDeligneSchemeMap n I distinguished :=
  (kottwitzHom n I distinguished).inverseDeligneGroupSchemeMap_hom (harrisArchimedeanBasis n I)

end Langlands.Shimura
