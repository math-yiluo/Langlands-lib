import Langlands.Shimura.Unitary.DeligneCoordinates
import Langlands.Shimura.Unitary.SimilitudeCoordinates
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

noncomputable section

universe u v w

namespace Langlands.Shimura

open CategoryTheory

namespace DeligneTorus

@[simp] theorem point_id : point (AlgHom.id ℝ CoordinateRing) = universalPoint := by
  apply Units.ext
  rfl

/-- The algebra map realizing inversion of the Deligne-torus points. -/
def inversionComorphism : CoordinateRing →ₐ[ℝ] CoordinateRing :=
  classify universalPoint⁻¹

@[simp] theorem point_inversionComorphism {S : Type u} [CommRing S] [Algebra ℝ S]
    (f : CoordinateRing →ₐ[ℝ] S) :
    point (f.comp inversionComorphism) = (point f)⁻¹ := by
  rw [point_comp]
  change Units.map (map f.toRingHom).toMonoidHom (point (classify universalPoint⁻¹)) = _
  rw [point_classify, _root_.map_inv]
  rfl

theorem inversionComorphism_comp :
    inversionComorphism.comp inversionComorphism = AlgHom.id ℝ CoordinateRing := by
  apply homEquiv.injective
  change point _ = point _
  rw [point_inversionComorphism]
  change (point (classify universalPoint⁻¹))⁻¹ = _
  rw [point_classify, inv_inv, point_id]

/-- Inversion as an actual morphism of the affine real source. -/
def inversionSchemeMap : scheme ⟶ scheme :=
  AlgebraicGeometry.Spec.map (CommRingCat.ofHom inversionComorphism.toRingHom)

end DeligneTorus

namespace AlgebraInvolution

variable {A : Type u} [Ring A] [Algebra ℝ A]
variable {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ A) (σ : AlgebraInvolution ℝ A)

/-- The affine real scheme of the finitely presented similitude algebra. -/
def similitudeScheme : AlgebraicGeometry.Scheme :=
  AlgebraicGeometry.Spec (CommRingCat.of (σ.similitudeCoordinateRing b))

/-- The actual real structural map of the similitude scheme. -/
def similitudeStructureMap : σ.similitudeScheme b ⟶ AlgebraicGeometry.Spec (CommRingCat.of ℝ) :=
  AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap ℝ (σ.similitudeCoordinateRing b)))

namespace ComplexHom

variable {σ} (h : ComplexHom σ)

/-- Pointwise naturality of scalar extension, without a universe restriction on test algebras. -/
theorem delignePoints_map {S : Type v} {T : Type w}
    [CommRing S] [Algebra ℝ S] [CommRing T] [Algebra ℝ T]
    (f : S →ₐ[ℝ] T) (z : DeligneTorus.Points S) :
    h.delignePoints T (Units.map (DeligneTorus.map f.toRingHom).toMonoidHom z) =
      (σ.baseChange S).map (σ.baseChange T) (changeCoefficients f).toRingHom f.toRingHom
        (σ.changeCoefficients_involution f) (changeCoefficients_scalar f)
        (h.delignePoints S z) := by
  apply Subtype.ext
  apply Prod.ext <;> apply Units.ext
  · exact (h.deligneAlgebraMap_natural f (z : DeligneTorus.Complexification S)).symm
  · exact DeligneTorus.norm_map f.toRingHom (z : DeligneTorus.Complexification S)

/-- Classify the image of the universal Deligne point in the similitude functor. -/
def deligneComorphism : σ.similitudeCoordinateRing b →ₐ[ℝ] DeligneTorus.CoordinateRing :=
  σ.similitudeHom b (h.delignePoints DeligneTorus.CoordinateRing DeligneTorus.universalPoint)

/-- The constructed algebra map recovers the given natural homomorphism on every real algebra. -/
theorem deligneComorphism_point {S : Type v} [CommRing S] [Algebra ℝ S]
    (f : DeligneTorus.CoordinateRing →ₐ[ℝ] S) :
    σ.similitudePoint b (f.comp (h.deligneComorphism b)) =
      h.delignePoints S (DeligneTorus.point f) := by
  rw [similitudePoint_comp]
  unfold deligneComorphism
  rw [similitudePoint_similitudeHom]
  exact (h.delignePoints_map f DeligneTorus.universalPoint).symm

/-- Every quadratic unit is carried to its original scalar-extended similitude. -/
theorem deligneComorphism_classify {S : Type v} [CommRing S] [Algebra ℝ S]
    (z : DeligneTorus.Points S) :
    σ.similitudePoint b ((DeligneTorus.classify z).comp (h.deligneComorphism b)) =
      h.delignePoints S z := by
  rw [h.deligneComorphism_point, DeligneTorus.point_classify]

/-- The induced actual affine scheme morphism for the direct convention. -/
def deligneSchemeMap : DeligneTorus.scheme ⟶ σ.similitudeScheme b :=
  AlgebraicGeometry.Spec.map (CommRingCat.ofHom (h.deligneComorphism b).toRingHom)

/-- This morphism lies over the real base. -/
theorem deligneSchemeMap_over :
    h.deligneSchemeMap b ≫ σ.similitudeStructureMap b = DeligneTorus.structureMap := by
  change AlgebraicGeometry.Spec.map (CommRingCat.ofHom (h.deligneComorphism b).toRingHom) ≫
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap ℝ (σ.similitudeCoordinateRing b))) =
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap ℝ DeligneTorus.CoordinateRing))
  rw [← AlgebraicGeometry.Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact (h.deligneComorphism b).comp_algebraMap

/-- The inverse convention on coordinate algebras. -/
def inverseDeligneComorphism : σ.similitudeCoordinateRing b →ₐ[ℝ] DeligneTorus.CoordinateRing :=
  DeligneTorus.inversionComorphism.comp (h.deligneComorphism b)

/-- The inverse convention recovers the point homomorphism precomposed with inversion. -/
theorem inverseDeligneComorphism_point {S : Type v} [CommRing S] [Algebra ℝ S]
    (f : DeligneTorus.CoordinateRing →ₐ[ℝ] S) :
    σ.similitudePoint b (f.comp (h.inverseDeligneComorphism b)) =
      h.delignePoints S (DeligneTorus.point f)⁻¹ := by
  change σ.similitudePoint b ((f.comp DeligneTorus.inversionComorphism).comp
    (h.deligneComorphism b)) = _
  rw [h.deligneComorphism_point, DeligneTorus.point_inversionComorphism]

/-- Every quadratic unit is carried to the inverse-convention scalar-extended similitude. -/
theorem inverseDeligneComorphism_classify {S : Type v} [CommRing S] [Algebra ℝ S]
    (z : DeligneTorus.Points S) :
    σ.similitudePoint b ((DeligneTorus.classify z).comp (h.inverseDeligneComorphism b)) =
      h.delignePoints S z⁻¹ := by
  rw [h.inverseDeligneComorphism_point, DeligneTorus.point_classify]

/-- The inverse convention as a morphism of affine real schemes. -/
def inverseDeligneSchemeMap : DeligneTorus.scheme ⟶ σ.similitudeScheme b :=
  AlgebraicGeometry.Spec.map (CommRingCat.ofHom (h.inverseDeligneComorphism b).toRingHom)

theorem inverseDeligneSchemeMap_eq :
    h.inverseDeligneSchemeMap b = DeligneTorus.inversionSchemeMap ≫ h.deligneSchemeMap b := by
  exact AlgebraicGeometry.Spec.map_comp
    (CommRingCat.ofHom (h.deligneComorphism b).toRingHom)
    (CommRingCat.ofHom DeligneTorus.inversionComorphism.toRingHom)

/-- The inverse convention also lies over the real base. -/
theorem inverseDeligneSchemeMap_over :
    h.inverseDeligneSchemeMap b ≫ σ.similitudeStructureMap b = DeligneTorus.structureMap := by
  change AlgebraicGeometry.Spec.map (CommRingCat.ofHom (h.inverseDeligneComorphism b).toRingHom) ≫
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap ℝ (σ.similitudeCoordinateRing b))) =
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap ℝ DeligneTorus.CoordinateRing))
  rw [← AlgebraicGeometry.Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact (h.inverseDeligneComorphism b).comp_algebraMap

end ComplexHom
end AlgebraInvolution

/-- A finite real basis of the concrete archimedean matrix algebra. -/
def harrisArchimedeanBasis (n : ℕ) (I : Type) [Fintype I] :=
  Module.Free.chooseBasis ℝ (I → Matrix (Fin n) (Fin n) ℂ)

/-- The direct corrected Harris map as an actual morphism of affine real schemes. -/
def harrisDeligneSchemeMap (n : ℕ) (I : Type) [Fintype I] [DecidableEq I] (distinguished : I) :=
  (harrisArchimedeanHom n I distinguished).deligneSchemeMap (harrisArchimedeanBasis n I)

/-- Kottwitz's inverse convention as an actual morphism of affine real schemes. -/
def kottwitzDeligneSchemeMap (n : ℕ) (I : Type) [Fintype I] [DecidableEq I] (distinguished : I) :=
  (kottwitzHom n I distinguished).inverseDeligneSchemeMap (harrisArchimedeanBasis n I)

end Langlands.Shimura
