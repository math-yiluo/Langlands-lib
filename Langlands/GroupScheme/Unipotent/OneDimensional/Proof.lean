import Langlands.GroupScheme.Unipotent.OneDimensional.Geometry
import Langlands.GroupScheme.Unipotent.OneDimensionalStatement
import Langlands.GroupScheme.Rational.VectorGroupCoordinates
import Langlands.GroupScheme.Rational.RootSubgroupVectorTransport

/-! # One-dimensional unipotent groups over perfect fields are vector groups -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry Polynomial

namespace Langlands.GroupScheme.Unipotent.OneDimensional

open AffineLinearEmbedding

variable {k : Type u} [Field k]
  {F : CommAlgCat.{u} (CommRingCat.of k) ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} (CommRingCat.of k)}
  (e : (F ⋙ forget GrpCat).CorepresentableBy B)

/-- A primitive element that generates the coordinates as a polynomial ring identifies the
corepresented group with the one-dimensional vector group. -/
theorem nonempty_iso_of_primitive_bijective {y : B}
    (hy : letI := bialgebra e; Bialgebra.IsPrimitiveElem k y)
    (hbij : Function.Bijective (aeval y : k[X] →ₐ[k] B)) :
    Nonempty (Corepresented.groupScheme F e ≅ VectorGroup.groupScheme (CommRingCat.of k) 1) := by
  let q := VectorGroup.quotientMap (isPrimitiveFamily_of_isPrimitiveElem e hy)
  have hcomp : (MvPolynomial.aeval (fun _ : Fin 1 => y) : MvPolynomial (Fin 1) k →ₐ[k] B) =
      (aeval y : k[X] →ₐ[k] B).comp (MvPolynomial.uniqueAlgEquiv k (Fin 1)).toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [MvPolynomial.uniqueAlgEquiv_apply]
  have hmv : Function.Bijective
      (MvPolynomial.aeval (fun _ : Fin 1 => y) : MvPolynomial (Fin 1) k →ₐ[k] B) := by
    rw [hcomp]
    exact hbij.comp (MvPolynomial.uniqueAlgEquiv k (Fin 1)).bijective
  let φ : MvPolynomial (Fin 1) k ≃+* B := RingEquiv.ofBijective
    (MvPolynomial.aeval (fun _ : Fin 1 => y) : MvPolynomial (Fin 1) k →ₐ[k] B) hmv
  have : IsIso q.hom.hom.left := by
    rw [VectorGroup.quotientMap_left]
    exact (inferInstance : IsIso (Spec.map φ.toCommRingCatIso.hom))
  have : IsIso ((Over.forget _).map q.hom.hom) := by
    change IsIso q.hom.hom.left
    infer_instance
  have : IsIso q.hom.hom := isIso_of_reflects_iso q.hom.hom (Over.forget _)
  exact ⟨Grp.mkIso (asIso q.hom.hom) (IsMonHom.one_hom q.hom.hom) (IsMonHom.mul_hom q.hom.hom)⟩

end Langlands.GroupScheme.Unipotent.OneDimensional

namespace Langlands.GroupScheme

open Unipotent.OneDimensional

/-- **Milne 2017, 14.58 (converse).** A smooth connected affine unipotent group of dimension
one over a perfect field is the one-dimensional vector group. -/
theorem perfectFieldOneDimensionalUnipotent :
    PerfectFieldOneDimensionalUnipotentStatement.{u} := by
  intro k _ _ U _ _ hconn hU
  have : IsAffine U.X.left := isAffine_of_isAffineHom U.X.hom
  let eU := AffineCoordinates.groupSchemeIso U
  have : IsIso eU.hom.hom.hom.left :=
    inferInstanceAs (IsIso (((Grp.forget (Over _)) ⋙ Over.forget _).map eU.hom))
  have : IsIso eU.inv.hom.hom.left :=
    inferInstanceAs (IsIso (((Grp.forget (Over _)) ⋙ Over.forget _).map eU.inv))
  let : SmoothOfRelativeDimension 1 (Corepresented.groupScheme (AffineCoordinates.functor U)
      (AffineCoordinates.corepresentation U)).X.hom := by
    rw [← Over.w eU.hom.hom.hom]
    exact (inferInstance : SmoothOfRelativeDimension (0 + 1) (eU.hom.hom.hom.left ≫ U.X.hom))
  let : ConnectedSpace (Corepresented.groupScheme (AffineCoordinates.functor U)
      (AffineCoordinates.corepresentation U)).X.left :=
    Function.Surjective.connectedSpace
      (Scheme.homeoOfIso (asIso eU.inv.hom.hom.left)).surjective
      (Scheme.homeoOfIso (asIso eU.inv.hom.hom.left)).continuous
  have hU' : IsUnipotent (Corepresented.groupScheme (AffineCoordinates.functor U)
      (AffineCoordinates.corepresentation U)) := IsUnipotent.of_iso eU hU
  obtain ⟨y, hy, hbij⟩ :=
    exists_primitive_bijective_of_smooth (AffineCoordinates.corepresentation U) hU'
  obtain ⟨eq⟩ := nonempty_iso_of_primitive_bijective (AffineCoordinates.corepresentation U) hy hbij
  exact RelativeRoot.isVectorGroupOfDimension_iff_nonempty_iso.mpr ⟨eU.symm ≪≫ eq⟩

end Langlands.GroupScheme
