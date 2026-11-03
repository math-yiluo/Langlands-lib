import Langlands.GroupScheme.VectorGroupQuotient
import Langlands.GroupScheme.CorepresentedSmooth
import Langlands.GroupScheme.Rational.VectorLieCoordinates
import Langlands.GroupScheme.Rational.SplitUnipotentTransport

/-! # Actual vector-group isomorphisms from natural coordinates -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k]
    {V : GroupScheme (Spec (CommRingCat.of k))} {n m : ℕ}
    (e : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ V.X) ≃* Multiplicative (Fin n → Γ(T.left, ⊤)))

/-- The comparison of two natural vector coordinate models is natural. -/
theorem vectorGroupIso_naturality (he : IsNaturalVectorCoordinates e)
    {T W : Over (Spec (CommRingCat.of k))} (f : W ⟶ T) (v : T ⟶ V.X) :
    ((e W).trans (VectorGroup.coordinates (CommRingCat.of k) n W).symm) (f ≫ v) =
      f ≫ ((e T).trans (VectorGroup.coordinates (CommRingCat.of k) n T).symm) v := by
  apply (VectorGroup.coordinates (CommRingCat.of k) n W).injective
  apply Multiplicative.toAdd.injective
  simpa only [MulEquiv.trans_apply, MulEquiv.apply_symm_apply,
    VectorGroup.coordinates_comp] using he T W f v

/-- Natural vector coordinates induce an actual isomorphism with the standard
polynomial vector group of the same dimension. -/
def vectorGroupIso (he : IsNaturalVectorCoordinates e) :
    V ≅ VectorGroup.groupScheme (CommRingCat.of k) n :=
  isoOfPoints
    (fun T => (e T).trans (VectorGroup.coordinates (CommRingCat.of k) n T).symm)
    (vectorGroupIso_naturality e he)

/-- The actual isomorphism recovers the supplied coordinates on every test. -/
@[simp]
theorem coordinates_comp_vectorGroupIso_hom (he : IsNaturalVectorCoordinates e)
    (T : Over (Spec (CommRingCat.of k))) (v : T ⟶ V.X) :
    VectorGroup.coordinates (CommRingCat.of k) n T
      (v ≫ (vectorGroupIso e he).hom.hom.hom) = e T v := by
  have key := comp_isoOfPoints_hom
    (fun T => (e T).trans (VectorGroup.coordinates (CommRingCat.of k) n T).symm)
    (vectorGroupIso_naturality e he) T v
  rw [vectorGroupIso, key]
  exact (VectorGroup.coordinates (CommRingCat.of k) n T).apply_symm_apply _

/-- A vector-group predicate supplies an actual standard-vector-group
isomorphism; no prior affineness hypothesis is needed. -/
def IsVectorGroupOfDimension.iso (h : IsVectorGroupOfDimension V n) :
    V ≅ VectorGroup.groupScheme (CommRingCat.of k) n :=
  vectorGroupIso (Classical.choose h) (Classical.choose_spec h)

/-- The all-test vector-group predicate is equivalent to an actual
group-scheme isomorphism with the standard vector group. -/
theorem isVectorGroupOfDimension_iff_nonempty_iso :
    IsVectorGroupOfDimension V n ↔
      Nonempty (V ≅ VectorGroup.groupScheme (CommRingCat.of k) n) := by
  constructor
  · exact fun h => ⟨h.iso⟩
  · rintro ⟨f⟩
    exact (IsVectorGroupOfDimension.of_iso f.symm
      ⟨VectorGroup.coordinates (CommRingCat.of k) n,
        VectorGroup.isNaturalVectorCoordinates⟩)

/-- A vector group is affine over the field. -/
theorem IsVectorGroupOfDimension.isAffineHom (h : IsVectorGroupOfDimension V n) :
    IsAffineHom V.X.hom := by
  let f := h.iso
  have : IsIso f.hom.hom.hom.left :=
    (inferInstance : IsIso (((Grp.forget _) ⋙ Over.forget _).map f.hom))
  have : IsAffineHom (VectorGroup.groupScheme (CommRingCat.of k) n).X.hom := by
    change IsAffineHom (Spec.map
      (CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin n) k))))
    infer_instance
  rw [← Over.w f.hom.hom.hom]
  infer_instance

/-- A vector group is smooth over the field. -/
theorem IsVectorGroupOfDimension.smooth (h : IsVectorGroupOfDimension V n) :
    Smooth V.X.hom := by
  let f := h.iso
  have : IsIso f.hom.hom.hom.left :=
    (inferInstance : IsIso (((Grp.forget _) ⋙ Over.forget _).map f.hom))
  have : Smooth (VectorGroup.groupScheme (CommRingCat.of k) n).X.hom :=
    Corepresented.smooth_groupScheme_iff.mpr inferInstance
  rw [← Over.w f.hom.hom.hom]
  infer_instance

/-- A vector group is connected, including in dimension zero. -/
theorem IsVectorGroupOfDimension.connectedSpace (h : IsVectorGroupOfDimension V n) :
    ConnectedSpace V.X.left := by
  let f := ((Grp.forget _) ⋙ Over.forget _).mapIso h.iso
  have hconn : ConnectedSpace (VectorGroup.groupScheme (CommRingCat.of k) n).X.left := by
    change ConnectedSpace (Spec (CommRingCat.of (MvPolynomial (Fin n) k)))
    infer_instance
  exact (Scheme.homeoOfIso f).connectedSpace_iff.mpr hconn

variable {e}

/-- Two natural vector coordinate systems on the same group have the same
dimension, by their induced linear coordinates on its actual Lie kernel. -/
theorem IsNaturalVectorCoordinates.dimension_eq (he : IsNaturalVectorCoordinates e)
    {e' : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ V.X) ≃* Multiplicative (Fin m → Γ(T.left, ⊤))}
    (he' : IsNaturalVectorCoordinates e') : n = m := by
  let : IsAffineHom V.X.hom :=
    IsVectorGroupOfDimension.isAffineHom ⟨e, he⟩
  have h := ((vectorLieCoordinates e he (CommAlgCat.of k k)).symm.trans
    (vectorLieCoordinates e' he' (CommAlgCat.of k k))).finrank_eq
  simpa using h

/-- The dimension in the all-test vector-group predicate is unique. -/
theorem IsVectorGroupOfDimension.dimension_eq (h : IsVectorGroupOfDimension V n)
    (h' : IsVectorGroupOfDimension V m) : n = m := by
  obtain ⟨e, he⟩ := h
  obtain ⟨e', he'⟩ := h'
  exact IsNaturalVectorCoordinates.dimension_eq he he'

end Langlands.GroupScheme.RelativeRoot
