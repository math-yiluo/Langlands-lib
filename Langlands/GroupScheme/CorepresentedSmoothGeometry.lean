import Langlands.GroupScheme.Corepresented
import Langlands.GroupScheme.SmoothConnectedGeometryProof
import Langlands.AlgebraicGeometry.SmoothGeometricallyReducedProof
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.RingTheory.Nilpotent.GeometricallyReduced

/-! # Coordinate algebras of smooth corepresented groups over a field

The structure morphism of every group scheme is surjective, since the unit is a section. For a
corepresented group over a field `k` with coordinate algebra `B`, smoothness makes `B`
geometrically reduced over `k`, and smoothness together with connectedness makes `B` a domain.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme

/-- The structure morphism of a group scheme is surjective: the unit is a section of it. -/
theorem surjective_hom {S : Scheme.{u}} (P : GroupScheme S) : Surjective P.X.hom := by
  have h : (η[P.X]).left ≫ P.X.hom = 𝟙 S := Over.w η[P.X]
  refine ⟨fun s => ⟨(η[P.X]).left s, ?_⟩⟩
  change ((η[P.X]).left ≫ P.X.hom) s = s
  rw [h]
  rfl

variable {k : Type u} [Field k]

/-- A `k`-algebra whose spectrum is geometrically reduced over `Spec k` is geometrically
reduced. -/
theorem isGeometricallyReduced_of_geometricallyReduced_spec (A : Type u) [CommRing A]
    [Algebra k A] [GeometricallyReduced (Spec.map (CommRingCat.ofHom (algebraMap k A)))] :
    Algebra.IsGeometricallyReduced k A := by
  have h₁ : IsReduced (pullback (Spec.map (CommRingCat.ofHom (algebraMap k A)))
      (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))) :=
    pullback_of_geometrically
      (GeometricallyReduced.geometrically_isReduced
        (f := Spec.map (CommRingCat.ofHom (algebraMap k A)))) _ _
  have h₂ : IsReduced (Spec (CommRingCat.of (A ⊗[k] AlgebraicClosure k))) :=
    isReduced_of_isOpenImmersion (pullbackSpecIso k A (AlgebraicClosure k)).inv
  have h₃ : _root_.IsReduced (A ⊗[k] AlgebraicClosure k) := (affine_isReduced_iff _).mp h₂
  rw [Algebra.isGeometricallyReduced_field_iff]
  exact isReduced_of_injective (Algebra.TensorProduct.comm k (AlgebraicClosure k) A).toRingHom
    (Algebra.TensorProduct.comm k (AlgebraicClosure k) A).injective

namespace Corepresented

variable {F : CommAlgCat.{u} (CommRingCat.of k) ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} (CommRingCat.of k)} {e : (F ⋙ forget GrpCat).CorepresentableBy B}

/-- The coordinate algebra of a smooth corepresented group over a field is geometrically
reduced. -/
theorem isGeometricallyReduced_of_smooth [Smooth (groupScheme F e).X.hom] :
    Algebra.IsGeometricallyReduced k B := by
  have : GeometricallyReduced (Spec.map (CommRingCat.ofHom (algebraMap k B))) :=
    Langlands.AlgebraicGeometry.smoothGeometricallyReduced _ _ _
      (inferInstanceAs (Smooth (groupScheme F e).X.hom))
  exact isGeometricallyReduced_of_geometricallyReduced_spec B

/-- The coordinate algebra of a smooth connected corepresented group over a field is a
domain. -/
theorem isDomain_of_smooth_connected [Smooth (groupScheme F e).X.hom]
    [IsAffineHom (groupScheme F e).X.hom] [ConnectedSpace (groupScheme F e).X.left] :
    IsDomain B := by
  have : GeometricallyIntegral (groupScheme F e).X.hom :=
    smoothConnectedAffineGeometry.1 k (groupScheme F e) inferInstance inferInstance
      inferInstance
  have : IsIntegral (groupScheme F e).X.left :=
    GeometricallyIntegral.isIntegral_of_subsingleton (groupScheme F e).X.hom
  exact (affine_isIntegral_iff (CommRingCat.of B)).mp this

end Corepresented

end Langlands.GroupScheme
