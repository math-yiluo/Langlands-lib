import Langlands.GroupScheme.Dynamic.CoactionGrading
import Langlands.CommutativeAlgebra.GradedDVRIntegrality

/-! # Contracting points of the coaction of a cocharacter

For a corepresented affine group `Spec B` over a field `k` and a cocharacter `χ`, the coaction
`Corepresented.coaction χ` is a grading of `B` in the sense of
`CommutativeAlgebra.GradedDVRIntegrality.IsGrading`, the counit is compatible with it, and the
points of `U_G(χ)` are exactly the contracting points.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace Corepresented

open CommutativeAlgebra.GradedDVRIntegrality

variable {k : Type u} [Field k] {F : CommAlgCat.{u} (CommRingCat.of k) ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} (CommRingCat.of k)} {e : (F ⋙ forget GrpCat).CorepresentableBy B}
  (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ groupScheme F e)

/-- The coaction of a cocharacter is a grading of the coordinate ring. -/
theorem isGrading_coaction : IsGrading k (coaction χ).hom where
  map_algebraMap r := coaction_algebraMap χ r
  sum_coeff b := sum_coeff_coaction χ b
  coeff_coeff b n := coaction_coeff_coaction χ b n

variable (e) in
/-- The counit as a `k`-algebra map. -/
def counitAlgHom : B →ₐ[k] k where
  __ := (counit e).hom
  commutes' r := by
    have h := algebraMap_comp_pointRing (1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
      (groupScheme F e).X)
    rw [Spec.preimage_id] at h
    exact congrArg (fun φ => φ.hom r) h

theorem counitAlgHom_apply (b : B) : counitAlgHom e b = counit e b :=
  rfl

/-- The counit is compatible with the grading: it kills the components of nonzero weight. -/
theorem counit_coeff_coaction (b : B) (n : ℤ) :
    counitAlgHom e ((coaction χ b).coeff n) = if n = 0 then counitAlgHom e b else 0 := by
  have h := (mem_centralizer_iff χ (1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
    (groupScheme F e).X)).1 (one_mem _) b n
  rw [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, map_sub, sub_eq_zero] at h
  change counit e _ = _
  rw [counitAlgHom_apply]
  change counit e _ = counit e _ at h
  rw [h, LaurentPolynomial.C_apply]
  split_ifs <;> simp

variable {A : Type u} [CommRing A] [Algebra k A]

/-- The `k`-algebra map `B → A` classifying a point over `Spec A`. -/
def pointAlgHom
    (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A))) ⟶ (groupScheme F e).X) :
    B →ₐ[k] A where
  __ := (pointRing x).hom
  commutes' r := by
    have h := algebraMap_comp_pointRing x
    rw [Spec.preimage_map] at h
    exact congrArg (fun φ => φ.hom r) h

theorem pointAlgHom_apply
    (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A))) ⟶ (groupScheme F e).X)
    (b : B) : pointAlgHom x b = pointRing x b :=
  rfl

/-- The points of `U_G(χ)` are the contracting points. -/
theorem isContracting_pointAlgHom_iff
    (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A))) ⟶ (groupScheme F e).X) :
    IsContracting (coaction χ).hom (counitAlgHom e) (pointAlgHom x) ↔
      x ∈ (Dynamic.unipotent χ).carrier _ := by
  rw [mem_unipotent_iff]
  refine and_congr Iff.rfl (forall_congr' fun b => ?_)
  rw [map_sub, sub_eq_zero, pointAlgHom_apply]
  have h : pointRing x (algebraMap k B (counitAlgHom e b)) = algebraMap k A (counitAlgHom e b) :=
    (pointAlgHom x).commutes _
  exact ⟨fun h' => h'.trans h.symm, fun h' => h'.trans h⟩

end Corepresented

end Langlands.GroupScheme
