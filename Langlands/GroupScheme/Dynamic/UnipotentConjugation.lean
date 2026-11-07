import Langlands.AlgebraicGeometry.AxGrothendieckPoints
import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Langlands.GroupScheme.Dynamic.LimitMap

/-! # Conjugation on the contracting subgroup -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic

set_option backward.isDefEq.respectTransparency false

namespace Affine

variable {R : CommRingCat.{u}} {G : GroupScheme (Spec R)} [IsAffine G.X.left]
  (χ : (Gm (Spec R)).toGrp ⟶ G)
  {t : 𝟙_ (Over (Spec R)) ⟶ G.X}
  (ht : t ∈ (centralizer χ).carrier (𝟙_ _))

include ht

/-- The commutator with a centralizing base point factors through the actual
closed representative of the contracting subgroup. -/
theorem exists_unipotentCommutator :
    ∃ f : (unipotentScheme χ).X ⟶ (unipotentScheme χ).X,
      f ≫ (unipotentHom χ).hom.hom =
        (unipotentHom χ).hom.hom * (toUnit (unipotentScheme χ).X ≫ t) *
          (unipotentHom χ).hom.hom⁻¹ * (toUnit (unipotentScheme χ).X ≫ t)⁻¹ := by
  let i := unipotentHom χ
  have hrep := isRepresentedBy_unipotentHom χ
  have hi : i.hom.hom ∈ (unipotent χ).carrier (unipotentScheme χ).X := by
    rw [← hrep.2, SubgroupFunctor.mem_range]
    exact ⟨𝟙 _, by simp [i]⟩
  have ht' := (centralizer χ).comp_mem (toUnit (unipotentScheme χ).X) ht
  have hcomm : i.hom.hom * (toUnit (unipotentScheme χ).X ≫ t) *
      i.hom.hom⁻¹ * (toUnit (unipotentScheme χ).X ≫ t)⁻¹ ∈
        (unipotent χ).carrier (unipotentScheme χ).X := by
    simpa only [mul_assoc] using mul_mem hi
      (conj_mem_unipotent χ (centralizer_le_parabolic χ _ ht') (inv_mem hi))
  rw [← hrep.2, SubgroupFunctor.mem_range] at hcomm
  exact hcomm

/-- The actual scheme endomorphism `v ↦ v t v⁻¹ t⁻¹` of the contracting subgroup. -/
def unipotentCommutator : (unipotentScheme χ).X ⟶ (unipotentScheme χ).X :=
  (exists_unipotentCommutator χ ht).choose

theorem unipotentCommutator_comp :
    unipotentCommutator χ ht ≫ (unipotentHom χ).hom.hom =
      (unipotentHom χ).hom.hom * (toUnit (unipotentScheme χ).X ≫ t) *
        (unipotentHom χ).hom.hom⁻¹ * (toUnit (unipotentScheme χ).X ≫ t)⁻¹ :=
  (exists_unipotentCommutator χ ht).choose_spec

/-- The defining commutator formula holds on every test scheme. -/
theorem unipotentCommutator_apply {T : Over (Spec R)}
    (x : T ⟶ (unipotentScheme χ).X) :
    (x ≫ unipotentCommutator χ ht) ≫ (unipotentHom χ).hom.hom =
      (x ≫ (unipotentHom χ).hom.hom) * (toUnit T ≫ t) *
        (x ≫ (unipotentHom χ).hom.hom)⁻¹ * (toUnit T ≫ t)⁻¹ := by
  rw [Category.assoc, unipotentCommutator_comp]
  simp only [MonObj.comp_mul, GrpObj.comp_inv, comp_toUnit_assoc]

end Affine

/-- If a centralizing base point has no nontrivial commuting point in the
contracting subgroup, its conjugacy orbit contains every unipotent translate. -/
theorem exists_unipotent_conj_eq_mul
    {k : Type u} [Field k] [IsAlgClosed k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    {t : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G.X}
    (ht : t ∈ (centralizer χ).carrier (𝟙_ _))
    (hfree : ∀ v ∈ (unipotent χ).carrier (𝟙_ _), v * t = t * v → v = 1)
    {u : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G.X}
    (hu : u ∈ (unipotent χ).carrier (𝟙_ _)) :
    ∃ v ∈ (unipotent χ).carrier (𝟙_ _), v * t * v⁻¹ = u * t := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let U := Affine.unipotentScheme χ
  let i := Affine.unipotentHom χ
  have hrep := Affine.isRepresentedBy_unipotentHom χ
  have : Mono i.hom.hom := hrep.1
  have : IsClosedImmersion i.hom.hom.left := Affine.isClosedSubgroup_unipotentHom χ
  have : IsAffine U.X.left := isAffine_of_isAffineHom i.hom.hom.left
  have : LocallyOfFiniteType U.X.hom := by
    have h : LocallyOfFiniteType (i.hom.hom.left ≫ G.X.hom) := inferInstance
    simpa only [Over.w] using h
  have hmem {T : Over (Spec (CommRingCat.of k))} (x : T ⟶ U.X) :
      x ≫ i.hom.hom ∈ (unipotent χ).carrier T := by
    rw [← hrep.2, SubgroupFunctor.mem_range]
    exact ⟨x, rfl⟩
  have hinj : Function.Injective
      (fun x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ U.X =>
        x ≫ Affine.unipotentCommutator χ ht) := by
    intro x y hxy
    apply (cancel_mono i.hom.hom).mp
    have he : (x ≫ i.hom.hom) * t * (x ≫ i.hom.hom)⁻¹ * t⁻¹ =
        (y ≫ i.hom.hom) * t * (y ≫ i.hom.hom)⁻¹ * t⁻¹ := by
      have h := congrArg (fun z => z ≫ i.hom.hom) hxy
      simpa only [i, Affine.unipotentCommutator_apply, toUnit_unit, Category.id_comp] using h
    have he' := mul_right_cancel he
    have hc : ((y ≫ i.hom.hom)⁻¹ * (x ≫ i.hom.hom)) * t =
        t * ((y ≫ i.hom.hom)⁻¹ * (x ≫ i.hom.hom)) := by
      simpa only [mul_assoc, inv_mul_cancel, mul_one, inv_mul_cancel_left] using
        congrArg (fun z => (y ≫ i.hom.hom)⁻¹ * z * (x ≫ i.hom.hom)) he'
    exact (inv_mul_eq_one.mp (hfree _ (mul_mem (inv_mem (hmem y)) (hmem x)) hc)).symm
  have hsurj := Langlands.AlgebraicGeometry.axGrothendieck_points
    (Affine.unipotentCommutator χ ht) hinj
  have hu' : u ∈ (SubgroupFunctor.range i).carrier (𝟙_ _) := by
    rwa [hrep.2]
  obtain ⟨u', hu'⟩ := SubgroupFunctor.mem_range.mp hu'
  obtain ⟨v', hv'⟩ := hsurj u'
  refine ⟨v' ≫ i.hom.hom, hmem v', ?_⟩
  have he : (v' ≫ i.hom.hom) * t * (v' ≫ i.hom.hom)⁻¹ * t⁻¹ = u := by
    have h := congrArg (fun z => z ≫ i.hom.hom) hv'
    simpa only [i, Affine.unipotentCommutator_apply, toUnit_unit, Category.id_comp, hu'] using h
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using congrArg (fun z => z * t) he

end Langlands.GroupScheme.Dynamic
