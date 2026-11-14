import Langlands.GroupScheme.Dynamic.BaseTripleCell
import Langlands.GroupScheme.OpenCellGluing
import Langlands.GroupScheme.HenselianParabolicCovering
import Langlands.GroupScheme.SmoothConnectedGeometryProof

/-! # Integral section generation from dynamic open cells -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.GroupScheme

namespace CellGluing

variable {R : Type u} [CommRing R] [HenselianLocalRing R]
    [IsSepClosed (IsLocalRing.ResidueField R)]
    {G : GroupScheme (Spec (CommRingCat.of R))}
    [Smooth G.X.hom] [GeometricallyIrreducible G.X.hom]
    {C : Over (Spec (CommRingCat.of R))} (j : C ⟶ G.X)
    [IsOpenImmersion j.left]

/-- The image of the actual integral sections of an open cell. Multiplication
on the cell itself is not required. -/
def cellSectionImage : Set (rationalPoints G) :=
  Set.range (fun c : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ C => c ≫ j)

/-- Over a strictly Henselian local ring, every group section is a product
of two sections of any open cell containing the identity. -/
theorem exists_cellSection_product
    (e : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ C) (he : e ≫ j = 1)
    (g : rationalPoints G) :
    ∃ a b : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ C,
      (a ≫ j) * (b ≫ j) = g := by
  let V := splitOpen j g
  have hV : Covers V := covers_splitOpen e he g
  have hπ : Smooth (coverπ V).left := inferInstance
  have hπs : Surjective (coverπ V).left := hV
  have hw : (coverObj V).hom = (coverπ V).left := by
    simpa using (Over.w (coverπ V)).symm
  have : Smooth (coverObj V).hom := hw ▸ hπ
  have : Surjective (coverObj V).hom := hw ▸ hπs
  obtain ⟨s⟩ := HenselianParabolicCovering.nonempty_ringPoint_of_smooth R (coverObj V)
  let s₀ : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ coverObj V :=
    (Langlands.AlgebraicGeometry.PointTopology.rationalPointEquiv R (coverObj V)).symm s
  have hs : s₀ ≫ coverπ V = 𝟙 _ := toUnit_unique _ _
  let h : rationalPoints G := s₀ ≫ coverPt V
  have hh : InCell j h := (inCell_coverPt (j := j) (y := g) le_rfl).comp s₀
  have hgh : InCell j (g * h⁻¹) := by
    have ht := (inCell_coverπ_mul_inv (j := j) (y := g) le_rfl).comp s₀
    change InCell j (s₀ ≫ ((coverπ V ≫ g) * (coverPt V)⁻¹)) at ht
    rw [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, hs,
      Category.id_comp] at ht
    exact ht
  refine ⟨coord (g * h⁻¹) hgh, coord h hh, ?_⟩
  rw [coord_comp, coord_comp, inv_mul_cancel_right]

/-- The product of the section image of the cell with itself is the whole
group of integral sections. -/
theorem cellSectionImage_mul_self
    (e : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ C) (he : e ≫ j = 1) :
    cellSectionImage j * cellSectionImage j = Set.univ := by
  apply Set.eq_univ_of_forall
  intro g
  obtain ⟨a, b, hab⟩ := exists_cellSection_product j e he g
  exact ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, hab⟩

/-- A subgroup containing all actual cell sections contains all integral
group sections. -/
theorem eq_top_of_cellSections
    (e : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ C) (he : e ≫ j = 1)
    (K : Subgroup (rationalPoints G))
    (hK : ∀ c : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ C, c ≫ j ∈ K) :
    K = ⊤ := by
  apply top_unique
  intro g _
  obtain ⟨a, b, hab⟩ := exists_cellSection_product j e he g
  rw [← hab]
  exact K.mul_mem (hK a) (hK b)

end CellGluing

namespace Dynamic

variable {R : Type u} [CommRing R] [HenselianLocalRing R]
    [IsSepClosed (IsLocalRing.ResidueField R)]
    {G : GroupScheme (Spec (CommRingCat.of R))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [GeometricallyIrreducible G.X.hom]

/-- Over a strictly Henselian local ring, the actual sections of the two
dynamic radicals and the dynamic centralizer generate all group sections. -/
theorem eq_top_of_dynamic_section_ranges
    (χ : (Gm (Spec (CommRingCat.of R))).toGrp ⟶ G)
    {M Z U : GroupScheme (Spec (CommRingCat.of R))}
    {iM : M ⟶ G} {iZ : Z ⟶ G} {iU : U ⟶ G}
    (hM : (unipotent (CommGroupScheme.groupHom
      (Gm.powerHom _ (-1)) ≫ χ)).IsRepresentedBy iM)
    (hZ : (centralizer χ).IsRepresentedBy iZ)
    (hU : (unipotent χ).IsRepresentedBy iU)
    (K : Subgroup (rationalPoints G))
    (hKM : (rationalPoints.map iM).range ≤ K)
    (hKZ : (rationalPoints.map iZ).range ≤ K)
    (hKU : (rationalPoints.map iU).range ≤ K) :
    K = ⊤ := by
  let j := tripleCellMultiplication iM iZ iU
  have : IsOpenImmersion j.left :=
    isOpenImmersion_tripleCellMultiplication_overBase χ hM hZ hU
  let e : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ M.X ⊗ (Z.X ⊗ U.X) :=
    lift 1 (lift 1 1)
  have he : e ≫ j = 1 := by
    rw [lift_tripleCellMultiplication]
    simp only [MonObj.one_comp, one_mul]
  apply CellGluing.eq_top_of_cellSections j e he K
  intro c
  have hc : c = lift (c ≫ fst _ _)
      (lift (c ≫ snd _ _ ≫ fst _ _) (c ≫ snd _ _ ≫ snd _ _)) := by
    ext <;> simp
  rw [hc, lift_tripleCellMultiplication]
  exact K.mul_mem (hKM ⟨_, rfl⟩) (K.mul_mem (hKZ ⟨_, rfl⟩) (hKU ⟨_, rfl⟩))

end Dynamic
end Langlands.GroupScheme
