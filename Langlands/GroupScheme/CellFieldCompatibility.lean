import Langlands.GroupScheme.OpenCellGluing

/-! # Cell compatibility from field-valued points

`CellGluing.CellCompatible j ν` asks that a multiplication relation between points of an open
cell `j : C ⟶ G` in `G` also holds after replacing `j` by `ν : C ⟶ H`, for points over every
test scheme. If the scheme underlying `C ⊗ C` is reduced and `H` is separated, it is enough to
check this for points over fields. The relation is universal over the open subscheme of `C ⊗ C`
where the product of the two cell points stays in the cell, and two maps from a reduced scheme to
a separated scheme agree once they agree at all residue-field points.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.CellFieldCompatibility

open CellGluing

variable {S : Scheme.{u}} {G H : GroupScheme S} {C : Over S} (j : C ⟶ G.X) (ν : C ⟶ H.X)

/-- The relation of `CellGluing.CellCompatible`, required only for points over a field. -/
def FieldCompatible : Prop :=
  ∀ (K : Type u) [Field K] (s : Spec (CommRingCat.of K) ⟶ S) (x y c : Over.mk s ⟶ C),
    (x ≫ j) * (y ≫ j) = c ≫ j → (x ≫ ν) * (y ≫ ν) = c ≫ ν

/-- The product of the two universal cell points on `C ⊗ C`. -/
def prodMap : C ⊗ C ⟶ G.X := (fst C C ≫ j) * (snd C C ≫ j)

variable [IsOpenImmersion j.left]

/-- The open subscheme of `C ⊗ C` where the product of the two cell points lies in the cell. -/
def prodOpen : (C ⊗ C).left.Opens := (prodMap j).left ⁻¹ᵁ j.left.opensRange

/-- The open subscheme `prodOpen j` as an object over `S`. -/
abbrev prodObj : Over S := Over.mk ((prodOpen j).ι ≫ (C ⊗ C).hom)

/-- The inclusion of `prodObj j` into `C ⊗ C`. -/
def prodι : prodObj j ⟶ C ⊗ C := Over.homMk (prodOpen j).ι rfl

variable {j}

theorem inCell_prodι : InCell j (prodι j ≫ prodMap j) := by
  rintro _ ⟨z, rfl⟩
  obtain ⟨c, hc⟩ := z.2
  exact ⟨c, by rw [hc]; rfl⟩

/-- A pair of cell points whose product lies in the cell factors through `prodObj j`. -/
def prodLift {Z : Over S} (q : Z ⟶ C ⊗ C) (hq : InCell j (q ≫ prodMap j)) : Z ⟶ prodObj j :=
  Over.homMk (IsOpenImmersion.lift (prodOpen j).ι q.left (by
    rw [(prodOpen j).range_ι]
    rintro _ ⟨z, rfl⟩
    exact hq ⟨z, rfl⟩)) (by
    change _ ≫ (prodOpen j).ι ≫ _ = _
    rw [← Category.assoc, IsOpenImmersion.lift_fac]
    exact Over.w q)

@[reassoc (attr := simp)]
theorem prodLift_ι {Z : Over S} (q : Z ⟶ C ⊗ C) (hq : InCell j (q ≫ prodMap j)) :
    prodLift q hq ≫ prodι j = q :=
  Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)

/-- The cell coordinate of the product on `prodObj j`. -/
def prodCoord : prodObj j ⟶ C := coord (prodι j ≫ prodMap j) inCell_prodι

@[reassoc (attr := simp)]
theorem prodCoord_comp : prodCoord ≫ j = prodι j ≫ prodMap j := coord_comp _ _

/-- If the relation holds universally on `prodObj j`, the cells are compatible. -/
theorem cellCompatible_of_universal
    (h : (prodι j ≫ fst C C ≫ ν) * (prodι j ≫ snd C C ≫ ν) = prodCoord ≫ ν) :
    CellCompatible j ν := by
  intro Z x y c hxy
  have hq : lift x y ≫ prodMap j = c ≫ j := by
    rw [prodMap, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc, hxy]
  have hin : InCell j (lift x y ≫ prodMap j) := (inCell_comp j c).congr hq.symm
  have hc : prodLift (lift x y) hin ≫ prodCoord = c := by
    apply (cancel_mono j).mp
    rw [Category.assoc, prodCoord_comp, prodLift_ι_assoc, hq]
  have := congrArg (prodLift (lift x y) hin ≫ ·) h
  simp only [MonObj.comp_mul, prodLift_ι_assoc, lift_fst_assoc, lift_snd_assoc] at this
  rw [this, ← Category.assoc, hc]

/-- **Cell compatibility from field points.** If `C ⊗ C` is reduced and `H` is separated,
the relation of `CellGluing.CellCompatible` follows from its instances over fields. -/
theorem cellCompatible_of_fieldCompatible [IsReduced (C ⊗ C).left] [IsSeparated H.X.hom]
    (h : FieldCompatible j ν) : CellCompatible j ν := by
  have : IsReduced (prodObj j).left := inferInstanceAs (IsReduced (prodOpen j))
  apply cellCompatible_of_universal
  apply Over.OverMorphism.ext
  refine ext_of_fromSpecResidueField_eq _ _ H.X.hom Set.univ dense_univ ?_
    (by simp only [Over.w])
  intro w _
  let K := (prodObj j).left.residueField w
  let s : Spec (CommRingCat.of K) ⟶ S := (prodObj j).left.fromSpecResidueField w ≫ (prodObj j).hom
  let t : Over.mk s ⟶ prodObj j := Over.homMk ((prodObj j).left.fromSpecResidueField w) rfl
  have key := h K s (t ≫ prodι j ≫ fst C C) (t ≫ prodι j ≫ snd C C) (t ≫ prodCoord) (by
    simp only [Category.assoc, prodCoord_comp, prodMap, MonObj.comp_mul])
  simp only [Category.assoc] at key
  rw [← MonObj.comp_mul] at key
  exact congrArg CommaMorphism.left key

end Langlands.GroupScheme.CellFieldCompatibility
