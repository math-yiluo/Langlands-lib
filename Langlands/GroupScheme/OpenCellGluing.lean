import Langlands.GroupScheme.OpenCellIsomorphism
import Langlands.GroupScheme.Multiplicative

/-! # Isomorphisms of group schemes from compatible open cells -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.CellGluing

variable {S : Scheme.{u}}

/-! ### Points in an open cell -/

section Cell

variable {G : GroupScheme S} {C : Over S} (j : C ⟶ G.X)

/-- A point of `G` lies in the cell `j` when its image is contained in the image of `j`. -/
def InCell {Z : Over S} (x : Z ⟶ G.X) : Prop :=
  Set.range x.left ⊆ Set.range j.left

variable {j}

theorem InCell.comp {Z Z' : Over S} (a : Z' ⟶ Z) {x : Z ⟶ G.X} (hx : InCell j x) :
    InCell j (a ≫ x) := by
  rintro _ ⟨z, rfl⟩
  exact hx ⟨a.left z, by simp⟩

variable (j) in
theorem inCell_comp {Z : Over S} (c : Z ⟶ C) : InCell j (c ≫ j) := by
  rintro _ ⟨z, rfl⟩
  exact ⟨c.left z, by simp⟩

theorem InCell.congr {Z : Over S} {x y : Z ⟶ G.X} (hx : InCell j x) (h : x = y) :
    InCell j y := h ▸ hx

theorem inCell_one_of_comp_eq_one (e : 𝟙_ (Over S) ⟶ C) (he : e ≫ j = 1) (Z : Over S) :
    InCell j (1 : Z ⟶ G.X) :=
  (inCell_comp j (toUnit Z ≫ e)).congr (by rw [Category.assoc, he, MonObj.comp_one])

variable [IsOpenImmersion j.left]

instance mono_cell : Mono j := Over.mono_of_mono_left j

/-- The cell coordinate of a point lying in the cell. -/
def coord {Z : Over S} (x : Z ⟶ G.X) (hx : InCell j x) : Z ⟶ C := OpenCell.lift j x hx

@[reassoc (attr := simp)]
theorem coord_comp {Z : Over S} (x : Z ⟶ G.X) (hx : InCell j x) : coord x hx ≫ j = x :=
  OpenCell.lift_comp j x hx

theorem coord_eq_of_comp_eq {Z : Over S} (x : Z ⟶ G.X) (hx : InCell j x) (c : Z ⟶ C)
    (hc : c ≫ j = x) : coord x hx = c :=
  (cancel_mono j).mp (by rw [coord_comp, hc])

theorem comp_coord {Z Z' : Over S} (a : Z' ⟶ Z) (x : Z ⟶ G.X) (hx : InCell j x) :
    a ≫ coord x hx = coord (a ≫ x) (hx.comp a) :=
  (coord_eq_of_comp_eq _ _ _ (by rw [Category.assoc, coord_comp])).symm

theorem coord_congr {Z : Over S} {x y : Z ⟶ G.X} (hx : InCell j x) (hy : InCell j y)
    (h : x = y) : coord x hx = coord y hy := by
  subst h
  rfl

end Cell

/-! ### Fppf covers by auxiliary points -/

section Cover

variable {G : GroupScheme S} {Z : Over S}

/-- The open subscheme of `Z ⊗ G` indexed by an open `V`. -/
abbrev coverObj (V : (Z ⊗ G.X).left.Opens) : Over S := Over.mk (V.ι ≫ (Z ⊗ G.X).hom)

/-- The inclusion of the open subscheme. -/
def coverι (V : (Z ⊗ G.X).left.Opens) : coverObj V ⟶ Z ⊗ G.X := Over.homMk V.ι rfl

/-- The projection of the open subscheme to `Z`. -/
def coverπ (V : (Z ⊗ G.X).left.Opens) : coverObj V ⟶ Z := coverι V ≫ fst Z G.X

/-- The universal auxiliary point on the open subscheme. -/
def coverPt (V : (Z ⊗ G.X).left.Opens) : coverObj V ⟶ G.X := coverι V ≫ snd Z G.X

@[reassoc (attr := simp)]
theorem coverι_fst (V : (Z ⊗ G.X).left.Opens) : coverι V ≫ fst Z G.X = coverπ V := rfl

@[reassoc (attr := simp)]
theorem coverι_snd (V : (Z ⊗ G.X).left.Opens) : coverι V ≫ snd Z G.X = coverPt V := rfl

/-- A point of `Z ⊗ G` landing in `V` factors through the open subscheme. -/
def coverLift {Z' : Over S} (V : (Z ⊗ G.X).left.Opens) (s : Z' ⟶ Z ⊗ G.X)
    (hs : Set.range s.left ⊆ V) : Z' ⟶ coverObj V :=
  Over.homMk (IsOpenImmersion.lift V.ι s.left (by rw [V.range_ι]; exact hs)) (by
    change _ ≫ V.ι ≫ _ = _
    rw [← Category.assoc, IsOpenImmersion.lift_fac]
    exact Over.w s)

@[reassoc (attr := simp)]
theorem coverLift_ι {Z' : Over S} (V : (Z ⊗ G.X).left.Opens) (s : Z' ⟶ Z ⊗ G.X)
    (hs : Set.range s.left ⊆ V) : coverLift V s hs ≫ coverι V = s :=
  Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)

theorem coverπ_left (V : (Z ⊗ G.X).left.Opens) :
    (coverπ V).left = V.ι ≫ (fst Z G.X).left := rfl

/-- An open whose projection to `Z` is surjective. -/
def Covers (V : (Z ⊗ G.X).left.Opens) : Prop := Surjective (V.ι ≫ (fst Z G.X).left)

theorem covers_of_section (V : (Z ⊗ G.X).left.Opens) (s : Z ⟶ Z ⊗ G.X)
    (hs : s ≫ fst Z G.X = 𝟙 Z) (hV : Set.range s.left ⊆ V) : Covers V := by
  refine ⟨fun z => ⟨⟨s.left z, hV ⟨z, rfl⟩⟩, ?_⟩⟩
  change (fst Z G.X).left (s.left z) = z
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hs]
  rfl

theorem Covers.inf [Smooth G.X.hom] [GeometricallyIrreducible G.X.hom]
    {V W : (Z ⊗ G.X).left.Opens} (hV : Covers V) (hW : Covers W) : Covers (V ⊓ W) := by
  have : GeometricallyIrreducible (fst Z G.X).left :=
    inferInstanceAs (GeometricallyIrreducible (pullback.fst Z.hom G.X.hom))
  have : Smooth (fst Z G.X).left := inferInstanceAs (Smooth (pullback.fst Z.hom G.X.hom))
  have : Surjective (V.ι ≫ (fst Z G.X).left) := hV
  have : Surjective (W.ι ≫ (fst Z G.X).left) := hW
  exact OpenCell.surjective_intersection (fst Z G.X).left V W

instance smooth_coverπ [Smooth G.X.hom] (V : (Z ⊗ G.X).left.Opens) :
    Smooth (coverπ V).left := by
  have : Smooth (fst Z G.X).left := inferInstanceAs (Smooth (pullback.fst Z.hom G.X.hom))
  rw [coverπ_left]
  infer_instance

theorem Covers.effectiveEpi [Smooth G.X.hom] {V : (Z ⊗ G.X).left.Opens} (hV : Covers V) :
    EffectiveEpi (coverπ V).left := by
  have : Surjective (coverπ V).left := hV
  infer_instance

theorem Covers.epi [Smooth G.X.hom] {V : (Z ⊗ G.X).left.Opens} (hV : Covers V) :
    Epi (coverπ V) := by
  have := hV.effectiveEpi
  exact Over.epi_of_epi_left _

end Cover

/-! ### Cell conditions on auxiliary points -/

section CellCover

variable {G : GroupScheme S} {C : Over S} (j : C ⟶ G.X) [IsOpenImmersion j.left] {Z : Over S}

/-- The open of `Z ⊗ G` where the morphism `F` lands in the cell. -/
def cellOpen (F : Z ⊗ G.X ⟶ G.X) : (Z ⊗ G.X).left.Opens := F.left ⁻¹ᵁ j.left.opensRange

variable {j}

theorem inCell_of_le {F : Z ⊗ G.X ⟶ G.X} {V : (Z ⊗ G.X).left.Opens} (hV : V ≤ cellOpen j F) :
    InCell j (coverι V ≫ F) := by
  rintro _ ⟨w, rfl⟩
  exact hV w.2

theorem range_subset_cellOpen {Z' : Over S} {F : Z ⊗ G.X ⟶ G.X} {s : Z' ⟶ Z ⊗ G.X}
    (h : InCell j (s ≫ F)) : Set.range s.left ⊆ cellOpen j F := by
  rintro _ ⟨z, rfl⟩
  exact h ⟨z, rfl⟩

theorem covers_cellOpen (F : Z ⊗ G.X ⟶ G.X) (s : Z ⟶ Z ⊗ G.X) (hs : s ≫ fst Z G.X = 𝟙 Z)
    (hF : InCell j (s ≫ F)) : Covers (cellOpen j F) :=
  covers_of_section _ s hs (by
    rintro _ ⟨z, rfl⟩
    exact hF ⟨z, rfl⟩)

theorem covers_cellOpen_of_eq_one (e : 𝟙_ (Over S) ⟶ C) (he : e ≫ j = 1)
    (F : Z ⊗ G.X ⟶ G.X) (s : Z ⟶ Z ⊗ G.X) (hs : s ≫ fst Z G.X = 𝟙 Z) (hF : s ≫ F = 1) :
    Covers (cellOpen j F) :=
  covers_cellOpen F s hs ((inCell_one_of_comp_eq_one e he Z).congr hF.symm)

end CellCover

/-! ### The map on cell points -/

section CellMap

variable {G H : GroupScheme S} {C : Over S} (j : C ⟶ G.X) [IsOpenImmersion j.left]
  (ν : C ⟶ H.X)

/-- Cell multiplication in `G` implies the same relation in `H`. -/
def CellCompatible : Prop :=
  ∀ (Z : Over S) (x y c : Z ⟶ C), (x ≫ j) * (y ≫ j) = c ≫ j → (x ≫ ν) * (y ≫ ν) = c ≫ ν

open Classical in
/-- A point in the cell goes through its cell coordinate and `ν`; any other point goes
to `1`, a junk value that the lemmas below never use. -/
def cellMap {Z : Over S} (x : Z ⟶ G.X) : Z ⟶ H.X :=
  if hx : InCell j x then coord x hx ≫ ν else 1

variable {j ν}

theorem cellMap_of_inCell {Z : Over S} {x : Z ⟶ G.X} (hx : InCell j x) :
    cellMap j ν x = coord x hx ≫ ν := by
  simp [cellMap, hx]

@[simp]
theorem cellMap_comp_cell {Z : Over S} (c : Z ⟶ C) : cellMap j ν (c ≫ j) = c ≫ ν := by
  rw [cellMap_of_inCell (inCell_comp j c), coord_eq_of_comp_eq _ _ c rfl]

theorem comp_cellMap {Z Z' : Over S} (a : Z' ⟶ Z) {x : Z ⟶ G.X} (hx : InCell j x) :
    a ≫ cellMap j ν x = cellMap j ν (a ≫ x) := by
  rw [cellMap_of_inCell hx, cellMap_of_inCell (hx.comp a), ← Category.assoc, comp_coord]

variable (hc : CellCompatible j ν) (e : 𝟙_ (Over S) ⟶ C) (he : e ≫ j = 1)
include hc

theorem cellMap_mul {Z : Over S} {x y : Z ⟶ G.X} (hx : InCell j x) (hy : InCell j y)
    (hxy : InCell j (x * y)) : cellMap j ν (x * y) = cellMap j ν x * cellMap j ν y := by
  rw [cellMap_of_inCell hx, cellMap_of_inCell hy, cellMap_of_inCell hxy]
  exact (hc _ _ _ _ (by rw [coord_comp, coord_comp, coord_comp])).symm

include he in
theorem cellMap_one (Z : Over S) : cellMap j ν (1 : Z ⟶ G.X) = 1 := by
  have h1 := inCell_one_of_comp_eq_one e he Z
  have := cellMap_mul hc h1 h1 (by rwa [mul_one])
  rw [mul_one] at this
  exact mul_eq_left.mp this.symm

include he in
theorem cellMap_inv {Z : Over S} {x : Z ⟶ G.X} (hx : InCell j x) (hx' : InCell j x⁻¹) :
    cellMap j ν x⁻¹ = (cellMap j ν x)⁻¹ := by
  have h1 := inCell_one_of_comp_eq_one e he Z
  have := cellMap_mul hc hx hx' (by rwa [mul_inv_cancel])
  rw [mul_inv_cancel, cellMap_one hc e he] at this
  exact eq_inv_of_mul_eq_one_right this.symm

/-- Moving an auxiliary cell point from one side to the other. -/
theorem cellMap_split {Z : Over S} {y h g : Z ⟶ G.X} (hh : InCell j h) (hg : InCell j g)
    (hhg : InCell j (h * g)) (hyh : InCell j (y * h⁻¹)) (hyg : InCell j (y * g)) :
    cellMap j ν (y * h⁻¹) * cellMap j ν h = cellMap j ν (y * g) * (cellMap j ν g)⁻¹ := by
  have hyhg : y * h⁻¹ * (h * g) = y * g := by group
  have h1 := cellMap_mul hc hh hg hhg
  have h2 := cellMap_mul hc hyh hhg (hyg.congr hyhg.symm)
  rw [hyhg, h1] at h2
  rw [h2]
  group

end CellMap

/-! ### Splitting a point into two cell points, fppf-locally -/

section Split

variable {G : GroupScheme S} {C : Over S} (j : C ⟶ G.X) [IsOpenImmersion j.left]
  {Z : Over S}

/-- The open of auxiliary points `g` with `g` and `y g⁻¹` in the cell. -/
def splitOpen (y : Z ⟶ G.X) : (Z ⊗ G.X).left.Opens :=
  cellOpen j (snd Z G.X) ⊓ cellOpen j ((fst Z G.X ≫ y) * (snd Z G.X)⁻¹)

variable {j}

theorem covers_splitOpen [Smooth G.X.hom] [GeometricallyIrreducible G.X.hom]
    (e : 𝟙_ (Over S) ⟶ C) (he : e ≫ j = 1) (y : Z ⟶ G.X) : Covers (splitOpen j y) :=
  (covers_cellOpen_of_eq_one e he _ (lift (𝟙 Z) 1) (lift_fst _ _) (lift_snd _ _)).inf
    (covers_cellOpen_of_eq_one e he _ (lift (𝟙 Z) y) (lift_fst _ _)
      (by simp [MonObj.comp_mul, GrpObj.comp_inv]))

theorem inCell_coverPt {y : Z ⟶ G.X} {V : (Z ⊗ G.X).left.Opens} (hV : V ≤ splitOpen j y) :
    InCell j (coverPt V) :=
  inCell_of_le (hV.trans inf_le_left)

theorem inCell_coverπ_mul_inv {y : Z ⟶ G.X} {V : (Z ⊗ G.X).left.Opens}
    (hV : V ≤ splitOpen j y) : InCell j ((coverπ V ≫ y) * (coverPt V)⁻¹) :=
  (inCell_of_le (hV.trans inf_le_right)).congr (by simp [MonObj.comp_mul, GrpObj.comp_inv])

theorem range_subset_splitOpen {Z' : Over S} {y : Z ⟶ G.X} {s : Z' ⟶ Z ⊗ G.X}
    (h₁ : InCell j (s ≫ snd Z G.X)) (h₂ : InCell j ((s ≫ fst Z G.X ≫ y) * (s ≫ snd Z G.X)⁻¹)) :
    Set.range s.left ⊆ splitOpen j y :=
  Set.subset_inter (range_subset_cellOpen h₁)
    (range_subset_cellOpen (h₂.congr (by simp [MonObj.comp_mul, GrpObj.comp_inv])))

/-- Two morphisms of group schemes agreeing on the cell are equal. -/
theorem hom_ext_cell [Smooth G.X.hom] [GeometricallyIrreducible G.X.hom]
    (e : 𝟙_ (Over S) ⟶ C) (he : e ≫ j = 1) {K : GroupScheme S} {f f' : G ⟶ K}
    (h : j ≫ f.hom.hom = j ≫ f'.hom.hom) : f = f' := by
  have hcell : ∀ {T : Over S} (a : T ⟶ G.X), InCell j a → a ≫ f.hom.hom = a ≫ f'.hom.hom :=
    fun a ha => by rw [← coord_comp a ha, Category.assoc, h, Category.assoc]
  refine hom_ext_points fun T x => ?_
  have hV := covers_splitOpen e he x
  have := hV.epi
  apply (cancel_epi (coverπ (splitOpen j x))).mp
  have hx : coverπ (splitOpen j x) ≫ x =
      ((coverπ (splitOpen j x) ≫ x) * (coverPt (splitOpen j x))⁻¹) *
        coverPt (splitOpen j x) := by group
  rw [← Category.assoc, ← Category.assoc, hx, MonObj.mul_comp _ _ f.hom.hom,
    MonObj.mul_comp _ _ f'.hom.hom, hcell _ (inCell_coverπ_mul_inv le_rfl),
    hcell _ (inCell_coverPt le_rfl)]

end Split

/-! ### Independence of the auxiliary point -/

section Indep

variable {G H : GroupScheme S} [Smooth G.X.hom] [GeometricallyIrreducible G.X.hom]
  {C : Over S} {j : C ⟶ G.X} [IsOpenImmersion j.left] {ν : C ⟶ H.X}
  (hc : CellCompatible j ν) (e : 𝟙_ (Over S) ⟶ C) (he : e ≫ j = 1)
include hc e he

/-- The value `φ(y h⁻¹) φ(h)` does not depend on the cell point `h`. -/
theorem cellMap_indep {Z : Over S} {y h h' : Z ⟶ G.X} (hh : InCell j h)
    (hyh : InCell j (y * h⁻¹)) (hh' : InCell j h') (hyh' : InCell j (y * h'⁻¹)) :
    cellMap j ν (y * h⁻¹) * cellMap j ν h = cellMap j ν (y * h'⁻¹) * cellMap j ν h' := by
  let V := cellOpen j (snd Z G.X) ⊓ cellOpen j ((fst Z G.X ≫ h) * snd Z G.X) ⊓
    cellOpen j ((fst Z G.X ≫ h') * snd Z G.X) ⊓ cellOpen j ((fst Z G.X ≫ y) * snd Z G.X)
  have hV : Covers V :=
    (((covers_cellOpen_of_eq_one e he _ (lift (𝟙 Z) 1) (lift_fst _ _) (lift_snd _ _)).inf
      (covers_cellOpen_of_eq_one e he _ (lift (𝟙 Z) h⁻¹) (lift_fst _ _)
        (by simp [MonObj.comp_mul]))).inf
      (covers_cellOpen_of_eq_one e he _ (lift (𝟙 Z) h'⁻¹) (lift_fst _ _)
        (by simp [MonObj.comp_mul]))).inf
      (covers_cellOpen_of_eq_one e he _ (lift (𝟙 Z) y⁻¹) (lift_fst _ _)
        (by simp [MonObj.comp_mul]))
  have := hV.epi
  apply (cancel_epi (coverπ V)).mp
  have hg : InCell j (coverPt V) :=
    inCell_of_le (inf_le_left.trans (inf_le_left.trans inf_le_left))
  have hhg : InCell j ((coverπ V ≫ h) * coverPt V) :=
    (inCell_of_le (V := V) (inf_le_left.trans (inf_le_left.trans inf_le_right))).congr
      (by simp [MonObj.comp_mul])
  have hh'g : InCell j ((coverπ V ≫ h') * coverPt V) :=
    (inCell_of_le (V := V) (inf_le_left.trans inf_le_right)).congr (by simp [MonObj.comp_mul])
  have hyg : InCell j ((coverπ V ≫ y) * coverPt V) :=
    (inCell_of_le (V := V) inf_le_right).congr (by simp [MonObj.comp_mul])
  have e₁ : coverπ V ≫ (y * h⁻¹) = (coverπ V ≫ y) * (coverπ V ≫ h)⁻¹ := by
    rw [MonObj.comp_mul, GrpObj.comp_inv]
  have e₂ : coverπ V ≫ (y * h'⁻¹) = (coverπ V ≫ y) * (coverπ V ≫ h')⁻¹ := by
    rw [MonObj.comp_mul, GrpObj.comp_inv]
  rw [MonObj.comp_mul, MonObj.comp_mul, comp_cellMap _ hyh, comp_cellMap _ hh,
    comp_cellMap _ hyh', comp_cellMap _ hh', e₁, e₂,
    cellMap_split hc (hh.comp _) hg hhg ((hyh.comp _).congr e₁) hyg,
    cellMap_split hc (hh'.comp _) hg hh'g ((hyh'.comp _).congr e₂) hyg]

end Indep

/-! ### Descent of the cell map to the whole group -/

section Descent

variable {G H : GroupScheme S} {C : Over S} {j : C ⟶ G.X} [IsOpenImmersion j.left]
  {ν : C ⟶ H.X}

variable (j) in
/-- The universal split open, for the identity point of `G`. -/
abbrev univOpen : (G.X ⊗ G.X).left.Opens := splitOpen j (𝟙 G.X)

theorem inCell_univ_mul_inv :
    InCell j (coverπ (univOpen j) * (coverPt (univOpen j))⁻¹) :=
  (inCell_coverπ_mul_inv le_rfl).congr (by rw [Category.comp_id])

variable (j ν) in
/-- The map `(y, g) ↦ φ(y g⁻¹) φ(g)` on the universal split open. -/
def univMap : coverObj (univOpen j) ⟶ H.X :=
  cellMap j ν (coverπ (univOpen j) * (coverPt (univOpen j))⁻¹) *
    cellMap j ν (coverPt (univOpen j))

theorem comp_univMap {Z : Over S} (a : Z ⟶ coverObj (univOpen j)) :
    a ≫ univMap j ν = cellMap j ν ((a ≫ coverπ (univOpen j)) * (a ≫ coverPt (univOpen j))⁻¹) *
      cellMap j ν (a ≫ coverPt (univOpen j)) := by
  rw [univMap, MonObj.comp_mul, comp_cellMap _ inCell_univ_mul_inv,
    comp_cellMap _ (inCell_coverPt le_rfl), MonObj.comp_mul, GrpObj.comp_inv]

variable [Smooth G.X.hom] [GeometricallyIrreducible G.X.hom]
  (hc : CellCompatible j ν) (e : 𝟙_ (Over S) ⟶ C) (he : e ≫ j = 1)
include hc e he

/-- The descent condition along the universal split open. -/
theorem univMap_cond {Y : Scheme.{u}} (a b : Y ⟶ (coverObj (univOpen j)).left)
    (hab : a ≫ (coverπ (univOpen j)).left = b ≫ (coverπ (univOpen j)).left) :
    a ≫ (univMap j ν).left = b ≫ (univMap j ν).left := by
  have hw : (coverObj (univOpen j)).hom = (coverπ (univOpen j)).left ≫ G.X.hom :=
    (Over.w (coverπ (univOpen j))).symm
  let Y' : Over S := Over.mk (a ≫ (coverObj (univOpen j)).hom)
  let a' : Y' ⟶ coverObj (univOpen j) := Over.homMk a rfl
  let b' : Y' ⟶ coverObj (univOpen j) := Over.homMk b (by
    change b ≫ _ = a ≫ _
    rw [hw, ← Category.assoc, ← hab, Category.assoc])
  have hq : a' ≫ coverπ (univOpen j) = b' ≫ coverπ (univOpen j) := Over.OverMorphism.ext hab
  have key : a' ≫ univMap j ν = b' ≫ univMap j ν := by
    rw [comp_univMap, comp_univMap, hq]
    exact cellMap_indep hc e he ((inCell_coverPt le_rfl).comp a')
      ((inCell_univ_mul_inv.comp a').congr (by rw [MonObj.comp_mul, GrpObj.comp_inv, hq]))
      ((inCell_coverPt le_rfl).comp b')
      ((inCell_univ_mul_inv.comp b').congr (by rw [MonObj.comp_mul, GrpObj.comp_inv]))
  exact congrArg (fun x => x.left) key

/-- The descended morphism of underlying schemes. -/
def glueLeft : G.X.left ⟶ H.X.left :=
  haveI := (covers_splitOpen e he (𝟙 G.X)).effectiveEpi
  EffectiveEpi.desc (coverπ (univOpen j)).left (univMap j ν).left
    (fun a b hab => univMap_cond hc e he a b hab)

theorem fac_glueLeft : (coverπ (univOpen j)).left ≫ glueLeft hc e he = (univMap j ν).left := by
  have := (covers_splitOpen e he (𝟙 G.X)).effectiveEpi
  exact EffectiveEpi.fac _ _ _

/-- The descended morphism over `S`. -/
def glue : G.X ⟶ H.X :=
  Over.homMk (glueLeft hc e he) (by
    have := (covers_splitOpen e he (𝟙 G.X)).effectiveEpi
    apply (cancel_epi (coverπ (univOpen j)).left).mp
    rw [← Category.assoc, fac_glueLeft, Over.w, Over.w])

theorem coverπ_glue : coverπ (univOpen j) ≫ glue hc e he = univMap j ν :=
  Over.OverMorphism.ext (fac_glueLeft hc e he)

/-- The descended morphism on a point split as `y = (y h⁻¹) h` into cell points. -/
theorem comp_glue {Z : Over S} (y h : Z ⟶ G.X) (hh : InCell j h)
    (hyh : InCell j (y * h⁻¹)) :
    y ≫ glue hc e he = cellMap j ν (y * h⁻¹) * cellMap j ν h := by
  let k := coverLift (univOpen j) (lift y h)
    (range_subset_splitOpen (by rwa [lift_snd]) (by rwa [lift_fst_assoc, Category.comp_id,
      lift_snd]))
  have hk₁ : k ≫ coverπ (univOpen j) = y := by
    rw [← coverι_fst, coverLift_ι_assoc, lift_fst]
  have hk₂ : k ≫ coverPt (univOpen j) = h := by
    rw [← coverι_snd, coverLift_ι_assoc, lift_snd]
  calc y ≫ glue hc e he = (k ≫ coverπ (univOpen j)) ≫ glue hc e he := by rw [hk₁]
    _ = k ≫ univMap j ν := by rw [Category.assoc, coverπ_glue]
    _ = _ := by rw [comp_univMap, hk₁, hk₂]

theorem glue_one (Z : Over S) : (1 : Z ⟶ G.X) ≫ glue hc e he = 1 := by
  have h1 := inCell_one_of_comp_eq_one e he Z
  rw [comp_glue hc e he 1 1 h1 (by rwa [inv_one, mul_one]), inv_one, mul_one,
    cellMap_one hc e he, mul_one]

theorem cell_comp_glue : j ≫ glue hc e he = ν := by
  rw [comp_glue hc e he j 1 (inCell_one_of_comp_eq_one e he C)
    (by simpa using inCell_comp j (𝟙 C)), inv_one, mul_one, cellMap_one hc e he, mul_one]
  simpa using cellMap_comp_cell (j := j) (ν := ν) (𝟙 C)

/-- Right multiplication by a cell point. -/
theorem glue_mul_cell {Z : Over S} (y x : Z ⟶ G.X) (hx : InCell j x) :
    (y * x) ≫ glue hc e he = (y ≫ glue hc e he) * cellMap j ν x := by
  let V := splitOpen j y ⊓ cellOpen j (snd Z G.X * (fst Z G.X ≫ x))
  have hV : Covers V := (covers_splitOpen e he y).inf
    (covers_cellOpen_of_eq_one e he _ (lift (𝟙 Z) x⁻¹) (lift_fst _ _)
      (by simp [MonObj.comp_mul]))
  have := hV.epi
  apply (cancel_epi (coverπ V)).mp
  have hg : InCell j (coverPt V) := inCell_coverPt inf_le_left
  have hyg : InCell j ((coverπ V ≫ y) * (coverPt V)⁻¹) := inCell_coverπ_mul_inv inf_le_left
  have hgx : InCell j (coverPt V * (coverπ V ≫ x)) :=
    (inCell_of_le (V := V) inf_le_right).congr (by simp [MonObj.comp_mul])
  have hx' : InCell j (coverπ V ≫ x) := hx.comp _
  have eq : (coverπ V ≫ y) * (coverπ V ≫ x) * (coverPt V * (coverπ V ≫ x))⁻¹ =
      (coverπ V ≫ y) * (coverPt V)⁻¹ := by group
  rw [← Category.assoc, MonObj.comp_mul, MonObj.comp_mul, ← Category.assoc,
    comp_cellMap _ hx, comp_glue hc e he _ _ hgx (hyg.congr eq.symm), eq,
    comp_glue hc e he _ _ hg hyg, cellMap_mul hc hg hx' hgx, mul_assoc]

/-- The descended morphism is multiplicative on points. -/
theorem glue_mul {Z : Over S} (y y' : Z ⟶ G.X) :
    (y * y') ≫ glue hc e he = (y ≫ glue hc e he) * (y' ≫ glue hc e he) := by
  have hV := covers_splitOpen e he y'
  have := hV.epi
  apply (cancel_epi (coverπ (splitOpen j y'))).mp
  have hg : InCell j (coverPt (splitOpen j y')) := inCell_coverPt le_rfl
  have hyg : InCell j ((coverπ (splitOpen j y') ≫ y') * (coverPt (splitOpen j y'))⁻¹) :=
    inCell_coverπ_mul_inv le_rfl
  have eq : (coverπ (splitOpen j y') ≫ y) * (coverπ (splitOpen j y') ≫ y') =
      ((coverπ (splitOpen j y') ≫ y) *
        ((coverπ (splitOpen j y') ≫ y') * (coverPt (splitOpen j y'))⁻¹)) *
        coverPt (splitOpen j y') := by group
  rw [← Category.assoc, MonObj.comp_mul, MonObj.comp_mul, ← Category.assoc, ← Category.assoc,
    eq, glue_mul_cell hc e he _ _ hg, glue_mul_cell hc e he _ _ hyg,
    comp_glue hc e he (coverπ (splitOpen j y') ≫ y') _ hg hyg, mul_assoc]

/-- The glued homomorphism of group schemes. -/
def glueHom : G ⟶ H :=
  homOfPoints (fun T =>
    { toFun := fun x => x ≫ glue hc e he
      map_one' := glue_one hc e he T
      map_mul' := glue_mul hc e he })
    (fun a x => Category.assoc a x (glue hc e he))

theorem comp_glueHom {T : Over S} (x : T ⟶ G.X) :
    x ≫ (glueHom hc e he).hom.hom = x ≫ glue hc e he :=
  comp_homOfPoints _ (fun a x => Category.assoc a x (glue hc e he)) T x

theorem cell_comp_glueHom : j ≫ (glueHom hc e he).hom.hom = ν := by
  rw [comp_glueHom, cell_comp_glue]

end Descent

/-! ### The isomorphism -/

/-- **Gluing along compatible open cells.** Let `G` and `H` be smooth group schemes over `S`
with geometrically irreducible fibres, and let `j : C ⟶ G` and `ν : C ⟶ H` be open
immersions from a common scheme `C` with a point `e` mapping to the identity in both. If a
relation `x y = c` between cell points holds in `G` exactly when it holds in `H`, then there
is an isomorphism `G ≅ H` restricting to `ν` on the cell. -/
theorem exists_iso_of_cellCompatible {G H : GroupScheme S} [Smooth G.X.hom]
    [GeometricallyIrreducible G.X.hom] [Smooth H.X.hom] [GeometricallyIrreducible H.X.hom]
    {C : Over S} (j : C ⟶ G.X) (ν : C ⟶ H.X) [IsOpenImmersion j.left]
    [IsOpenImmersion ν.left] (e : 𝟙_ (Over S) ⟶ C) (he : e ≫ j = 1) (he' : e ≫ ν = 1)
    (hc : CellCompatible j ν) (hc' : CellCompatible ν j) :
    ∃ ψ : G ≅ H, j ≫ ψ.hom.hom.hom = ν := by
  refine ⟨⟨glueHom hc e he, glueHom hc' e he', ?_, ?_⟩, cell_comp_glueHom hc e he⟩
  · apply hom_ext_cell e he
    rw [Grp.comp_hom_hom, ← Category.assoc, cell_comp_glueHom, cell_comp_glueHom,
      Grp.id_hom_hom, Category.comp_id]
  · apply hom_ext_cell e he'
    rw [Grp.comp_hom_hom, ← Category.assoc, cell_comp_glueHom, cell_comp_glueHom,
      Grp.id_hom_hom, Category.comp_id]

end Langlands.GroupScheme.CellGluing
