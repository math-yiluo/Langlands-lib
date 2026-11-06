import Langlands.GroupScheme.Reductive.SplitRankOneRootCellReduction
import Langlands.GroupScheme.Reductive.RankOneCellData
import Langlands.GroupScheme.Reductive.SplitRankOneRootCellStatement
import Langlands.GroupScheme.InnerAutomorphismHom
import Langlands.GroupScheme.Dynamic.ConnectedProof

/-! # Points of the additive group, character values and the open cell

Supporting notation for the proof of `SplitRankOneRootCellStatement`: points `gpt x` of `𝔾ₐ`,
values `cu χ t` of characters as units, and a structure `CellData` bundling a torus `T ⊆ G`,
two root groups `xp` and `xm` on which `T` acts through `α` and `-α`, and the open immersion
of the cell `xm(Y) t xp(X)`. The results are elementary identities for these points, the
uniqueness of cell coordinates, and criteria for a point to lie in the cell. -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace RankOneRootCellRelation

variable {k : Type u} [Field k]

/-- The additive group `𝔾ₐ` over `k`. -/
abbrev Ga (k : Type u) [Field k] : GroupScheme (Spec (CommRingCat.of k)) :=
  RootCell.Ga k

/-! ### Points of the additive group -/

section Additive

variable {Z W : Over (Spec (CommRingCat.of k))}

/-- The point of `𝔾ₐ` with coordinate `x`. -/
abbrev gpt (x : Γ(Z.left, ⊤)) : Z ⟶ (Ga k).X :=
  RootCell.pt x

theorem coordinates_gpt (x : Γ(Z.left, ⊤)) (j : Fin 1) :
    (VectorGroup.coordinates (CommRingCat.of k) 1 Z (gpt x)).toAdd j = x := by
  rw [gpt, RootCell.pt, MulEquiv.apply_symm_apply, toAdd_ofAdd]

theorem eq_gpt (a : Z ⟶ (Ga k).X) :
    a = gpt ((VectorGroup.coordinates (CommRingCat.of k) 1 Z a).toAdd 0) :=
  VectorGroup.points_ext fun j => by rw [coordinates_gpt, Subsingleton.elim j 0]

theorem gpt_injective : Function.Injective (gpt (k := k) (Z := Z)) := fun x y h => by
  have := congrArg (fun a => (VectorGroup.coordinates (CommRingCat.of k) 1 Z a).toAdd 0) h
  simpa only [coordinates_gpt] using this

theorem gpt_add (x y : Γ(Z.left, ⊤)) : (gpt (x + y) : Z ⟶ (Ga k).X) = gpt x * gpt y :=
  VectorGroup.points_ext fun j => by
    rw [VectorGroup.coordinates_mul, Pi.add_apply, coordinates_gpt, coordinates_gpt,
      coordinates_gpt]

theorem gpt_zero : (gpt (0 : Γ(Z.left, ⊤)) : Z ⟶ (Ga k).X) = 1 :=
  VectorGroup.points_ext fun j => by
    rw [coordinates_gpt, map_one, toAdd_one, Pi.zero_apply]

theorem gpt_neg (x : Γ(Z.left, ⊤)) : (gpt (-x) : Z ⟶ (Ga k).X) = (gpt x)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← gpt_add, neg_add_cancel, gpt_zero]

theorem comp_gpt (f : W ⟶ Z) (x : Γ(Z.left, ⊤)) :
    f ≫ (gpt x : Z ⟶ (Ga k).X) = gpt (f.left.appTop x) :=
  VectorGroup.points_ext fun j => by
    have h := congrFun (VectorGroup.coordinates_comp f (gpt (k := k) x)) j
    rw [h, coordinates_gpt, coordinates_gpt]

theorem weightPointAction_gpt {S : CommGroupScheme (Spec (CommRingCat.of k))}
    (χ : characterLattice S) (t : Z ⟶ S.X) (x : Γ(Z.left, ⊤)) :
    VectorGroup.weightPointAction χ Z t (gpt x) =
      (gpt (VectorGroup.charValue χ Z t * x) : Z ⟶ (Ga k).X) :=
  VectorGroup.points_ext fun j => by
    rw [VectorGroup.coordinates_weightPointAction, Pi.smul_apply, coordinates_gpt,
      coordinates_gpt, smul_eq_mul]

end Additive

/-! ### Values of characters -/

section CharacterValue

variable {S : CommGroupScheme (Spec (CommRingCat.of k))} {Z W : Over (Spec (CommRingCat.of k))}

/-- The unit value of a character at a point of a commutative group scheme. -/
def cu (χ : characterLattice S) (t : Z ⟶ S.X) : Γ(Z.left, ⊤)ˣ :=
  Gm.pointsEquiv _ Z (t ≫ (CommGroupScheme.groupHom χ).hom.hom)

theorem charValue_eq_cu (χ : characterLattice S) (t : Z ⟶ S.X) :
    VectorGroup.charValue χ Z t = (cu χ t : Γ(Z.left, ⊤)) := rfl

theorem cu_mul (χ : characterLattice S) (t s : Z ⟶ S.X) : cu χ (t * s) = cu χ t * cu χ s := by
  rw [cu, MonObj.mul_comp, map_mul]
  rfl

theorem cu_one (χ : characterLattice S) : cu χ (1 : Z ⟶ S.X) = 1 := by
  rw [cu, MonObj.one_comp, map_one]

theorem cu_inv (χ : characterLattice S) (t : Z ⟶ S.X) : cu χ t⁻¹ = (cu χ t)⁻¹ := by
  rw [cu, GrpObj.inv_comp, map_inv]
  rfl

theorem cu_neg (χ : characterLattice S) (t : Z ⟶ S.X) : cu (-χ) t = (cu χ t)⁻¹ := by
  have h : t ≫ (CommGroupScheme.groupHom (-χ)).hom.hom =
      (t ≫ (CommGroupScheme.groupHom χ).hom.hom)⁻¹ :=
    congrArg Additive.toMul ((evalPoint t).map_neg χ)
  rw [cu, h, map_inv]
  rfl

theorem cu_comp (χ : characterLattice S) (f : W ⟶ Z) (t : Z ⟶ S.X) :
    cu χ (f ≫ t) = Units.map f.left.appTop.hom.toMonoidHom (cu χ t) := by
  rw [cu, Category.assoc, Gm.pointsEquiv_naturality]
  rfl

end CharacterValue

/-! ### The open cell -/

/-- A split maximal torus `i` with root groups `xp`, `xm` of weights `α`, `-α` whose triple
cell multiplication is an open immersion. -/
structure CellData (k : Type u) [Field k] where
  G : GroupScheme (Spec (CommRingCat.of k))
  T : CommGroupScheme (Spec (CommRingCat.of k))
  i : T.toGrp ⟶ G
  xp : Ga k ⟶ G
  xm : Ga k ⟶ G
  α : characterLattice T
  hxp : ∀ (Z : Over (Spec (CommRingCat.of k))) (t : Z ⟶ T.X) (a : Z ⟶ (Ga k).X),
    (t ≫ i.hom.hom) * (a ≫ xp.hom.hom) * (t ≫ i.hom.hom)⁻¹ =
      VectorGroup.weightPointAction α Z t a ≫ xp.hom.hom
  hxm : ∀ (Z : Over (Spec (CommRingCat.of k))) (t : Z ⟶ T.X) (b : Z ⟶ (Ga k).X),
    (t ≫ i.hom.hom) * (b ≫ xm.hom.hom) * (t ≫ i.hom.hom)⁻¹ =
      VectorGroup.weightPointAction (-α) Z t b ≫ xm.hom.hom
  open_cell : IsOpenImmersion (Dynamic.tripleCellMultiplication xm i xp).left

namespace CellData

variable (D : CellData k) {Z W : Over (Spec (CommRingCat.of k))}

/-- The point `xp(x)`. -/
def A (x : Γ(Z.left, ⊤)) : Z ⟶ D.G.X := gpt x ≫ D.xp.hom.hom

/-- The point `xm(y)`. -/
def B (y : Γ(Z.left, ⊤)) : Z ⟶ D.G.X := gpt y ≫ D.xm.hom.hom

/-- The point of `G` given by a point of the torus. -/
def I (t : Z ⟶ D.T.X) : Z ⟶ D.G.X := t ≫ D.i.hom.hom

/-- The cell multiplication. -/
abbrev cellMul : (Ga k).X ⊗ (D.T.X ⊗ (Ga k).X) ⟶ D.G.X :=
  Dynamic.tripleCellMultiplication D.xm D.i D.xp

/-- The point `xm(y) t xp(x)` of the open cell. -/
def cellPt (y : Γ(Z.left, ⊤)) (t : Z ⟶ D.T.X) (x : Γ(Z.left, ⊤)) : Z ⟶ D.G.X :=
  D.B y * (D.I t * D.A x)

/-- A point lies in the open cell. -/
def InCell (g : Z ⟶ D.G.X) : Prop :=
  ∃ c, c ≫ D.cellMul = g

theorem A_add (x y : Γ(Z.left, ⊤)) : D.A (x + y) = D.A x * D.A y := by
  rw [A, A, A, gpt_add, MonObj.mul_comp]

theorem B_add (x y : Γ(Z.left, ⊤)) : D.B (x + y) = D.B x * D.B y := by
  rw [B, B, B, gpt_add, MonObj.mul_comp]

theorem A_zero : D.A (0 : Γ(Z.left, ⊤)) = 1 := by
  rw [A, gpt_zero, MonObj.one_comp]

theorem B_zero : D.B (0 : Γ(Z.left, ⊤)) = 1 := by
  rw [B, gpt_zero, MonObj.one_comp]

theorem A_neg (x : Γ(Z.left, ⊤)) : D.A (-x) = (D.A x)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← A_add, neg_add_cancel, A_zero]

theorem B_neg (x : Γ(Z.left, ⊤)) : D.B (-x) = (D.B x)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← B_add, neg_add_cancel, B_zero]

theorem A_sub (x y : Γ(Z.left, ⊤)) : D.A (x - y) = D.A x * (D.A y)⁻¹ := by
  rw [sub_eq_add_neg, A_add, A_neg]

theorem I_mul (t s : Z ⟶ D.T.X) : D.I (t * s) = D.I t * D.I s := by
  rw [I, I, I, MonObj.mul_comp]

theorem I_one : D.I (1 : Z ⟶ D.T.X) = 1 := by
  rw [I, MonObj.one_comp]

theorem I_inv (t : Z ⟶ D.T.X) : D.I t⁻¹ = (D.I t)⁻¹ := by
  rw [I, I, GrpObj.inv_comp]

theorem comp_A (f : W ⟶ Z) (x : Γ(Z.left, ⊤)) : f ≫ D.A x = D.A (f.left.appTop x) := by
  rw [A, A, ← Category.assoc, comp_gpt]

theorem comp_B (f : W ⟶ Z) (y : Γ(Z.left, ⊤)) : f ≫ D.B y = D.B (f.left.appTop y) := by
  rw [B, B, ← Category.assoc, comp_gpt]

theorem comp_I (f : W ⟶ Z) (t : Z ⟶ D.T.X) : f ≫ D.I t = D.I (f ≫ t) := by
  rw [I, I, Category.assoc]

theorem I_mul_A (t : Z ⟶ D.T.X) (x : Γ(Z.left, ⊤)) :
    D.I t * D.A x = D.A ((cu D.α t : Γ(Z.left, ⊤)) * x) * D.I t := by
  have h := D.hxp Z t (gpt x)
  rw [weightPointAction_gpt, charValue_eq_cu] at h
  rw [A, A, I, ← h, inv_mul_cancel_right]

theorem I_mul_B (t : Z ⟶ D.T.X) (y : Γ(Z.left, ⊤)) :
    D.I t * D.B y = D.B ((↑(cu D.α t)⁻¹ : Γ(Z.left, ⊤)) * y) * D.I t := by
  have h := D.hxm Z t (gpt y)
  rw [weightPointAction_gpt, charValue_eq_cu, cu_neg] at h
  rw [B, B, I, ← h, inv_mul_cancel_right]

theorem A_mul_I (t : Z ⟶ D.T.X) (x : Γ(Z.left, ⊤)) :
    D.A x * D.I t = D.I t * D.A ((↑(cu D.α t)⁻¹ : Γ(Z.left, ⊤)) * x) := by
  rw [I_mul_A, Units.mul_inv_cancel_left]

theorem B_mul_I (t : Z ⟶ D.T.X) (y : Γ(Z.left, ⊤)) :
    D.B y * D.I t = D.I t * D.B ((cu D.α t : Γ(Z.left, ⊤)) * y) := by
  rw [I_mul_B, Units.inv_mul_cancel_left]

theorem lift_cellMul (y : Γ(Z.left, ⊤)) (t : Z ⟶ D.T.X) (x : Γ(Z.left, ⊤)) :
    lift (gpt y) (lift t (gpt x)) ≫ D.cellMul = D.cellPt y t x :=
  Dynamic.lift_tripleCellMultiplication _ _ _ _ _ _

theorem inCell_iff (g : Z ⟶ D.G.X) :
    D.InCell g ↔ ∃ y t x, g = D.cellPt y t x := by
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨(VectorGroup.coordinates (CommRingCat.of k) 1 Z (c ≫ fst _ _)).toAdd 0,
      c ≫ snd _ _ ≫ fst _ _,
      (VectorGroup.coordinates (CommRingCat.of k) 1 Z (c ≫ snd _ _ ≫ snd _ _)).toAdd 0, ?_⟩
    rw [← lift_cellMul, ← eq_gpt, ← eq_gpt]
    congr 1
    apply CartesianMonoidalCategory.hom_ext
    · rw [lift_fst]
    · rw [lift_snd]
      apply CartesianMonoidalCategory.hom_ext
      · rw [lift_fst, Category.assoc]
      · rw [lift_snd, Category.assoc]
  · rintro ⟨y, t, x, rfl⟩
    exact ⟨_, D.lift_cellMul y t x⟩

theorem inCell_cellPt (y : Γ(Z.left, ⊤)) (t : Z ⟶ D.T.X) (x : Γ(Z.left, ⊤)) :
    D.InCell (D.cellPt y t x) :=
  ⟨_, D.lift_cellMul y t x⟩

theorem cellPt_inj {y y' : Γ(Z.left, ⊤)} {t t' : Z ⟶ D.T.X} {x x' : Γ(Z.left, ⊤)}
    (h : D.cellPt y t x = D.cellPt y' t' x') : y = y' ∧ t = t' ∧ x = x' := by
  have := D.open_cell
  rw [← lift_cellMul, ← lift_cellMul] at h
  have h2 : lift (gpt y) (lift t (gpt x)) = lift (gpt y') (lift t' (gpt x')) := by
    apply Over.OverMorphism.ext
    have h3 := congrArg CommaMorphism.left h
    simp only [Over.comp_left] at h3
    exact (cancel_mono _).mp h3
  have h4 := congrArg (· ≫ fst _ _) h2
  have h5 := congrArg (· ≫ snd _ _ ≫ fst _ _) h2
  have h6 := congrArg (· ≫ snd _ _ ≫ snd _ _) h2
  simp only [lift_fst, lift_snd_assoc, lift_snd] at h4 h5 h6
  exact ⟨gpt_injective h4, h5, gpt_injective h6⟩

theorem one_eq_cellPt : (1 : Z ⟶ D.G.X) = D.cellPt 0 1 0 := by
  rw [cellPt, A_zero, B_zero, I_one, one_mul, one_mul]

theorem A_eq_cellPt (x : Γ(Z.left, ⊤)) : D.A x = D.cellPt 0 1 x := by
  rw [cellPt, B_zero, I_one, one_mul, one_mul]

theorem I_eq_cellPt (t : Z ⟶ D.T.X) : D.I t = D.cellPt 0 t 0 := by
  rw [cellPt, B_zero, A_zero, one_mul, mul_one]

theorem B_mul_cellPt (y' y : Γ(Z.left, ⊤)) (t : Z ⟶ D.T.X) (x : Γ(Z.left, ⊤)) :
    D.B y' * D.cellPt y t x = D.cellPt (y' + y) t x := by
  rw [cellPt, cellPt, B_add, mul_assoc]

theorem I_mul_cellPt (s : Z ⟶ D.T.X) (y : Γ(Z.left, ⊤)) (t : Z ⟶ D.T.X) (x : Γ(Z.left, ⊤)) :
    D.I s * D.cellPt y t x = D.cellPt ((↑(cu D.α s)⁻¹ : Γ(Z.left, ⊤)) * y) (s * t) x := by
  rw [cellPt, cellPt, ← mul_assoc, I_mul_B, I_mul]
  simp only [mul_assoc]

theorem cellPt_mul_A (y : Γ(Z.left, ⊤)) (t : Z ⟶ D.T.X) (x x' : Γ(Z.left, ⊤)) :
    D.cellPt y t x * D.A x' = D.cellPt y t (x + x') := by
  rw [cellPt, cellPt, A_add]
  simp only [mul_assoc]

theorem cellPt_mul_I (y : Γ(Z.left, ⊤)) (t : Z ⟶ D.T.X) (x : Γ(Z.left, ⊤)) (s : Z ⟶ D.T.X) :
    D.cellPt y t x * D.I s = D.cellPt y (t * s) ((↑(cu D.α s)⁻¹ : Γ(Z.left, ⊤)) * x) := by
  rw [cellPt, cellPt, mul_assoc, mul_assoc, A_mul_I, I_mul]
  simp only [mul_assoc]

theorem comp_cellPt (f : W ⟶ Z) (y : Γ(Z.left, ⊤)) (t : Z ⟶ D.T.X) (x : Γ(Z.left, ⊤)) :
    f ≫ D.cellPt y t x = D.cellPt (f.left.appTop y) (f ≫ t) (f.left.appTop x) := by
  rw [cellPt, cellPt, MonObj.comp_mul, MonObj.comp_mul, comp_A, comp_B, comp_I]

theorem InCell.B_mul {g : Z ⟶ D.G.X} (hg : D.InCell g) (y : Γ(Z.left, ⊤)) :
    D.InCell (D.B y * g) := by
  obtain ⟨y', t, x, rfl⟩ := (D.inCell_iff g).mp hg
  rw [B_mul_cellPt]
  exact D.inCell_cellPt _ _ _

theorem InCell.I_mul {g : Z ⟶ D.G.X} (hg : D.InCell g) (s : Z ⟶ D.T.X) :
    D.InCell (D.I s * g) := by
  obtain ⟨y', t, x, rfl⟩ := (D.inCell_iff g).mp hg
  rw [I_mul_cellPt]
  exact D.inCell_cellPt _ _ _

theorem InCell.mul_A {g : Z ⟶ D.G.X} (hg : D.InCell g) (x : Γ(Z.left, ⊤)) :
    D.InCell (g * D.A x) := by
  obtain ⟨y', t, x, rfl⟩ := (D.inCell_iff g).mp hg
  rw [cellPt_mul_A]
  exact D.inCell_cellPt _ _ _

theorem InCell.mul_I {g : Z ⟶ D.G.X} (hg : D.InCell g) (s : Z ⟶ D.T.X) :
    D.InCell (g * D.I s) := by
  obtain ⟨y', t, x, rfl⟩ := (D.inCell_iff g).mp hg
  rw [cellPt_mul_I]
  exact D.inCell_cellPt _ _ _

theorem InCell.comp {g : Z ⟶ D.G.X} (hg : D.InCell g) (f : W ⟶ Z) : D.InCell (f ≫ g) := by
  obtain ⟨c, rfl⟩ := hg
  exact ⟨f ≫ c, Category.assoc _ _ _⟩

/-- A point whose image lies in the image of the cell lies in the cell. -/
theorem inCell_of_range_subset {g : Z ⟶ D.G.X}
    (h : Set.range g.left ⊆ Set.range D.cellMul.left) : D.InCell g := by
  have := D.open_cell
  refine ⟨Over.homMk (IsOpenImmersion.lift D.cellMul.left g.left h) ?_, ?_⟩
  · rw [← Over.w D.cellMul, ← Category.assoc, IsOpenImmersion.lift_fac, Over.w g]
  · apply Over.OverMorphism.ext
    simp only [Over.comp_left, Over.homMk_left, IsOpenImmersion.lift_fac]

theorem range_subset_of_inCell {g : Z ⟶ D.G.X} (hg : D.InCell g) :
    Set.range g.left ⊆ Set.range D.cellMul.left := by
  obtain ⟨c, rfl⟩ := hg
  rintro _ ⟨z, rfl⟩
  exact ⟨c.left z, by simp only [Over.comp_left, Scheme.Hom.comp_apply]⟩

/-- Membership in the cell descends along morphisms that are surjective on points. -/
theorem InCell.of_comp {f : W ⟶ Z} (hf : Function.Surjective f.left) {g : Z ⟶ D.G.X}
    (h : D.InCell (f ≫ g)) : D.InCell g := by
  apply D.inCell_of_range_subset
  rintro _ ⟨z, rfl⟩
  obtain ⟨w, rfl⟩ := hf z
  apply D.range_subset_of_inCell h
  exact ⟨w, by simp only [Over.comp_left, Scheme.Hom.comp_apply]⟩

end CellData

end RankOneRootCellRelation

end Langlands.GroupScheme
