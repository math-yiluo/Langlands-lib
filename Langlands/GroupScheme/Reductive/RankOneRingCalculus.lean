import Langlands.GroupScheme.Reductive.LocalSplitCell
import Langlands.GroupScheme.Absolute.TripleCell
import Langlands.GroupScheme.InnerAutomorphismHom
import Langlands.GroupScheme.Torus.Maximal
import Langlands.GroupScheme.Rational.TorusNormalizer

/-! # Exact rank-one cell calculus over commutative rings -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace RingRootCell

variable {k : Type u} [CommRing k]

/-- The additive group `𝔾ₐ` over `k`. -/
abbrev Ga (k : Type u) [CommRing k] : GroupScheme (Spec (CommRingCat.of k)) :=
  LocalSplitCell.Ga k

/-! ### Points of the additive group -/

section Additive

variable {Z W : Over (Spec (CommRingCat.of k))}

/-- The point of `𝔾ₐ` with coordinate `x`. -/
abbrev gpt (x : Γ(Z.left, ⊤)) : Z ⟶ (Ga k).X :=
  VectorGroup.scalarPoint (CommRingCat.of k) Z x

theorem coordinates_gpt (x : Γ(Z.left, ⊤)) (j : Fin 1) :
    (VectorGroup.coordinates (CommRingCat.of k) 1 Z (gpt x)).toAdd j = x := by
  exact VectorGroup.coordinates_scalarPoint _ _ _ _

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

/-- A commutative group-scheme map `i` and additive-group maps `xp`, `xm` of weights
`α`, `-α` whose triple cell multiplication is an open immersion. -/
structure CellData (k : Type u) [CommRing k] where
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

namespace CellData

variable (D : CellData k) {Z : Over (Spec (CommRingCat.of k))}

theorem cellPt_zero_right (y : Γ(Z.left, ⊤)) (t : Z ⟶ D.T.X) :
    D.cellPt y t 0 = D.B y * D.I t := by
  rw [cellPt, A_zero, mul_one]

theorem I_mul_A_eq_cellPt (t : Z ⟶ D.T.X) (x : Γ(Z.left, ⊤)) :
    D.I t * D.A x = D.cellPt 0 t x := by
  rw [cellPt, B_zero, one_mul]

theorem I_mul_B' (t : Z ⟶ D.T.X) (y : Γ(Z.left, ⊤)) :
    D.B ((↑(cu D.α t)⁻¹ : Γ(Z.left, ⊤)) * y) = D.I t * D.B y * (D.I t)⁻¹ := by
  rw [I_mul_B, mul_inv_cancel_right]

/-- If `xp(x) xm(y)` lies in `xm(𝔾ₐ) T`, then `x = 0`. -/
theorem eq_zero_of_A_mul_B {x y y' : Γ(Z.left, ⊤)} {t : Z ⟶ D.T.X}
    (h : D.A x * D.B y = D.B y' * D.I t) : x = 0 := by
  have h1 : D.A x = D.cellPt (y' + (↑(cu D.α t)⁻¹ : Γ(Z.left, ⊤)) * -y) t 0 := by
    rw [cellPt_zero_right, B_add, mul_assoc, ← I_mul_B, ← mul_assoc, ← h, mul_assoc, ← B_add,
      add_neg_cancel, B_zero, mul_one]
  rw [A_eq_cellPt] at h1
  exact (D.cellPt_inj h1).2.2

end CellData

/-- Reflection defined by an actual character-cocharacter composite equal to two. -/
def reflectionIso {k : Type u} [CommRing k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (α : characterLattice T) (h : cocharacterLattice T)
    (hh : h ≫ α = (2 : ℤ) • 𝟙 (Gm (Spec (CommRingCat.of k)))) : T ≅ T := by
  let a : T ⟶ T := α ≫ h
  have ha : a ≫ a = (2 : ℤ) • a := by
    change (α ≫ h) ≫ (α ≫ h) = _
    calc
      (α ≫ h) ≫ (α ≫ h) = (α ≫ (h ≫ α)) ≫ h := by simp only [Category.assoc]
      _ = (2 : ℤ) • (α ≫ h) := by
        rw [hh, Preadditive.comp_zsmul, Category.comp_id, Preadditive.zsmul_comp]
  have hr : (𝟙 T - a) ≫ (𝟙 T - a) = 𝟙 T := by
    rw [Preadditive.sub_comp, Preadditive.comp_sub, Preadditive.comp_sub,
      Category.id_comp, Category.id_comp, Category.comp_id, ha]
    module
  exact ⟨𝟙 T - a, 𝟙 T - a, hr, hr⟩

/-- The base as a test scheme. -/
abbrev base (k : Type u) [CommRing k] : Over (Spec (CommRingCat.of k)) := Over.mk (𝟙 _)

/-- The structure morphism into the base test. -/
def toBase (Z : Over (Spec (CommRingCat.of k))) : Z ⟶ base k :=
  Over.homMk Z.hom (by simp)

/-- Exact normalizer and unit cell data, supplied over an arbitrary ring. -/
structure WeylData (k : Type u) [CommRing k] extends CellData k where
  h : cocharacterLattice T
  hh : h ≫ α = (2 : ℤ) • 𝟙 (Gm (Spec (CommRingCat.of k)))
  n : base k ⟶ G.X
  hn : IsNormalizingPoint i n (reflectionIso α h hh)
  hn2 : ∃ z : base k ⟶ T.X, n * n = z ≫ i.hom.hom
  cβ : Γ((base k).left, ⊤)
  ct : base k ⟶ T.X
  cδ : Γ((base k).left, ⊤)
  unitβ : IsUnit cβ
  unitδ : IsUnit cδ
  decomp : toCellData.A 1 * n = toCellData.cellPt cβ ct cδ

namespace WeylData

variable (D : WeylData k) {Z W : Over (Spec (CommRingCat.of k))}

/-- The point `h(c)` of the torus. -/
def tH (c : Γ(Z.left, ⊤)ˣ) : Z ⟶ D.T.X :=
  (Gm.pointsEquiv _ Z).symm c ≫ (CommGroupScheme.groupHom D.h).hom.hom

/-- The point `h(c)` of `G`. -/
def H (c : Γ(Z.left, ⊤)ˣ) : Z ⟶ D.G.X := D.I (D.tH c)

/-- The Weyl point over a test scheme. -/
def N (Z : Over (Spec (CommRingCat.of k))) : Z ⟶ D.G.X := D.G.constantPoint D.n Z

theorem tH_mul (c d : Γ(Z.left, ⊤)ˣ) : D.tH (c * d) = D.tH c * D.tH d := by
  rw [tH, tH, tH, map_mul, MonObj.mul_comp]

theorem tH_one : D.tH (1 : Γ(Z.left, ⊤)ˣ) = 1 := by
  rw [tH, map_one, MonObj.one_comp]

theorem tH_inv (c : Γ(Z.left, ⊤)ˣ) : D.tH c⁻¹ = (D.tH c)⁻¹ := by
  rw [tH, tH, map_inv, GrpObj.inv_comp]

theorem H_mul (c d : Γ(Z.left, ⊤)ˣ) : D.H (c * d) = D.H c * D.H d := by
  rw [H, H, H, tH_mul, CellData.I_mul]

theorem H_inv (c : Γ(Z.left, ⊤)ˣ) : D.H c⁻¹ = (D.H c)⁻¹ := by
  rw [H, H, tH_inv, CellData.I_inv]

theorem cu_tH (c : Γ(Z.left, ⊤)ˣ) : cu D.α (D.tH c) = c * c := by
  have h2 := Gm.comp_zsmul_id ((Gm.pointsEquiv _ Z).symm c) 2
  rw [← D.hh, comp_groupHom_comp] at h2
  rw [cu, tH, h2, map_zpow, MulEquiv.apply_symm_apply, zpow_two]

theorem comp_tH (f : W ⟶ Z) (c : Γ(Z.left, ⊤)ˣ) :
    f ≫ D.tH c = D.tH (Units.map f.left.appTop.hom.toMonoidHom c) := by
  rw [tH, tH, ← Category.assoc]
  congr 1
  apply (Gm.pointsEquiv _ W).injective
  rw [Gm.pointsEquiv_naturality, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

theorem comp_N (f : W ⟶ Z) : f ≫ D.N Z = D.N W :=
  D.G.constantPoint_naturality D.n f

/-- Conjugation by the Weyl point acts on the torus through the reflection. -/
theorem N_mul_I (t : Z ⟶ D.T.X) :
    D.N Z * D.I t * (D.N Z)⁻¹ =
      D.I (t ≫ (CommGroupScheme.groupHom (𝟙 D.T - D.α ≫ D.h)).hom.hom) :=
  D.hn.conj_comp Z t

theorem tH_comp_reflection (c : Γ(Z.left, ⊤)ˣ) :
    D.tH c ≫ (CommGroupScheme.groupHom (𝟙 D.T - D.α ≫ D.h)).hom.hom = (D.tH c)⁻¹ := by
  have hneg : D.tH c ≫ (CommGroupScheme.groupHom (-(D.α ≫ D.h))).hom.hom =
      (D.tH c ≫ (CommGroupScheme.groupHom (D.α ≫ D.h)).hom.hom)⁻¹ :=
    congrArg Additive.toMul ((evalPoint (D.tH c)).map_neg (D.α ≫ D.h))
  have hid : D.tH c ≫ (CommGroupScheme.groupHom (𝟙 D.T)).hom.hom = D.tH c := by
    rw [show (CommGroupScheme.groupHom (𝟙 D.T)).hom.hom = 𝟙 D.T.X from rfl, Category.comp_id]
  have hah : D.tH c ≫ (CommGroupScheme.groupHom (D.α ≫ D.h)).hom.hom = D.tH c * D.tH c := by
    rw [comp_groupHom_comp, ← D.tH_mul, ← D.cu_tH]
    simp only [tH, cu, MulEquiv.symm_apply_apply]
  rw [sub_eq_add_neg, comp_groupHom_add, hneg, hid, hah, mul_inv_rev, mul_inv_cancel_left]

theorem N_mul_H (c : Γ(Z.left, ⊤)ˣ) : D.N Z * D.H c * (D.N Z)⁻¹ = (D.H c)⁻¹ := by
  rw [H, N_mul_I, tH_comp_reflection, CellData.I_inv]

theorem N_mul_H' (c : Γ(Z.left, ⊤)ˣ) : D.N Z * D.H c = (D.H c)⁻¹ * D.N Z := by
  rw [← D.N_mul_H c, inv_mul_cancel_right]

theorem H_mul_N (c : Γ(Z.left, ⊤)ˣ) : D.H c * D.N Z = D.N Z * (D.H c)⁻¹ := by
  have := D.N_mul_H' c⁻¹
  rw [H_inv, inv_inv] at this
  exact this.symm

theorem inv_H_mul_N (c : Γ(Z.left, ⊤)ˣ) : (D.H c)⁻¹ * D.N Z = D.N Z * D.H c :=
  (D.N_mul_H' c).symm

theorem I_mul_A' (t : Z ⟶ D.T.X) (x : Γ(Z.left, ⊤)) :
    D.A ((↑(cu D.α t) : Γ(Z.left, ⊤)) * x) = D.I t * D.A x * (D.I t)⁻¹ := by
  rw [CellData.I_mul_A, mul_inv_cancel_right]

/-- **Equivariance.** `xp(c²x) n = h(c) xp(x) n h(c)`. -/
theorem A_mul_N (c : Γ(Z.left, ⊤)ˣ) (x : Γ(Z.left, ⊤)) :
    D.A ((↑(c * c) : Γ(Z.left, ⊤)) * x) * D.N Z = D.H c * (D.A x * D.N Z) * D.H c := by
  have h := D.I_mul_A' (D.tH c) x
  rw [cu_tH] at h
  rw [h, ← H, mul_assoc, inv_H_mul_N]
  simp only [mul_assoc]

/-- The supplied decomposition over the base. -/
theorem A_one_mul_N_base :
    D.A (1 : Γ((base k).left, ⊤)) * D.N (base k) = D.cellPt D.cβ D.ct D.cδ := by
  simpa only [N, constantPoint_self] using D.decomp

/-- Pull back a global section of the base to a test scheme. -/
abbrev pb (Z : Over (Spec (CommRingCat.of k))) (x : Γ((base k).left, ⊤)) : Γ(Z.left, ⊤) :=
  (toBase Z).left.appTop x

theorem N_eq_comp (Z : Over (Spec (CommRingCat.of k))) : D.N Z = toBase Z ≫ D.n := rfl

theorem A_one_mul_N (Z : Over (Spec (CommRingCat.of k))) :
    D.A (1 : Γ(Z.left, ⊤)) * D.N Z = D.cellPt (pb Z D.cβ) (toBase Z ≫ D.ct) (pb Z D.cδ) := by
  have h := congrArg (fun g => toBase Z ≫ g) D.A_one_mul_N_base
  rw [MonObj.comp_mul, CellData.comp_A, comp_N, map_one, CellData.comp_cellPt] at h
  exact h

/-- `xp(c²) n = xm(c⁻² β) h(c) γ h(c) xp(c⁻² δ)`. -/
theorem A_sq_mul_N (c : Γ(Z.left, ⊤)ˣ) :
    D.A (↑(c * c) : Γ(Z.left, ⊤)) * D.N Z =
      D.cellPt ((↑(c * c)⁻¹ : Γ(Z.left, ⊤)) * pb Z D.cβ) (D.tH c * (toBase Z ≫ D.ct) * D.tH c)
        ((↑(c * c)⁻¹ : Γ(Z.left, ⊤)) * pb Z D.cδ) := by
  have h := D.A_mul_N c 1
  rw [mul_one, A_one_mul_N, H, CellData.I_mul_cellPt, CellData.cellPt_mul_I, cu_tH] at h
  exact h

theorem N_mul_N (Z : Over (Spec (CommRingCat.of k))) :
    ∃ z : Z ⟶ D.T.X, D.N Z * D.N Z = D.I z := by
  obtain ⟨z₀, hz₀⟩ := D.hn2
  refine ⟨toBase Z ≫ z₀, ?_⟩
  rw [N_eq_comp, ← MonObj.comp_mul, hz₀, CellData.I, Category.assoc]

theorem inCell_A (x : Γ(Z.left, ⊤)) : D.InCell (D.A x) := by
  rw [CellData.A_eq_cellPt]
  exact D.inCell_cellPt _ _ _

theorem cβ_isUnit : IsUnit D.cβ := D.unitβ

theorem cδ_isUnit : IsUnit D.cδ := D.unitδ

theorem cu_mul_eq_neg_one_aux {β δ : Γ(Z.left, ⊤)} {g g' z : Z ⟶ D.T.X} (r : Γ(Z.left, ⊤)ˣ)
    (hβ : IsUnit β) (hr : (r : Γ(Z.left, ⊤)) = δ)
    (e1 : D.A 1 * D.N Z = D.cellPt β g δ)
    (e2 : D.A δ * D.N Z = D.cellPt ((↑r⁻¹ : Γ(Z.left, ⊤)) * β) g' 1)
    (hz : D.N Z * D.N Z = D.I z) :
    (cu D.α g : Γ(Z.left, ⊤)) * δ = -1 := by
  have hN1 : D.N Z = D.A (-1) * D.cellPt β g δ := by
    rw [← e1, ← mul_assoc, ← CellData.A_add, neg_add_cancel, CellData.A_zero, one_mul]
  have hN2 : D.N Z = D.A (-δ) * D.cellPt ((↑r⁻¹ : Γ(Z.left, ⊤)) * β) g' 1 := by
    rw [← e2, ← mul_assoc, ← CellData.A_add, neg_add_cancel, CellData.A_zero, one_mul]
  have hP : D.N Z * D.N Z =
      D.A (-1) * D.cellPt (β + (↑(cu D.α g)⁻¹ : Γ(Z.left, ⊤)) * ((↑r⁻¹ : Γ(Z.left, ⊤)) * β)) (g * g') 1 := by
    calc D.N Z * D.N Z = D.A (-1) * D.cellPt β g δ * (D.A (-δ) * D.cellPt ((↑r⁻¹ : Γ(Z.left, ⊤)) * β) g' 1) :=
          congrArg₂ (· * ·) hN1 hN2
      _ = D.A (-1) * (D.cellPt β g δ * D.A (-δ) * D.cellPt ((↑r⁻¹ : Γ(Z.left, ⊤)) * β) g' 1) := by
          simp only [mul_assoc]
      _ = D.A (-1) * (D.B β * (D.I g * D.cellPt ((↑r⁻¹ : Γ(Z.left, ⊤)) * β) g' 1)) := by
          rw [CellData.cellPt_mul_A, add_neg_cancel, CellData.cellPt_zero_right, mul_assoc]
      _ = _ := by rw [CellData.I_mul_cellPt, CellData.B_mul_cellPt]
  have hP' : D.cellPt (β + (↑(cu D.α g)⁻¹ : Γ(Z.left, ⊤)) * ((↑r⁻¹ : Γ(Z.left, ⊤)) * β)) (g * g') 1 =
      D.cellPt 0 z ((↑(cu D.α z)⁻¹ : Γ(Z.left, ⊤)) * 1) := by
    rw [← CellData.I_mul_A_eq_cellPt, ← CellData.A_mul_I, ← hz, hP, ← mul_assoc (D.A 1),
      ← CellData.A_add, add_neg_cancel, CellData.A_zero, one_mul]
  have h0 := (D.cellPt_inj hP').1
  obtain ⟨b, rfl⟩ := hβ
  have hl := Units.mul_inv (cu D.α g)
  have hrr := Units.mul_inv r
  have hb := Units.mul_inv b
  linear_combination ((cu D.α g : Γ(Z.left, ⊤)) * ↑r * ↑b⁻¹) * h0 - (cu D.α g : Γ(Z.left, ⊤)) * hr
    - ((cu D.α g : Γ(Z.left, ⊤)) * ↑r + 1) * hb - (↑r * ↑r⁻¹ * ↑b * ↑b⁻¹) * hl
    - (↑b * ↑b⁻¹) * hrr

/-- **`λ δ = -1`** for `λ = α(γ)`, over a test scheme where `δ` is a square. -/
theorem cu_ct_mul_cδ (d : Γ(Z.left, ⊤)ˣ) (hd : (↑(d * d) : Γ(Z.left, ⊤)) = pb Z D.cδ) :
    (cu D.α (toBase Z ≫ D.ct) : Γ(Z.left, ⊤)) * pb Z D.cδ = -1 := by
  obtain ⟨z, hz⟩ := D.N_mul_N Z
  have e2 := D.A_sq_mul_N d
  have h1 : (↑(d * d)⁻¹ : Γ(Z.left, ⊤)) * pb Z D.cδ = 1 := by
    rw [← hd, Units.inv_mul]
  rw [hd, h1] at e2
  exact D.cu_mul_eq_neg_one_aux (d * d) (D.cβ_isUnit.map (toBase Z).left.appTop.hom) hd
    (D.A_one_mul_N Z) e2 hz

/-! ### The rank-one relation over test schemes with square roots -/

/-- From `xp(r) n` and `xp(s) n` in the normal form of `xp(c²) n`, the product
`xp(r - s) xm(s⁻¹ β)` lies in the open cell. -/
theorem A_sub_mul_B_aux {β δ : Γ(Z.left, ⊤)} {gr gs : Z ⟶ D.T.X} (r s : Γ(Z.left, ⊤)ˣ)
    (er : D.A (r : Γ(Z.left, ⊤)) * D.N Z =
      D.cellPt ((↑r⁻¹ : Γ(Z.left, ⊤)) * β) gr ((↑r⁻¹ : Γ(Z.left, ⊤)) * δ))
    (es : D.A (s : Γ(Z.left, ⊤)) * D.N Z =
      D.cellPt ((↑s⁻¹ : Γ(Z.left, ⊤)) * β) gs ((↑s⁻¹ : Γ(Z.left, ⊤)) * δ)) :
    D.A ((r : Γ(Z.left, ⊤)) - (s : Γ(Z.left, ⊤))) * D.B ((↑s⁻¹ : Γ(Z.left, ⊤)) * β) =
      D.cellPt ((↑r⁻¹ : Γ(Z.left, ⊤)) * β) (gr * gs⁻¹)
        ((cu D.α gs : Γ(Z.left, ⊤)) *
          ((↑r⁻¹ : Γ(Z.left, ⊤)) * δ - (↑s⁻¹ : Γ(Z.left, ⊤)) * δ)) := by
  have h1 : D.A ((r : Γ(Z.left, ⊤)) - (s : Γ(Z.left, ⊤))) *
      D.cellPt ((↑s⁻¹ : Γ(Z.left, ⊤)) * β) gs ((↑s⁻¹ : Γ(Z.left, ⊤)) * δ) =
      D.cellPt ((↑r⁻¹ : Γ(Z.left, ⊤)) * β) gr ((↑r⁻¹ : Γ(Z.left, ⊤)) * δ) := by
    rw [← es, ← er, ← mul_assoc, ← CellData.A_add, sub_add_cancel]
  calc D.A ((r : Γ(Z.left, ⊤)) - (s : Γ(Z.left, ⊤))) * D.B ((↑s⁻¹ : Γ(Z.left, ⊤)) * β)
      = D.A ((r : Γ(Z.left, ⊤)) - (s : Γ(Z.left, ⊤))) *
          D.cellPt ((↑s⁻¹ : Γ(Z.left, ⊤)) * β) gs ((↑s⁻¹ : Γ(Z.left, ⊤)) * δ) *
          D.A (-((↑s⁻¹ : Γ(Z.left, ⊤)) * δ)) * D.I gs⁻¹ := by
        rw [CellData.cellPt, CellData.A_neg, CellData.I_inv]
        simp only [mul_assoc, mul_inv_cancel, mul_one]
    _ = _ := by
        rw [h1, CellData.cellPt_mul_A, CellData.cellPt_mul_I, cu_inv, inv_inv, ← sub_eq_add_neg]

/-- The rank-one relation for a unit second coordinate, after adjoining the three
specified square roots of units. -/
theorem relation_of_unit_squares (X : Γ(Z.left, ⊤)) (w u d c c' : Γ(Z.left, ⊤)ˣ)
    (hu : (u : Γ(Z.left, ⊤)) = 1 + X * (w : Γ(Z.left, ⊤)))
    (hd : (↑(d * d) : Γ(Z.left, ⊤)) = pb Z D.cδ)
    (hc : c * c = u * w⁻¹) (hc' : c' * c' = w⁻¹) :
    D.A X * D.B (pb Z D.cβ * (w : Γ(Z.left, ⊤))) =
      D.cellPt (pb Z D.cβ * ((↑u⁻¹ : Γ(Z.left, ⊤)) * (w : Γ(Z.left, ⊤))))
        (D.tH u) ((↑u⁻¹ : Γ(Z.left, ⊤)) * X) := by
  have hl := D.cu_ct_mul_cδ d hd
  have hw := Units.mul_inv w
  have hu' := Units.mul_inv u
  have ha : X = (↑(c * c) : Γ(Z.left, ⊤)) - (↑(c' * c') : Γ(Z.left, ⊤)) := by
    rw [hc, hc', Units.val_mul]
    linear_combination -X * hw - (↑w⁻¹ : Γ(Z.left, ⊤)) * hu
  have hb : pb Z D.cβ * ↑w = (↑(c' * c')⁻¹ : Γ(Z.left, ⊤)) * pb Z D.cβ := by
    rw [hc', inv_inv, mul_comm]
  have key : D.tH u * (D.tH c' * D.tH c') = D.tH c * D.tH c := by
    rw [← D.tH_mul c', ← D.tH_mul u, ← D.tH_mul c, hc', hc]
  calc D.A X * D.B (pb Z D.cβ * ↑w)
      = D.A ((↑(c * c) : Γ(Z.left, ⊤)) - (↑(c' * c') : Γ(Z.left, ⊤))) * D.B ((↑(c' * c')⁻¹ : Γ(Z.left, ⊤)) * pb Z D.cβ) := by
        rw [← ha, hb]
    _ = _ := D.A_sub_mul_B_aux (c * c) (c' * c') (D.A_sq_mul_N c) (D.A_sq_mul_N c')
    _ = _ := by
        congr 1
        · rw [hc]
          simp only [mul_inv_rev, inv_inv, Units.val_mul]
          ring
        · rw [mul_inv_eq_iff_eq_mul]
          calc D.tH c * (toBase Z ≫ D.ct) * D.tH c
              = (toBase Z ≫ D.ct) * (D.tH c * D.tH c) := by
                rw [mul_comm (D.tH c) (toBase Z ≫ D.ct), mul_assoc]
            _ = D.tH u * (D.tH c' * (toBase Z ≫ D.ct) * D.tH c') := by
                rw [← key, mul_comm (D.tH c') (toBase Z ≫ D.ct), mul_assoc (toBase Z ≫ D.ct),
                  mul_left_comm (toBase Z ≫ D.ct) (D.tH u)]
        · rw [cu_mul, cu_mul, cu_tH, hc, hc']
          simp only [mul_inv_rev, inv_inv, Units.val_mul]
          linear_combination (↑u⁻¹ : Γ(Z.left, ⊤)) * (↑w⁻¹ : Γ(Z.left, ⊤)) * hu -
            (↑w⁻¹ : Γ(Z.left, ⊤)) * hu' -
            ((↑w⁻¹ : Γ(Z.left, ⊤)) * ((↑u⁻¹ : Γ(Z.left, ⊤)) - 1) -
              (↑u⁻¹ : Γ(Z.left, ⊤)) * X) * hw +
            (↑w⁻¹ : Γ(Z.left, ⊤)) * (↑w⁻¹ : Γ(Z.left, ⊤)) * ↑w *
              ((↑u⁻¹ : Γ(Z.left, ⊤)) - 1) * hl

end WeylData

end RingRootCell

end Langlands.GroupScheme
