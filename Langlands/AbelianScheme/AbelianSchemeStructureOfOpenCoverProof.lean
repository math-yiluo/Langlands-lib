import Langlands.AbelianScheme.AbelianSchemeStructureOfOpenCoverStatement
import Langlands.AbelianScheme.PointedMorphismRigidityProof

/-! # Abelian-scheme structure from local abelian charts and a section -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme

namespace OpenCoverStructure

variable {S : Scheme.{u}} (P : Over S) (s : 𝟙_ (Over S) ⟶ P)

@[reassoc]
theorem sec_hom : s.left ≫ P.hom = 𝟙 S := Over.w s

/-- A point `a : Z ⟶ P` lying over `t ≫ g`, as a point of the restriction of `P` along `g`. -/
def ptLift {V Z : Scheme.{u}} (g : V ⟶ S) (t : Z ⟶ V) (a : Z ⟶ P.left)
    (ha : a ≫ P.hom = t ≫ g) : Over.mk t ⟶ (Over.pullback g).obj P :=
  Over.homMk (pullback.lift a t ha) (by
    simp only [Over.pullback_obj_hom, Over.mk_hom, pullback.lift_snd])

/-- The canonical identification of the two iterated restrictions of `P`. -/
def restrictIso {V V' : Scheme.{u}} (h : V' ⟶ V) (g : V ⟶ S) :
    (Over.pullback (h ≫ g)).obj P ≅ (Over.pullback h).obj ((Over.pullback g).obj P) :=
  Over.isoMk (pullbackLeftPullbackSndIso P.hom g h).symm (by
    simp only [Over.pullback_obj_hom, Over.pullback_obj_left, Iso.symm_hom,
      pullbackLeftPullbackSndIso_inv_snd_snd])

/-- The unit of the restriction adjunction at a point. -/
def unitPt {V V' Z : Scheme.{u}} (h : V' ⟶ V) (t : Z ⟶ V') :
    Over.mk t ⟶ (Over.pullback h).obj (Over.mk (t ≫ h)) :=
  Over.homMk (pullback.lift (𝟙 Z) t (by simp)) (by
    simp only [Over.pullback_obj_hom, Over.mk_hom, pullback.lift_snd])

theorem ptLift_restrictIso {V V' Z : Scheme.{u}} (g : V ⟶ S) (h : V' ⟶ V) (t : Z ⟶ V')
    (a : Z ⟶ P.left) (ha : a ≫ P.hom = t ≫ h ≫ g) :
    ptLift P (h ≫ g) t a ha ≫ (restrictIso P h g).hom =
      unitPt h t ≫
        (Over.pullback h).map (ptLift P g (t ≫ h) a (by rw [ha, Category.assoc])) := by
  ext
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp [ptLift, unitPt, restrictIso, pullback.lift_fst, pullback.lift_fst_assoc]
    · simp [ptLift, unitPt, restrictIso, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_fst_assoc, pullback.lift_snd_assoc]
  · simp [ptLift, unitPt, restrictIso, pullback.lift_snd]

/-- A pointed abelian chart of `P` over `g : V ⟶ S`: an abelian scheme over `V` and an
isomorphism from the restriction of `P` carrying the restriction of `s` to the unit. -/
structure Chart (V : Scheme.{u}) (g : V ⟶ S) where
  A : AbelianScheme V
  ψ : (Over.pullback g).obj P ≅ A.X
  pointed : ∀ {Z : Scheme.{u}} (t : Z ⟶ V),
    ptLift P g t (t ≫ g ≫ s.left) (by simp) ≫ ψ.hom = 1

namespace Chart

variable {P s} {V : Scheme.{u}} {g : V ⟶ S} (c : Chart P s V g)

/-- The local point of the chart's abelian scheme attached to a point of `P` over `t ≫ g`. -/
def loc {Z : Scheme.{u}} (t : Z ⟶ V) (a : Z ⟶ P.left) (ha : a ≫ P.hom = t ≫ g) :
    Over.mk t ⟶ c.A.X :=
  ptLift P g t a ha ≫ c.ψ.hom

/-- The point of `P` attached to a local point of the chart. -/
def glob {Z : Scheme.{u}} {t : Z ⟶ V} (x : Over.mk t ⟶ c.A.X) : Z ⟶ P.left :=
  (x ≫ c.ψ.inv).left ≫ pullback.fst P.hom g

@[reassoc]
theorem glob_w {Z : Scheme.{u}} {t : Z ⟶ V} (x : Over.mk t ⟶ c.A.X) :
    c.glob x ≫ P.hom = t ≫ g := by
  have h := Over.w (x ≫ c.ψ.inv)
  simp only [Over.pullback_obj_hom, Over.mk_hom] at h
  rw [glob, Category.assoc, pullback.condition, ← Category.assoc, h]

@[simp]
theorem glob_loc {Z : Scheme.{u}} (t : Z ⟶ V) (a : Z ⟶ P.left) (ha : a ≫ P.hom = t ≫ g) :
    c.glob (c.loc t a ha) = a := by
  simp [glob, loc, ptLift, pullback.lift_fst]

@[simp]
theorem loc_glob {Z : Scheme.{u}} {t : Z ⟶ V} (x : Over.mk t ⟶ c.A.X) :
    c.loc t (c.glob x) (c.glob_w x) = x := by
  rw [loc, ← Iso.eq_comp_inv]
  have h := Over.w (x ≫ c.ψ.inv)
  simp only [Over.pullback_obj_hom, Over.mk_hom, Over.comp_left, Category.assoc] at h
  ext
  apply pullback.hom_ext
  · simp [ptLift, glob, pullback.lift_fst]
  · simp [ptLift, h, pullback.lift_snd]

theorem loc_congr {Z : Scheme.{u}} {t : Z ⟶ V} {a a' : Z ⟶ P.left}
    (h : a = a') (ha : a ≫ P.hom = t ≫ g) (ha' : a' ≫ P.hom = t ≫ g) :
    c.loc t a ha = c.loc t a' ha' := by
  subst h
  rfl

theorem loc_inj {Z : Scheme.{u}} {t : Z ⟶ V} {a b : Z ⟶ P.left}
    (ha : a ≫ P.hom = t ≫ g) (hb : b ≫ P.hom = t ≫ g) (h : c.loc t a ha = c.loc t b hb) :
    a = b := by
  rw [← c.glob_loc t a ha, h, c.glob_loc]

theorem loc_one {Z : Scheme.{u}} (t : Z ⟶ V) :
    c.loc t (t ≫ g ≫ s.left) (by simp) = 1 :=
  c.pointed t

theorem loc_comp {Z Z' : Scheme.{u}} (φ : Z' ⟶ Z) (t : Z ⟶ V) (a : Z ⟶ P.left)
    (ha : a ≫ P.hom = t ≫ g) :
    c.loc (φ ≫ t) (φ ≫ a) (by rw [Category.assoc, ha, Category.assoc]) =
      (Over.homMk φ : Over.mk (φ ≫ t) ⟶ Over.mk t) ≫ c.loc t a ha := by
  simp only [loc, ← Category.assoc]
  congr 1
  ext
  apply pullback.hom_ext
  · simp [ptLift, pullback.lift_fst]
  · simp [ptLift, pullback.lift_snd]

theorem glob_comp {Z Z' : Scheme.{u}} (φ : Z' ⟶ Z) {t : Z ⟶ V} (x : Over.mk t ⟶ c.A.X) :
    c.glob ((Over.homMk φ : Over.mk (φ ≫ t) ⟶ Over.mk t) ≫ x) = φ ≫ c.glob x := by
  simp [glob]

/-- The chart's multiplication of two points of `P` over `t ≫ g`. -/
def mul {Z : Scheme.{u}} (t : Z ⟶ V) (a b : Z ⟶ P.left) (ha : a ≫ P.hom = t ≫ g)
    (hb : b ≫ P.hom = t ≫ g) : Z ⟶ P.left :=
  c.glob (c.loc t a ha * c.loc t b hb)

/-- The chart's inverse of a point of `P` over `t ≫ g`. -/
def inv {Z : Scheme.{u}} (t : Z ⟶ V) (a : Z ⟶ P.left) (ha : a ≫ P.hom = t ≫ g) :
    Z ⟶ P.left :=
  c.glob (c.loc t a ha)⁻¹

@[reassoc]
theorem mul_w {Z : Scheme.{u}} (t : Z ⟶ V) (a b : Z ⟶ P.left) (ha : a ≫ P.hom = t ≫ g)
    (hb : b ≫ P.hom = t ≫ g) : c.mul t a b ha hb ≫ P.hom = t ≫ g :=
  c.glob_w _

@[reassoc]
theorem inv_w {Z : Scheme.{u}} (t : Z ⟶ V) (a : Z ⟶ P.left) (ha : a ≫ P.hom = t ≫ g) :
    c.inv t a ha ≫ P.hom = t ≫ g :=
  c.glob_w _

theorem loc_mul {Z : Scheme.{u}} (t : Z ⟶ V) (a b : Z ⟶ P.left) (ha : a ≫ P.hom = t ≫ g)
    (hb : b ≫ P.hom = t ≫ g) :
    c.loc t (c.mul t a b ha hb) (c.mul_w t a b ha hb) = c.loc t a ha * c.loc t b hb :=
  c.loc_glob _

theorem loc_inv {Z : Scheme.{u}} (t : Z ⟶ V) (a : Z ⟶ P.left) (ha : a ≫ P.hom = t ≫ g) :
    c.loc t (c.inv t a ha) (c.inv_w t a ha) = (c.loc t a ha)⁻¹ :=
  c.loc_glob _

theorem comp_mul {Z Z' : Scheme.{u}} (φ : Z' ⟶ Z) (t : Z ⟶ V) (a b : Z ⟶ P.left)
    (ha : a ≫ P.hom = t ≫ g) (hb : b ≫ P.hom = t ≫ g) :
    φ ≫ c.mul t a b ha hb = c.mul (φ ≫ t) (φ ≫ a) (φ ≫ b)
      (by rw [Category.assoc, ha, Category.assoc])
      (by rw [Category.assoc, hb, Category.assoc]) := by
  rw [mul, mul, c.loc_comp, c.loc_comp, ← MonObj.comp_mul, c.glob_comp]

theorem comp_inv {Z Z' : Scheme.{u}} (φ : Z' ⟶ Z) (t : Z ⟶ V) (a : Z ⟶ P.left)
    (ha : a ≫ P.hom = t ≫ g) :
    φ ≫ c.inv t a ha = c.inv (φ ≫ t) (φ ≫ a)
      (by rw [Category.assoc, ha, Category.assoc]) := by
  rw [inv, inv, c.loc_comp, ← GrpObj.comp_inv, c.glob_comp]

theorem mul_congr {Z : Scheme.{u}} {t t' : Z ⟶ V} {a a' b b' : Z ⟶ P.left} (ht : t = t')
    (ha : a = a') (hb : b = b') (h₁ : a ≫ P.hom = t ≫ g) (h₂ : b ≫ P.hom = t ≫ g)
    (h₃ : a' ≫ P.hom = t' ≫ g) (h₄ : b' ≫ P.hom = t' ≫ g) :
    c.mul t a b h₁ h₂ = c.mul t' a' b' h₃ h₄ := by
  subst ht ha hb
  rfl

theorem inv_congr {Z : Scheme.{u}} {t t' : Z ⟶ V} {a a' : Z ⟶ P.left} (ht : t = t')
    (ha : a = a') (h₁ : a ≫ P.hom = t ≫ g) (h₃ : a' ≫ P.hom = t' ≫ g) :
    c.inv t a h₁ = c.inv t' a' h₃ := by
  subst ht ha
  rfl

/-! ### Two charts over the same base morphism define the same operations -/

theorem pointed_unit : ptLift P g (𝟙 V) (𝟙 V ≫ g ≫ s.left) (by simp) ≫
    c.ψ.hom = (1 : Over.mk (𝟙 V) ⟶ c.A.X) :=
  c.pointed (𝟙 V)

theorem isMonHom_trans (c₁ c₂ : Chart P s V g) : IsMonHom (c₁.ψ.inv ≫ c₂.ψ.hom) := by
  refine pointedMorphismRigidity.{u} V c₁.A.toGrp c₂.A.toGrp c₁.A.isAbelian
    inferInstance inferInstance inferInstance (c₁.ψ.inv ≫ c₂.ψ.hom) ?_
  have h₁ := c₁.pointed_unit
  have h₂ := c₂.pointed_unit
  have hu : (toUnit (Over.mk (𝟙 V)) : Over.mk (𝟙 V) ⟶ 𝟙_ (Over V)) = 𝟙 (𝟙_ (Over V)) :=
    toUnit_unique _ _
  have e₁ : η[c₁.A.X] = (1 : Over.mk (𝟙 V) ⟶ c₁.A.X) := by
    rw [CategoryTheory.Hom.one_def, hu]; exact (Category.id_comp _).symm
  have e₂ : η[c₂.A.X] = (1 : Over.mk (𝟙 V) ⟶ c₂.A.X) := by
    rw [CategoryTheory.Hom.one_def, hu]; exact (Category.id_comp _).symm
  change η[c₁.A.X] ≫ c₁.ψ.inv ≫ c₂.ψ.hom = η[c₂.A.X]
  rw [e₁, e₂, ← h₁, ← h₂]
  simp

theorem loc_trans (c₁ c₂ : Chart P s V g) {Z : Scheme.{u}} (t : Z ⟶ V) (a : Z ⟶ P.left)
    (ha : a ≫ P.hom = t ≫ g) :
    c₂.loc t a ha = c₁.loc t a ha ≫ (c₁.ψ.inv ≫ c₂.ψ.hom) := by
  simp [loc]

theorem glob_trans (c₁ c₂ : Chart P s V g) {Z : Scheme.{u}} {t : Z ⟶ V}
    (x : Over.mk t ⟶ c₁.A.X) : c₂.glob (x ≫ (c₁.ψ.inv ≫ c₂.ψ.hom)) = c₁.glob x := by
  simp [glob]

theorem mul_eq (c₁ c₂ : Chart P s V g) {Z : Scheme.{u}} (t : Z ⟶ V) (a b : Z ⟶ P.left)
    (ha : a ≫ P.hom = t ≫ g) (hb : b ≫ P.hom = t ≫ g) :
    c₁.mul t a b ha hb = c₂.mul t a b ha hb := by
  have := c₁.isMonHom_trans c₂
  rw [mul, mul, loc_trans c₁ c₂, loc_trans c₁ c₂, ← MonObj.mul_comp, glob_trans]

theorem inv_eq (c₁ c₂ : Chart P s V g) {Z : Scheme.{u}} (t : Z ⟶ V) (a : Z ⟶ P.left)
    (ha : a ≫ P.hom = t ≫ g) :
    c₁.inv t a ha = c₂.inv t a ha := by
  have := c₁.isMonHom_trans c₂
  rw [inv, inv, loc_trans c₁ c₂, ← GrpObj.inv_comp, glob_trans]

theorem mul_eq_of_eq {g₁ g₂ : V ⟶ S} (hg : g₁ = g₂) (c₁ : Chart P s V g₁)
    (c₂ : Chart P s V g₂) {Z : Scheme.{u}} (t : Z ⟶ V) (a b : Z ⟶ P.left)
    (ha₁ : a ≫ P.hom = t ≫ g₁) (hb₁ : b ≫ P.hom = t ≫ g₁)
    (ha₂ : a ≫ P.hom = t ≫ g₂) (hb₂ : b ≫ P.hom = t ≫ g₂) :
    c₁.mul t a b ha₁ hb₁ = c₂.mul t a b ha₂ hb₂ := by
  subst hg
  exact mul_eq c₁ c₂ t a b ha₁ hb₁

theorem inv_eq_of_eq {g₁ g₂ : V ⟶ S} (hg : g₁ = g₂) (c₁ : Chart P s V g₁)
    (c₂ : Chart P s V g₂) {Z : Scheme.{u}} (t : Z ⟶ V) (a : Z ⟶ P.left)
    (ha₁ : a ≫ P.hom = t ≫ g₁) (ha₂ : a ≫ P.hom = t ≫ g₂) :
    c₁.inv t a ha₁ = c₂.inv t a ha₂ := by
  subst hg
  exact inv_eq c₁ c₂ t a ha₁

/-! ### Restriction of a chart along a morphism of bases -/

/-- The isomorphism of the restricted chart. -/
def restrictψ {V' : Scheme.{u}} (h : V' ⟶ V) :
    (Over.pullback (h ≫ g)).obj P ≅ ((AbelianScheme.baseChange h).obj c.A).X :=
  restrictIso P h g ≪≫ (Over.pullback h).mapIso c.ψ

theorem ptLift_restrictψ {V' Z : Scheme.{u}} (h : V' ⟶ V) (t : Z ⟶ V') (a : Z ⟶ P.left)
    (ha : a ≫ P.hom = t ≫ h ≫ g) :
    ptLift P (h ≫ g) t a ha ≫ (c.restrictψ h).hom =
      unitPt h t ≫ (Over.pullback h).map (c.loc (t ≫ h) a (by rw [ha, Category.assoc])) := by
  change ptLift P (h ≫ g) t a ha ≫ (restrictIso P h g).hom ≫ (Over.pullback h).map c.ψ.hom =
    unitPt h t ≫ (Over.pullback h).map
      (ptLift P g (t ≫ h) a (by rw [ha, Category.assoc]) ≫ c.ψ.hom)
  rw [Functor.map_comp, reassoc_of% (ptLift_restrictIso P g h t a ha)]

open scoped CategoryTheory.Obj in
/-- The restriction of a chart along `h : V' ⟶ V`, using the base-changed abelian scheme. -/
def restrict {V' : Scheme.{u}} (h : V' ⟶ V) : Chart P s V' (h ≫ g) where
  A := (AbelianScheme.baseChange h).obj c.A
  ψ := c.restrictψ h
  pointed := by
    intro Z t
    rw [c.ptLift_restrictψ h t]
    rw [c.loc_congr (show t ≫ (h ≫ g) ≫ s.left = (t ≫ h) ≫ g ≫ s.left by simp)
      _ (by simp)]
    rw [c.loc_one]
    erw [Functor.map_one]
    exact MonObj.comp_one _

/-- A local point of the chart, transported to the restricted chart. -/
def rmap {V' Z : Scheme.{u}} (h : V' ⟶ V) {t : Z ⟶ V'} (x : Over.mk (t ≫ h) ⟶ c.A.X) :
    Over.mk t ⟶ (c.restrict h).A.X :=
  unitPt h t ≫ (Over.pullback h).map x

open scoped CategoryTheory.Obj in
theorem rmap_mul {V' Z : Scheme.{u}} (h : V' ⟶ V) {t : Z ⟶ V'}
    (x y : Over.mk (t ≫ h) ⟶ c.A.X) : c.rmap h (x * y) = c.rmap h x * c.rmap h y := by
  change unitPt h t ≫ (Over.pullback h).map (x * y) = _
  rw [Functor.map_mul, MonObj.comp_mul]
  rfl

open scoped CategoryTheory.Obj in
theorem rmap_inv {V' Z : Scheme.{u}} (h : V' ⟶ V) {t : Z ⟶ V'}
    (x : Over.mk (t ≫ h) ⟶ c.A.X) : c.rmap h x⁻¹ = (c.rmap h x)⁻¹ := by
  change unitPt h t ≫ (Over.pullback h).map x⁻¹ = _
  rw [Functor.map_inv', GrpObj.comp_inv]
  rfl

theorem restrict_loc {V' Z : Scheme.{u}} (h : V' ⟶ V) (t : Z ⟶ V') (a : Z ⟶ P.left)
    (ha : a ≫ P.hom = t ≫ h ≫ g) :
    (c.restrict h).loc t a ha = c.rmap h (c.loc (t ≫ h) a (by rw [ha, Category.assoc])) :=
  c.ptLift_restrictψ h t a ha

theorem restrict_glob {V' Z : Scheme.{u}} (h : V' ⟶ V) {t : Z ⟶ V'}
    (x : Over.mk (t ≫ h) ⟶ c.A.X) :
    (c.restrict h).glob (c.rmap h x) = c.glob x := by
  have e := c.restrict_loc h t (c.glob x) (by rw [c.glob_w x, Category.assoc])
  rw [c.loc_glob] at e
  rw [← e, glob_loc]

theorem restrict_mul {V' Z : Scheme.{u}} (h : V' ⟶ V) (t : Z ⟶ V') (a b : Z ⟶ P.left)
    (ha : a ≫ P.hom = t ≫ h ≫ g) (hb : b ≫ P.hom = t ≫ h ≫ g) :
    (c.restrict h).mul t a b ha hb = c.mul (t ≫ h) a b (by rw [ha, Category.assoc])
      (by rw [hb, Category.assoc]) := by
  rw [mul, mul, restrict_loc, restrict_loc, ← rmap_mul, restrict_glob]

theorem restrict_inv {V' Z : Scheme.{u}} (h : V' ⟶ V) (t : Z ⟶ V') (a : Z ⟶ P.left)
    (ha : a ≫ P.hom = t ≫ h ≫ g) :
    (c.restrict h).inv t a ha = c.inv (t ≫ h) a (by rw [ha, Category.assoc]) := by
  rw [inv, inv, restrict_loc, ← rmap_inv, restrict_glob]

/-! ### Charts over different base morphisms agree on common points -/

theorem mul_eq_mul {V₁ V₂ : Scheme.{u}} {g₁ : V₁ ⟶ S} {g₂ : V₂ ⟶ S}
    (c₁ : Chart P s V₁ g₁) (c₂ : Chart P s V₂ g₂) {Z : Scheme.{u}} {t₁ : Z ⟶ V₁}
    {t₂ : Z ⟶ V₂} (ht : t₁ ≫ g₁ = t₂ ≫ g₂) {a₁ a₂ b₁ b₂ : Z ⟶ P.left} (ha : a₁ = a₂)
    (hb : b₁ = b₂) (ha₁ : a₁ ≫ P.hom = t₁ ≫ g₁) (hb₁ : b₁ ≫ P.hom = t₁ ≫ g₁)
    (ha₂ : a₂ ≫ P.hom = t₂ ≫ g₂) (hb₂ : b₂ ≫ P.hom = t₂ ≫ g₂) :
    c₁.mul t₁ a₁ b₁ ha₁ hb₁ = c₂.mul t₂ a₂ b₂ ha₂ hb₂ := by
  subst ha hb
  have h₁ : c₁.mul t₁ a₁ b₁ ha₁ hb₁ = (c₁.restrict (pullback.fst g₁ g₂)).mul
      (pullback.lift t₁ t₂ ht) a₁ b₁ (by rw [pullback.lift_fst_assoc, ha₁])
      (by rw [pullback.lift_fst_assoc, hb₁]) := by
    rw [restrict_mul]
    exact c₁.mul_congr (pullback.lift_fst _ _ _).symm rfl rfl _ _ _ _
  have h₂ : c₂.mul t₂ a₁ b₁ ha₂ hb₂ = (c₂.restrict (pullback.snd g₁ g₂)).mul
      (pullback.lift t₁ t₂ ht) a₁ b₁ (by rw [pullback.lift_snd_assoc, ha₂])
      (by rw [pullback.lift_snd_assoc, hb₂]) := by
    rw [restrict_mul]
    exact c₂.mul_congr (pullback.lift_snd _ _ _).symm rfl rfl _ _ _ _
  rw [h₁, h₂]
  exact mul_eq_of_eq pullback.condition _ _ _ _ _ _ _ _ _

theorem inv_eq_inv {V₁ V₂ : Scheme.{u}} {g₁ : V₁ ⟶ S} {g₂ : V₂ ⟶ S}
    (c₁ : Chart P s V₁ g₁) (c₂ : Chart P s V₂ g₂) {Z : Scheme.{u}} {t₁ : Z ⟶ V₁}
    {t₂ : Z ⟶ V₂} (ht : t₁ ≫ g₁ = t₂ ≫ g₂) {a₁ a₂ : Z ⟶ P.left} (ha : a₁ = a₂)
    (ha₁ : a₁ ≫ P.hom = t₁ ≫ g₁) (ha₂ : a₂ ≫ P.hom = t₂ ≫ g₂) :
    c₁.inv t₁ a₁ ha₁ = c₂.inv t₂ a₂ ha₂ := by
  subst ha
  have h₁ : c₁.inv t₁ a₁ ha₁ = (c₁.restrict (pullback.fst g₁ g₂)).inv
      (pullback.lift t₁ t₂ ht) a₁ (by rw [pullback.lift_fst_assoc, ha₁]) := by
    rw [restrict_inv]
    exact c₁.inv_congr (pullback.lift_fst _ _ _).symm rfl _ _
  have h₂ : c₂.inv t₂ a₁ ha₂ = (c₂.restrict (pullback.snd g₁ g₂)).inv
      (pullback.lift t₁ t₂ ht) a₁ (by rw [pullback.lift_snd_assoc, ha₂]) := by
    rw [restrict_inv]
    exact c₂.inv_congr (pullback.lift_snd _ _ _).symm rfl _ _
  rw [h₁, h₂]
  exact inv_eq_of_eq pullback.condition _ _ _ _ _ _

end Chart

/-! ### Gluing the chart operations over an open cover of the base -/

section Glue

variable {P s} {𝒰 : S.OpenCover.{u}} (c : ∀ i, Chart P s (𝒰.X i) (𝒰.f i))

theorem pt_w {T : Over S} (x : T ⟶ P) (i : 𝒰.I₀) :
    (pullback.fst T.hom (𝒰.f i) ≫ x.left) ≫ P.hom = pullback.snd T.hom (𝒰.f i) ≫ 𝒰.f i := by
  rw [Category.assoc, Over.w x, pullback.condition]

theorem overlap_w {T : Over S} (i j : 𝒰.I₀) :
    (pullback.fst (pullback.fst T.hom (𝒰.f i)) (pullback.fst T.hom (𝒰.f j)) ≫
        pullback.snd T.hom (𝒰.f i)) ≫ 𝒰.f i =
      (pullback.snd (pullback.fst T.hom (𝒰.f i)) (pullback.fst T.hom (𝒰.f j)) ≫
        pullback.snd T.hom (𝒰.f j)) ≫ 𝒰.f j := by
  rw [Category.assoc, Category.assoc, ← pullback.condition, ← pullback.condition,
    pullback.condition_assoc]

/-- The glued product of two points of `P`, as a morphism of schemes. -/
def gmulLeft {T : Over S} (x y : T ⟶ P) : T.left ⟶ P.left :=
  Scheme.Cover.glueMorphisms (𝒰.pullback₁ T.hom)
    (fun i => (c i).mul (pullback.snd T.hom (𝒰.f i)) (pullback.fst T.hom (𝒰.f i) ≫ x.left)
      (pullback.fst T.hom (𝒰.f i) ≫ y.left) (pt_w x i) (pt_w y i))
    (by
      intro (i : 𝒰.I₀) (j : 𝒰.I₀)
      change pullback.fst (pullback.fst T.hom (𝒰.f i)) (pullback.fst T.hom (𝒰.f j)) ≫
          (c i).mul (pullback.snd T.hom (𝒰.f i)) (pullback.fst T.hom (𝒰.f i) ≫ x.left)
            (pullback.fst T.hom (𝒰.f i) ≫ y.left) (pt_w x i) (pt_w y i) =
        pullback.snd (pullback.fst T.hom (𝒰.f i)) (pullback.fst T.hom (𝒰.f j)) ≫
          (c j).mul (pullback.snd T.hom (𝒰.f j)) (pullback.fst T.hom (𝒰.f j) ≫ x.left)
            (pullback.fst T.hom (𝒰.f j) ≫ y.left) (pt_w x j) (pt_w y j)
      rw [Chart.comp_mul, Chart.comp_mul]
      exact Chart.mul_eq_mul _ _ (overlap_w i j) (pullback.condition_assoc _)
        (pullback.condition_assoc _) _ _ _ _)

/-- The glued inverse of a point of `P`, as a morphism of schemes. -/
def ginvLeft {T : Over S} (x : T ⟶ P) : T.left ⟶ P.left :=
  Scheme.Cover.glueMorphisms (𝒰.pullback₁ T.hom)
    (fun i => (c i).inv (pullback.snd T.hom (𝒰.f i)) (pullback.fst T.hom (𝒰.f i) ≫ x.left)
      (pt_w x i))
    (by
      intro (i : 𝒰.I₀) (j : 𝒰.I₀)
      change pullback.fst (pullback.fst T.hom (𝒰.f i)) (pullback.fst T.hom (𝒰.f j)) ≫
          (c i).inv (pullback.snd T.hom (𝒰.f i)) (pullback.fst T.hom (𝒰.f i) ≫ x.left)
            (pt_w x i) =
        pullback.snd (pullback.fst T.hom (𝒰.f i)) (pullback.fst T.hom (𝒰.f j)) ≫
          (c j).inv (pullback.snd T.hom (𝒰.f j)) (pullback.fst T.hom (𝒰.f j) ≫ x.left)
            (pt_w x j)
      rw [Chart.comp_inv, Chart.comp_inv]
      exact Chart.inv_eq_inv _ _ (overlap_w i j) (pullback.condition_assoc _) _ _)

theorem fst_gmulLeft {T : Over S} (x y : T ⟶ P) (i : 𝒰.I₀) :
    pullback.fst T.hom (𝒰.f i) ≫ gmulLeft c x y =
      (c i).mul (pullback.snd T.hom (𝒰.f i)) (pullback.fst T.hom (𝒰.f i) ≫ x.left)
        (pullback.fst T.hom (𝒰.f i) ≫ y.left) (pt_w x i) (pt_w y i) := by
  unfold gmulLeft
  exact Scheme.Cover.ι_glueMorphisms (𝒰.pullback₁ T.hom)
    (fun (i : 𝒰.I₀) => (c i).mul (pullback.snd T.hom (𝒰.f i))
      (pullback.fst T.hom (𝒰.f i) ≫ x.left) (pullback.fst T.hom (𝒰.f i) ≫ y.left)
      (pt_w x i) (pt_w y i)) _ i

theorem fst_ginvLeft {T : Over S} (x : T ⟶ P) (i : 𝒰.I₀) :
    pullback.fst T.hom (𝒰.f i) ≫ ginvLeft c x =
      (c i).inv (pullback.snd T.hom (𝒰.f i)) (pullback.fst T.hom (𝒰.f i) ≫ x.left)
        (pt_w x i) := by
  unfold ginvLeft
  exact Scheme.Cover.ι_glueMorphisms (𝒰.pullback₁ T.hom)
    (fun (i : 𝒰.I₀) => (c i).inv (pullback.snd T.hom (𝒰.f i))
      (pullback.fst T.hom (𝒰.f i) ≫ x.left) (pt_w x i)) _ i

omit c in
theorem left_ext {T : Over S} {X : Scheme.{u}} {a b : T.left ⟶ X}
    (h : ∀ i, pullback.fst T.hom (𝒰.f i) ≫ a = pullback.fst T.hom (𝒰.f i) ≫ b) : a = b :=
  Scheme.Cover.hom_ext (𝒰.pullback₁ T.hom) _ _ h

omit c in
theorem hom_ext' {T : Over S} {x y : T ⟶ P}
    (h : ∀ i, pullback.fst T.hom (𝒰.f i) ≫ x.left = pullback.fst T.hom (𝒰.f i) ≫ y.left) :
    x = y :=
  Over.OverMorphism.ext (left_ext (𝒰 := 𝒰) h)

/-- The glued product of two points of `P`. -/
def gmul {T : Over S} (x y : T ⟶ P) : T ⟶ P :=
  Over.homMk (gmulLeft c x y) (by
    apply left_ext (𝒰 := 𝒰)
    intro i
    rw [reassoc_of% (fst_gmulLeft c x y i), Chart.mul_w, pullback.condition])

/-- The glued inverse of a point of `P`. -/
def ginv {T : Over S} (x : T ⟶ P) : T ⟶ P :=
  Over.homMk (ginvLeft c x) (by
    apply left_ext (𝒰 := 𝒰)
    intro i
    rw [reassoc_of% (fst_ginvLeft c x i), Chart.inv_w, pullback.condition])

theorem comp_gmul_left {T : Over S} (x y : T ⟶ P) (i : 𝒰.I₀) {Z : Scheme.{u}}
    (z : Z ⟶ T.left) (t : Z ⟶ 𝒰.X i) (hz : z ≫ T.hom = t ≫ 𝒰.f i) :
    z ≫ (gmul c x y).left = (c i).mul t (z ≫ x.left) (z ≫ y.left)
      (by rw [Category.assoc, Over.w x, hz]) (by rw [Category.assoc, Over.w y, hz]) := by
  have hz' : z = pullback.lift z t hz ≫ pullback.fst T.hom (𝒰.f i) :=
    (pullback.lift_fst _ _ _).symm
  conv_lhs => rw [hz']
  change (pullback.lift z t hz ≫ pullback.fst T.hom (𝒰.f i)) ≫ gmulLeft c x y = _
  rw [Category.assoc, fst_gmulLeft, Chart.comp_mul]
  exact (c i).mul_congr (pullback.lift_snd _ _ _) (pullback.lift_fst_assoc _ _ _ _)
    (pullback.lift_fst_assoc _ _ _ _) _ _ _ _

theorem comp_ginv_left {T : Over S} (x : T ⟶ P) (i : 𝒰.I₀) {Z : Scheme.{u}}
    (z : Z ⟶ T.left) (t : Z ⟶ 𝒰.X i) (hz : z ≫ T.hom = t ≫ 𝒰.f i) :
    z ≫ (ginv c x).left = (c i).inv t (z ≫ x.left)
      (by rw [Category.assoc, Over.w x, hz]) := by
  have hz' : z = pullback.lift z t hz ≫ pullback.fst T.hom (𝒰.f i) :=
    (pullback.lift_fst _ _ _).symm
  conv_lhs => rw [hz']
  change (pullback.lift z t hz ≫ pullback.fst T.hom (𝒰.f i)) ≫ ginvLeft c x = _
  rw [Category.assoc, fst_ginvLeft, Chart.comp_inv]
  exact (c i).inv_congr (pullback.lift_snd _ _ _) (pullback.lift_fst_assoc _ _ _ _) _ _

theorem loc_gmul {T : Over S} (x y : T ⟶ P) (i : 𝒰.I₀) :
    (c i).loc (pullback.snd T.hom (𝒰.f i)) (pullback.fst T.hom (𝒰.f i) ≫ (gmul c x y).left)
        (pt_w _ i) =
      (c i).loc _ _ (pt_w x i) * (c i).loc _ _ (pt_w y i) := by
  rw [(c i).loc_congr (comp_gmul_left c x y i _ _ pullback.condition) _
    ((c i).mul_w _ _ _ _ _), Chart.loc_mul]

theorem loc_ginv {T : Over S} (x : T ⟶ P) (i : 𝒰.I₀) :
    (c i).loc (pullback.snd T.hom (𝒰.f i)) (pullback.fst T.hom (𝒰.f i) ≫ (ginv c x).left)
        (pt_w _ i) = ((c i).loc _ _ (pt_w x i))⁻¹ := by
  rw [(c i).loc_congr (comp_ginv_left c x i _ _ pullback.condition) _
    ((c i).inv_w _ _ _), Chart.loc_inv]

theorem loc_gone {T : Over S} (i : 𝒰.I₀) :
    (c i).loc (pullback.snd T.hom (𝒰.f i))
        (pullback.fst T.hom (𝒰.f i) ≫ (toUnit T ≫ s).left) (pt_w _ i) = 1 := by
  rw [(c i).loc_congr (show pullback.fst T.hom (𝒰.f i) ≫ (toUnit T ≫ s).left =
      pullback.snd T.hom (𝒰.f i) ≫ 𝒰.f i ≫ s.left by
        rw [Over.comp_left, Over.toUnit_left, pullback.condition_assoc]) _ (by simp),
    Chart.loc_one]

theorem gmul_assoc {T : Over S} (x y z : T ⟶ P) :
    gmul c (gmul c x y) z = gmul c x (gmul c y z) := by
  refine hom_ext' (𝒰 := 𝒰) fun i => (c i).loc_inj (pt_w _ i) (pt_w _ i) ?_
  rw [loc_gmul, loc_gmul, loc_gmul, loc_gmul, mul_assoc]

theorem gmul_comm {T : Over S} (x y : T ⟶ P) : gmul c x y = gmul c y x := by
  refine hom_ext' (𝒰 := 𝒰) fun i => (c i).loc_inj (pt_w _ i) (pt_w _ i) ?_
  rw [loc_gmul, loc_gmul, mul_comm]

theorem gone_mul {T : Over S} (x : T ⟶ P) : gmul c (toUnit T ≫ s) x = x := by
  refine hom_ext' (𝒰 := 𝒰) fun i => (c i).loc_inj (pt_w _ i) (pt_w _ i) ?_
  rw [loc_gmul, loc_gone, one_mul]

theorem gmul_one {T : Over S} (x : T ⟶ P) : gmul c x (toUnit T ≫ s) = x := by
  refine hom_ext' (𝒰 := 𝒰) fun i => (c i).loc_inj (pt_w _ i) (pt_w _ i) ?_
  rw [loc_gmul, loc_gone, mul_one]

theorem ginv_mul {T : Over S} (x : T ⟶ P) : gmul c (ginv c x) x = toUnit T ≫ s := by
  refine hom_ext' (𝒰 := 𝒰) fun i => (c i).loc_inj (pt_w _ i) (pt_w _ i) ?_
  rw [loc_gmul, loc_ginv, inv_mul_cancel, loc_gone]

theorem comp_gmul {T T' : Over S} (φ : T' ⟶ T) (x y : T ⟶ P) :
    φ ≫ gmul c x y = gmul c (φ ≫ x) (φ ≫ y) := by
  refine hom_ext' (𝒰 := 𝒰) fun i => ?_
  have hz : (pullback.fst T'.hom (𝒰.f i) ≫ φ.left) ≫ T.hom =
      pullback.snd T'.hom (𝒰.f i) ≫ 𝒰.f i := by
    rw [Category.assoc, Over.w φ, pullback.condition]
  rw [Over.comp_left, ← Category.assoc, comp_gmul_left c x y i _ _ hz,
    comp_gmul_left c (φ ≫ x) (φ ≫ y) i _ _ pullback.condition]
  exact (c i).mul_congr rfl (by simp) (by simp) _ _ _ _

theorem comp_ginv {T T' : Over S} (φ : T' ⟶ T) (x : T ⟶ P) :
    φ ≫ ginv c x = ginv c (φ ≫ x) := by
  refine hom_ext' (𝒰 := 𝒰) fun i => ?_
  have hz : (pullback.fst T'.hom (𝒰.f i) ≫ φ.left) ≫ T.hom =
      pullback.snd T'.hom (𝒰.f i) ≫ 𝒰.f i := by
    rw [Category.assoc, Over.w φ, pullback.condition]
  rw [Over.comp_left, ← Category.assoc, comp_ginv_left c x i _ _ hz,
    comp_ginv_left c (φ ≫ x) i _ _ pullback.condition]
  exact (c i).inv_congr rfl (by simp) _ _

/-- The glued commutative group structure on the points of `P` with values in `T`. -/
@[instance_reducible]
def homGroup (T : Over S) : CommGroup (T ⟶ P) where
  mul := gmul c
  one := toUnit T ≫ s
  inv := ginv c
  mul_assoc := gmul_assoc c
  one_mul := gone_mul c
  mul_one := gmul_one c
  inv_mul_cancel := ginv_mul c
  mul_comm := gmul_comm c

/-- The presheaf of commutative groups of points of `P`. -/
def pointsFunctor : (Over S)ᵒᵖ ⥤ CommGrpCat.{u} where
  obj T := @CommGrpCat.of (T.unop ⟶ P) (homGroup c T.unop)
  map {T T'} φ :=
    letI := homGroup c T.unop
    letI := homGroup c T'.unop
    CommGrpCat.ofHom
      { toFun := fun x => φ.unop ≫ x
        map_one' := by
          change φ.unop ≫ toUnit _ ≫ s = toUnit _ ≫ s
          rw [comp_toUnit_assoc]
        map_mul' := fun x y => comp_gmul c φ.unop x y }
  map_id T := by
    apply CommGrpCat.ext
    intro x
    exact Category.id_comp x
  map_comp φ ψ := by
    apply CommGrpCat.ext
    intro x
    exact Category.assoc _ _ x

/-- The points presheaf is represented by `P`. -/
def pointsRep : (pointsFunctor c ⋙ forget _).RepresentableBy P where
  homEquiv := Equiv.refl _
  homEquiv_comp _ _ := rfl

end Glue

/-! ### Recentred charts from the local hypothesis -/

/-- The restriction of the section `s` along `g`, a section of the restriction of `P`. -/
def sec {V : Scheme.{u}} (g : V ⟶ S) : 𝟙_ (Over V) ⟶ (Over.pullback g).obj P :=
  Over.homMk (pullback.lift (g ≫ s.left) (𝟙 V)
    (by rw [Category.assoc, sec_hom, Category.comp_id]; exact (Category.id_comp g).symm))
    (pullback.lift_snd _ _ _)

theorem ptLift_eq {V Z : Scheme.{u}} (g : V ⟶ S) (t : Z ⟶ V)
    (h : (t ≫ g ≫ s.left) ≫ P.hom = t ≫ g) :
    ptLift P g t (t ≫ g ≫ s.left) h = toUnit (Over.mk t) ≫ sec P s g := by
  ext
  apply pullback.hom_ext
  · simp [ptLift, sec, Over.toUnit_left, pullback.lift_fst]
  · simp [ptLift, sec, Over.toUnit_left, pullback.lift_snd]

omit P s in
theorem comp_mulRight_inv {V : Scheme.{u}} (A : AbelianScheme V) (q : 𝟙_ (Over V) ⟶ A.X) :
    q ≫ (GrpObj.mulRight q⁻¹).hom = η[A.X] := by
  rw [GrpObj.mulRight_hom, comp_lift_assoc, Category.comp_id, comp_toUnit_assoc, toUnit_unit,
    Category.id_comp, ← CategoryTheory.Hom.mul_def, mul_inv_cancel, CategoryTheory.Hom.one_def,
    toUnit_unit, Category.id_comp]

/-- A chart from an arbitrary local isomorphism, recentred by a translation so that the
restriction of `s` becomes the unit. -/
def Chart.ofIso {V : Scheme.{u}} {g : V ⟶ S} (A : AbelianScheme V)
    (e : (Over.pullback g).obj P ≅ A.X) : Chart P s V g where
  A := A
  ψ := e ≪≫ GrpObj.mulRight (sec P s g ≫ e.hom)⁻¹
  pointed := by
    intro Z t
    rw [ptLift_eq, Iso.trans_hom, Category.assoc, ← Category.assoc (sec P s g),
      comp_mulRight_inv, CategoryTheory.Hom.one_def]

omit P s in
theorem prop_hom_of_iso (Q : MorphismProperty Scheme.{u}) [Q.RespectsIso] {V : Scheme.{u}}
    {X Y : Over V} (e : X ≅ Y) (h : Q Y.hom) : Q X.hom := by
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget V).mapIso e).hom)
  rw [← Over.w e.hom, Q.cancel_left_of_respectsIso]
  exact h

omit P s in
theorem smooth_hom_of_iso {V : Scheme.{u}} {X Y : Over V} (e : X ≅ Y) (h : Smooth Y.hom) :
    Smooth X.hom := by
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget V).mapIso e).hom)
  rw [← Over.w e.hom]
  infer_instance

end OpenCoverStructure

open OpenCoverStructure in
/-- An abelian-scheme structure on `P` with unit `s`, from local abelian charts. -/
theorem abelianSchemeStructureOfOpenCover : AbelianSchemeStructureOfOpenCoverStatement.{u} := by
  intro S P s 𝒰 hloc
  choose B e using hloc
  let c : ∀ i, Chart P s (𝒰.X i) (𝒰.f i) := fun i => Chart.ofIso P s (B i) (e i).some
  let : CommGrpObj P := CommGrpObj.ofRepresentableBy P (pointsFunctor c) (pointsRep c)
  have : IsZariskiLocalAtTarget @Smooth.{u} := HasRingHomProperty.instIsZariskiLocalAtTarget _
  have hsm : Smooth P.hom := IsZariskiLocalAtTarget.of_openCover 𝒰 fun i =>
    smooth_hom_of_iso (e i).some (B i).smooth
  have hpr : IsProper P.hom := IsZariskiLocalAtTarget.of_openCover 𝒰 fun i =>
    prop_hom_of_iso @IsProper (e i).some (B i).proper
  have hgc : GeometricallyConnected P.hom := by
    rw [geometricallyConnected_iff]
    exact IsZariskiLocalAtTarget.of_openCover 𝒰 fun i =>
      prop_hom_of_iso (geometrically (ConnectedSpace ·)) (e i).some
        ((geometricallyConnected_iff _).mp (B i).geometricallyConnected)
  refine ⟨
    { toCommGroupScheme := { toGrp := ⟨P⟩ }
      smooth := hsm
      proper := hpr
      geometricallyConnected := hgc }, Iso.refl P, ?_⟩
  change s ≫ 𝟙 P = toUnit (𝟙_ (Over S)) ≫ s
  rw [Category.comp_id, toUnit_unit, Category.id_comp]

end Langlands.AbelianScheme
