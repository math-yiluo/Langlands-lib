import Langlands.AlgebraicGeometry.SmoothLifting.LiftModule
import Langlands.GroupScheme.Lie.SquareZeroKernel

/-! # Square-zero reduction kernels of arbitrary group schemes

For a group scheme `G` over `Spec R` (not assumed affine or separated), an `R`-algebra `A` and a
square-zero ideal `J` of `A`, the kernel of `G(A) → G(A ⧸ J)` is a commutative group, and its
group law is the addition of lifts of the identity computed by affine combinations in charts.
-/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Lie.NonaffineKernel

open Langlands.AlgebraicGeometry.SmoothLifting

variable {R : CommRingCat.{u}} (G : GroupScheme (Spec R))
variable {A : Type u} [CommRing A] [Algebra R A] (J : Ideal A)

/-- Reduction of actual points modulo an ideal. -/
abbrev reduction : AffinePoints G A →* AffinePoints G (A ⧸ J) :=
  SquareZero.reduction G J

/-- The actual reduction kernel. No affineness assumption is made. -/
abbrev kernel : Subgroup (AffinePoints G A) := SquareZero.kernel G J

/-- The structure morphism of an affine test. -/
abbrev str (A : Type u) [CommRing A] [Algebra R A] : Spec (CommRingCat.of A) ⟶ Spec R :=
  Spec.map (CommRingCat.ofHom (algebraMap R A))

/-- The identity point modulo `J`. -/
abbrev unit₀ : Spec (CommRingCat.of (CommRingCat.of A ⧸ J)) ⟶ G.X.left :=
  (1 : AffinePoints G (A ⧸ J)).left

theorem left_comp (x : AffinePoints G A) : x.left ≫ G.X.hom = str A := Over.w x

theorem reduction_left (x : AffinePoints G A) :
    (reduction G J x).left = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ x.left := rfl

/-- Lifts of the identity: the data of `SmoothLifting` for the kernel. -/
abbrev KLift := GLift G.X.hom J (unit₀ G J) (str A)

/-- A kernel point as a lift of the identity. -/
def toLift (x : kernel G J) : KLift G J :=
  ⟨x.1.left, ⟨by rw [← reduction_left, show reduction G J x.1 = 1 from x.2],
    left_comp G x.1⟩⟩

/-- A lift of the identity as an actual point. -/
def ofLift (y : KLift G J) : AffinePoints G A := Over.homMk y.1 y.2.2

theorem ofLift_mem (y : KLift G J) : ofLift G J y ∈ kernel G J := by
  change reduction G J (ofLift G J y) = 1
  apply Over.OverMorphism.ext
  rw [reduction_left]
  exact y.2.1

/-- Kernel points are exactly lifts of the identity. -/
def kernelEquiv : kernel G J ≃ KLift G J where
  toFun := toLift G J
  invFun y := ⟨ofLift G J y, ofLift_mem G J y⟩
  left_inv _ := Subtype.ext (Over.OverMorphism.ext rfl)
  right_inv _ := rfl

/-- The identity point, as the base lift. -/
abbrev base : KLift G J := toLift G J 1

/-! ### Pairs of points -/

/-- The identity pair modulo `J`. -/
abbrev unitP : Spec (CommRingCat.of (CommRingCat.of A ⧸ J)) ⟶ (G.X ⊗ G.X).left :=
  (lift (1 : AffinePoints G (A ⧸ J)) 1).left

/-- Lifts of the identity pair. -/
abbrev PLift := GLift (G.X ⊗ G.X).hom J (unitP G J) (str A)

/-- The pair of two lifts of the identity. -/
def pair (x y : KLift G J) : PLift G J :=
  ⟨(lift (ofLift G J x) (ofLift G J y)).left, ⟨by
    change ((algSpec R).map (CommAlgCat.ofHom (Ideal.Quotient.mkₐ R J)).op ≫
      lift (ofLift G J x) (ofLift G J y)).left = _
    rw [comp_lift]
    have hx : (algSpec R).map (CommAlgCat.ofHom (Ideal.Quotient.mkₐ R J)).op ≫ ofLift G J x = 1 :=
      ofLift_mem G J x
    have hy : (algSpec R).map (CommAlgCat.ofHom (Ideal.Quotient.mkₐ R J)).op ≫ ofLift G J y = 1 :=
      ofLift_mem G J y
    rw [hx, hy], Over.w _⟩⟩

theorem fst_unitP : unitP G J ≫ (fst G.X G.X).left = unit₀ G J :=
  congrArg (fun h => h.left) (lift_fst (1 : AffinePoints G (A ⧸ J)) (1 : AffinePoints G (A ⧸ J)))

theorem snd_unitP : unitP G J ≫ (snd G.X G.X).left = unit₀ G J :=
  congrArg (fun h => h.left) (lift_snd (1 : AffinePoints G (A ⧸ J)) (1 : AffinePoints G (A ⧸ J)))

theorem mul_unitP : unitP G J ≫ (μ : G.X ⊗ G.X ⟶ G.X).left = unit₀ G J :=
  congrArg (fun h => h.left) ((Hom.mul_def (1 : AffinePoints G (A ⧸ J)) 1).symm.trans (mul_one _))

theorem pair_fst (x y : KLift G J) :
    (pair G J x y).1 ≫ (fst G.X G.X).left = x.1 := by
  change (lift (ofLift G J x) (ofLift G J y)).left ≫ _ = _
  rw [← Over.comp_left, lift_fst]
  rfl

theorem pair_snd (x y : KLift G J) :
    (pair G J x y).1 ≫ (snd G.X G.X).left = y.1 := by
  change (lift (ofLift G J x) (ofLift G J y)).left ≫ _ = _
  rw [← Over.comp_left, lift_snd]
  rfl

theorem pair_mul (x y : KLift G J) :
    (pair G J x y).1 ≫ (μ : G.X ⊗ G.X ⟶ G.X).left = (ofLift G J x * ofLift G J y).left := by
  change (lift (ofLift G J x) (ofLift G J y)).left ≫ _ = _
  rw [← Over.comp_left, ← Hom.mul_def]

/-- Lifts of the identity pair are determined by their two components. -/
theorem PLift.ext {z z' : PLift G J} (h₁ : z.1 ≫ (fst G.X G.X).left = z'.1 ≫ (fst G.X G.X).left)
    (h₂ : z.1 ≫ (snd G.X G.X).left = z'.1 ≫ (snd G.X G.X).left) : z = z' := by
  let Z : (algSpec R).obj (op (CommAlgCat.of R A)) ⟶ G.X ⊗ G.X := Over.homMk z.1 z.2.2
  let Z' : (algSpec R).obj (op (CommAlgCat.of R A)) ⟶ G.X ⊗ G.X := Over.homMk z'.1 z'.2.2
  have : Z = Z' := by
    apply CartesianMonoidalCategory.hom_ext
    · exact Over.OverMorphism.ext h₁
    · exact Over.OverMorphism.ext h₂
  exact Subtype.ext (congrArg CommaMorphism.left this)

theorem ofLift_toLift (x : kernel G J) : ofLift G J (toLift G J x) = x.1 :=
  Over.OverMorphism.ext rfl

/-! ### The group law is addition of lifts -/

variable (hJ : SqZero J)

/-- The kernel point `x * y` is the sum of the lifts `x` and `y`. -/
theorem toLift_mul (x y : kernel G J) :
    LiftModule.of hJ (base G J) (toLift G J (x * y)) =
      LiftModule.of hJ (base G J) (toLift G J x) + LiftModule.of hJ (base G J) (toLift G J y) := by
  let e := base G J
  let X' : KLift G J := toLift G J x
  let Y' : KLift G J := toLift G J y
  let u : PLift G J := pair G J X' e
  let v : PLift G J := pair G J e Y'
  let eP : PLift G J := pair G J e e
  let w : LiftModule hJ eP := LiftModule.of hJ eP u + LiftModule.of hJ eP v
  have hfst : ∀ a b : KLift G J,
      (pair G J a b).map (fst G.X G.X).left (Over.w _) (fst_unitP G J) = a := fun a b =>
    Subtype.ext (pair_fst G J a b)
  have hsnd : ∀ a b : KLift G J,
      (pair G J a b).map (snd G.X G.X).left (Over.w _) (snd_unitP G J) = b := fun a b =>
    Subtype.ext (pair_snd G J a b)
  have hw1 : w.1 ≫ (fst G.X G.X).left = X'.1 := by
    change (LiftModule.lin hJ eP u v 1 1).1 ≫ _ = _
    rw [LiftModule.lin_map (fst G.X G.X).left (Over.w _) (fst_unitP G J) hJ eP e
      (pair_fst G J e e) u v 1 1, hfst, hfst]
    exact congrArg Subtype.val (add_zero (LiftModule.of hJ e X'))
  have hw2 : w.1 ≫ (snd G.X G.X).left = Y'.1 := by
    change (LiftModule.lin hJ eP u v 1 1).1 ≫ _ = _
    rw [LiftModule.lin_map (snd G.X G.X).left (Over.w _) (snd_unitP G J) hJ eP e
      (pair_snd G J e e) u v 1 1, hsnd, hsnd]
    exact congrArg Subtype.val (zero_add (LiftModule.of hJ e Y'))
  have hpair : pair G J X' Y' = w :=
    PLift.ext G J (by rw [pair_fst, hw1]) (by rw [pair_snd, hw2])
  have hμ : ∀ a b : KLift G J,
      (pair G J a b).map (μ : G.X ⊗ G.X ⟶ G.X).left (Over.w _) (mul_unitP G J) =
        toLift G J ⟨ofLift G J a * ofLift G J b,
          mul_mem (ofLift_mem G J a) (ofLift_mem G J b)⟩ := fun a b =>
    Subtype.ext (pair_mul G J a b)
  have hX : toLift G J ⟨ofLift G J X' * ofLift G J e,
      mul_mem (ofLift_mem G J X') (ofLift_mem G J e)⟩ = X' := by
    refine Subtype.ext ?_
    change (ofLift G J X' * ofLift G J e).left = X'.1
    rw [ofLift_toLift, ofLift_toLift, OneMemClass.coe_one, mul_one]
    rfl
  have hY : toLift G J ⟨ofLift G J e * ofLift G J Y',
      mul_mem (ofLift_mem G J e) (ofLift_mem G J Y')⟩ = Y' := by
    refine Subtype.ext ?_
    change (ofLift G J e * ofLift G J Y').left = Y'.1
    rw [ofLift_toLift, ofLift_toLift, OneMemClass.coe_one, one_mul]
    rfl
  apply Subtype.ext
  change (x.1 * y.1).left = (LiftModule.lin hJ e X' Y' 1 1).1
  have h1 : (pair G J X' Y').1 ≫ (μ : G.X ⊗ G.X ⟶ G.X).left = (x.1 * y.1).left := by
    rw [pair_mul, ofLift_toLift, ofLift_toLift]
  rw [← h1, hpair]
  change (LiftModule.lin hJ eP u v 1 1).1 ≫ _ = _
  rw [LiftModule.lin_map (μ : G.X ⊗ G.X ⟶ G.X).left (Over.w _) (mul_unitP G J) hJ eP e
    (by rw [pair_mul, ofLift_toLift, OneMemClass.coe_one, mul_one]; rfl) u v 1 1, hμ, hμ, hX, hY]

/-- Square-zero reduction kernels are commutative. -/
theorem kernel_mul_comm (hJ : SqZero J) (x y : kernel G J) : x * y = y * x := by
  apply (kernelEquiv G J).injective
  change toLift G J (x * y) = toLift G J (y * x)
  have h := toLift_mul G J hJ x y
  have h' := toLift_mul G J hJ y x
  exact (h.trans (add_comm _ _)).trans h'.symm

/-- The module of lifts of the identity, over the test algebra itself. -/
instance liftModuleModule : Module A (LiftModule hJ (base G J)) :=
  LiftModule.instModuleLift hJ (base G J)

/-- The additive identification of the kernel with lifts of the identity. -/
def toLM : Additive (kernel G J) →+ LiftModule hJ (base G J) where
  toFun x := LiftModule.of hJ (base G J) (toLift G J x.toMul)
  map_zero' := rfl
  map_add' x y := toLift_mul G J hJ x.toMul y.toMul

theorem toLM_injective : Function.Injective (toLM G J hJ) := fun _ _ h =>
  Additive.toMul.injective ((kernelEquiv G J).injective h)

theorem toLM_surjective : Function.Surjective (toLM G J hJ) := fun y =>
  ⟨Additive.ofMul ((kernelEquiv G J).symm y), (kernelEquiv G J).apply_symm_apply y⟩

section Instances

variable [hJ' : Fact (SqZero J)]

instance kernelCommGroup : CommGroup (kernel G J) :=
  { (inferInstance : Group (kernel G J)) with mul_comm := kernel_mul_comm G J hJ'.out }

/-- Scalars act on the kernel through lifts of the identity. -/
instance kernelSMul : SMul A (Additive (kernel G J)) :=
  ⟨fun a x => Additive.ofMul ((kernelEquiv G J).symm (a • toLM G J hJ'.out x))⟩

theorem toLM_smul (a : A) (x : Additive (kernel G J)) :
    toLM G J hJ'.out (a • x) = a • toLM G J hJ'.out x :=
  (kernelEquiv G J).apply_symm_apply _

/-- The kernel of reduction modulo a square-zero ideal is an `A`-module. -/
instance kernelModule : Module A (Additive (kernel G J)) :=
  Function.Injective.module A (toLM G J hJ'.out) (toLM_injective G J hJ'.out) (toLM_smul G J)

/-- The identification with lifts of the identity as a linear equivalence. -/
def toLMEquiv : Additive (kernel G J) ≃ₗ[A] LiftModule hJ'.out (base G J) :=
  LinearEquiv.ofBijective
    { toLM G J hJ'.out with map_smul' := toLM_smul G J }
    ⟨toLM_injective G J hJ'.out, toLM_surjective G J hJ'.out⟩

/-- The square-zero ideal acts trivially on the kernel. -/
theorem kernel_isTorsionBySet : Module.IsTorsionBySet A (Additive (kernel G J)) J := by
  intro x a
  apply toLM_injective G J hJ'.out
  rw [toLM_smul, map_zero]
  exact LiftModule.smul_eq_zero_of_mem hJ'.out (base G J) a.2 _

/-- The kernel as a module over the reduced ring `A ⧸ J`. -/
instance kernelQuotientModule : Module (A ⧸ J) (Additive (kernel G J)) :=
  (kernel_isTorsionBySet G J).module

instance kernelQuotientScalarTower : IsScalarTower A (A ⧸ J) (Additive (kernel G J)) :=
  (kernel_isTorsionBySet G J).isScalarTower

end Instances

/-! ### Conjugation -/

/-- The underlying morphism of a reduced point. -/
abbrev redLeft (p : AffinePoints G (A ⧸ J)) : Spec (CommRingCat.of (CommRingCat.of A ⧸ J)) ⟶
    G.X.left :=
  p.left

/-- Lifts of an arbitrary reduced point. -/
abbrev LiftAt (p : AffinePoints G (A ⧸ J)) := GLift G.X.hom J (redLeft G J p) (str A)

/-- An actual point as a lift of its reduction. -/
def liftAt (g : AffinePoints G A) : LiftAt G J (reduction G J g) :=
  ⟨g.left, ⟨(reduction_left G J g).symm, left_comp G g⟩⟩

/-- The conjugation morphism `(h, x) ↦ h x h⁻¹`. -/
abbrev conjMor : G.X ⊗ G.X ⟶ G.X := fst G.X G.X * snd G.X G.X * (fst G.X G.X)⁻¹

theorem lift_conjMor {T : Over (Spec R)} (h x : T ⟶ G.X) :
    lift h x ≫ conjMor G = h * x * h⁻¹ := by
  simp only [conjMor, MonObj.comp_mul, GrpObj.comp_inv, lift_fst, lift_snd]

/-- The reduced pair `(ḡ, 1)`. -/
abbrev unitG (g : AffinePoints G A) : Spec (CommRingCat.of (CommRingCat.of A ⧸ J)) ⟶
    (G.X ⊗ G.X).left :=
  (lift (reduction G J g) 1).left

/-- Lifts of the reduced pair `(ḡ, 1)`. -/
abbrev GLiftG (g : AffinePoints G A) := GLift (G.X ⊗ G.X).hom J (unitG G J g) (str A)

/-- The pair `(g, x)` for a kernel lift `x`. -/
def pairG (g : AffinePoints G A) (x : KLift G J) : GLiftG G J g :=
  ⟨(lift g (ofLift G J x)).left, ⟨by
    change ((algSpec R).map (CommAlgCat.ofHom (Ideal.Quotient.mkₐ R J)).op ≫
      lift g (ofLift G J x)).left = _
    rw [comp_lift]
    have hx : (algSpec R).map (CommAlgCat.ofHom (Ideal.Quotient.mkₐ R J)).op ≫ ofLift G J x = 1 :=
      ofLift_mem G J x
    rw [hx]
    rfl, Over.w _⟩⟩

theorem pairG_ext (g : AffinePoints G A) {z z' : GLiftG G J g}
    (h₁ : z.1 ≫ (fst G.X G.X).left = z'.1 ≫ (fst G.X G.X).left)
    (h₂ : z.1 ≫ (snd G.X G.X).left = z'.1 ≫ (snd G.X G.X).left) : z = z' := by
  let Z : (algSpec R).obj (op (CommAlgCat.of R A)) ⟶ G.X ⊗ G.X := Over.homMk z.1 z.2.2
  let Z' : (algSpec R).obj (op (CommAlgCat.of R A)) ⟶ G.X ⊗ G.X := Over.homMk z'.1 z'.2.2
  have : Z = Z' := by
    apply CartesianMonoidalCategory.hom_ext
    · exact Over.OverMorphism.ext h₁
    · exact Over.OverMorphism.ext h₂
  exact Subtype.ext (congrArg CommaMorphism.left this)

theorem pairG_fst (g : AffinePoints G A) (x : KLift G J) :
    (pairG G J g x).1 ≫ (fst G.X G.X).left = g.left :=
  congrArg (fun h => h.left) (lift_fst g (ofLift G J x))

theorem pairG_snd (g : AffinePoints G A) (x : KLift G J) :
    (pairG G J g x).1 ≫ (snd G.X G.X).left = x.1 :=
  congrArg (fun h => h.left) (lift_snd g (ofLift G J x))

theorem pairG_conj (g : AffinePoints G A) (x : KLift G J) :
    (pairG G J g x).1 ≫ (conjMor G).left = (g * ofLift G J x * g⁻¹).left :=
  congrArg (fun h => h.left) (lift_conjMor G g (ofLift G J x))

theorem unitG_fst (g : AffinePoints G A) :
    unitG G J g ≫ (fst G.X G.X).left = redLeft G J (reduction G J g) :=
  congrArg (fun h => h.left) (lift_fst (reduction G J g) (1 : AffinePoints G (A ⧸ J)))

theorem unitG_snd (g : AffinePoints G A) : unitG G J g ≫ (snd G.X G.X).left = unit₀ G J :=
  congrArg (fun h => h.left) (lift_snd (reduction G J g) (1 : AffinePoints G (A ⧸ J)))

theorem unitG_conj (g : AffinePoints G A) : unitG G J g ≫ (conjMor G).left = unit₀ G J := by
  have := congrArg (fun h => h.left) (lift_conjMor G (reduction G J g) 1)
  rw [mul_one, mul_inv_cancel] at this
  exact this

theorem pairG_lin (g : AffinePoints G A) (x y : KLift G J) (a b : A) :
    pairG G J g (LiftModule.lin hJ (base G J) x y a b) =
      LiftModule.lin hJ (pairG G J g (base G J)) (pairG G J g x) (pairG G J g y) a b := by
  apply pairG_ext
  · rw [pairG_fst, LiftModule.lin_map (fst G.X G.X).left (Over.w _) (unitG_fst G J g) hJ
      (pairG G J g (base G J)) (liftAt G J g) (pairG_fst G J g _)]
    have e1 : ∀ z, GLift.map (fst G.X G.X).left (Over.w _) (unitG_fst G J g) (pairG G J g z) =
        liftAt G J g := fun z => Subtype.ext (pairG_fst G J g z)
    rw [e1, e1, LiftModule.lin_self]
    rfl
  · rw [pairG_snd, LiftModule.lin_map (snd G.X G.X).left (Over.w _) (unitG_snd G J g) hJ
      (pairG G J g (base G J)) (base G J) (pairG_snd G J g _)]
    have e2 : ∀ z, GLift.map (snd G.X G.X).left (Over.w _) (unitG_snd G J g) (pairG G J g z) =
        z := fun z => Subtype.ext (pairG_snd G J g z)
    rw [e2, e2]

/-- Conjugation of kernel lifts by an actual point. -/
def conjLift (g : AffinePoints G A) (x : KLift G J) : KLift G J :=
  GLift.map (conjMor G).left (Over.w _) (unitG_conj G J g) (pairG G J g x)

theorem conjLift_base (g : AffinePoints G A) : conjLift G J g (base G J) = base G J := by
  apply Subtype.ext
  change (pairG G J g (base G J)).1 ≫ _ = _
  rw [pairG_conj]
  change (g * ofLift G J (toLift G J 1) * g⁻¹).left = _
  rw [ofLift_toLift, OneMemClass.coe_one, mul_one, mul_inv_cancel]
  rfl

theorem conjLift_lin (g : AffinePoints G A) (x y : KLift G J) (a b : A) :
    conjLift G J g (LiftModule.lin hJ (base G J) x y a b) =
      LiftModule.lin hJ (base G J) (conjLift G J g x) (conjLift G J g y) a b := by
  apply Subtype.ext
  change (pairG G J g _).1 ≫ _ = _
  rw [pairG_lin G J hJ g x y a b]
  exact LiftModule.lin_map (conjMor G).left (Over.w _) (unitG_conj G J g) hJ _ (base G J)
    (congrArg Subtype.val (conjLift_base G J g)) _ _ a b

theorem conjLift_toLift (g : AffinePoints G A) (x : kernel G J) :
    conjLift G J g (toLift G J x) =
      toLift G J ⟨g * x.1 * g⁻¹, (reduction G J).normal_ker.conj_mem x.1 x.2 g⟩ := by
  apply Subtype.ext
  change (pairG G J g (toLift G J x)).1 ≫ _ = _
  rw [pairG_conj, ofLift_toLift]
  rfl

section ConjLinear

variable [hJ' : Fact (SqZero J)]

/-- Conjugation by an actual point, as a linear map on lifts of the identity. -/
def conjLM (g : AffinePoints G A) :
    LiftModule hJ'.out (base G J) →ₗ[A] LiftModule hJ'.out (base G J) where
  toFun x := LiftModule.of _ _ (conjLift G J g x)
  map_add' x y := conjLift_lin G J hJ'.out g x y 1 1
  map_smul' a x := by
    refine (conjLift_lin G J hJ'.out g x (base G J) a 0).trans ?_
    rw [conjLift_base]
    rfl

/-- Conjugation by an actual point on the square-zero kernel, as an `A`-linear map. -/
def kernelConjugationLinear (g : AffinePoints G A) :
    Additive (kernel G J) →ₗ[A] Additive (kernel G J) :=
  (toLMEquiv G J).symm.toLinearMap ∘ₗ conjLM G J g ∘ₗ (toLMEquiv G J).toLinearMap

/-- The linear conjugation is actual conjugation of points. -/
theorem kernelConjugationLinear_apply (g : AffinePoints G A) (x : Additive (kernel G J)) :
    (kernelConjugationLinear G J g x).toMul =
      ⟨g * x.toMul.1 * g⁻¹, (reduction G J).normal_ker.conj_mem x.toMul.1 x.toMul.2 g⟩ := by
  apply (kernelEquiv G J).injective
  have h : toLMEquiv G J (kernelConjugationLinear G J g x) =
      conjLM G J g (toLMEquiv G J x) := by
    simp only [kernelConjugationLinear, LinearMap.coe_comp, LinearEquiv.coe_coe,
      Function.comp_apply, LinearEquiv.apply_symm_apply]
  exact h.trans (conjLift_toLift G J g x.toMul)

/-- Conjugation on the kernel depends only on the reduction of the conjugating point. -/
theorem kernelConjugationLinear_eq_of_reduction_eq (g g' : AffinePoints G A)
    (h : reduction G J g = reduction G J g') :
    kernelConjugationLinear G J g = kernelConjugationLinear G J g' := by
  refine LinearMap.ext fun x => ?_
  apply Additive.toMul.injective
  rw [kernelConjugationLinear_apply, kernelConjugationLinear_apply]
  apply Subtype.ext
  change g * x.toMul.1 * g⁻¹ = g' * x.toMul.1 * g'⁻¹
  have hk : g⁻¹ * g' ∈ kernel G J := by
    change reduction G J (g⁻¹ * g') = 1
    rw [map_mul, map_inv, h, inv_mul_cancel]
  have hc := congrArg Subtype.val (kernel_mul_comm G J hJ'.out ⟨g⁻¹ * g', hk⟩ x.toMul)
  change (g⁻¹ * g') * x.toMul.1 = x.toMul.1 * (g⁻¹ * g') at hc
  calc g * x.toMul.1 * g⁻¹ = g * (x.toMul.1 * (g⁻¹ * g')) * g'⁻¹ := by group
    _ = g * ((g⁻¹ * g') * x.toMul.1) * g'⁻¹ := by rw [hc]
    _ = g' * x.toMul.1 * g'⁻¹ := by group

end ConjLinear

end Langlands.GroupScheme.Lie.NonaffineKernel
