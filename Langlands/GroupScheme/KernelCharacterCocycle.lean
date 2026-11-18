import Langlands.GroupScheme.Torus.LineBundlePicardCocycle
import Langlands.GroupScheme.CentralIsogeny.Basic
import Langlands.AlgebraicGeometry.Modules.UnitCocyclePicardTrivial

/-! # Descent of characters of the full kernel -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.Scheme.Modules

open Langlands.SchemeModule Langlands.AlgebraicGeometry.Picard
open Langlands.Scheme.UnitCocycleDescent

/-- Actual line-bundle triviality on the target makes every natural
multiplicative unit cocycle on an affine faithfully flat cover a coboundary. -/
theorem exists_unit_coboundary_of_lineBundle_trivial
    {X Y : Scheme.{u}} (p : X ⟶ Y)
    [IsAffineHom p] [Flat p] [Surjective p]
    (hpic : ∀ L : LineBundle Y, Nonempty (L ≅ LineBundle.trivial Y))
    (c : ∀ (Z : Scheme.{u}) (a b : Z ⟶ X), a ≫ p = b ≫ p → Γ(Z, ⊤)ˣ)
    (hnat : IsNatural p c) (hmul : IsMultiplicative p c) :
    ∃ q : Γ(X, ⊤)ˣ, ∀ (Z : Scheme.{u}) (a b : Z ⟶ X) (h : a ≫ p = b ≫ p),
      c Z a b h =
        Units.map a.appTop.hom.toMonoidHom q *
          (Units.map b.appTop.hom.toMonoidHom q)⁻¹ :=
  exists_unit_coboundary_of_lineBundlesTrivial hpic p c hnat hmul

end Langlands.Scheme.Modules

namespace Langlands.GroupScheme.KernelCharacterCocycle

variable {S : Scheme.{u}} {H G : GroupScheme S} (f : H ⟶ G)

/-- The right difference of two points with the same image, valued in the
full scheme-theoretic kernel. -/
def difference {T : Over S} (a b : T ⟶ H.X)
    (h : a ≫ f.hom.hom = b ≫ f.hom.hom) : T ⟶ (kernel f).X :=
  (kernelPointsEquiv f T).symm ⟨a⁻¹ * b, by
    change (a⁻¹ * b) ≫ f.hom.hom = 1
    rw [MonObj.mul_comp, GrpObj.inv_comp, h, inv_mul_cancel]⟩

@[simp] theorem difference_comp {T : Over S} (a b : T ⟶ H.X)
    (h : a ≫ f.hom.hom = b ≫ f.hom.hom) :
    difference f a b h ≫ (kernelι f).hom.hom = a⁻¹ * b :=
  congrArg Subtype.val ((kernelPointsEquiv f T).apply_symm_apply _)

theorem difference_naturality {T T' : Over S} (q : T' ⟶ T)
    (a b : T ⟶ H.X) (h : a ≫ f.hom.hom = b ≫ f.hom.hom)
    (h' : (q ≫ a) ≫ f.hom.hom = (q ≫ b) ≫ f.hom.hom) :
    difference f (q ≫ a) (q ≫ b) h' = q ≫ difference f a b h := by
  apply (cancel_mono (kernelι f).hom.hom).mp
  simp only [Category.assoc, difference_comp, MonObj.comp_mul, GrpObj.comp_inv]

theorem difference_mul {T : Over S} (a b d : T ⟶ H.X)
    (h : a ≫ f.hom.hom = b ≫ f.hom.hom)
    (h' : b ≫ f.hom.hom = d ≫ f.hom.hom)
    (h'' : a ≫ f.hom.hom = d ≫ f.hom.hom) :
    difference f a b h * difference f b d h' = difference f a d h'' := by
  apply (cancel_mono (kernelι f).hom.hom).mp
  simp only [MonObj.mul_comp, difference_comp]
  group

lemma pair_base_eq {U : Scheme.{u}} {a b : U ⟶ H.X.left}
    (h : a ≫ f.hom.hom.left = b ≫ f.hom.hom.left) :
    a ≫ H.X.hom = b ≫ H.X.hom := by
  rw [← Over.w f.hom.hom, ← Category.assoc, h, Category.assoc]

def pairFirst {U : Scheme.{u}} (a : U ⟶ H.X.left) :
    Over.mk (a ≫ H.X.hom) ⟶ H.X := Over.homMk a

def pairSecond {U : Scheme.{u}} (a b : U ⟶ H.X.left)
    (h : a ≫ f.hom.hom.left = b ≫ f.hom.hom.left) :
    Over.mk (a ≫ H.X.hom) ⟶ H.X :=
  Over.homMk b (pair_base_eq f h).symm

lemma pair_comp_eq {U : Scheme.{u}} (a b : U ⟶ H.X.left)
    (h : a ≫ f.hom.hom.left = b ≫ f.hom.hom.left) :
    pairFirst a ≫ f.hom.hom = pairSecond f a b h ≫ f.hom.hom :=
  Over.OverMorphism.ext h

/-- Evaluation of a kernel character on the right difference of every
scheme-valued equal-image pair. -/
def cocycle (χ : rationalCharacters (kernel f)) (U : Scheme.{u})
    (a b : U ⟶ H.X.left) (h : a ≫ f.hom.hom.left = b ≫ f.hom.hom.left) : Γ(U, ⊤)ˣ :=
  characterEval χ (Over.mk (a ≫ H.X.hom))
    (difference f (pairFirst a) (pairSecond f a b h) (pair_comp_eq f a b h))

theorem cocycle_on_over (χ : rationalCharacters (kernel f)) (T : Over S)
    (a b : T ⟶ H.X) (h : a ≫ f.hom.hom = b ≫ f.hom.hom) :
    cocycle f χ T.left a.left b.left (congrArg Over.Hom.left h) =
      characterEval χ T (difference f a b h) := by
  let q : Over.mk (a.left ≫ H.X.hom) ⟶ T :=
    Over.homMk (𝟙 T.left) (by simp)
  have ha : pairFirst a.left = q ≫ a := by ext; simp [pairFirst, q]
  have hb : pairSecond f a.left b.left (congrArg Over.Hom.left h) = q ≫ b := by
    ext; simp [pairSecond, q]
  have h' : (q ≫ a) ≫ f.hom.hom = (q ≫ b) ≫ f.hom.hom := by
    simpa only [Category.assoc] using congrArg (fun t => q ≫ t) h
  have hd : difference f (pairFirst a.left)
      (pairSecond f a.left b.left (congrArg Over.Hom.left h))
      (pair_comp_eq f a.left b.left (congrArg Over.Hom.left h)) =
      difference f (q ≫ a) (q ≫ b) h' := by
    apply (cancel_mono (kernelι f).hom.hom).mp
    simp only [difference_comp, ha, hb]
  unfold cocycle
  rw [hd, difference_naturality f q a b h h', characterEval_naturality]
  simp [q]

theorem cocycle_isNatural (χ : rationalCharacters (kernel f)) :
    Langlands.Scheme.UnitCocycleDescent.IsNatural f.hom.hom.left (cocycle f χ) := by
  intro U V q a b h h'
  let T := Over.mk (a ≫ H.X.hom)
  let T' := Over.mk (q ≫ T.hom)
  let g : T' ⟶ T := Over.homMk q
  let x : T ⟶ H.X := pairFirst a
  let y : T ⟶ H.X := pairSecond f a b h
  have hxy : x ≫ f.hom.hom = y ≫ f.hom.hom := pair_comp_eq f a b h
  have hxy' : (g ≫ x) ≫ f.hom.hom = (g ≫ y) ≫ f.hom.hom := by
    simpa only [Category.assoc] using congrArg (fun t => g ≫ t) hxy
  change cocycle f χ T'.left (g ≫ x).left (g ≫ y).left
      (congrArg Over.Hom.left hxy') =
    Units.map g.left.appTop.hom.toMonoidHom
      (cocycle f χ T.left x.left y.left (congrArg Over.Hom.left hxy))
  rw [cocycle_on_over f χ T' (g ≫ x) (g ≫ y) hxy',
    cocycle_on_over f χ T x y hxy,
    difference_naturality f g x y hxy hxy', characterEval_naturality]

theorem cocycle_isMultiplicative (χ : rationalCharacters (kernel f)) :
    Langlands.Scheme.UnitCocycleDescent.IsMultiplicative f.hom.hom.left (cocycle f χ) := by
  intro U a b d h h' h''
  let T := Over.mk (a ≫ H.X.hom)
  let x : T ⟶ H.X := pairFirst a
  let y : T ⟶ H.X := pairSecond f a b h
  let z : T ⟶ H.X := pairSecond f a d h''
  have hxy : x ≫ f.hom.hom = y ≫ f.hom.hom := pair_comp_eq f a b h
  have hyz : y ≫ f.hom.hom = z ≫ f.hom.hom := Over.OverMorphism.ext h'
  have hxz : x ≫ f.hom.hom = z ≫ f.hom.hom := pair_comp_eq f a d h''
  change cocycle f χ T.left x.left y.left (congrArg Over.Hom.left hxy) *
      cocycle f χ T.left y.left z.left (congrArg Over.Hom.left hyz) =
    cocycle f χ T.left x.left z.left (congrArg Over.Hom.left hxz)
  rw [cocycle_on_over f χ T x y hxy, cocycle_on_over f χ T y z hyz,
    cocycle_on_over f χ T x z hxz, ← map_mul, difference_mul f x y z hxy hyz hxz]

open Langlands.AlgebraicGeometry.Picard

/-- For an affine faithfully flat homomorphism with line-bundle-trivial target,
the character of every full kernel difference is a global unit coboundary. -/
theorem exists_unit_coboundary
    [IsAffineHom f.hom.hom.left] [Flat f.hom.hom.left] [Surjective f.hom.hom.left]
    (hpic : ∀ L : LineBundle G.X.left, Nonempty (L ≅ LineBundle.trivial G.X.left))
    (χ : rationalCharacters (kernel f)) :
    ∃ q : Γ(H.X.left, ⊤)ˣ, ∀ (T : Over S) (a b : T ⟶ H.X)
        (h : a ≫ f.hom.hom = b ≫ f.hom.hom),
      characterEval χ T (difference f a b h) =
        Units.map a.left.appTop.hom.toMonoidHom q *
          (Units.map b.left.appTop.hom.toMonoidHom q)⁻¹ := by
  obtain ⟨q, hq⟩ :=
    Langlands.Scheme.Modules.exists_unit_coboundary_of_lineBundle_trivial
      f.hom.hom.left hpic (cocycle f χ) (cocycle_isNatural f χ) (cocycle_isMultiplicative f χ)
  refine ⟨q, fun T a b h => ?_⟩
  rw [← cocycle_on_over f χ T a b h]
  exact hq T.left a.left b.left (congrArg Over.Hom.left h)

end Langlands.GroupScheme.KernelCharacterCocycle
