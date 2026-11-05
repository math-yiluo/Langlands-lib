import Langlands.GroupScheme.VectorGroupQuotient
import Langlands.AlgebraicGeometry.AffineAdditiveCocycle

/-! # Additive coordinates on affine extensions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AdditiveExtensionCoordinate

section Difference

variable {B : Scheme.{u}} {E H : GroupScheme B} (q : E ⟶ H)

/-- The difference of two points in the same quotient fibre, in the actual kernel. -/
def kernelDifference {T : Over B} (g h : T ⟶ E.X)
    (hgh : g ≫ q.hom.hom = h ≫ q.hom.hom) : T ⟶ (kernel q).X :=
  (kernelPointsEquiv q T).symm ⟨g * h⁻¹, by
    change (g * h⁻¹) ≫ q.hom.hom = 1
    rw [MonObj.mul_comp, GrpObj.inv_comp, hgh, mul_inv_cancel]⟩

@[reassoc]
theorem kernelDifference_comp {T : Over B} (g h : T ⟶ E.X)
    (hgh : g ≫ q.hom.hom = h ≫ q.hom.hom) :
    kernelDifference q g h hgh ≫ (kernelι q).hom.hom = g * h⁻¹ :=
  congrArg Subtype.val ((kernelPointsEquiv q T).apply_symm_apply _)

theorem kernelDifference_naturality {T T' : Over B} (t : T' ⟶ T)
    (g h : T ⟶ E.X) (hgh : g ≫ q.hom.hom = h ≫ q.hom.hom) :
    kernelDifference q (t ≫ g) (t ≫ h) (by simp only [Category.assoc, hgh]) =
      t ≫ kernelDifference q g h hgh := by
  apply (cancel_mono (kernelι q).hom.hom).mp
  rw [kernelDifference_comp, Category.assoc, kernelDifference_comp,
    MonObj.comp_mul, GrpObj.comp_inv]

theorem kernelDifference_cocycle {T : Over B} (g h l : T ⟶ E.X)
    (hgh : g ≫ q.hom.hom = h ≫ q.hom.hom)
    (hhl : h ≫ q.hom.hom = l ≫ q.hom.hom) :
    kernelDifference q g l (hgh.trans hhl) =
      kernelDifference q g h hgh * kernelDifference q h l hhl := by
  apply (cancel_mono (kernelι q).hom.hom).mp
  rw [kernelDifference_comp, MonObj.mul_comp, kernelDifference_comp,
    kernelDifference_comp]
  group

end Difference

section Coordinates

variable {R : CommRingCat.{u}} {E H : GroupScheme (Spec R)} (q : E ⟶ H)

/-- The point of the extension underlying a point of the quotient cover. -/
def coverPoint {Z : Over H.X.left} (x : Z ⟶ Over.mk q.hom.hom.left) :
    (Over.map H.X.hom).obj Z ⟶ E.X :=
  Over.homMk x.left (by
    change x.left ≫ E.X.hom = Z.hom ≫ H.X.hom
    have hx : x.left ≫ q.hom.hom.left = Z.hom := Over.w x
    rw [← Over.w q.hom.hom, ← Category.assoc, hx])

theorem coverPoint_quotient {Z : Over H.X.left}
    (x y : Z ⟶ Over.mk q.hom.hom.left) :
    coverPoint q x ≫ q.hom.hom = coverPoint q y ≫ q.hom.hom := by
  apply Over.OverMorphism.ext
  exact (Over.w x).trans (Over.w y).symm

theorem coverPoint_naturality {Z Z' : Over H.X.left} (t : Z' ⟶ Z)
    (x : Z ⟶ Over.mk q.hom.hom.left) :
    coverPoint q (t ≫ x) = (Over.map H.X.hom).map t ≫ coverPoint q x := by
  apply Over.OverMorphism.ext
  rfl

variable {n : ℕ} (a : kernel q ⟶ VectorGroup.groupScheme R n)

open Langlands.AlgebraicGeometry.AffineAdditiveCocycle

/-- Each coordinate of the image of the kernel difference is an additive cocycle on the
actual quotient cover. -/
def scalarCocycle (i : Fin n) : AddCocycle (Over.mk q.hom.hom.left) where
  toFun x y := (VectorGroup.coordinates R n _
    (kernelDifference q (coverPoint q x) (coverPoint q y) (coverPoint_quotient q x y) ≫
      a.hom.hom)).toAdd i
  naturality t x y := by
    simp only [coverPoint_naturality]
    rw [kernelDifference_naturality q _ _ _ (coverPoint_quotient q x y),
      Category.assoc, VectorGroup.coordinates_comp]
    rfl
  cocycle x y z := by
    rw [kernelDifference_cocycle q _ (coverPoint q y) _ (coverPoint_quotient q x y)
      (coverPoint_quotient q y z), MonObj.mul_comp, map_mul, toAdd_mul, Pi.add_apply]

variable [IsAffine E.X.left] [IsAffine H.X.left]
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left]

/-- A homomorphism from the full kernel to a vector group extends to a regular map on the
extension which has the prescribed difference on every quotient fibre. -/
theorem exists_fiberCoordinate :
    ∃ f : E.X ⟶ (VectorGroup.groupScheme R n).X,
      ∀ (T : Over (Spec R)) (g h : T ⟶ E.X)
        (hgh : g ≫ q.hom.hom = h ≫ q.hom.hom),
        kernelDifference q g h hgh ≫ a.hom.hom = (g ≫ f) * (h ≫ f)⁻¹ := by
  let : IsAffine (Over.mk q.hom.hom.left).left := ‹IsAffine E.X.left›
  let : Flat (Over.mk q.hom.hom.left).hom := ‹Flat q.hom.hom.left›
  let : Surjective (Over.mk q.hom.hom.left).hom := ‹Surjective q.hom.hom.left›
  choose β hβ using fun i : Fin n => (scalarCocycle q a i).exists_coboundary
  let f : E.X ⟶ (VectorGroup.groupScheme R n).X :=
    (VectorGroup.coordinates R n E.X).symm (Multiplicative.ofAdd β)
  refine ⟨f, fun T g h hgh => ?_⟩
  let Z : Over H.X.left := Over.mk (g.left ≫ q.hom.hom.left)
  let x : Z ⟶ Over.mk q.hom.hom.left := Over.homMk g.left rfl
  let y : Z ⟶ Over.mk q.hom.hom.left := Over.homMk h.left (by
    exact (congrArg (fun f => f.left) hgh).symm)
  let t : T ⟶ (Over.map H.X.hom).obj Z := Over.homMk (𝟙 T.left) (by
    change 𝟙 T.left ≫ ((g.left ≫ q.hom.hom.left) ≫ H.X.hom) = T.hom
    rw [Category.id_comp, Category.assoc, Over.w q.hom.hom, Over.w g])
  have htx : t ≫ coverPoint q x = g := by
    apply Over.OverMorphism.ext
    exact Category.id_comp _
  have hty : t ≫ coverPoint q y = h := by
    apply Over.OverMorphism.ext
    exact Category.id_comp _
  apply VectorGroup.points_ext
  intro i
  rw [map_mul, map_inv, toAdd_mul, toAdd_inv, Pi.add_apply, Pi.neg_apply,
    VectorGroup.coordinates_comp g f, VectorGroup.coordinates_comp h f]
  simp only [f, MulEquiv.apply_symm_apply, toAdd_ofAdd]
  change (VectorGroup.coordinates R n T (kernelDifference q g h hgh ≫ a.hom.hom)).toAdd i =
    g.left.appTop (β i) + -(h.left.appTop (β i))
  have hi := hβ i x y
  have hn := congrArg (fun p =>
    (VectorGroup.coordinates R n T (p ≫ a.hom.hom)).toAdd i)
    (kernelDifference_naturality q t (coverPoint q x) (coverPoint q y)
      (coverPoint_quotient q x y))
  simp only [htx, hty] at hn
  simp only [Category.assoc, VectorGroup.coordinates_comp] at hn
  have ht : t.left.appTop (scalarCocycle q a i |>.toFun x y) =
      (scalarCocycle q a i).toFun x y := by
    change (𝟙 T.left : T.left ⟶ T.left).appTop _ = _
    simp
  change _ = t.left.appTop ((scalarCocycle q a i).toFun x y) at hn
  rw [ht, hi] at hn
  exact hn.trans (sub_eq_add_neg _ _)

end Coordinates

end Langlands.GroupScheme.AdditiveExtensionCoordinate
