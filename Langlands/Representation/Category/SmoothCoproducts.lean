import Langlands.Representation.Category.Abelian
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Basic.Complex.Basic

/-! # Concrete coproducts of smooth complex representations

The componentwise action on the algebraic direct sum is smooth, since each
vector is a finite sum of smooth component vectors.
-/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe uG uI uV

namespace Langlands.SmoothRep

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {ι : Type uI} [DecidableEq ι] (A : ι → SmoothRep.{0, uG, max uI uV} ℂ G)

/-- A finite-support sum of smooth representations, on its actual direct-sum carrier. -/
def directSum : SmoothRep.{0, uG, max uI uV} ℂ G :=
  of (Representation.directSum (fun i => (A i).representation)) (by
    intro x
    induction x using DirectSum.induction_on with
    | zero => exact isSmoothVector_zero
    | of i v =>
        obtain ⟨K, hK⟩ := (A i).isSmooth v
        refine ⟨K, ?_⟩
        intro k
        simpa [Representation.directSum, DirectSum.lof_eq_of] using! congrArg (DirectSum.lof ℂ ι (fun i => A i) i) (hK k)
    | add x y hx hy => exact isSmoothVector_add hx hy)

@[simp]
theorem directSum_representation :
    (directSum A).representation = Representation.directSum (fun i => (A i).representation) := rfl

/-- The actual equivariant inclusion of a summand. -/
def directSumι (i : ι) : A i ⟶ directSum A :=
  ofHom {
    toLinearMap := DirectSum.lof ℂ ι (fun i => A i) i
    isIntertwining' g := by
      ext v
      change DirectSum.lof ℂ ι (fun i => A i) i ((A i).representation g v) =
        DirectSum.lmap (fun i => (A i).representation g)
          (DirectSum.lof ℂ ι (fun i => A i) i v)
      exact (DirectSum.lmap_lof (fun i => (A i).representation g) i v).symm }

/-- The actual equivariant projection to a summand. -/
def directSumπ (i : ι) : directSum A ⟶ A i :=
  ofHom {
    toLinearMap := DirectSum.component ℂ ι (fun i => A i) i
    isIntertwining' g := by
      ext v
      rfl }

/-- The cofan of actual summand inclusions. -/
def directSumCofan : Cofan A := Cofan.mk (directSum A) (directSumι A)

/-- The direct-sum cofan is a categorical coproduct in smooth representations. -/
def directSumIsColimit : IsColimit (directSumCofan A) where
  desc s := ofHom {
    toLinearMap := DirectSum.toModule ℂ ι s.pt (fun i => (hom (s.ι.app ⟨i⟩)).toLinearMap)
    isIntertwining' g := by
      apply DirectSum.linearMap_ext
      intro i
      ext v
      change (DirectSum.toModule ℂ ι s.pt
          (fun i => (hom (s.ι.app ⟨i⟩)).toLinearMap))
          (DirectSum.lmap (fun i => (A i).representation g)
            (DirectSum.lof ℂ ι (fun i => A i) i v)) =
        s.pt.representation g ((DirectSum.toModule ℂ ι s.pt
          (fun i => (hom (s.ι.app ⟨i⟩)).toLinearMap))
          (DirectSum.lof ℂ ι (fun i => A i) i v))
      have hd (w : A i) :
          (DirectSum.toModule ℂ ι s.pt (fun i => (hom (s.ι.app ⟨i⟩)).toLinearMap))
            (DirectSum.lof ℂ ι (fun i => A i) i w) = hom (s.ι.app ⟨i⟩) w := by
        apply DirectSum.toModule_lof
      rw [DirectSum.lmap_lof, hd, hd]
      exact (hom (s.ι.app ⟨i⟩)).isIntertwining _ _ g v }
  fac s j := by
    rcases j with ⟨i⟩
    apply ObjectProperty.hom_ext
    ext v
    change (DirectSum.toModule ℂ ι s.pt
      (fun i => (hom (s.ι.app ⟨i⟩)).toLinearMap))
      (DirectSum.lof ℂ ι (fun i => A i) i v) = hom (s.ι.app ⟨i⟩) v
    apply DirectSum.toModule_lof
  uniq s m h := by
    apply ObjectProperty.hom_ext
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply DirectSum.linearMap_ext
    intro i
    ext v
    have hi := congrArg (fun f => hom f v) (h ⟨i⟩)
    simpa [directSumCofan, directSumι] using! hi

end Langlands.SmoothRep
