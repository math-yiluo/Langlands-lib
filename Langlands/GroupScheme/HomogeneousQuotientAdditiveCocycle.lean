import Langlands.AlgebraicGeometry.AffineAdditiveCocycle
import Langlands.GroupScheme.HomogeneousQuotientFromEmbedding

/-! # Functions on a group with prescribed additive left translation by a subgroup -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.HomogeneousQuotientAdditiveCocycle

open HomogeneousQuotientFromEmbedding (HomogeneousQuotient)
open Langlands.AlgebraicGeometry.AffineAdditiveCocycle (AddCocycle)

variable {S : Scheme.{u}} {G N : GroupScheme S} {j : N ⟶ G} (Q : HomogeneousQuotient j)

/-- The left-coset projection `g ↦ π(g⁻¹)` of a homogeneous quotient. -/
def leftProjection : G.X ⟶ Q.scheme :=
  (𝟙 G.X)⁻¹ ≫ Q.projection

theorem comp_leftProjection {T : Over S} (x : T ⟶ G.X) :
    x ≫ leftProjection Q = x⁻¹ ≫ Q.projection := by
  rw [leftProjection, ← Category.assoc, GrpObj.comp_inv, Category.comp_id]

/-- Two points have the same image under the left-coset projection exactly when they lie in
the same left coset. -/
theorem leftProjection_eq_iff {T : Over S} (a b : T ⟶ G.X) :
    a ≫ leftProjection Q = b ≫ leftProjection Q ↔
      a * b⁻¹ ∈ (SubgroupFunctor.range j).carrier T := by
  rw [comp_leftProjection, comp_leftProjection, Q.fibers, inv_inv]

/-- A point of `N` whose image is `a * b⁻¹`, for points `a`, `b` in the same left coset. -/
def witness {T : Over S} (a b : T ⟶ G.X)
    (h : a ≫ leftProjection Q = b ≫ leftProjection Q) : T ⟶ N.X :=
  Classical.choose (SubgroupFunctor.mem_range.mp ((leftProjection_eq_iff Q a b).mp h))

theorem witness_spec {T : Over S} (a b : T ⟶ G.X)
    (h : a ≫ leftProjection Q = b ≫ leftProjection Q) :
    witness Q a b h ≫ j.hom.hom = a * b⁻¹ :=
  Classical.choose_spec (SubgroupFunctor.mem_range.mp ((leftProjection_eq_iff Q a b).mp h))

theorem eq_witness [Mono j.hom.hom] {T : Over S} (a b : T ⟶ G.X)
    (h : a ≫ leftProjection Q = b ≫ leftProjection Q) (n : T ⟶ N.X)
    (hn : n ≫ j.hom.hom = a * b⁻¹) : n = witness Q a b h :=
  (cancel_mono j.hom.hom).mp (hn.trans (witness_spec Q a b h).symm)

/-- `G` as a scheme over the quotient, through the left-coset projection. -/
abbrev cover : Over Q.scheme.left :=
  Over.mk (leftProjection Q).left

/-- A test scheme over the quotient, viewed over `S`. -/
abbrev baseObj (Z : Over Q.scheme.left) : Over S :=
  Over.mk (Z.hom ≫ Q.scheme.hom)

/-- A point of the cover, viewed as a point of `G` over `S`. -/
def basePoint {Z : Over Q.scheme.left} (a : Z ⟶ cover Q) : baseObj Q Z ⟶ G.X :=
  Over.homMk a.left (by
    have h₁ : a.left ≫ (leftProjection Q).left = Z.hom := Over.w a
    have h₂ : (leftProjection Q).left ≫ Q.scheme.hom = G.X.hom := Over.w (leftProjection Q)
    change a.left ≫ G.X.hom = Z.hom ≫ Q.scheme.hom
    rw [← h₂, ← Category.assoc, h₁])

theorem basePoint_leftProjection {Z : Over Q.scheme.left} (a b : Z ⟶ cover Q) :
    basePoint Q a ≫ leftProjection Q = basePoint Q b ≫ leftProjection Q := by
  apply Over.OverMorphism.ext
  change a.left ≫ (leftProjection Q).left = b.left ≫ (leftProjection Q).left
  exact (Over.w a).trans (Over.w b).symm

/-- The additive cocycle `(a, b) ↦ χ(n)`, where `n` is the point of `N` with image
`a * b⁻¹`. -/
def cocycle [Mono j.hom.hom] (χ : ∀ {T : Over S}, (T ⟶ N.X) → Γ(T.left, ⊤))
    (hχ : ∀ {T T' : Over S} (t : T' ⟶ T) (n : T ⟶ N.X), χ (t ≫ n) = t.left.appTop (χ n))
    (hadd : ∀ {T : Over S} (n m : T ⟶ N.X), χ (n * m) = χ n + χ m) :
    AddCocycle (cover Q) where
  toFun a b := χ (witness Q (basePoint Q a) (basePoint Q b) (basePoint_leftProjection Q a b))
  naturality := by
    intro Z Z' t a b
    let t' : baseObj Q Z' ⟶ baseObj Q Z := Over.homMk t.left (by
      change t.left ≫ Z.hom ≫ Q.scheme.hom = Z'.hom ≫ Q.scheme.hom
      rw [← Category.assoc, Over.w t])
    have ha : basePoint Q (t ≫ a) = t' ≫ basePoint Q a := Over.OverMorphism.ext rfl
    have hb : basePoint Q (t ≫ b) = t' ≫ basePoint Q b := Over.OverMorphism.ext rfl
    have hw : witness Q (basePoint Q (t ≫ a)) (basePoint Q (t ≫ b))
        (basePoint_leftProjection Q _ _) =
        t' ≫ witness Q (basePoint Q a) (basePoint Q b) (basePoint_leftProjection Q a b) := by
      symm
      apply eq_witness
      rw [Category.assoc, witness_spec, ha, hb, MonObj.comp_mul, GrpObj.comp_inv]
    rw [hw, hχ]
    rfl
  cocycle := by
    intro Z a b c
    rw [← hadd]
    congr 1
    symm
    apply eq_witness
    rw [MonObj.mul_comp, witness_spec, witness_spec, mul_assoc, inv_mul_cancel_left]

/-- Let `Q` be a homogeneous quotient `G/N` with `G` and `G/N` affine, and let `χ` be a
natural additive function on the points of `N`. Then some global function `f` on `G`
satisfies `f(n · x) = f(x) + χ(n)` for all points `n` of `N` and `x` of `G`. -/
theorem exists_leftTranslate [Mono j.hom.hom] [IsAffine G.X.left] (hQ : IsAffine Q.scheme.left)
    (χ : ∀ {T : Over S}, (T ⟶ N.X) → Γ(T.left, ⊤))
    (hχ : ∀ {T T' : Over S} (t : T' ⟶ T) (n : T ⟶ N.X), χ (t ≫ n) = t.left.appTop (χ n))
    (hadd : ∀ {T : Over S} (n m : T ⟶ N.X), χ (n * m) = χ n + χ m) :
    ∃ f : Γ(G.X.left, ⊤), ∀ {T : Over S} (n : T ⟶ N.X) (x : T ⟶ G.X),
      ((n ≫ j.hom.hom) * x).left.appTop f = x.left.appTop f + χ n := by
  have hiso : IsIso ((𝟙 G.X)⁻¹ : G.X ⟶ G.X).left := by
    have : IsIso ((𝟙 G.X)⁻¹ : G.X ⟶ G.X) :=
      ⟨⟨(𝟙 G.X)⁻¹, by rw [GrpObj.comp_inv, Category.comp_id, inv_inv],
        by rw [GrpObj.comp_inv, Category.comp_id, inv_inv]⟩⟩
    exact inferInstanceAs (IsIso ((Over.forget S).map (𝟙 G.X)⁻¹))
  have : Smooth Q.projection.left := Q.smooth_projection
  have : Surjective Q.projection.left := Q.surjective_projection
  have : Flat (cover Q).hom := by
    change Flat (((𝟙 G.X)⁻¹ : G.X ⟶ G.X).left ≫ Q.projection.left)
    infer_instance
  have : Surjective (cover Q).hom := by
    change Surjective (((𝟙 G.X)⁻¹ : G.X ⟶ G.X).left ≫ Q.projection.left)
    infer_instance
  have : IsAffine (cover Q).left := inferInstanceAs (IsAffine G.X.left)
  obtain ⟨β, hβ⟩ := (cocycle Q χ hχ hadd).exists_coboundary
  refine ⟨β, fun {T} n x => ?_⟩
  have hyx : ((n ≫ j.hom.hom) * x) * x⁻¹ = n ≫ j.hom.hom := mul_inv_cancel_right _ _
  have hp : ((n ≫ j.hom.hom) * x) ≫ leftProjection Q = x ≫ leftProjection Q :=
    (leftProjection_eq_iff Q _ x).mpr (SubgroupFunctor.mem_range.mpr ⟨n, hyx.symm⟩)
  let Z : Over Q.scheme.left := Over.mk (x ≫ leftProjection Q).left
  let ya : Z ⟶ cover Q := Over.homMk ((n ≫ j.hom.hom) * x).left (congrArg (fun g => g.left) hp)
  let xa : Z ⟶ cover Q := Over.homMk x.left rfl
  let e : baseObj Q Z ⟶ T := Over.homMk (𝟙 T.left) (by
    change 𝟙 T.left ≫ T.hom = (x ≫ leftProjection Q).left ≫ Q.scheme.hom
    rw [Category.id_comp]
    exact (Over.w (x ≫ leftProjection Q)).symm)
  have hya : basePoint Q ya = e ≫ ((n ≫ j.hom.hom) * x) :=
    Over.OverMorphism.ext (Category.id_comp _).symm
  have hxa : basePoint Q xa = e ≫ x := Over.OverMorphism.ext (Category.id_comp _).symm
  have hw : witness Q (basePoint Q ya) (basePoint Q xa) (basePoint_leftProjection Q ya xa) =
      e ≫ n := by
    symm
    apply eq_witness
    rw [Category.assoc, ← hyx, hya, hxa, MonObj.comp_mul, GrpObj.comp_inv]
  have h₁ := hβ ya xa
  change χ (witness Q (basePoint Q ya) (basePoint Q xa) _) = _ at h₁
  rw [hw, hχ] at h₁
  change χ n = ((n ≫ j.hom.hom) * x).left.appTop β - x.left.appTop β at h₁
  rw [h₁, add_sub_cancel]

/-- The form of `exists_leftTranslate` over an affine base, with an affine quotient
morphism. -/
theorem exists_leftTranslate_of_isAffineHom [IsAffine S] [Mono j.hom.hom] [IsAffine G.X.left]
    (hQ : IsAffineHom Q.scheme.hom) (χ : ∀ {T : Over S}, (T ⟶ N.X) → Γ(T.left, ⊤))
    (hχ : ∀ {T T' : Over S} (t : T' ⟶ T) (n : T ⟶ N.X), χ (t ≫ n) = t.left.appTop (χ n))
    (hadd : ∀ {T : Over S} (n m : T ⟶ N.X), χ (n * m) = χ n + χ m) :
    ∃ f : Γ(G.X.left, ⊤), ∀ {T : Over S} (n : T ⟶ N.X) (x : T ⟶ G.X),
      ((n ≫ j.hom.hom) * x).left.appTop f = x.left.appTop f + χ n :=
  exists_leftTranslate Q (isAffine_of_isAffineHom Q.scheme.hom) χ hχ hadd

end Langlands.GroupScheme.HomogeneousQuotientAdditiveCocycle
