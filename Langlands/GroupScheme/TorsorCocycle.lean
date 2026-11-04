import Langlands.AbelianScheme.GroupScheme
import Mathlib.CategoryTheory.EffectiveEpi.Basic
import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod

/-! # Group-valued cocycles on covers, and sections of torsors

A cocycle on a cover `U` of the base is written as a natural family of group points on
pairs of points of `U` over every test scheme, so no fibre products appear. A torsor with
a point over `U` gives such a cocycle, and a trivialization of that cocycle descends to a
section of the torsor along an effective epimorphism.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}}

/-- A natural group-valued cocycle on pairs of points of `U` over all test schemes. -/
structure Cocycle (G : GroupScheme S) (U : Over S) where
  /-- The value on a pair of points of `U` over the same test scheme. -/
  toFun : ∀ {Z : Over S}, (Z ⟶ U) → (Z ⟶ U) → (Z ⟶ G.X)
  naturality : ∀ {Z Z' : Over S} (t : Z' ⟶ Z) (a b : Z ⟶ U),
    toFun (t ≫ a) (t ≫ b) = t ≫ toFun a b
  cocycle : ∀ {Z : Over S} (a b c : Z ⟶ U), toFun a c = toFun a b * toFun b c

namespace Cocycle

variable {G H : GroupScheme S} {U : Over S}

/-- A cocycle is trivial when it is the coboundary of one point of `G` over `U`. -/
def IsTrivial (ξ : Cocycle G U) : Prop :=
  ∃ f : U ⟶ G.X, ∀ {Z : Over S} (a b : Z ⟶ U), ξ.toFun a b = (a ≫ f) * (b ≫ f)⁻¹

/-- The coboundary `(a, b) ↦ f(a) f(b)⁻¹` of a point `f` of `G` over `U`. -/
def coboundary (f : U ⟶ G.X) : Cocycle G U where
  toFun a b := (a ≫ f) * (b ≫ f)⁻¹
  naturality t a b := by simp only [MonObj.comp_mul, GrpObj.comp_inv, Category.assoc]
  cocycle a b c := by group

/-- The image of a cocycle under a homomorphism of group schemes. -/
def map (ξ : Cocycle G U) (φ : G ⟶ H) : Cocycle H U where
  toFun a b := ξ.toFun a b ≫ φ.hom.hom
  naturality t a b := by rw [ξ.naturality, Category.assoc]
  cocycle a b c := by rw [ξ.cocycle a b c, MonObj.mul_comp]

/-- The twist `(a, b) ↦ f(a)⁻¹ ξ(a, b) f(b)` of a cocycle by a point of `G` over `U`. -/
def twist (ξ : Cocycle G U) (f : U ⟶ G.X) : Cocycle G U where
  toFun a b := (a ≫ f)⁻¹ * ξ.toFun a b * (b ≫ f)
  naturality t a b := by
    simp only [MonObj.comp_mul, GrpObj.comp_inv, Category.assoc, ξ.naturality]
  cocycle a b c := by rw [ξ.cocycle a b c]; group

/-- A cocycle is trivial when one of its twists is. -/
theorem IsTrivial.of_twist {ξ : Cocycle G U} {f : U ⟶ G.X} (h : (ξ.twist f).IsTrivial) :
    ξ.IsTrivial := by
  obtain ⟨f₂, hf₂⟩ := h
  refine ⟨f * f₂, fun a b => ?_⟩
  have h : (a ≫ f)⁻¹ * ξ.toFun a b * (b ≫ f) = (a ≫ f₂) * (b ≫ f₂)⁻¹ := hf₂ a b
  rw [MonObj.comp_mul, MonObj.comp_mul]
  calc ξ.toFun a b = (a ≫ f) * ((a ≫ f)⁻¹ * ξ.toFun a b * (b ≫ f)) * (b ≫ f)⁻¹ := by group
    _ = _ := by rw [h]; group

/-- A cocycle valued in the image of a monomorphism of group schemes, read in the source. -/
def lift (ξ : Cocycle G U) (j : H ⟶ G) [Mono j.hom.hom]
    (hξ : ∀ {Z : Over S} (a b : Z ⟶ U), ∃ k : Z ⟶ H.X, k ≫ j.hom.hom = ξ.toFun a b) :
    Cocycle H U where
  toFun a b := (hξ a b).choose
  naturality t a b := by
    rw [← cancel_mono j.hom.hom, Category.assoc, (hξ (t ≫ a) (t ≫ b)).choose_spec,
      (hξ a b).choose_spec, ξ.naturality]
  cocycle a b c := by
    rw [← cancel_mono j.hom.hom, MonObj.mul_comp, (hξ a c).choose_spec, (hξ a b).choose_spec,
      (hξ b c).choose_spec, ξ.cocycle a b c]

theorem lift_toFun (ξ : Cocycle G U) (j : H ⟶ G) [Mono j.hom.hom]
    (hξ : ∀ {Z : Over S} (a b : Z ⟶ U), ∃ k : Z ⟶ H.X, k ≫ j.hom.hom = ξ.toFun a b)
    {Z : Over S} (a b : Z ⟶ U) : (ξ.lift j hξ).toFun a b ≫ j.hom.hom = ξ.toFun a b :=
  (hξ a b).choose_spec

/-- A cocycle is trivial when its lift to a subgroup is. -/
theorem IsTrivial.of_lift {ξ : Cocycle G U} {j : H ⟶ G} [Mono j.hom.hom]
    {hξ : ∀ {Z : Over S} (a b : Z ⟶ U), ∃ k : Z ⟶ H.X, k ≫ j.hom.hom = ξ.toFun a b}
    (h : (ξ.lift j hξ).IsTrivial) : ξ.IsTrivial := by
  obtain ⟨f, hf⟩ := h
  refine ⟨f ≫ j.hom.hom, fun a b => ?_⟩
  rw [← lift_toFun ξ j hξ a b, hf, MonObj.mul_comp, GrpObj.inv_comp, Category.assoc,
    Category.assoc]

end Cocycle

/-- A point over an effective epimorphism which agrees on any two points over the same test
scheme descends to a section over the base. -/
theorem exists_section_of_forall_eq {U Y : Over S} [EffectiveEpi U.hom] (φ : U ⟶ Y)
    (h : ∀ {Z : Over S} (a b : Z ⟶ U), a ≫ φ = b ≫ φ) :
    ∃ s : S ⟶ Y.left, U.hom ≫ s = φ.left ∧ s ≫ Y.hom = 𝟙 S := by
  refine ⟨EffectiveEpi.desc U.hom φ.left fun {Z} g₁ g₂ hg => ?_, EffectiveEpi.fac _ _ _, ?_⟩
  · exact show g₁ ≫ φ.left = g₂ ≫ φ.left from congrArg (fun f => f.left)
      (h (Z := Over.mk (g₁ ≫ U.hom)) (Over.homMk g₁) (Over.homMk g₂ hg.symm))
  · rw [← cancel_epi U.hom, ← Category.assoc, EffectiveEpi.fac, Over.w φ, Category.comp_id]

section Torsor

variable {G : GroupScheme S} {X : Over S} [ModObj G.X X]

/-- In a torsor, the unique group point carrying one point to another. -/
def torsorDiff (hX : IsIso (ModObj.leftSMul G.X X)) {Z : Over S} (x y : Z ⟶ X) : Z ⟶ G.X :=
  ((ModObj.isIso_leftSMul_iff.mp hX) Z x y).exists.choose

theorem torsorDiff_smul (hX : IsIso (ModObj.leftSMul G.X X)) {Z : Over S} (x y : Z ⟶ X) :
    torsorDiff hX x y • x = y :=
  ((ModObj.isIso_leftSMul_iff.mp hX) Z x y).exists.choose_spec

theorem eq_torsorDiff (hX : IsIso (ModObj.leftSMul G.X X)) {Z : Over S} {x y : Z ⟶ X}
    {m : Z ⟶ G.X} (hm : m • x = y) : m = torsorDiff hX x y :=
  ((ModObj.isIso_leftSMul_iff.mp hX) Z x y).unique hm (torsorDiff_smul hX x y)

/-- The cocycle of a torsor with a point over `U`: the group point carrying the second
image point to the first. -/
def torsorCocycle (hX : IsIso (ModObj.leftSMul G.X X)) {U : Over S} (u : U ⟶ X) :
    Cocycle G U where
  toFun a b := torsorDiff hX (b ≫ u) (a ≫ u)
  naturality t a b := by
    symm
    apply eq_torsorDiff
    rw [Category.assoc, Category.assoc, ← ModObj.comp_smul, torsorDiff_smul]
  cocycle a b c := by
    symm
    apply eq_torsorDiff
    rw [mul_smul, torsorDiff_smul, torsorDiff_smul]

/-- A torsor has a section once the cocycle of a point over an effective epimorphism is
trivial. -/
theorem exists_section_of_isTrivial (hX : IsIso (ModObj.leftSMul G.X X)) {U : Over S}
    [EffectiveEpi U.hom] (u : U ⟶ X) (h : (torsorCocycle hX u).IsTrivial) :
    ∃ s : S ⟶ X.left, s ≫ X.hom = 𝟙 S := by
  obtain ⟨f, hf⟩ := h
  obtain ⟨s, -, hs⟩ := exists_section_of_forall_eq (f⁻¹ • u) fun {Z} a b => by
    have hab : ((a ≫ f) * (b ≫ f)⁻¹) • (b ≫ u) = a ≫ u := by
      rw [← hf a b]
      exact torsorDiff_smul hX _ _
    rw [ModObj.comp_smul, ModObj.comp_smul, GrpObj.comp_inv, GrpObj.comp_inv, ← hab, smul_smul]
    congr 1
    group
  exact ⟨s, hs⟩

end Torsor

end Langlands.GroupScheme
