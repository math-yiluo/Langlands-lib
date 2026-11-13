import Langlands.GroupScheme.Rational.SplitSteinbergQuotient
import Langlands.GroupScheme.Rational.EvenChainFieldBaseChange

/-! # The Steinberg cross-section on rational points, and ascent of quotient equalities -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme

namespace SplitPinning

section Bijection

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] {p : SplitPinning G} {r : ℕ}

/-- The ordinary Steinberg product at the rational coordinates `cf`, followed by the canonical
quotient map: `cf ↦ ρ(∏_j x_(E j)(cf_j) n_(E j))`, the product taken in increasing `j`. -/
def steinbergClassMap (E : Fin r ≃ p.base.support) (x : p.NormalizedSimpleRootParametrizations)
    (n : p.SimpleReflectionRepresentatives) (cf : Fin r → k) :
    Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ ClassFunctions.quotient G :=
  (List.ofFn fun j => (x (E j)).toRootParametrization.rationalPoint (cf j) *
    (n (E j)).point).prod ≫ ClassFunctions.rho G

/-- The global-function Steinberg product at the base test, at the constants `cf`, is the
product of the rational root points and representatives. -/
theorem steinbergProductPoint_rational (E : Fin r ≃ p.base.support)
    (x : p.NormalizedSimpleRootParametrizations) (n : p.SimpleReflectionRepresentatives)
    (cf : Fin r → k) :
    steinbergProductPoint E x n (Over.mk (𝟙 _))
        (fun j => (Scheme.ΓSpecIso (CommRingCat.of k)).inv (cf j)) =
      (List.ofFn fun j => (x (E j)).toRootParametrization.rationalPoint (cf j) *
        (n (E j)).point).prod := by
  have hT : ∀ y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      toUnit (Over.mk (𝟙 (Spec (CommRingCat.of k)))) ≫ y = y := fun y => by
    rw [show toUnit (Over.mk (𝟙 _)) = 𝟙 _ from toUnit_unique _ _, Category.id_comp]
  simp only [steinbergProductPoint, hT]
  rfl

/-- **Steinberg's cross-section on rational points.** For a simply connected group, the map
`cf ↦ ρ(∏_j x_(E j)(cf_j) n_(E j))` from `k^r` to the rational points of the canonical quotient
is bijective. -/
theorem bijective_steinbergClassMap (hG : IsSimplyConnected G) (E : Fin r ≃ p.base.support)
    (x : p.NormalizedSimpleRootParametrizations) (n : p.SimpleReflectionRepresentatives) :
    Function.Bijective (steinbergClassMap E x n) := by
  have := splitSteinbergQuotient k G p hG r E x n
  set f := steinbergProduct E x n ≫ ClassFunctions.rho G with hf
  have h1 : Function.Bijective (fun v : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
      (VectorGroup.groupScheme (CommRingCat.of k) r).X => v ≫ f) :=
    ⟨fun v w h => (cancel_mono f).mp h, fun w => ⟨w ≫ inv f, by simp⟩⟩
  have h2 : Function.Bijective (fun c : Fin r → Γ(Spec (CommRingCat.of k), ⊤) =>
      (VectorGroup.coordinates (CommRingCat.of k) r (Over.mk (𝟙 _))).symm
        (Multiplicative.ofAdd c)) :=
    (VectorGroup.coordinates (CommRingCat.of k) r (Over.mk (𝟙 _))).symm.bijective.comp
      Multiplicative.ofAdd.bijective
  have h3 : Function.Bijective (fun (cf : Fin r → k) (j : Fin r) =>
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv (cf j)) :=
    Function.Bijective.comp_left
      (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm.bijective
  convert h1.comp (h2.comp h3) using 1
  funext cf
  simp only [Function.comp_apply, hf]
  rw [← Category.assoc, coordinatesPoint_comp_steinbergProduct, steinbergProductPoint_rational]
  rfl

end Bijection

section Charpoly

variable {k : Type u} [Field k]

/-- Rational points with the same image in the canonical quotient have matrices with the same
characteristic polynomial in every representation. -/
theorem charpoly_rationalMatrix_eq_of_rho_eq {H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom H.X.hom] {n : Type} [Fintype n] [DecidableEq n] (ρ : MatrixRepresentation H n)
    {g g' : rationalPoints H} (h : g ≫ ClassFunctions.rho H = g' ≫ ClassFunctions.rho H) :
    (ρ.rationalMatrix g : Matrix n n k).charpoly = (ρ.rationalMatrix g' : Matrix n n k).charpoly := by
  ext i
  rw [← classEvaluation_charpolyCoeffClassFunction, ← classEvaluation_charpolyCoeffClassFunction,
    classEvaluation_eq_of_rho_eq h]

end Charpoly

section HighestWeightVector

open Langlands.LinearAlgebra.RootDatumPathWeights

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] {p : SplitPinning G}

/-- A fundamental representation at the first vertex of a path has a nonzero vector of its
highest weight, the weight `pathWeight β lam 0 = lam`. -/
theorem FundamentalRepresentation.exists_pathWeightSpace_ne_zero {L : ℕ}
    {β : Fin L → p.base.support} (hβ : IsPathComponent β)
    (F : p.FundamentalRepresentation (β ⟨0, hβ.pos⟩)) :
    ∃ v₀ : p.representationWeightSpace F.representation (pathWeight β F.highestWeight 0),
      v₀ ≠ 0 := by
  have h : Module.finrank k
      (p.representationWeightSpace F.representation (pathWeight β F.highestWeight 0)) = 1 := by
    rw [pathWeight_zero]
    exact F.isHighestWeight.2.2.1
  obtain ⟨v, hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp (by rw [h]; omega)
  exact ⟨v, hv⟩

end HighestWeightVector

section Bijection

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] {p : SplitPinning G} {r : ℕ}
    (E : Fin r ≃ p.base.support) (x : p.NormalizedSimpleRootParametrizations)
    (n : p.SimpleReflectionRepresentatives)

/-- The ordered Steinberg product at rational coordinates `c`, as a rational point:
the product, in increasing `Fin r` order, of the root points `x (E j)` at `c j` followed by
the supplied reflection representatives `n (E j)`. -/
def rationalSteinbergProduct (c : Fin r → k) : rationalPoints G :=
  (List.ofFn fun j => (x (E j)).toRootParametrization.rationalPoint (c j) * (n (E j)).point).prod

theorem rationalSteinbergProduct_eq (c : Fin r → k) :
    rationalSteinbergProduct E x n c =
      (List.ofFn fun j =>
        (x (E j)).toRootParametrization.rationalPoint (c j) * (n (E j)).point).prod :=
  rfl

theorem steinbergProductPoint_eq_rationalSteinbergProduct (c : Fin r → k) :
    steinbergProductPoint E x n (Over.mk (𝟙 _))
        (fun j => (Scheme.ΓSpecIso (CommRingCat.of k)).inv (c j)) =
      rationalSteinbergProduct E x n c :=
  steinbergProductPoint_rational E x n c

/-- **Rational Steinberg bijection.** For a simply connected group with split pinning over a
field `k`, the ordered Steinberg product at rational coordinates followed by the canonical class
quotient map is a bijection from `k ^ r` onto the rational points of the class quotient. -/
theorem bijective_steinbergProductPoint_rho (hG : IsSimplyConnected G) :
    Function.Bijective (fun c : Fin r → k =>
      steinbergProductPoint E x n (Over.mk (𝟙 _))
          (fun j => (Scheme.ΓSpecIso (CommRingCat.of k)).inv (c j)) ≫
        ClassFunctions.rho G) := by
  have hiso := splitSteinbergQuotient k G p hG r E x n
  have hpost : Function.Bijective
      (fun c : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
          (VectorGroup.groupScheme (CommRingCat.of k) r).X =>
        c ≫ (steinbergProduct E x n ≫ ClassFunctions.rho G)) :=
    (Iso.homCongr (Iso.refl _)
      (asIso (steinbergProduct E x n ≫ ClassFunctions.rho G))).bijective
  have hcoord : Function.Bijective (fun c : Fin r → k =>
      (VectorGroup.coordinates (CommRingCat.of k) r (Over.mk (𝟙 _))).symm
        (Multiplicative.ofAdd fun j => (Scheme.ΓSpecIso (CommRingCat.of k)).inv (c j))) := by
    refine (VectorGroup.coordinates (CommRingCat.of k) r (Over.mk (𝟙 _))).symm.bijective.comp
      (Multiplicative.ofAdd.bijective.comp ?_)
    exact (Equiv.piCongrRight fun _ =>
      ((Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm.toEquiv)).bijective
  convert hpost.comp hcoord using 1
  funext c
  simp only [Function.comp_apply]
  rw [← Category.assoc, coordinatesPoint_comp_steinbergProduct]

/-- The rational Steinberg bijection in terms of `rationalSteinbergProduct`. -/
theorem bijective_rationalSteinbergProduct_rho (hG : IsSimplyConnected G) :
    Function.Bijective (fun c : Fin r → k =>
      rationalSteinbergProduct E x n c ≫ ClassFunctions.rho G) := by
  have h := bijective_steinbergProductPoint_rho E x n hG
  simp only [steinbergProductPoint_eq_rationalSteinbergProduct] at h
  exact h

end Bijection

end SplitPinning

section Ascent

variable {k F : Type u} [Field k] [Field F] [Algebra k F]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local notation "bc" => algebraBaseMap k F
local notation "GF" => Functor.obj (GroupScheme.baseChange bc) G

local instance steinbergRationalBijectionIsAffineHom : IsAffineHom (GF).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom bc)
  infer_instance

/-- **Ascent of quotient equalities.** Two rational points with the same image in the
canonical quotient keep the same image after extension to any field extension. -/
theorem baseChangeBasePoint_rho_eq_of_rho_eq {g g' : rationalPoints G}
    (h : g ≫ ClassFunctions.rho G = g' ≫ ClassFunctions.rho G) :
    baseChangeBasePoint bc G g ≫ ClassFunctions.rho (GF) =
      baseChangeBasePoint bc G g' ≫ ClassFunctions.rho (GF) := by
  apply SplitPinning.rho_eq_of_classEvaluation_eq
  intro f
  obtain ⟨y, rfl⟩ := (ClassFunctions.BaseChange.invariants k F G).surjective f
  induction y with
  | tmul a f₀ =>
    have hy : ClassFunctions.BaseChange.invariants k F G (a ⊗ₜ f₀) =
        a • ClassFunctions.fieldExtension (F := F) f₀ := by
      rw [ClassFunctions.fieldExtension, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul,
        mul_one]
    rw [hy, map_smul, map_smul, classEvaluation_baseChangeBasePoint,
      classEvaluation_baseChangeBasePoint, SplitPinning.classEvaluation_eq_of_rho_eq h]
  | add y z hy hz => rw [map_add, map_add, map_add, hy, hz]

end Ascent

end Langlands.GroupScheme
