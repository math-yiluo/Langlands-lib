import Langlands.GroupScheme.Reductive.RankOneRingCalculus
import Langlands.GroupScheme.SubgroupFunctor.ZariskiLocality
import Mathlib.RingTheory.AdjoinRoot

/-! # Removing unit square-root inputs from the ring cell calculation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RingRootCell

namespace UnitSquareExtension

variable {R : Type u} [CommRing R]

/-- A monic quadratic adjoining a square root of the given unit. -/
def polynomial (a : Rˣ) : Polynomial R := Polynomial.X ^ 2 - Polynomial.C (a : R)

/-- The ring obtained by adjoining the square root. -/
abbrev Ring (a : Rˣ) := AdjoinRoot (polynomial a)

/-- The coefficient homomorphism into the square-root extension. -/
def inclusion (a : Rˣ) : R →+* Ring a := AdjoinRoot.of (polynomial a)

theorem inclusion_injective (a : Rˣ) : Function.Injective (inclusion a) := by
  cases subsingleton_or_nontrivial R with
  | inl h => exact Function.injective_of_subsingleton _
  | inr h =>
    apply AdjoinRoot.of.injective_of_monic_of_degree_pos
    · exact Polynomial.monic_X_pow_sub_C _ (by decide)
    · rw [polynomial, Polynomial.degree_X_pow_sub_C (by decide)]
      decide

theorem root_sq (a : Rˣ) : AdjoinRoot.root (polynomial a) ^ 2 = inclusion a (a : R) := by
  have h := AdjoinRoot.eval₂_root (polynomial a)
  change (Polynomial.X ^ 2 - Polynomial.C (a : R)).eval₂ (inclusion a)
    (AdjoinRoot.root (polynomial a)) = 0 at h
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_C] at h
  exact sub_eq_zero.mp h

/-- The adjoined root is a unit, without inverting two. -/
def rootUnit (a : Rˣ) : (Ring a)ˣ :=
  ((isUnit_pow_iff (by decide : (2 : ℕ) ≠ 0)).mp
    ((root_sq a).symm ▸ a.isUnit.map (inclusion a))).unit

theorem rootUnit_mul (a : Rˣ) :
    rootUnit a * rootUnit a = Units.map (inclusion a).toMonoidHom a := by
  apply Units.ext
  simp only [Units.val_mul, rootUnit, IsUnit.unit_spec, Units.coe_map]
  exact (pow_two _).symm.trans (root_sq a)

/-- Finitely many units admit simultaneous square roots in an injective ring extension. -/
theorem exists_squareRoots {n : ℕ} (a : Fin n → Rˣ) :
    ∃ (B : Type u) (_ : CommRing B) (f : R →+* B), Function.Injective f ∧
      ∃ r : Fin n → Bˣ, ∀ j, r j * r j = Units.map f.toMonoidHom (a j) := by
  induction n with
  | zero =>
    exact ⟨R, inferInstance, RingHom.id R, Function.injective_id, Fin.elim0,
      fun j => Fin.elim0 j⟩
  | succ n ih =>
    obtain ⟨B, hB, f, hf, r, hr⟩ := ih (Fin.tail a)
    let b := Units.map f.toMonoidHom (a 0)
    let g := inclusion b
    refine ⟨Ring b, inferInstance, g.comp f, (inclusion_injective b).comp hf,
      Fin.cons (rootUnit b) (fun j => Units.map g.toMonoidHom (r j)), ?_⟩
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · exact rootUnit_mul b
    · change Units.map g.toMonoidHom (r i) * Units.map g.toMonoidHom (r i) = _
      rw [← map_mul, hr]
      rfl

end UnitSquareExtension

section SchemeTests

/-- Global sections of the affine test attached to a coefficient map. -/
theorem appTop_specMap_isoSpec_inv {Z : Scheme.{u}} [IsAffine Z]
    {B : CommRingCat.{u}} (f : Γ(Z, ⊤) ⟶ B) :
    (Spec.map f ≫ Z.isoSpec.inv).appTop = f ≫ (Scheme.ΓSpecIso B).inv := by
  have h : Z.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(Z, ⊤)).inv := by
    rw [← cancel_epi (Scheme.ΓSpecIso Γ(Z, ⊤)).hom, Iso.hom_inv_id,
      ← Scheme.toSpecΓ_appTop, ← Scheme.Hom.comp_appTop]
    simp
  rw [Scheme.Hom.comp_appTop, h, Scheme.ΓSpecIso_inv_naturality]

/-- An affine test has a refinement injective on sections on which finitely many
units have square roots. -/
theorem exists_squareRoot_test {S : Scheme.{u}} (Z : Over S) [IsAffine Z.left]
    {n : ℕ} (a : Fin n → Γ(Z.left, ⊤)ˣ) :
    ∃ (W : Over S) (j : W ⟶ Z), Function.Injective j.left.appTop ∧
      ∃ r : Fin n → Γ(W.left, ⊤)ˣ,
        ∀ i, r i * r i = Units.map j.left.appTop.hom.toMonoidHom (a i) := by
  obtain ⟨B, hB, f, hf, r, hr⟩ := UnitSquareExtension.exists_squareRoots a
  let φ : Γ(Z.left, ⊤) ⟶ CommRingCat.of B := CommRingCat.ofHom f
  let j₀ : Spec (CommRingCat.of B) ⟶ Z.left := Spec.map φ ≫ Z.left.isoSpec.inv
  let W : Over S := Over.mk (j₀ ≫ Z.hom)
  let j : W ⟶ Z := Over.homMk j₀
  have hj : j.left.appTop = φ ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).inv :=
    appTop_specMap_isoSpec_inv φ
  refine ⟨W, j, ?_, fun i =>
    Units.map (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom.toMonoidHom (r i), ?_⟩
  · rw [hj]
    exact ((ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of B)).inv).1).comp hf
  · intro i
    rw [← map_mul, hr, hj]
    rfl

/-- Equality of points with affine target descends through any map injective on
global sections. -/
theorem points_ext_of_injective_appTop {S : Scheme.{u}} {Z W Y : Over S}
    [IsAffine Y.left] (j : W ⟶ Z) (hj : Function.Injective j.left.appTop)
    {f g : Z ⟶ Y} (h : j ≫ f = j ≫ g) : f = g := by
  apply Over.OverMorphism.ext
  apply ext_of_isAffine
  apply ConcreteCategory.hom_ext
  intro x
  apply hj
  have ht := congrArg (fun a => a.left.appTop) h
  rw [Over.comp_left, Over.comp_left, Scheme.Hom.comp_appTop,
    Scheme.Hom.comp_appTop] at ht
  exact ConcreteCategory.congr_hom ht x

end SchemeTests

namespace WeylData

variable {k : Type u} [CommRing k] (D : WeylData k)
  {Z W : Over (Spec (CommRingCat.of k))}

theorem comp_pb (j : W ⟶ Z) (x : Γ((base k).left, ⊤)) :
    j.left.appTop (pb Z x) = pb W x := by
  change j.left.appTop (Z.hom.appTop x) = W.hom.appTop x
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, Over.w j]

/-- The unit-coordinate rank-one relation on affine tests, with no supplied
square roots. -/
theorem relation_of_unit_affine [IsAffine D.G.X.left] [IsAffine Z.left]
    (X : Γ(Z.left, ⊤)) (w u : Γ(Z.left, ⊤)ˣ)
    (hu : (u : Γ(Z.left, ⊤)) = 1 + X * (w : Γ(Z.left, ⊤))) :
    D.A X * D.B (pb Z D.cβ * (w : Γ(Z.left, ⊤))) =
      D.cellPt (pb Z D.cβ * ((↑u⁻¹ : Γ(Z.left, ⊤)) * (w : Γ(Z.left, ⊤))))
        (D.tH u) ((↑u⁻¹ : Γ(Z.left, ⊤)) * X) := by
  let δ := Units.map (toBase Z).left.appTop.hom.toMonoidHom D.unitδ.unit
  have hδ : (δ : Γ(Z.left, ⊤)) = pb Z D.cδ := by
    simp only [δ, Units.coe_map, IsUnit.unit_spec]
    rfl
  let a : Fin 3 → Γ(Z.left, ⊤)ˣ := ![δ, w⁻¹, u * w⁻¹]
  obtain ⟨W, j, hj, r, hr⟩ := exists_squareRoot_test Z a
  let w' := Units.map j.left.appTop.hom.toMonoidHom w
  let u' := Units.map j.left.appTop.hom.toMonoidHom u
  have hu' : (u' : Γ(W.left, ⊤)) = 1 + j.left.appTop X * (w' : Γ(W.left, ⊤)) := by
    change j.left.appTop (u : Γ(Z.left, ⊤)) =
      1 + j.left.appTop X * j.left.appTop (w : Γ(Z.left, ⊤))
    rw [hu, map_add, map_one, map_mul]
  have hd' : (↑(r 0 * r 0) : Γ(W.left, ⊤)) = pb W D.cδ := by
    rw [hr]
    change j.left.appTop (δ : Γ(Z.left, ⊤)) = _
    rw [hδ, comp_pb]
  have hc : r 2 * r 2 = u' * w'⁻¹ := by
    rw [hr]
    change Units.map j.left.appTop.hom.toMonoidHom (u * w⁻¹) = _
    rw [map_mul, map_inv]
  have hc' : r 1 * r 1 = w'⁻¹ := by
    rw [hr]
    change Units.map j.left.appTop.hom.toMonoidHom w⁻¹ = _
    rw [map_inv]
  have h := D.relation_of_unit_squares (j.left.appTop X) w' u' (r 0) (r 2) (r 1)
    hu' hd' hc hc'
  apply points_ext_of_injective_appTop j hj
  rw [MonObj.comp_mul, CellData.comp_A, CellData.comp_B, CellData.comp_cellPt,
    comp_tH]
  have hv (v : Γ(Z.left, ⊤)ˣ) :
      (Units.map j.left.appTop.hom.toMonoidHom v : Γ(W.left, ⊤)) =
        j.left.appTop (v : Γ(Z.left, ⊤)) := rfl
  simpa only [w', u', map_mul, comp_pb, ← map_inv, hv] using h

/-- The rank-one relation for a unit second coordinate on every scheme test.
No square roots are part of the hypotheses. -/
theorem relation_of_unit [IsAffine D.G.X.left]
    (X : Γ(Z.left, ⊤)) (w u : Γ(Z.left, ⊤)ˣ)
    (hu : (u : Γ(Z.left, ⊤)) = 1 + X * (w : Γ(Z.left, ⊤))) :
    D.A X * D.B (pb Z D.cβ * (w : Γ(Z.left, ⊤))) =
      D.cellPt (pb Z D.cβ * ((↑u⁻¹ : Γ(Z.left, ⊤)) * (w : Γ(Z.left, ⊤))))
        (D.tH u) ((↑u⁻¹ : Γ(Z.left, ⊤)) * X) := by
  apply Over.OverMorphism.ext
  apply Z.left.affineCover.hom_ext
  intro i
  let V := SubgroupFunctor.coverObj Z.left.affineCover i
  let : IsAffine V.left := inferInstanceAs (IsAffine (Z.left.affineCover.X i))
  let j : V ⟶ Z := SubgroupFunctor.coverMap Z.left.affineCover i
  let w' := Units.map j.left.appTop.hom.toMonoidHom w
  let u' := Units.map j.left.appTop.hom.toMonoidHom u
  have hv (v : Γ(Z.left, ⊤)ˣ) :
      (Units.map j.left.appTop.hom.toMonoidHom v : Γ(V.left, ⊤)) =
        j.left.appTop (v : Γ(Z.left, ⊤)) := rfl
  have hu' : (u' : Γ(V.left, ⊤)) = 1 + j.left.appTop X * (w' : Γ(V.left, ⊤)) := by
    change j.left.appTop (u : Γ(Z.left, ⊤)) =
      1 + j.left.appTop X * j.left.appTop (w : Γ(Z.left, ⊤))
    rw [hu, map_add, map_one, map_mul]
  have h := D.relation_of_unit_affine (j.left.appTop X) w' u' hu'
  have h' : j ≫ (D.A X * D.B (pb Z D.cβ * (w : Γ(Z.left, ⊤)))) =
      j ≫ D.cellPt (pb Z D.cβ * ((↑u⁻¹ : Γ(Z.left, ⊤)) * (w : Γ(Z.left, ⊤))))
        (D.tH u) ((↑u⁻¹ : Γ(Z.left, ⊤)) * X) := by
    rw [MonObj.comp_mul, CellData.comp_A, CellData.comp_B, CellData.comp_cellPt,
      comp_tH]
    simpa only [w', u', map_mul, comp_pb, ← map_inv, hv] using h
  exact congrArg (fun f => f.left) h'

end WeylData

end Langlands.GroupScheme.RingRootCell
