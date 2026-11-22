import Langlands.Geometry.FormalGroup.PDivisibleGroupTateGeometric

/-! # Reduction modulo a prime power of schematic Tate points -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.PDivisibleGroup

open CommGroupScheme

variable {R : CommRingCat.{u}} {p : ℕ} [Fact p.Prime] (G : PDivisibleGroup R p)
variable (A : CommAlgCat.{u} R)

private abbrev affineEval (A : CommAlgCat.{u} R) :
    CommGroupScheme (Spec R) ⥤ AddCommGrpCat.{u} :=
  additivePointFunctor (Spec R) ⋙ (evaluation _ _).obj (op (affineTest A))

private abbrev tatePresheaf (G : PDivisibleGroup R p) :=
  (schematicTatePointFunctor R p).obj G

private abbrev sectionProjection (G : PDivisibleGroup R p) (A : CommAlgCat.{u} R) (n : ℕ) :=
  (G.schematicTatePointProjection n).app (op (affineTest A))

local notation "E" => affineEval A
local notation "P" => tatePresheaf G
local notation "π" => sectionProjection G A

private theorem eval_inclusion_injective {m n : ℕ} (i : m ⟶ n) :
    Function.Injective ((E).map (G.inclusions.map i)) := by
  intro x y h
  exact congrArg Additive.ofMul
    (G.inclusion_affine_injective i A (congrArg Additive.toMul h))

private theorem eval_transfer_projection {m n : ℕ} (i : m ⟶ n)
    (x : (P).obj (op (affineTest A))) :
    (E).map (G.transfer i) (π n x) = π m x :=
  ConcreteCategory.congr_hom (NatTrans.congr_app (G.schematicTatePointProjection_transfer i)
    (op (affineTest A))) x

private theorem eval_factorization {m n : ℕ} (i : m ⟶ n)
    (x : (E).obj (G.inclusions.obj n)) :
    (E).map (G.inclusions.map i) ((E).map (G.transfer i) x) = p ^ (n - m) • x := by
  have h : (E).map (G.transfer i) ≫ (E).map (G.inclusions.map i) =
      p ^ (n - m) • 𝟙 ((E).obj (G.inclusions.obj n)) := by
    rw [← Functor.map_comp, G.multiplication, Functor.map_nsmul, (E).map_id]
  exact ConcreteCategory.congr_hom h x

private theorem eval_factorization_reverse {m n : ℕ} (i : m ⟶ n)
    (x : (E).obj (G.inclusions.obj m)) :
    (E).map (G.transfer i) ((E).map (G.inclusions.map i) x) = p ^ (n - m) • x := by
  apply G.eval_inclusion_injective A i
  rw [G.eval_factorization A i]
  exact (map_nsmul ((E).map (G.inclusions.map i)).hom _ _).symm

private theorem eval_level_zero (x : (E).obj (G.inclusions.obj 0)) : x = 0 := by
  let z : affineTest A ⟶ (G.inclusions.obj 0).X := x.toMul
  let j : 0 ⟶ 0 := 𝟙 0
  have hi : homOfLE (Nat.le_add_left 0 0) = j := Subsingleton.elim _ _
  have h := (G.shortExact 0 0).2.1 A z
  rw [hi] at h
  change (z ≫ (G.transfer (𝟙 0)).toMul.hom.hom = 1) ↔
    ∃ y, y ≫ (G.inclusions.map (𝟙 0)).toMul.hom.hom = z at h
  rw [G.transfer_id, G.inclusions.map_id] at h
  have hx : z = 1 := (Category.comp_id _).symm.trans (h.mpr ⟨z, Category.comp_id _⟩)
  exact congrArg Additive.ofMul hx

/-- The finite level `n` is killed by `p ^ n` on every affine test. -/
theorem schematicTateFiniteLevel_nsmul (n : ℕ) (x : (E).obj (G.inclusions.obj n)) :
    (p ^ n : ℕ) • x = 0 := by
  let i : 0 ⟶ n := homOfLE (Nat.zero_le n)
  have hh := G.eval_factorization A i x
  rw [Nat.sub_zero, G.eval_level_zero A ((E).map (G.transfer i) x)] at hh
  exact hh.symm.trans (map_zero ((E).map (G.inclusions.map i)).hom)

private abbrev shiftInclusion (b n : ℕ) : n ⟶ b + n := homOfLE (Nat.le_add_left n b)

private abbrev shiftTransfer {m n : ℕ} (b : ℕ) (a : m ⟶ n) : b + m ⟶ b + n :=
  homOfLE (Nat.add_le_add_left (leOfHom a) b)

private theorem eval_shift_square {m n : ℕ} (b : ℕ) (a : m ⟶ n)
    (x : (E).obj (G.inclusions.obj n)) :
    (E).map (G.transfer (shiftTransfer b a))
        ((E).map (G.inclusions.map (shiftInclusion b n)) x) =
      (E).map (G.inclusions.map (shiftInclusion b m)) ((E).map (G.transfer a) x) := by
  let a' := shiftTransfer b a
  let j := shiftInclusion b m
  let i := shiftInclusion b n
  have h : a ≫ i = j ≫ a' := Subsingleton.elim _ _
  have hd : b + n - (b + m) = n - m := by omega
  have hh : (G.inclusions.map i ≫ G.transfer a') ≫ G.inclusions.map a' =
      (G.transfer a ≫ G.inclusions.map j) ≫ G.inclusions.map a' := by
    calc
      _ = p ^ (n - m) • G.inclusions.map i := by
        rw [Category.assoc, G.multiplication a', Preadditive.comp_nsmul, Category.comp_id]
        rw [show b + n - (b + m) = n - m from hd]
      _ = _ := by
        symm
        rw [Category.assoc, ← G.inclusions.map_comp, ← h, G.inclusions.map_comp,
          ← Category.assoc, G.multiplication a, Preadditive.nsmul_comp, Category.id_comp]
  apply G.eval_inclusion_injective A a'
  have hh' := ConcreteCategory.congr_hom (congrArg (fun f => (E).map f) hh) x
  rwa [Functor.map_comp, Functor.map_comp, Functor.map_comp, Functor.map_comp] at hh'

private theorem exists_level_inclusion (b : ℕ) (x : (P).obj (op (affineTest A)))
    (hx : π b x = 0) (n : ℕ) :
    ∃ y : (E).obj (G.inclusions.obj n), (E).map (G.inclusions.map (shiftInclusion b n)) y =
      π (b + n) x := by
  let j : b ⟶ b + n := homOfLE (Nat.le_add_right b n)
  have hz := (G.eval_transfer_projection A j x).trans hx
  have hz' : (π (b + n) x).toMul ≫ (G.transfer j).toMul.hom.hom = 1 :=
    congrArg Additive.toMul hz
  obtain ⟨y, hy⟩ := ((G.shortExact b n).2.1 A (π (b + n) x).toMul).mp hz'
  exact ⟨Additive.ofMul y, congrArg Additive.ofMul hy⟩

/-- Divide a section with zero projection at `b` by shifting its finite
components through the actual scheme-level kernels. -/
def schematicTateDivide (b : ℕ) (x : (P).obj (op (affineTest A))) (hx : π b x = 0) :
    (P).obj (op (affineTest A)) := by
  let y (n : ℕ) := (G.exists_level_inclusion A b x hx n).choose
  have hy (n : ℕ) : (E).map (G.inclusions.map (shiftInclusion b n)) (y n) = π (b + n) x :=
    (G.exists_level_inclusion A b x hx n).choose_spec
  refine (G.schematicTatePointEquivSections (affineTest A)).symm ⟨fun n => y n.unop, ?_⟩
  intro n m i
  change (E).map (G.transfer i.unop) (y n.unop) = y m.unop
  apply G.eval_inclusion_injective A (shiftInclusion b m.unop)
  rw [← G.eval_shift_square A b i.unop, hy, hy]
  exact G.eval_transfer_projection A (shiftTransfer b i.unop) x

theorem schematicTateDivide_projection (b : ℕ) (x : (P).obj (op (affineTest A)))
    (hx : π b x = 0) (n : ℕ) :
    (E).map (G.inclusions.map (shiftInclusion b n)) (π n (G.schematicTateDivide A b x hx)) =
      π (b + n) x := by
  unfold schematicTateDivide
  rw [schematicTatePointEquivSections_symm_apply]
  exact (G.exists_level_inclusion A b x hx n).choose_spec

/-- Multiplication by the specified prime power recovers the original section. -/
theorem schematicTateDivide_nsmul (b : ℕ) (x : (P).obj (op (affineTest A))) (hx : π b x = 0) :
    (p ^ b : ℕ) • G.schematicTateDivide A b x hx = x := by
  apply schematicTatePoint_ext
  intro n
  let i := shiftInclusion b n
  let y := G.schematicTateDivide A b x hx
  have hk : b + n - n = b := Nat.add_sub_cancel_right _ _
  change (π n).hom ((p ^ b : ℕ) • y) = π n x
  rw [map_nsmul, ← hk, ← G.eval_factorization_reverse A i, G.schematicTateDivide_projection]
  exact G.eval_transfer_projection A i x

/-- The kernel of the `n`-th projection consists precisely of `p ^ n` multiples. -/
theorem schematicTatePointProjection_ker (n : ℕ) :
    (π n).hom.ker =
      (nsmulAddMonoidHom (α := (P).obj (op (affineTest A))) (p ^ n)).range := by
  ext x
  constructor
  · intro hx
    exact ⟨G.schematicTateDivide A n x hx, G.schematicTateDivide_nsmul A n x hx⟩
  · rintro ⟨y, rfl⟩
    change (π n).hom ((p ^ n : ℕ) • y) = 0
    rw [map_nsmul]
    exact G.schematicTateFiniteLevel_nsmul A n (π n y)

variable (K : Type u) [Field K] [IsAlgClosed K] [Algebra R K]

local notation "Tₖ" => affineTest (CommAlgCat.of R K)

/-- Reduction of a geometric Tate section modulo `p ^ n` is the actual
point group at level `n`. -/
def schematicTateGeometricReductionEquiv (n : ℕ) :
    ((P).obj (op Tₖ) ⧸ (nsmulAddMonoidHom (α := (P).obj (op Tₖ)) (p ^ n)).range) ≃+
      (GroupScheme.additivePoints (G.inclusions.obj n).toGrp).obj (op Tₖ) :=
  (QuotientAddGroup.quotientAddEquivOfEq
    (G.schematicTatePointProjection_ker (CommAlgCat.of R K) n).symm).trans
    (G.schematicTateProjectionQuotientEquiv K n)

@[simp] theorem schematicTateGeometricReductionEquiv_mk (n : ℕ) (x : (P).obj (op Tₖ)) :
    G.schematicTateGeometricReductionEquiv K n (QuotientAddGroup.mk x) =
      (G.schematicTatePointProjection n).app (op Tₖ) x := rfl

end Langlands.PDivisibleGroup
