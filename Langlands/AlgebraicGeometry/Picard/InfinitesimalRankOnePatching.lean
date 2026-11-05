import Langlands.AlgebraicGeometry.Picard.NilpotentUnitReduction
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-! # Free rank-one patching across an infinitesimal ring square -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.AlgebraicGeometry.Picard.InfinitesimalRankOnePatching

variable {R A B C : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing C]

section Rings

variable (p : R →+* A) (q : R →+* B) (a : A →+* C) (b : B →+* C)
  (h : IsPullback (CommRingCat.ofHom p) (CommRingCat.ofHom q)
    (CommRingCat.ofHom a) (CommRingCat.ofHom b))

include p q a b h

/-- The actual ring square commutes on elements. -/
lemma comm_apply (r : R) : a (p r) = b (q r) :=
  congrArg (fun f : CommRingCat.of R ⟶ CommRingCat.of C ↦ f r) h.w

/-- The two actual ring projections jointly detect equality. -/
lemma element_ext {r s : R} (hp : p r = p s) (hq : q r = q s) : r = s :=
  Types.ext_of_isPullback (h.map (forget CommRingCat)) hp hq

/-- Every compatible pair of actual ring elements has a lift. -/
lemma exists_lift (x : A) (y : B) (hxy : a x = b y) :
    ∃ r : R, p r = x ∧ q r = y :=
  Types.exists_of_isPullback (h.map (forget CommRingCat)) x y hxy

/-- The other projection is surjective when the given leg is surjective. -/
lemma fst_surjective (hb : Function.Surjective b) : Function.Surjective p := by
  intro x
  obtain ⟨y, hy⟩ := hb (a x)
  obtain ⟨r, hr, _⟩ := exists_lift p q a b h x y hy.symm
  exact ⟨r, hr⟩

/-- Compatible actual units patch uniquely, without a nilpotence hypothesis. -/
lemma existsUnique_unit (x : Aˣ) (y : Bˣ)
    (hxy : Units.map a.toMonoidHom x = Units.map b.toMonoidHom y) :
    ∃! r : Rˣ, Units.map p.toMonoidHom r = x ∧ Units.map q.toMonoidHom r = y := by
  obtain ⟨r, hrp, hrq⟩ := exists_lift p q a b h (x : A) (y : B)
    (congrArg Units.val hxy)
  have hinv : Units.map a.toMonoidHom x⁻¹ = Units.map b.toMonoidHom y⁻¹ := by
    simpa only [map_inv] using congrArg Inv.inv hxy
  obtain ⟨s, hsp, hsq⟩ := exists_lift p q a b h (↑x⁻¹ : A) (↑y⁻¹ : B)
    (congrArg Units.val hinv)
  have hrs : r * s = 1 := by
    apply element_ext p q a b h <;> simp [map_mul, hrp, hrq, hsp, hsq]
  let u : Rˣ := ⟨r, s, hrs, by simpa only [mul_comm] using hrs⟩
  refine ⟨u, ⟨Units.ext hrp, Units.ext hrq⟩, ?_⟩
  intro v hv
  apply Units.ext
  exact element_ext p q a b h ((congrArg Units.val hv.1).trans hrp.symm)
    ((congrArg Units.val hv.2).trans hrq.symm)

end Rings

section Modules

variable [Algebra R A] [Algebra R B]
  (a : A →+* C) (b : B →+* C)
  (h : IsPullback (CommRingCat.ofHom (algebraMap R A))
    (CommRingCat.ofHom (algebraMap R B)) (CommRingCat.ofHom a) (CommRingCat.ofHom b))

include a b h

local notation "p" => algebraMap R A
local notation "q" => algebraMap R B

/-- The actual module of pairs with the prescribed overlap multiplier. -/
def patchedModule (c : Cˣ) : Submodule R (A × B) where
  carrier := {z | a z.1 = (c : C) * b z.2}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change a (x.1 + y.1) = (c : C) * b (x.2 + y.2)
    rw [map_add, map_add, hx, hy, mul_add]
  smul_mem' := by
    intro r z hz
    change a (r • z.1) = (c : C) * b (r • z.2)
    simp only [Algebra.smul_def]
    rw [map_mul, map_mul, comm_apply p q a b h r, hz]
    ring

/-- A lift of the overlap unit gives an actual frame of the patched module. -/
def frameMap (c : Cˣ) (v : Bˣ) (hv : Units.map b.toMonoidHom v = c) :
    R →ₗ[R] patchedModule a b h c where
  toFun r := ⟨(p r, (↑v⁻¹ : B) * q r), by
    change a (p r) = (c : C) * b ((↑v⁻¹ : B) * q r)
    have hc : (c : C) * b (↑v⁻¹ : B) = 1 := by
      rw [← hv]
      change b (v : B) * b (↑v⁻¹ : B) = 1
      rw [← map_mul]
      simp
    rw [map_mul, ← mul_assoc, hc, one_mul]
    exact comm_apply p q a b h r⟩
  map_add' r s := by
    apply Subtype.ext
    ext <;> simp [map_add, mul_add]
  map_smul' r s := by
    apply Subtype.ext
    ext
    · change p (r * s) = r • p s
      rw [Algebra.smul_def, map_mul]
    · change (↑v⁻¹ : B) * q (r * s) = r • ((↑v⁻¹ : B) * q s)
      rw [Algebra.smul_def, map_mul]
      ring

/-- This frame map is bijective for the actual pullback ring. -/
lemma frameMap_bijective (c : Cˣ) (v : Bˣ)
    (hv : Units.map b.toMonoidHom v = c) :
    Function.Bijective (frameMap a b h c v hv) := by
  constructor
  · intro r s hrs
    apply element_ext p q a b h
    · exact congrArg (fun z : patchedModule a b h c ↦ z.val.1) hrs
    · have he := congrArg (fun z : patchedModule a b h c ↦ (v : B) * z.val.2) hrs
      simpa [frameMap, ← mul_assoc] using he
  · intro z
    have hv' : b (v : B) = (c : C) := congrArg Units.val hv
    have hz : a z.val.1 = b ((v : B) * z.val.2) := by
      rw [map_mul, hv']
      exact z.property
    obtain ⟨r, hrp, hrq⟩ := exists_lift p q a b h z.val.1 ((v : B) * z.val.2) hz
    refine ⟨r, Subtype.ext ?_⟩
    ext
    · exact hrp
    · change (↑v⁻¹ : B) * q r = z.val.2
      rw [hrq, ← mul_assoc]
      simp

/-- The frame equivalence retains the chosen unit lift and prescribed multiplier. -/
def frameEquiv (c : Cˣ) (v : Bˣ) (hv : Units.map b.toMonoidHom v = c) :
    R ≃ₗ[R] patchedModule a b h c :=
  LinearEquiv.ofBijective (frameMap a b h c v hv)
    (frameMap_bijective a b h c v hv)

@[simp] lemma frameEquiv_fst (c : Cˣ) (v : Bˣ)
    (hv : Units.map b.toMonoidHom v = c) (r : R) :
    (frameEquiv a b h c v hv r).val.1 = p r := rfl

@[simp] lemma frameEquiv_snd (c : Cˣ) (v : Bˣ)
    (hv : Units.map b.toMonoidHom v = c) (r : R) :
    (frameEquiv a b h c v hv r).val.2 = (↑v⁻¹ : B) * q r := rfl

/-- A surjective nilpotent leg supplies a frame for every prescribed overlap unit. -/
lemma exists_frame (hb : Function.Surjective b) (hker : IsNilpotent (RingHom.ker b))
    (c : Cˣ) :
    ∃ v : Bˣ, Units.map b.toMonoidHom v = c ∧
      ∃ e : R ≃ₗ[R] patchedModule a b h c,
        (∀ r, (e r).val.1 = p r) ∧
          ∀ r, (e r).val.2 = (↑v⁻¹ : B) * q r := by
  obtain ⟨v, hv⟩ := NilpotentUnitReduction.unitsMap_surjective b hb hker c
  exact ⟨v, hv, frameEquiv a b h c v hv, fun _ ↦ rfl, fun _ ↦ rfl⟩

/-- Compatible scalar maps act on the actual pair module componentwise. -/
def diagonalMap (c d : Cˣ) (x : A) (y : B)
    (hxy : a x * (c : C) = (d : C) * b y) :
    patchedModule a b h c →ₗ[R] patchedModule a b h d where
  toFun z := ⟨(x * z.val.1, y * z.val.2), by
    change a (x * z.val.1) = (d : C) * b (y * z.val.2)
    rw [map_mul, map_mul, z.property, ← mul_assoc, hxy, mul_assoc]⟩
  map_add' z w := by
    apply Subtype.ext
    ext <;> simp [mul_add]
  map_smul' r z := by
    apply Subtype.ext
    ext
    · change x * (r • z.val.1) = r • (x * z.val.1)
      simp only [Algebra.smul_def]
      ring
    · change y * (r • z.val.2) = r • (y * z.val.2)
      simp only [Algebra.smul_def]
      ring

@[simp] lemma diagonalMap_fst (c d : Cˣ) (x : A) (y : B)
    (hxy : a x * (c : C) = (d : C) * b y) (z : patchedModule a b h c) :
    (diagonalMap a b h c d x y hxy z).val.1 = x * z.val.1 := rfl

@[simp] lemma diagonalMap_snd (c d : Cˣ) (x : A) (y : B)
    (hxy : a x * (c : C) = (d : C) * b y) (z : patchedModule a b h c) :
    (diagonalMap a b h c d x y hxy z).val.2 = y * z.val.2 := rfl

/-- A map of pair modules is uniquely determined by its two actual projections. -/
lemma linearMap_ext (c d : Cˣ)
    (F G : patchedModule a b h c →ₗ[R] patchedModule a b h d)
    (hfst : ∀ z, (F z).val.1 = (G z).val.1)
    (hsnd : ∀ z, (F z).val.2 = (G z).val.2) : F = G := by
  apply LinearMap.ext
  intro z
  exact Subtype.ext (Prod.ext (hfst z) (hsnd z))

/-- Compatible scalar maps have a unique lift with the prescribed projections. -/
lemma diagonalMap_unique (c d : Cˣ) (x : A) (y : B)
    (hxy : a x * (c : C) = (d : C) * b y)
    (F : patchedModule a b h c →ₗ[R] patchedModule a b h d)
    (hfst : ∀ z, (F z).val.1 = x * z.val.1)
    (hsnd : ∀ z, (F z).val.2 = y * z.val.2) :
    F = diagonalMap a b h c d x y hxy :=
  linearMap_ext a b h c d F _ hfst hsnd

omit h in
/-- Compatibility of actual overlap isomorphisms also holds for their inverses. -/
lemma inverse_compat (c d : Cˣ) (x : Aˣ) (y : Bˣ)
    (hxy : Units.map a.toMonoidHom x * c = d * Units.map b.toMonoidHom y) :
    Units.map a.toMonoidHom x⁻¹ * d = c * Units.map b.toMonoidHom y⁻¹ := by
  have he := congrArg (fun z : Cˣ ↦ (Units.map a.toMonoidHom x)⁻¹ * z *
    (Units.map b.toMonoidHom y)⁻¹) hxy
  simpa [map_inv, mul_assoc] using he.symm

/-- Compatible prescribed unit multipliers induce an actual linear equivalence. -/
def diagonalEquiv (c d : Cˣ) (x : Aˣ) (y : Bˣ)
    (hxy : Units.map a.toMonoidHom x * c = d * Units.map b.toMonoidHom y) :
    patchedModule a b h c ≃ₗ[R] patchedModule a b h d where
  toLinearMap := diagonalMap a b h c d (x : A) (y : B) (congrArg Units.val hxy)
  invFun := diagonalMap a b h d c (↑x⁻¹ : A) (↑y⁻¹ : B)
    (congrArg Units.val (inverse_compat a b c d x y hxy))
  left_inv z := by
    apply Subtype.ext
    ext
    · change (↑x⁻¹ : A) * ((x : A) * z.val.1) = z.val.1
      simp [← mul_assoc]
    · change (↑y⁻¹ : B) * ((y : B) * z.val.2) = z.val.2
      simp [← mul_assoc]
  right_inv z := by
    apply Subtype.ext
    ext
    · change (x : A) * ((↑x⁻¹ : A) * z.val.1) = z.val.1
      simp [← mul_assoc]
    · change (y : B) * ((↑y⁻¹ : B) * z.val.2) = z.val.2
      simp [← mul_assoc]

@[simp] lemma diagonalEquiv_fst (c d : Cˣ) (x : Aˣ) (y : Bˣ)
    (hxy : Units.map a.toMonoidHom x * c = d * Units.map b.toMonoidHom y)
    (z : patchedModule a b h c) :
    (diagonalEquiv a b h c d x y hxy z).val.1 = (x : A) * z.val.1 := rfl

@[simp] lemma diagonalEquiv_snd (c d : Cˣ) (x : Aˣ) (y : Bˣ)
    (hxy : Units.map a.toMonoidHom x * c = d * Units.map b.toMonoidHom y)
    (z : patchedModule a b h c) :
    (diagonalEquiv a b h c d x y hxy z).val.2 = (y : B) * z.val.2 := rfl

/-- The prescribed unit multipliers determine the equivalence uniquely. -/
lemma diagonalEquiv_unique (c d : Cˣ) (x : Aˣ) (y : Bˣ)
    (hxy : Units.map a.toMonoidHom x * c = d * Units.map b.toMonoidHom y)
    (F : patchedModule a b h c ≃ₗ[R] patchedModule a b h d)
    (hfst : ∀ z, (F z).val.1 = (x : A) * z.val.1)
    (hsnd : ∀ z, (F z).val.2 = (y : B) * z.val.2) :
    F = diagonalEquiv a b h c d x y hxy := by
  apply LinearEquiv.toLinearMap_injective
  exact diagonalMap_unique a b h c d (x : A) (y : B) (congrArg Units.val hxy)
    F.toLinearMap hfst hsnd

end Modules

end Langlands.AlgebraicGeometry.Picard.InfinitesimalRankOnePatching
