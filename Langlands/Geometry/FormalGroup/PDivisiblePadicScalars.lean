import Langlands.Geometry.FormalGroup.PDivisibleGroupMorphisms
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.NumberTheory.Padics.RingHoms

/-! # The natural p-adic scalar action on a p-divisible group -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.PDivisibleGroup

variable {R : CommRingCat.{u}} {p : ℕ} [Fact p.Prime] (G : PDivisibleGroup R p)

/-- Every affine point of the zeroth level is the identity point. -/
theorem levelZero_affinePoint_eq_one (A : CommAlgCat.{u} R)
    (x : CommGroupScheme.affineTest A ⟶ (G.inclusions.obj 0).X) : x = 1 := by
  let h := (G.shortExact 0 0).2.1 A x
  let i : (0 : ℕ) ⟶ 0 := homOfLE (Nat.le_refl 0)
  have hi : i = 𝟙 0 := Subsingleton.elim _ _
  have hinc : G.inclusions.map i = 𝟙 (G.inclusions.obj 0) := by
    rw [hi]
    exact G.inclusions.map_id 0
  have hmul : G.transfer i = 𝟙 (G.inclusions.obj 0) := hi ▸ G.transfer_id 0
  have h' := h.mpr ⟨x, by
    change x ≫ (G.inclusions.map i).toMul.hom.hom = x
    rw [hinc]
    exact Category.comp_id x⟩
  change x ≫ (G.transfer i).toMul.hom.hom = 1 at h'
  rw [hmul] at h'
  exact (Category.comp_id x).symm.trans h'

/-- The actual n-th finite group scheme is killed by multiplication by p^n. -/
theorem level_nsmul_id_eq_zero (n : ℕ) :
    p ^ n • (𝟙 (G.inclusions.obj n)) = (0 : End (G.inclusions.obj n)) := by
  let i : 0 ⟶ n := homOfLE (Nat.zero_le n)
  have hm := G.multiplication i
  rw [Nat.sub_zero] at hm
  rw [← hm]
  have : IsFinite (G.inclusions.obj n).X.hom := (G.finiteLocallyFree n).1
  have : IsAffine (G.inclusions.obj n).X.left :=
    GroupScheme.Cartier.FiniteDual.isAffine_of_isFinite (G.inclusions.obj n).toGrp
  obtain ⟨C, _, _, ⟨e⟩⟩ := GroupScheme.Cartier.FiniteDual.exists_iso_algSpec (G.inclusions.obj n).X
  let y := e.inv ≫ (G.transfer i).toMul.hom.hom
  have hy : y = 1 := G.levelZero_affinePoint_eq_one (CommAlgCat.of R C) y
  change Additive.ofMul (G.transfer i).toMul ≫ G.inclusions.map i = 0
  apply congrArg Additive.ofMul
  apply Grp.hom_ext
  apply (cancel_epi e.inv).mp
  change e.inv ≫ ((G.transfer i).toMul.hom.hom ≫ (G.inclusions.map i).toMul.hom.hom) =
    e.inv ≫ (1 : (G.inclusions.obj n).X ⟶ (G.inclusions.obj n).X)
  rw [MonObj.comp_one, ← Category.assoc]
  change y ≫ (G.inclusions.map i).toMul.hom.hom = 1
  rw [hy, MonObj.one_comp]

/-- Integers modulo p^n act on the actual n-th level. -/
def levelZModAction (n : ℕ) : ZMod (p ^ n) →+* End (G.inclusions.obj n) := by
  let E := End (G.inclusions.obj n)
  let : CharP E (ringChar E) := ringChar.charP E
  have h : ringChar E ∣ p ^ n := ringChar.dvd (R := E) (by
    rw [← nsmul_one]
    exact G.level_nsmul_id_eq_zero n)
  exact ZMod.castHom (m := ringChar E) h E

/-- An actual finite level carries the residue of a p-adic scalar. -/
def levelPadicAction (n : ℕ) : ℤ_[p] →+* End (G.inclusions.obj n) :=
  (G.levelZModAction n).comp (PadicInt.toZModPow n)

/-- A representative of the scalar at level n acts by its integral multiple
at every level m at most n. -/
theorem levelPadicAction_eq_nsmul_of_le {m n : ℕ} (h : m ≤ n) (a : ℤ_[p]) :
    G.levelPadicAction m a = (PadicInt.toZModPow n a).val • (𝟙 (G.inclusions.obj m)) := by
  let j := PadicInt.toZModPow n a
  let r := ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ m))
  have hn : (j.val : ZMod (p ^ n)) = j := ZMod.natCast_zmod_val j
  have hm : PadicInt.toZModPow m a = (j.val : ZMod (p ^ m)) := by
    have he := DFunLike.congr_fun (PadicInt.zmod_cast_comp_toZModPow (p := p) m n h) a
    change r j = PadicInt.toZModPow m a at he
    exact he.symm.trans ((congrArg r hn.symm).trans (map_natCast r j.val))
  change G.levelZModAction m (PadicInt.toZModPow m a) = _
  rw [hm, map_natCast, ← nsmul_one]
  rfl

/-- The natural p-adic scalar action on the entire actual tower. -/
def padicAction : ℤ_[p] →+* End G where
  toFun a := Hom.ofComponents (fun n => G.levelPadicAction n a) (by
    intro m n i
    rw [G.levelPadicAction_eq_nsmul_of_le (leOfHom i), G.levelPadicAction_eq_nsmul_of_le (le_refl n)]
    simp) (by
    intro m n i
    rw [G.levelPadicAction_eq_nsmul_of_le (leOfHom i), G.levelPadicAction_eq_nsmul_of_le (le_refl n)]
    simp)
  map_one' := Hom.ext fun n => (G.levelPadicAction n).map_one
  map_zero' := Hom.ext fun n => (G.levelPadicAction n).map_zero
  map_add' a b := Hom.ext fun n => (G.levelPadicAction n).map_add a b
  map_mul' a b := Hom.ext fun n => (G.levelPadicAction n).map_mul a b

@[simp] theorem padicAction_app (n : ℕ) (a : ℤ_[p]) :
    (Hom.app (G.padicAction a) n) = G.levelPadicAction n a := rfl

/-- All morphisms commute with the natural p-adic scalar actions. -/
theorem padicAction_naturality {H : PDivisibleGroup R p} (f : G ⟶ H) (a : ℤ_[p]) :
    G.padicAction a ≫ f = f ≫ H.padicAction a := by
  apply Hom.ext
  intro n
  rw [Hom.comp_app, Hom.comp_app, padicAction_app, padicAction_app,
    G.levelPadicAction_eq_nsmul_of_le (le_refl n), H.levelPadicAction_eq_nsmul_of_le (le_refl n)]
  simp

/-- The actual category of p-divisible groups is linear over the p-adic integers. -/
instance : CategoryTheory.Linear ℤ_[p] (PDivisibleGroup R p) where
  homModule G H := Module.compHom (G ⟶ H) H.padicAction
  smul_comp G H J a f g := by
    change (f ≫ H.padicAction a) ≫ g = (f ≫ g) ≫ J.padicAction a
    rw [Category.assoc, H.padicAction_naturality, ← Category.assoc]
  comp_smul _ _ J f a g := (Category.assoc f g (J.padicAction a)).symm

/-- Scalar multiplication of a morphism is postcomposition by the scalar on the target. -/
theorem smul_eq_comp_padicAction {G H : PDivisibleGroup R p} (a : ℤ_[p]) (f : G ⟶ H) :
    a • f = f ≫ H.padicAction a := rfl

end Langlands.PDivisibleGroup
