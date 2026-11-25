import Langlands.Geometry.FormalGroup.FormalModulePDivisibleMorphism
import Langlands.Geometry.FormalGroup.PDivisibleRationalHom

/-! # Rational formal maps on the actual p-divisible towers -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1900000
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory TensorProduct

namespace Langlands.PDivisibleGroup

variable {R : CommRingCat.{u}} {p : ℕ} [Fact p.Prime]

/-- Evaluate an actual tower endomorphism at the indicated finite level. -/
def endAt (G : PDivisibleGroup R p) (n : ℕ) : End G →+* End (G.inclusions.obj n) where
  toFun f := End.of (f.asHom.app n)
  map_zero' := congrArg End.of (Hom.zero_app n)
  map_one' := congrArg End.of (Hom.id_app G n)
  map_add' f g := congrArg End.of (Hom.add_app f.asHom g.asHom n)
  map_mul' f g := congrArg End.of (Hom.comp_app g.asHom f.asHom n)

/-- A ring action of the p-adic integers on the actual tower is necessarily its
canonical one, since each level is killed by a known power of p. -/
theorem padicAction_unique (G : PDivisibleGroup R p) (f : ℤ_[p] →+* End G) : f = G.padicAction := by
  apply RingHom.ext
  intro a
  apply End.ext
  apply Hom.ext
  intro n
  let T := End (G.inclusions.obj n)
  let fₙ : ℤ_[p] →+* T := (G.endAt n).comp f
  let m := (PadicInt.toZModPow n a).val
  change (fₙ a).asHom = (G.levelPadicAction n a).asHom
  congr 1
  have hm : PadicInt.toZModPow n a = PadicInt.toZModPow n (m : ℤ_[p]) :=
    ((map_natCast (PadicInt.toZModPow n) m).trans
      (ZMod.natCast_zmod_val (PadicInt.toZModPow n a))).symm
  have hz : a - (m : ℤ_[p]) ∈ RingHom.ker (PadicInt.toZModPow n) := by
    rw [RingHom.mem_ker, map_sub, hm, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hz
  obtain ⟨b, hb⟩ := hz
  have hp : fₙ ((p : ℤ_[p]) ^ n) = 0 := by
    have hs : (p ^ n : ℕ) • (1 : T) = ((p ^ n : ℕ) : T) := nsmul_one _
    rw [← Nat.cast_pow]
    exact (map_natCast fₙ _).trans (hs.symm.trans (congrArg End.of (G.level_nsmul_id_eq_zero n)))
  have he : fₙ (a - (m : ℤ_[p])) = 0 := by
    calc
      fₙ (a - (m : ℤ_[p])) = fₙ ((p : ℤ_[p]) ^ n * b) := congrArg fₙ hb
      _ = fₙ ((p : ℤ_[p]) ^ n) * fₙ b := fₙ.map_mul _ _
      _ = 0 := (congrArg (· * fₙ b) hp).trans (zero_mul _)
  have hs : fₙ (a - (m : ℤ_[p])) = fₙ a - fₙ (m : ℤ_[p]) := fₙ.map_sub _ _
  have ha : fₙ a = fₙ (m : ℤ_[p]) := sub_eq_zero.mp (hs.symm.trans he)
  exact ha.trans ((map_natCast fₙ m).trans ((nsmul_one m).symm.trans
    (End.ext (G.levelPadicAction_eq_nsmul_of_le (le_refl n) a).symm)))

end Langlands.PDivisibleGroup

namespace Langlands.FormalGroup.ModuleLaw

variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Algebra ℤ_[p] R]
variable {σ τ υ : Type} [Finite σ] [Finite τ] [Finite υ]
variable {M : ModuleLaw ℤ_[p] R σ} {N : ModuleLaw ℤ_[p] R τ} {P : ModuleLaw ℤ_[p] R υ}

namespace Hom

/-- The scalar action on the formal law induces the given p-adic action on its actual tower. -/
theorem pDivisibleMap_scalarHom (hM : M.IsPiDivisible (p : ℤ_[p])) (a : ℤ_[p]) :
    (M.scalarHom a).pDivisibleMap hM hM = (hM.pDivisibleGroup.padicAction a).asHom := by
  let s : ℤ_[p] →+* Hom M M := {
    toFun := M.scalarHom
    map_zero' := zero_smul _ _
    map_one' := one_smul _ _
    map_add' a b := add_smul a b _
    map_mul' a b := by
      change (a * b) • Hom.id M = (a • Hom.id M).comp (b • Hom.id M)
      rw [Hom.smul_comp, Hom.comp_smul, Hom.id_comp, mul_smul] }
  exact congrArg End.asHom
    (DFunLike.congr_fun (hM.pDivisibleGroup.padicAction_unique ((pDivisibleEnd hM).comp s)) a)

/-- Restriction of formal morphisms to the actual p-power kernels is p-adic linear. -/
def pDivisibleMapLinear (hM : M.IsPiDivisible (p : ℤ_[p])) (hN : N.IsPiDivisible (p : ℤ_[p])) :
    Hom M N →ₗ[ℤ_[p]] (hM.pDivisibleGroup ⟶ hN.pDivisibleGroup) where
  __ := pDivisibleMapAdd hM hN
  map_smul' a f := by
    have hf : a • f = (N.scalarHom a).comp f := by
      rw [scalarHom, Hom.smul_comp, Hom.id_comp]
    change (a • f).pDivisibleMap hM hN = a • f.pDivisibleMap hM hN
    rw [hf, pDivisibleMap_comp, pDivisibleMap_scalarHom]
    exact (PDivisibleGroup.smul_eq_comp_padicAction a (f.pDivisibleMap hM hN)).symm

end Hom

namespace RationalHom

/-- A rational formal homomorphism acts on the actual towers up to isogeny. -/
def pDivisibleMap (hM : M.IsPiDivisible (p : ℤ_[p])) (hN : N.IsPiDivisible (p : ℤ_[p])) :
    RationalHom ℚ_[p] M N →ₗ[ℚ_[p]] PDivisibleGroup.RationalHom hM.pDivisibleGroup hN.pDivisibleGroup :=
  (Hom.pDivisibleMapLinear hM hN).baseChange ℚ_[p]

@[simp] theorem pDivisibleMap_tmul (hM : M.IsPiDivisible (p : ℤ_[p])) (hN : N.IsPiDivisible (p : ℤ_[p]))
    (a : ℚ_[p]) (f : Hom M N) :
    pDivisibleMap hM hN (a ⊗ₜ[ℤ_[p]] f) = a ⊗ₜ[ℤ_[p]] (f.pDivisibleMap hM hN) := rfl

@[simp] theorem pDivisibleMap_ofHom (hM : M.IsPiDivisible (p : ℤ_[p])) (hN : N.IsPiDivisible (p : ℤ_[p]))
    (f : Hom M N) :
    pDivisibleMap hM hN (ofHom f) = PDivisibleGroup.RationalHom.ofHom (f.pDivisibleMap hM hN) := rfl

@[simp] theorem pDivisibleMap_id (hM : M.IsPiDivisible (p : ℤ_[p])) :
    pDivisibleMap hM hM (id M) = PDivisibleGroup.RationalHom.id hM.pDivisibleGroup := by
  rw [id, pDivisibleMap_ofHom, Hom.pDivisibleMap_id, PDivisibleGroup.RationalHom.ofHom_id]

@[simp] theorem pDivisibleMap_comp
    (hM : M.IsPiDivisible (p : ℤ_[p])) (hN : N.IsPiDivisible (p : ℤ_[p]))
    (hP : P.IsPiDivisible (p : ℤ_[p])) (g : RationalHom ℚ_[p] N P) (f : RationalHom ℚ_[p] M N) :
    pDivisibleMap hM hP (comp g f) =
      PDivisibleGroup.RationalHom.comp (pDivisibleMap hM hN f) (pDivisibleMap hN hP g) := by
  induction g using TensorProduct.inductionOn with
  | add g g' hg hg' => simp only [add_comp, PDivisibleGroup.RationalHom.comp_add, map_add, hg, hg']
  | tmul a g =>
    induction f using TensorProduct.inductionOn with
    | add f f' hf hf' => simp only [comp_add, PDivisibleGroup.RationalHom.add_comp, map_add, hf, hf']
    | tmul b f => simp only [comp_tmul, pDivisibleMap_tmul, PDivisibleGroup.RationalHom.comp_tmul,
        Hom.pDivisibleMap_comp g f hM hN hP, mul_comm a b]

end RationalHom

/-- A formal quasi-isogeny induces an actual tower quasi-isogeny. -/
def QuasiIsogeny.pDivisibleMap (e : QuasiIsogeny ℚ_[p] M N)
    (hM : M.IsPiDivisible (p : ℤ_[p])) (hN : N.IsPiDivisible (p : ℤ_[p])) :
    PDivisibleGroup.QuasiIsogeny hM.pDivisibleGroup hN.pDivisibleGroup where
  hom := RationalHom.pDivisibleMap hM hN e.hom
  inv := RationalHom.pDivisibleMap hN hM e.inv
  hom_inv_id := by
    change PDivisibleGroup.RationalHom.comp (RationalHom.pDivisibleMap hM hN e.hom)
      (RationalHom.pDivisibleMap hN hM e.inv) = PDivisibleGroup.RationalHom.id hM.pDivisibleGroup
    rw [← RationalHom.pDivisibleMap_comp, e.inv_hom, RationalHom.pDivisibleMap_id]
  inv_hom_id := by
    change PDivisibleGroup.RationalHom.comp (RationalHom.pDivisibleMap hN hM e.inv)
      (RationalHom.pDivisibleMap hM hN e.hom) = PDivisibleGroup.RationalHom.id hN.pDivisibleGroup
    rw [← RationalHom.pDivisibleMap_comp, e.hom_inv, RationalHom.pDivisibleMap_id]

end Langlands.FormalGroup.ModuleLaw
