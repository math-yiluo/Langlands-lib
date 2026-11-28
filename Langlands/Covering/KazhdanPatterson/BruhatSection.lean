import Langlands.Group.GL.UnipotentDoubleCoset
import Langlands.GroupTheory.ExtensionPushout

/-! # The Bruhat section from unipotent and monomial lifts -/

namespace Langlands.KazhdanPatterson

open Matrix (SpecialLinearGroup)
open Matrix.SpecialLinearGroup

noncomputable section

universe u v

variable {F : Type u} [Field F] {n : ℕ}

/-- The upper-unipotent subgroup of the actual special linear group. -/
def slUpperUnipotent (n : ℕ) (F : Type u) [Field F] :
    Subgroup (SpecialLinearGroup (Fin n) F) :=
  (GeneralLinear.upperUnipotent n F).comap toGL

/-- Monomial matrices in the special linear group, expressed in actual entries. -/
def IsSpecialLinearMonomial (m : SpecialLinearGroup (Fin n) F) : Prop :=
  ∃ (w : Equiv.Perm (Fin n)) (d : Fin n → Fˣ),
    toGL m = GeneralLinear.monomialRepresentative w d

theorem isSpecialLinearMonomial_one : IsSpecialLinearMonomial (1 : SpecialLinearGroup (Fin n) F) := by
  refine ⟨1, 1, ?_⟩
  simp [GeneralLinear.monomialRepresentative]

/-- A factorization through a determinant-one monomial matrix. -/
structure BruhatFactors (g : SpecialLinearGroup (Fin n) F) where
  left : slUpperUnipotent n F
  middle : {m : SpecialLinearGroup (Fin n) F // IsSpecialLinearMonomial m}
  right : slUpperUnipotent n F
  factorization : g = left.val * middle.val * right.val

private theorem det_upperUnipotent (a : GeneralLinear.upperUnipotent n F) :
    GeneralLinear.determinant a.val = 1 := by
  apply Units.ext
  change a.val.val.det = 1
  rw [Matrix.det_of_isUpperTriangular a.property.1]
  simp only [show ∀ i, a.val.val i i = 1 from a.property.2, Finset.prod_const_one]

private theorem exists_bruhatFactors (g : SpecialLinearGroup (Fin n) F) :
    Nonempty (BruhatFactors g) := by
  obtain ⟨w, d, a, b, hg⟩ := GeneralLinear.exists_unipotent_mul_monomial_mul (toGL g)
  let m := GeneralLinear.monomialRepresentative w d
  have hm : GeneralLinear.determinant m = 1 := by
    have h := congrArg GeneralLinear.determinant hg
    simpa only [coeToGL_det, map_mul, det_upperUnipotent, one_mul, mul_one] using h.symm
  let a' := toGLKerEquiv.symm ⟨a.val, det_upperUnipotent a⟩
  let b' := toGLKerEquiv.symm ⟨b.val, det_upperUnipotent b⟩
  let m' := toGLKerEquiv.symm ⟨m, hm⟩
  have ha' : toGL a' = a.val := congrArg Subtype.val
    (toGLKerEquiv.apply_symm_apply ⟨a.val, det_upperUnipotent a⟩)
  have hb' : toGL b' = b.val := congrArg Subtype.val
    (toGLKerEquiv.apply_symm_apply ⟨b.val, det_upperUnipotent b⟩)
  have hm' : toGL m' = m := congrArg Subtype.val
    (toGLKerEquiv.apply_symm_apply ⟨m, hm⟩)
  have haN : a' ∈ slUpperUnipotent n F := by
    change toGL a' ∈ GeneralLinear.upperUnipotent n F
    rw [ha']
    exact a.property
  have hbN : b' ∈ slUpperUnipotent n F := by
    change toGL b' ∈ GeneralLinear.upperUnipotent n F
    rw [hb']
    exact b.property
  refine ⟨⟨⟨a', haN⟩, ⟨m', w, d, hm'⟩, ⟨b', hbN⟩, ?_⟩⟩
  apply toGL_injective
  simpa only [map_mul, ha', hb', hm'] using hg

private theorem monomial_eq_of_mul_unipotent {m m' : SpecialLinearGroup (Fin n) F}
    (hm : IsSpecialLinearMonomial m) (hm' : IsSpecialLinearMonomial m')
    (x y : GeneralLinear.upperUnipotent n F)
    (h : toGL m' = x.val * toGL m * y.val) : m = m' := by
  obtain ⟨w, d, hw⟩ := hm
  obtain ⟨w', d', hw'⟩ := hm'
  let e := GeneralLinear.monomialDoubleCosetEquiv (K := F) (n := n)
  have hc : e (w, d) = e (w', d') := by
    let N := GeneralLinear.upperUnipotent n F
    change DoubleCoset.mk N N (GeneralLinear.monomialRepresentative w d) =
      DoubleCoset.mk N N (GeneralLinear.monomialRepresentative w' d')
    apply DoubleCoset.eq.mpr
    exact ⟨x.val, x.property, y.val, y.property, by simpa only [hw, hw'] using h⟩
  have hwd : (w, d) = (w', d') := e.injective hc
  cases hwd
  exact toGL_injective (hw.trans hw'.symm)

private theorem BruhatFactors.middle_eq {g : SpecialLinearGroup (Fin n) F}
    (a b : BruhatFactors g) : a.middle = b.middle := by
  apply Subtype.ext
  let x := b.left⁻¹ * a.left
  let y := a.right * b.right⁻¹
  refine monomial_eq_of_mul_unipotent a.middle.property b.middle.property
    ⟨toGL x.val, x.property⟩ ⟨toGL y.val, y.property⟩ ?_
  have h := a.factorization.symm.trans b.factorization
  have hm : b.middle.val = x.val * a.middle.val * y.val := by
    change b.middle.val = (b.left.val⁻¹ * a.left.val) * a.middle.val *
      (a.right.val * b.right.val⁻¹)
    calc
      _ = b.left.val⁻¹ * (b.left.val * b.middle.val * b.right.val) * b.right.val⁻¹ := by group
      _ = _ := by
        rw [← h]
        group
  simpa only [map_mul] using congrArg toGL hm

variable {W : Type v} [Group W]

/-- The lifts in the Bruhat formula, with the conjugation identity on the overlap. -/
structure BruhatLiftData (q : W →* SpecialLinearGroup (Fin n) F) where
  unipotent : slUpperUnipotent n F →* W
  monomial : {m : SpecialLinearGroup (Fin n) F // IsSpecialLinearMonomial m} → W
  unipotent_projects : ∀ a, q (unipotent a) = a.val
  monomial_projects : ∀ m, q (monomial m) = m.val
  monomial_one : monomial ⟨1, isSpecialLinearMonomial_one⟩ = 1
  overlap : ∀ a m b, a.val * m.val = m.val * b.val →
    unipotent a * monomial m = monomial m * unipotent b

namespace BruhatLiftData

variable {q : W →* SpecialLinearGroup (Fin n) F} (L : BruhatLiftData q)

private def lift {g : SpecialLinearGroup (Fin n) F} (a : BruhatFactors g) : W :=
  L.unipotent a.left * L.monomial a.middle * L.unipotent a.right

private theorem lift_eq {g : SpecialLinearGroup (Fin n) F}
    (a b : BruhatFactors g) : L.lift a = L.lift b := by
  have hm := a.middle_eq b
  have h : (b.left⁻¹ * a.left).val * a.middle.val =
      a.middle.val * (b.right * a.right⁻¹).val := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have hg := a.factorization.symm.trans b.factorization
    rw [← hm] at hg
    calc
      _ = b.left.val⁻¹ * (a.left.val * a.middle.val * a.right.val) * a.right.val⁻¹ := by group
      _ = _ := by rw [hg]; group
  have hl := L.overlap _ _ _ h
  simp only [map_mul, map_inv] at hl
  unfold lift
  calc
    _ = L.unipotent b.left * ((L.unipotent b.left)⁻¹ * L.unipotent a.left *
        L.monomial a.middle) * L.unipotent a.right := by group
    _ = _ := by
      rw [hl, hm]
      group

/-- The normalized section obtained by multiplying the three lifts in Bruhat order. -/
def sectionMap : GroupExtensionPushout.Section q where
  toFun g := L.lift (Classical.choice (exists_bruhatFactors g))
  right_inv g := by
    let a := Classical.choice (exists_bruhatFactors g)
    change q (L.lift a) = g
    rw [lift, map_mul, map_mul, L.unipotent_projects, L.unipotent_projects, L.monomial_projects]
    exact a.factorization.symm
  normalized := by
    let a : BruhatFactors (1 : SpecialLinearGroup (Fin n) F) :=
      ⟨1, ⟨1, isSpecialLinearMonomial_one⟩, 1, by simp⟩
    change L.lift (Classical.choice (exists_bruhatFactors 1)) = 1
    rw [L.lift_eq _ a]
    simp [lift, a, L.monomial_one]

theorem sectionMap_eq {g : SpecialLinearGroup (Fin n) F} (a : BruhatFactors g) :
    L.sectionMap g = L.unipotent a.left * L.monomial a.middle * L.unipotent a.right :=
  L.lift_eq _ a

end BruhatLiftData
end

end Langlands.KazhdanPatterson
