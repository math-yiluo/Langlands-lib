import Langlands.Representation.Derivative.MirabolicProductMinusCompatibilityStatement
import Langlands.Group.GL.MirabolicProjection

/-!
# The source-rank-one boundaries of BZ77 Proposition 4.13(b,c)
-/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.Derivative.MirabolicProductMinus

open GeneralLinear GeneralLinear.Mirabolic GeneralLinear.Mirabolic.MixedProduct
  HarmonicAnalysis

universe uF uV

section Groups

variable {R : Type uF} [CommRing R]

/-- For `r = 0` the case (II) subgroup is the whole mirabolic group. -/
theorem mem_leftSubgroup_zero_right {k : ℕ} (g : mirabolic (k + 0) R) :
    g ∈ leftSubgroup k 0 R := by
  rw [mem_leftSubgroup_iff_entry]
  intro i j
  obtain rfl : i = Fin.last 0 := Fin.ext (by omega)
  rw [leftIndex_last, g.property, ite_eq_right_iff]
  intro h
  exfalso
  have := congrArg Fin.val h
  simp at this
  omega

/-- For `r = 0`, radical elements lie in the case (II) kernel. -/
theorem mem_leftKernel_zero_right_of_mem_radical {k : ℕ} {g : mirabolic (k + 0) R}
    (hg : g ∈ radical (k + 0) R) :
    (⟨g, mem_leftSubgroup_zero_right g⟩ : leftSubgroup k 0 R) ∈ leftKernel k 0 R := by
  change leftProjection _ = 1
  refine Prod.ext ?_ (rankOne_eq_one _)
  apply Units.ext
  ext i j
  rw [leftProjection_gl_apply]
  have hj : leftIndex k 0 (Sum.inl j) = (⟨j.val, by omega⟩ : Fin (k + 0)).castSucc :=
    Fin.ext (by simp)
  rw [hj, hg]
  show _ = (1 : Matrix (Fin k) (Fin k) R) i j
  rw [Matrix.one_apply]
  congr 1
  apply propext
  rw [← hj, Equiv.apply_eq_iff_eq, Sum.inl.injEq]

end Groups

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- For `r = 0`, the radical of `P_(k+1)` acts trivially on `A × B`. -/
theorem leftMixedProduct_zero_right_radical (T : F.TopologicalData) {k : ℕ}
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (mirabolic 0 F.Carrier))
    (f : letI := T.topology; (T.leftMixedProductFunctor k 0).obj X)
    {u : mirabolic (k + 0) F.Carrier} (hu : u ∈ radical (k + 0) F.Carrier) :
    letI := T.topology
    ((T.leftMixedProductFunctor k 0).obj X).representation u f = f := by
  let _ := T.topology
  apply T.leftMixedEval_injective X
  funext x
  rw [T.leftMixedProductFunctor_action]
  have hc : x * u * x⁻¹ ∈ radical (k + 0) F.Carrier :=
    (radical_normal (n := k + 0) (F := F.Carrier)).conj_mem u hu x
  have e := T.leftMixedEval_of_mem_leftKernel_mul X f
    (mem_leftKernel_zero_right_of_mem_radical hc) x
  rw [← e]
  congr 1
  change x * u = x * u * x⁻¹ * x
  group

/-- BZ77 4.13(b) at source `P_1`: `Φ⁻(ρ × τ) = 0`. -/
theorem leftPhiBoundary (T : F.TopologicalData) : LeftPhiBoundary.{uF, uV} F T := by
  let _ := T.topology
  intro ψ k X
  obtain ⟨t, ht⟩ : ∃ t : F.Carrier, ψ.complex t ≠ 1 := by
    by_contra h
    push Not at h
    apply ψ.nontrivial
    ext t
    have := h t
    rw [UnitaryAdditiveCharacter.complex_apply] at this
    rw [AddChar.one_apply]
    exact this.trans Circle.coe_one.symm
  let u : radical (k + 0 + 1) F.Carrier := radicalElement (Pi.single (Fin.last (k + 0)) t)
  have hθ : (T.mirabolicTheta ψ (k + 0) u : ℂ) ≠ 1 := by
    change (Derivative.Mirabolic.theta ψ (k + 0) u : ℂ) ≠ 1
    rw [Derivative.Mirabolic.theta_radicalElement]
    simpa using ht
  let A := (T.leftMixedProductFunctor.{uF, uV} (k + 1) 0).obj X
  have hA : ∀ v : A, A.representation (u : mirabolic (k + 0 + 1) F.Carrier) v = v :=
    fun v => leftMixedProduct_zero_right_radical T X v u.property
  refine ⟨fun a b => ?_⟩
  suffices h : ∀ w : (leftPhiProduct.{uF, uV} T ψ k 0).obj X, w = 0 by rw [h a, h b]
  intro w
  obtain ⟨v, rfl⟩ := Mirabolic.phiMinusQuotient_surjective T ψ (k + 0) A w
  have h1 := Mirabolic.phiMinusQuotient_radical T ψ (k + 0) A u v
  rw [hA v] at h1
  have h2 : ((T.mirabolicTheta ψ (k + 0) u : ℂ) - 1) •
      Mirabolic.phiMinusQuotient T ψ (k + 0) A v = 0 := by
    rw [sub_smul, ← h1, one_smul, sub_self]
  exact (smul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hθ)

end Langlands.Derivative.MirabolicProductMinus
