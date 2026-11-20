import Mathlib.GroupTheory.DoubleCoset
import Langlands.Automorphic.CuspidalL2.Representation
import Langlands.Automorphic.CuspidalL2.SiegelCover

/-! # Finite double cosets and archimedean restrictions at open finite level -/

noncomputable section
universe u
set_option autoImplicit false

namespace Langlands.Automorphic

open Langlands.Global

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

/-- The rational diagonal restricted to the finite adelic factor. -/
def finiteRationalGL : RationalGL F n →* FiniteAdelicGL F n :=
  (AdelicGL.finite F n).toMonoidHom.comp (AdelicGL.rational F n)

/-- The double cosets `GL_n(F) \ GL_n(𝔸_f) / L`. -/
abbrev FiniteLevelDoubleCosets (L : OpenSubgroup (FiniteAdelicGL F n)) :=
  DoubleCoset.Quotient ((finiteRationalGL F n).range : Set (FiniteAdelicGL F n)) L.toSubgroup

/-- The rational elements whose finite components preserve `bL` by left multiplication. -/
def finiteLevelSliceStabilizer (L : OpenSubgroup (FiniteAdelicGL F n))
    (b : FiniteAdelicGL F n) : Subgroup (RationalGL F n) :=
  L.toSubgroup.comap ((MulAut.conj b⁻¹).toMonoidHom.comp (finiteRationalGL F n))

theorem mem_finiteLevelSliceStabilizer_iff (L : OpenSubgroup (FiniteAdelicGL F n))
    (b : FiniteAdelicGL F n) (γ : RationalGL F n) :
    γ ∈ finiteLevelSliceStabilizer F n L b ↔
      b⁻¹ * finiteRationalGL F n γ * b ∈ L := by
  simp only [finiteLevelSliceStabilizer, Subgroup.mem_comap, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  rfl

/-- The representatives of the finite level classes cover the adelic double quotient. -/
theorem finite_finiteLevelDoubleCosets (L : OpenSubgroup (FiniteAdelicGL F n)) :
    Finite (FiniteLevelDoubleCosets F n L) := by
  obtain ⟨Q, _, hQ, _, hred⟩ := exists_siegelDecomposition F n
  obtain ⟨t, ht⟩ := OperatorRealization.exists_finite_level_cover L.toSubgroup L.isOpen Q hQ
  let H := (finiteRationalGL F n).range
  refine Finite.of_surjective (fun b : t => DoubleCoset.mk H L.toSubgroup (b : FiniteAdelicGL F n)) ?_
  intro c
  let b : FiniteAdelicGL F n := c.out
  obtain ⟨γ, x, q, hq, hγ, _⟩ := hred (AdelicGL.ofFinite F n b)
  obtain ⟨y, hy, hyq⟩ := ht q hq
  refine ⟨⟨y, hy⟩, ?_⟩
  have hfin : finiteRationalGL F n γ * b = AdelicGL.finite F n q := by
    change AdelicGL.finite F n (AdelicGL.rational F n γ) * b = AdelicGL.finite F n q
    simpa only [map_mul, AdelicGL.finite_ofInfinite, AdelicGL.finite_ofFinite, one_mul] using
      congrArg (AdelicGL.finite F n) hγ
  change DoubleCoset.mk H L.toSubgroup y = c
  refine (DoubleCoset.eq.mpr ⟨finiteRationalGL F n γ⁻¹, ⟨γ⁻¹, rfl⟩,
    y⁻¹ * AdelicGL.finite F n q, hyq, ?_⟩ :
      DoubleCoset.mk H L.toSubgroup y = DoubleCoset.mk H L.toSubgroup b).trans
    (DoubleCoset.out_eq' c)
  rw [mul_assoc, mul_inv_cancel_left, ← hfin, map_inv, inv_mul_cancel_left]

/-- Every finite component belongs to the double coset of its selected representative. -/
theorem exists_eq_finiteRationalGL_mul_out_mul (L : OpenSubgroup (FiniteAdelicGL F n))
    (b : FiniteAdelicGL F n) :
    ∃ (γ : RationalGL F n) (l : L), b = finiteRationalGL F n γ *
      (DoubleCoset.mk (finiteRationalGL F n).range L.toSubgroup b).out * (l : FiniteAdelicGL F n) := by
  obtain ⟨_, ⟨γ, rfl⟩, l, hl, h⟩ :=
    DoubleCoset.eq.mp (DoubleCoset.out_eq' (DoubleCoset.mk (finiteRationalGL F n).range L.toSubgroup b))
  exact ⟨γ, ⟨l, hl⟩, h⟩

/-- Restriction to one infinite slice per double coset is faithful on the existing
rational-covariant smooth families at level `L`. -/
theorem finiteLevelSmoothSliceFamilies_restrict_injective
    (L : OpenSubgroup (FiniteAdelicGL F n)) :
    Function.Injective (fun f : FiniteLevelSmoothSliceFamilies F n L =>
      fun c : FiniteLevelDoubleCosets F n L => f.val c.out) := by
  intro f g h
  apply Subtype.ext
  funext b
  apply Subtype.ext
  funext a
  let c := DoubleCoset.mk (finiteRationalGL F n).range L.toSubgroup b
  obtain ⟨γ, l, hb⟩ := exists_eq_finiteRationalGL_mul_out_mul F n L b
  let d := AdelicGL.infinite F n (AdelicGL.rational F n γ)
  have hfg : f.val c.out = g.val c.out := congrFun h c
  have hf := f.property.2 γ c.out (d⁻¹ * a)
  have hg := g.property.2 γ c.out (d⁻¹ * a)
  change (f.val (finiteRationalGL F n γ * c.out)).val (d * (d⁻¹ * a)) = _ at hf
  change (g.val (finiteRationalGL F n γ * c.out)).val (d * (d⁻¹ * a)) = _ at hg
  rw [mul_inv_cancel_left] at hf hg
  change (f.val b).val a = (g.val b).val a
  change b = finiteRationalGL F n γ * c.out * (l : FiniteAdelicGL F n) at hb
  rw [hb, f.property.1, g.property.1, hf, hg]
  exact congrArg (fun s : ArchimedeanGL.SmoothFunctions F n => s.val (d⁻¹ * a)) hfg

end Langlands.Automorphic
