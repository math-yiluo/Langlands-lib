/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Picard.Group
import WeilConjectures.AlgebraicGeometry.Curve.PicardDecomposition
import WeilConjectures.AlgebraicGeometry.Curve.PicProperNTorsionDiv
import Mathlib.Algebra.Group.TypeTags.Hom
@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry
/-- The prime-to-characteristic Picard cokernel for a proper smooth curve.
Source: blueprint `corollary-torsion-jacobian-field-extension`, final cokernel calculation.
(blueprint: lem-sc-pic-proper-ntorsion-coker)

Proof: the Picard decomposition gives a subgroup P0 with underlying set `f.picZero`
and an equivalence `Pic(C) ≃ ℤ × P0`. Degree-zero divisibility makes the nth-power
map on P0 surjective. Compose the first coordinate with the integer cast into ZMod n.
This homomorphism is surjective since integer cast is surjective. Its kernel is the
nth-power image: an nth power maps to zero modulo n; conversely, if the integer
coordinate is n times z, choose an nth root of the P0 coordinate, and apply the inverse
decomposition to the pair (z, root). The resulting class has nth power equal to the
original class. The first isomorphism theorem now gives the required cokernel. -/
theorem Scheme.Hom.pic_proper_ntorsion_coker
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] [IsProper f]
    (n : ℕ) (_hn : (n : k) ≠ 0) :
    Nonempty (C.Pic ⧸ (powMonoidHom n : C.Pic →* C.Pic).range ≃*
      Multiplicative (ZMod n)) := by
  classical
  obtain ⟨P0, hP0, e, hfirst, hsecond⟩ := f.exists_mulEquiv_prod_picZero
  clear hfirst hsecond
  have hdiv : Function.Surjective (fun x : P0 ↦ x ^ n) := by
    intro L
    obtain ⟨M, hM, hpow⟩ := f.pic_proper_ntorsion_div n _hn L (by
      rw [← hP0]
      exact L.property)
    refine ⟨⟨M, by change M ∈ (P0 : Set C.Pic); rw [hP0]; exact hM⟩, ?_⟩
    exact Subtype.ext hpow
  let φ : C.Pic →* Multiplicative (ZMod n) :=
    (Int.castAddHom (ZMod n)).toMultiplicative.comp
      ((MonoidHom.fst (Multiplicative ℤ) P0).comp e.toMonoidHom)
  have hφ : Function.Surjective φ := by
    intro a
    obtain ⟨z, hz⟩ := ZMod.intCast_surjective (Multiplicative.toAdd a)
    refine ⟨e.symm (Multiplicative.ofAdd z, 1), ?_⟩
    change Multiplicative.ofAdd (((e (e.symm (Multiplicative.ofAdd z, 1))).1.toAdd : ℤ) :
      ZMod n) = a
    simpa using congrArg Multiplicative.ofAdd hz
  have hker : (powMonoidHom n : C.Pic →* C.Pic).range = φ.ker := by
    ext L
    constructor
    · rintro ⟨M, rfl⟩
      change φ (M ^ n) = 1
      rw [map_pow]
      change Multiplicative.ofAdd (n • Multiplicative.toAdd (φ M)) = 1
      simp
    · intro hL
      have hz : (((e L).1.toAdd : ℤ) : ZMod n) = 0 := by
        exact congrArg Multiplicative.toAdd hL
      obtain ⟨z, hz⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz
      obtain ⟨M, hM⟩ := hdiv (e L).2
      refine ⟨e.symm (Multiplicative.ofAdd z, M), ?_⟩
      change (e.symm (Multiplicative.ofAdd z, M)) ^ n = L
      apply e.injective
      rw [map_pow, e.apply_symm_apply]
      apply Prod.ext
      · change Multiplicative.ofAdd (n • z) = (e L).1
        apply Multiplicative.toAdd.injective
        simpa [nsmul_eq_mul, mul_comm] using hz.symm
      · exact hM
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hφ)⟩
end AlgebraicGeometry
