/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.RootsOfUnityTop
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorExtensionMap

/-!
# The pairing between `ℤ/m`-torsors and `m`-torsion line bundles on a curve

Let `X` be a smooth proper connected curve over an algebraically closed field `k` and `m` an
integer prime to the characteristic. A `ℤ/m`-torsor `t` over `X` defines the extension
`0 ⟶ μ_m ⟶ K₂ ⟶ μ_m ⟶ 0` of `WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorExtension`,
whose connecting homomorphism `H¹(X, μ_m) ⟶ H²(X, μ_m)` is the cup product with the class of
`t` (`AlgebraicGeometry.Scheme.EtaleTorsor.cupMu`). Composing with the Kummer identification
`Pic(X)[m] ≅ H¹(X, μ_m)` and the trace `H²(X, μ_m) ≅ ℤ/m` gives a character

`AlgebraicGeometry.Scheme.EtaleTorsor.picPairing t : Pic(X)[m] ⟶ ℤ/m`.

## Main definitions

- `AlgebraicGeometry.Scheme.EtaleTorsor.picPairing`: the character attached to a torsor.

## Main statements

- `AlgebraicGeometry.Scheme.EtaleTorsor.picPairing_eq_of_isIsomorphic`: isomorphic torsors
  have the same character.
- `AlgebraicGeometry.Scheme.EtaleTorsor.picPairing_zsmul`: compatibility with reduction of
  torsors and the `ℓ`-th power map on line bundles.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-! ### Compatibility of the Kummer maps with the inclusions `μ_m ⊆ μ_{m'}` -/

section Inclusion

open EtaleTorsor

lemma rootsOfUnityInclusion_self (m : ℕ) :
    rootsOfUnityInclusion (X := X) m m dvd_rfl = 𝟙 _ := by
  rw [← cancel_mono (kernel.ι (m • 𝟙 X.gmSheaf)), rootsOfUnityInclusion_ι, Category.id_comp]

variable [IsProper (X ↘ Spec (.of k))]

/-- The Kummer identification `H¹(X, μ_m) ≅ Pic(X)[m]` is compatible with the inclusion
`μ_m ⊆ μ_{m'}`. -/
lemma coe_kummerTorsionEquiv_map_rootsOfUnityInclusion (m m' : ℕ) (hm : (m : k) ≠ 0)
    (hm' : (m' : k) ≠ 0) (hmm' : m ∣ m') (x : Sheaf.H (X.rootsOfUnitySheaf m) 1) :
    (kummerTorsionEquiv m' hm' (Sheaf.H.map (rootsOfUnityInclusion m m' hmm') 1 x) :
      Additive X.Pic) = kummerTorsionEquiv m hm x := by
  have e := congrArg (fun f ↦ Sheaf.H.map f 1 x) (rootsOfUnityInclusion_ι (X := X) m m' hmm')
  simp only [Sheaf.H.map_comp_apply] at e
  rw [coe_kummerTorsionEquiv_apply, coe_kummerTorsionEquiv_apply]
  exact congrArg _ e

variable [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]

/-- The morphism of Kummer sequences `(μ_m ⊆ μ_{dm}, 𝟙, d)`. -/
noncomputable def kummerSequenceMap (m d : ℕ) :
    X.kummerSequence m ⟶ X.kummerSequence (m * d) where
  τ₁ := rootsOfUnityInclusion m (m * d) (dvd_mul_right m d)
  τ₂ := 𝟙 _
  τ₃ := d • 𝟙 _
  comm₁₂ := by
    simp [kummerSequence]
  comm₂₃ := by
    simp only [kummerSequence, Preadditive.comp_nsmul, Category.comp_id]
    rw [mul_comm, mul_smul]

omit [IsProper (X ↘ Spec (.of k))] [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
  [IsAlgClosed k] in
/-- The Kummer map to `H²` is compatible with the inclusion `μ_m ⊆ μ_{dm}`: the class of `L`
is sent to the class of `L^d`. -/
lemma map_rootsOfUnityInclusion_picToSheafHTwo (m d : ℕ) (hm : (m : k) ≠ 0)
    (hmd : ((m * d : ℕ) : k) ≠ 0) (L : Additive X.Pic) :
    Sheaf.H.map (rootsOfUnityInclusion m (m * d) (dvd_mul_right m d)) 2
        (picToSheafHTwo m hm L) = picToSheafHTwo (m * d) hmd (d • L) := by
  have h := Sheaf.H.map_δSucc (X.kummerSequence_shortExact m (isUnit_natCast_appTop m hm))
    (X.kummerSequence_shortExact (m * d) (isUnit_natCast_appTop (m * d) hmd))
    (kummerSequenceMap m d) 1 (Pic.toCohomologicalPicardGroupAddEquiv X L)
  refine h.trans ?_
  rw [picToSheafHTwo, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, map_nsmul]
  congr 1
  simp only [kummerSequenceMap, Sheaf.H.map_nsmul_apply]
  erw [Sheaf.H.map_id_apply]

/-- The trace is compatible with the inclusion `μ_m ⊆ μ_{dm}`: on Kummer classes, the trace
of the image of the class of `L` is `d · deg L`. -/
lemma sheafHTwoTrace_map_rootsOfUnityInclusion (m d : ℕ) (hm : (m : k) ≠ 0)
    (hmd : ((m * d : ℕ) : k) ≠ 0) (L : Additive X.Pic) :
    sheafHTwoTrace (m * d) hmd (Sheaf.H.map (rootsOfUnityInclusion m (m * d)
        (dvd_mul_right m d)) 2 (picToSheafHTwo m hm L)) =
      ((d : ℤ) * (picDegreeHom k X L.toMul).toAdd : ℤ) := by
  rw [map_rootsOfUnityInclusion_picToSheafHTwo m d hm hmd, sheafHTwoTrace_picToSheafHTwo]
  change (((picDegreeHom k X (d • L).toMul).toAdd : ℤ) : ZMod (m * d)) = _
  rw [toMul_nsmul, map_pow, toAdd_pow, nsmul_eq_mul]

end Inclusion

/-! ### The pairing -/

namespace EtaleTorsor

variable [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))]

/-- The character `Pic(X)[m] ⟶ ℤ/m` attached to a `ℤ/m`-torsor `t` on a smooth proper curve
over an algebraically closed field: a line bundle `L` with `L^m ≅ 𝒪` is sent to the trace of
the cup product of the class of `t` with the Kummer class of `L`. -/
noncomputable def picPairing {m : ℕ} [NeZero m] (hm : (m : k) ≠ 0)
    (t : EtaleTorsor (ULift.{u + 1} (ZMod m)) X) :
    AddSubgroup.torsionBy (Additive X.Pic) (m : ℤ) →+ ZMod m :=
  (sheafHTwoTrace m hm).comp (t.cupMu.comp (kummerTorsionEquiv m hm).symm.toAddMonoidHom)

lemma picPairing_apply {m : ℕ} [NeZero m] (hm : (m : k) ≠ 0)
    (t : EtaleTorsor (ULift.{u + 1} (ZMod m)) X)
    (y : AddSubgroup.torsionBy (Additive X.Pic) (m : ℤ)) :
    t.picPairing hm y = sheafHTwoTrace m hm (t.cupMu ((kummerTorsionEquiv m hm).symm y)) :=
  rfl

/-- The cup products of two `ℤ/m`-torsors related by a morphism of total spaces multiplying the
action by `c` differ by `c`. -/
lemma cupMu_eq_cupMu_nsmul {m : ℕ} [NeZero m] (t t' : EtaleTorsor (ULift.{u + 1} (ZMod m)) X)
    (h : t'.P ⟶ t.P) (hπ : h ≫ t.π = t'.π) (c : ℕ) (hc : t'.vadd 1 ≫ h = h ≫ t.vadd (c • 1))
    (x : Sheaf.H (X.rootsOfUnitySheaf m) 1) : t.cupMu x = t'.cupMu (c • x) := by
  have := t.map_cupMu t' h c hπ hc dvd_rfl x
  rwa [rootsOfUnityInclusion_self, Sheaf.H.map_id_apply, Sheaf.H.map_id_apply] at this

/-- Isomorphic torsors have the same character. -/
lemma picPairing_eq_of_isIsomorphic {m : ℕ} [NeZero m] (hm : (m : k) ≠ 0)
    {t₁ t₂ : EtaleTorsor (ULift.{u + 1} (ZMod m)) X} (h : t₁.IsIsomorphic t₂) :
    t₁.picPairing hm = t₂.picPairing hm := by
  obtain ⟨φ, hφ, hv⟩ := h
  ext y
  rw [picPairing_apply, picPairing_apply, t₁.cupMu_eq_cupMu_nsmul t₂ φ.inv
    (by rw [← hφ, Iso.inv_hom_id_assoc]) 1 (by rw [one_nsmul, Iso.comp_inv_eq, Category.assoc,
      hv, Iso.inv_hom_id_assoc]), one_nsmul]

omit [IsAlgClosed k] [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
  [IsProper (X ↘ Spec (.of k))] in
/-- Cancellation of a nonzero factor `d` in `ℤ/md`, followed by reduction modulo `m`. -/
lemma _root_.ZMod.castHom_eq_of_natCast_mul_eq {m d : ℕ} (hd : d ≠ 0) (a b : ZMod (m * d))
    (h : (d : ZMod (m * d)) * a = d * b) :
    ZMod.castHom (dvd_mul_right m d) (ZMod m) a = ZMod.castHom (dvd_mul_right m d) (ZMod m) b := by
  obtain ⟨A, rfl⟩ := ZMod.intCast_surjective a
  obtain ⟨B, rfl⟩ := ZMod.intCast_surjective b
  rw [map_intCast, map_intCast, ZMod.intCast_eq_intCast_iff_dvd_sub]
  have h' : ((d * B - d * A : ℤ) : ZMod (m * d)) = 0 := by
    push_cast
    rw [h, sub_self]
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, Nat.cast_mul, ← mul_sub] at h'
  rw [mul_comm] at h'
  exact (Int.dvd_of_mul_dvd_mul_left (by exact_mod_cast hd) h')

/-- **Compatibility with reduction.** Let `t` be a `ℤ/m`-torsor and `t'` a `ℤ/m'`-torsor,
`m' = m d`, with a morphism `h : P' ⟶ P` of total spaces compatible with the generators of the
actions (e.g. `t` is the reduction of `t'`). Then the character of `t` on `d • y` is the
reduction of the character of `t'` on `y`. -/
lemma picPairing_nsmul {m d m' : ℕ} [NeZero m] [NeZero m'] (hmd : m' = m * d)
    (hm : (m : k) ≠ 0) (hm' : (m' : k) ≠ 0) (t : EtaleTorsor (ULift.{u + 1} (ZMod m)) X)
    (t' : EtaleTorsor (ULift.{u + 1} (ZMod m')) X) (h : t'.P ⟶ t.P) (hπ : h ≫ t.π = t'.π)
    (hc : t'.vadd 1 ≫ h = h ≫ t.vadd (1 • 1))
    (y : AddSubgroup.torsionBy (Additive X.Pic) (m' : ℤ)) (hy : (d : ℤ) • (y : Additive X.Pic) ∈
      AddSubgroup.torsionBy (Additive X.Pic) (m : ℤ)) :
    t.picPairing hm ⟨_, hy⟩ = ZMod.castHom (hmd ▸ dvd_mul_right m d) (ZMod m)
      (t'.picPairing hm' y) := by
  subst hmd
  have hd : d ≠ 0 := right_ne_zero_of_mul (NeZero.ne (m * d))
  obtain ⟨x, hxd⟩ : ∃ x, x = (kummerTorsionEquiv m hm).symm ⟨_, hy⟩ := ⟨_, rfl⟩
  have hx : Sheaf.H.map (rootsOfUnityInclusion m (m * d) (dvd_mul_right m d)) 1 x =
      d • (kummerTorsionEquiv (m * d) hm').symm y := by
    apply (kummerTorsionEquiv (m * d) hm').injective
    apply Subtype.ext
    rw [map_nsmul, AddEquiv.apply_symm_apply, coe_kummerTorsionEquiv_map_rootsOfUnityInclusion m
      (m * d) hm hm', AddSubgroup.coe_nsmul, hxd, AddEquiv.apply_symm_apply]
    exact natCast_zsmul _ _
  have key := t.map_cupMu t' h 1 hπ hc (dvd_mul_right m d) x
  rw [one_nsmul, hx, map_nsmul] at key
  obtain ⟨L, hL⟩ := surjective_picToSheafHTwo m hm (t.cupMu x)
  have h1 := sheafHTwoTrace_map_rootsOfUnityInclusion m d hm hm' L
  rw [hL, key, map_nsmul, nsmul_eq_mul] at h1
  push_cast at h1
  rw [picPairing_apply, ← hxd, ← hL, sheafHTwoTrace_picToSheafHTwo]
  change (((picDegreeHom k X L.toMul).toAdd : ℤ) : ZMod m) = _
  rw [← map_intCast (ZMod.castHom (dvd_mul_right m d) (ZMod m))]
  exact ZMod.castHom_eq_of_natCast_mul_eq hd _ _ h1.symm

end EtaleTorsor

end AlgebraicGeometry.Scheme
