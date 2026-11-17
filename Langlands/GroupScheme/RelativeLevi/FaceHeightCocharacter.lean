import Langlands.GroupScheme.RelativeLevi.SplitParabolicWeightChart

/-! # Coordinate cocharacters realizing multiples of face heights -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.LocalSplitCell

variable {I : Type u} [Fintype I] {J : Type u}

/-- Every integral linear form on the root span is the restriction of the
coordinate pairing with a cocharacter after multiplication by a positive integer. -/
theorem exists_coPairing_eq_rootSpanLinear
    (P : RootDatum J (I → ℤ) (I → ℤ)) (b : P.Base)
    (h : P.rootSpan ℤ →ₗ[ℤ] ℤ) :
    ∃ d : ℤ, 0 < d ∧ ∃ cv : I → ℤ,
      ∀ x : P.rootSpan ℤ, coPairing (x : I → ℤ) cv = d * h x := by
  classical
  let castL : (I → ℤ) →ₗ[ℤ] (I → ℚ) := (Int.castAddHom ℚ).toIntLinearMap.compLeft I
  have hcast : Function.Injective castL := fun x y he => funext fun j => by
    have he' := congrFun he j
    simpa [castL] using he'
  have hZ : LinearIndependent ℤ (fun a : b.support => P.root a) := b.linearIndepOn_root
  have hZQ : LinearIndependent ℤ (fun a : b.support => castL (P.root a)) :=
    hZ.map' castL (LinearMap.ker_eq_bot.mpr hcast)
  have hQ : LinearIndependent ℚ (fun a : b.support => castL (P.root a)) :=
    (LinearIndependent.iff_fractionRing ℤ ℚ).mp hZQ
  let Wsp : Submodule ℚ (I → ℚ) :=
    Submodule.span ℚ (Set.range fun a : b.support => castL (P.root a))
  let f : (I → ℚ) →ₗ[ℚ] ℚ :=
    Subspace.dualLift Wsp ((Module.Basis.span hQ).constr ℚ
      (fun a => (h (P.rootSpanMem ℤ a) : ℚ)))
  have hf (a : b.support) : f (castL (P.root a)) = (h (P.rootSpanMem ℤ a) : ℚ) := by
    dsimp only [f]
    rw [← Module.Basis.coe_span_apply hQ a, Subspace.dualLift_of_subtype,
      Module.Basis.constr_basis]
  let q : I → ℚ := fun j => f (Pi.single j 1)
  obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) q
  choose a ha using hc
  have hc0 : (c : ℤ) ≠ 0 := nonZeroDivisors.ne_zero c.property
  have ha' (j : I) : (a j : ℚ) = (c : ℤ) * q j := by
    simpa [Algebra.smul_def, algebraMap_int_eq] using ha j
  have hpair (x : I → ℤ) :
      (coPairing x (fun j => (c : ℤ) * a j) : ℚ) = ((c : ℤ) ^ 2 : ℤ) * f (castL x) := by
    have hfx : f (castL x) = ∑ j, (x j : ℚ) * q j := by
      have hx : castL x = ∑ j, (x j : ℚ) • Pi.single j (1 : ℚ) := by
        funext j
        simp [castL, Finset.sum_apply, Pi.single_apply]
      rw [hx, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, smul_eq_mul]
    rw [hfx, coPairing, Int.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    rw [ha']
    ring
  have hroot (j : J) :
      coPairing (P.root j) (fun k => (c : ℤ) * a k) =
        (c : ℤ) ^ 2 * h (P.rootSpanMem ℤ j) := by
    obtain ⟨g, -, -, hg⟩ := b.exists_root_eq_sum_int j
    have hx : P.rootSpanMem ℤ j = ∑ k ∈ b.support, g k • P.rootSpanMem ℤ k := by
      apply Subtype.ext
      simpa using hg
    have hsum : f (castL (P.root j)) =
        ∑ k ∈ b.support, (g k : ℚ) * (h (P.rootSpanMem ℤ k) : ℚ) := by
      rw [hg, map_sum, map_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [map_zsmul, map_zsmul, hf ⟨k, hk⟩, zsmul_eq_mul]
    have he := hpair (P.root j)
    rw [hsum] at he
    rw [hx, map_sum]
    simp only [map_zsmul, zsmul_eq_mul]
    exact_mod_cast he
  refine ⟨(c : ℤ) ^ 2, sq_pos_of_ne_zero hc0, fun j => (c : ℤ) * a j, ?_⟩
  intro x
  have he : (coPairingLinear (fun j => (c : ℤ) * a j)).comp
      (P.rootSpan ℤ).subtype = ((c : ℤ) ^ 2) • h := by
    apply b.toWeightBasisInt.ext
    intro j
    have hj : b.toWeightBasisInt j = P.rootSpanMem ℤ j := by
      ext
      simp
    simp only [LinearMap.comp_apply, hj, Submodule.subtype_apply,
      LinearMap.smul_apply, smul_eq_mul]
    exact hroot j
  exact LinearMap.congr_fun he x

/-- A positive-multiple realization of a root-span linear form by an actual
coordinate cocharacter, recording its exact equality on the entire root span. -/
structure RootSpanCocharacterRealization
    (P : RootDatum J (I → ℤ) (I → ℤ)) (h : P.rootSpan ℤ →ₗ[ℤ] ℤ) where
  multiplier : ℤ
  multiplier_pos : 0 < multiplier
  cocharacter : I → ℤ
  pairing_eq : ∀ x : P.rootSpan ℤ,
    coPairing (x : I → ℤ) cocharacter = multiplier * h x

/-- Choose the proved positive-multiple cocharacter realization of an integral
root-span linear form. Neither the multiplier nor the extension is canonical. -/
def rootSpanCocharacterRealization
    (P : RootDatum J (I → ℤ) (I → ℤ)) (b : P.Base)
    (h : P.rootSpan ℤ →ₗ[ℤ] ℤ) : RootSpanCocharacterRealization P h :=
  Classical.choice <| by
    obtain ⟨d, hd, cv, hcv⟩ := exists_coPairing_eq_rootSpanLinear P b h
    exact ⟨⟨d, hd, cv, hcv⟩⟩

/-- Choose a positive-multiple realization of the canonical integral face
height, preserving its exact unscaled values as part of the realization data. -/
def faceHeightCocharacterRealization
    (P : RootDatum J (I → ℤ) (I → ℤ)) (b : P.Base) (cv : I → ℤ) :
    RootSpanCocharacterRealization P
      (Langlands.LinearAlgebra.RootDatumFaceHeight.faceHeight b cv) :=
  rootSpanCocharacterRealization P b
    (Langlands.LinearAlgebra.RootDatumFaceHeight.faceHeight b cv)

/-- The canonical integral face height is realized on every root by a positive
multiple of one actual coordinate cocharacter. -/
theorem exists_coPairing_eq_faceHeight
    (P : RootDatum J (I → ℤ) (I → ℤ)) (b : P.Base) (cv : I → ℤ) :
    ∃ d : ℤ, 0 < d ∧ ∃ wt : I → ℤ, ∀ j,
      coPairing (P.root j) wt =
        d * Langlands.LinearAlgebra.RootDatumFaceHeight.faceHeight b cv (P.rootSpanMem ℤ j) := by
  obtain ⟨d, hd, wt, hwt⟩ := exists_coPairing_eq_rootSpanLinear P b
    (Langlands.LinearAlgebra.RootDatumFaceHeight.faceHeight b cv)
  exact ⟨d, hd, wt, fun j => hwt (P.rootSpanMem ℤ j)⟩

end Langlands.GroupScheme.LocalSplitCell
