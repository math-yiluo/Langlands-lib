import Langlands.Global.RankinSelberg.RealPlaceContragredientPremises
import Langlands.Global.RankinSelberg.RealStandardPairingPremises
import Langlands.Representation.Archimedean.RealContragredientProof
import Langlands.Representation.Archimedean.RealStandardModuleAdmissible
import Langlands.Representation.Archimedean.RealStandardNontrivialProof
import Langlands.Representation.Archimedean.RealLargeLanglandsQuotientReduction

/-! # Reducing the local pairing premise to duality and factor invariance

`RealStandardPairingPairLStatement` (module `RealPlaceContragredientPremises`) says: if the
`O(n)`-finite real standard modules `I(ds)` and `I(dds)` are irreducible and carry a nonzero
invariant pairing, then `dds` and `ds.map dualBlock` have pair `L`-factors with the same
denominator against every list of real blocks, in either slot. This module proves that it
follows from the two local statements of `RealStandardPairingPremises`:
`RealStandardDualPairingStatement` (duality) and `RealStandardIntertwinerPairLStatement`
(factor invariance).

The proof (`realStandardPairingPairLReduction`) identifies `I(dds)` and `I(ds.map dualBlock)`
with the `O(n)`-finite dual of `I(ds)`, which is irreducible by the Library's
`RealContragredient.isIrreducible_kDual`. See the paired Markdown.
-/

noncomputable section
open scoped TensorProduct
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.Automorphic Langlands.LocalFactor.Archimedean Langlands.Archimedean
open Langlands.KFiniteDual

/-- **The reduction.** Duality and factor invariance imply the local pairing premise
`RealStandardPairingPairLStatement`. -/
def RealStandardPairingPairLReductionStatement : Prop :=
  RealStandardDualPairingStatement → RealStandardIntertwinerPairLStatement →
    RealStandardPairingPairLStatement

namespace RealStandardPairingReduction

/-! ## A pairing as a map into the finite dual -/

section Pairing

variable {n : ℕ} {ds es : List RealBlock}
  {P : realStandardKFinite n ds →ₗ[ℂ] realStandardKFinite n es →ₗ[ℂ] ℂ}

/-- Invariance under `O(n)`: `P(·, k h)` is the dual translate of `P(·, h)`. -/
theorem flip_rep (hP : IsRealStandardInvariantPairing n ds es P)
    (k : Matrix.unitaryGroup (Fin n) ℝ) (h : realStandardKFinite n es) :
    P.flip (realStandardRep n es k h) = (realStandardRep n ds).dual k (P.flip h) := by
  apply LinearMap.ext
  intro f
  rw [dual_apply_apply, LinearMap.flip_apply, LinearMap.flip_apply]
  have := hP.1 k (realStandardRep n ds k⁻¹ f) h
  rw [Representation.self_inv_apply] at this
  exact this

/-- Invariance under `𝔤`: `P(·, Y h) = -P(Y ·, h)` for every `Y ∈ ℂ ⊗_ℝ 𝔤𝔩_n(ℝ)`. -/
theorem flip_lie (hP : IsRealStandardInvariantPairing n ds es P)
    (Y : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) (f : realStandardKFinite n ds)
    (h : realStandardKFinite n es) :
    P f (realStandardLie n es Y h) = -P (realStandardLie n ds Y f) h := by
  induction Y using TensorProduct.inductionOn with
  | tmul c X =>
    have hc : (c ⊗ₜ[ℝ] X : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) = c • ((1 : ℂ) ⊗ₜ[ℝ] X) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have h1 := hP.2 X f h
    rw [hc, map_smul, map_smul, LinearMap.smul_apply, LinearMap.smul_apply, map_smul,
      map_smul, LinearMap.smul_apply, eq_neg_of_add_eq_zero_right h1, smul_eq_mul, smul_eq_mul,
      mul_neg]
  | add Y Z hY hZ =>
    rw [map_add, LinearMap.add_apply, map_add, hY, hZ, map_add, LinearMap.add_apply,
      map_add, LinearMap.add_apply, neg_add]

/-- `P(·, h)` is an `O(n)`-finite functional on `I(ds)`. -/
theorem isFiniteVector_flip (hP : IsRealStandardInvariantPairing n ds es P)
    (h : realStandardKFinite n es) :
    FiniteVectors.IsFiniteVector (realStandardRep n ds).dual (P.flip h) := by
  have hh : Module.Finite ℂ (FiniteVectors.orbitSpan (realStandardRep n es) h) :=
    (isRealGKModule_realStandardModule n es).1 h
  have hle : FiniteVectors.orbitSpan (realStandardRep n ds).dual (P.flip h) ≤
      (FiniteVectors.orbitSpan (realStandardRep n es) h).map P.flip := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    exact ⟨_, FiniteVectors.action_mem_orbitSpan _ k h, flip_rep hP k h⟩
  exact Submodule.finiteDimensional_of_le hle

/-- The map `h ↦ P(·, h)` from `I(es)` to the `O(n)`-finite dual of `I(ds)`. -/
def toKDual (hP : IsRealStandardInvariantPairing n ds es P) :
    realStandardKFinite n es →ₗ[ℂ] kDual (realStandardRep n ds) :=
  LinearMap.codRestrict _ P.flip fun h => isFiniteVector_flip hP h

@[simp]
theorem toKDual_apply_apply (hP : IsRealStandardInvariantPairing n ds es P)
    (h : realStandardKFinite n es) (f : realStandardKFinite n ds) :
    ((toKDual hP h : kDual (realStandardRep n ds)) : Module.Dual ℂ _) f = P f h :=
  rfl

theorem toKDual_rep (hP : IsRealStandardInvariantPairing n ds es P)
    (k : Matrix.unitaryGroup (Fin n) ℝ) (h : realStandardKFinite n es) :
    toKDual hP (realStandardRep n es k h) = kDualRep (realStandardRep n ds) k (toKDual hP h) :=
  Subtype.ext (flip_rep hP k h)

theorem toKDual_lie (hP : IsRealStandardInvariantPairing n ds es P)
    (Y : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) (h : realStandardKFinite n es) :
    toKDual hP (realStandardLie n es Y h) =
      RealContragredient.dualLie (isRealGKModule_realStandardModule n ds) Y (toKDual hP h) := by
  apply Subtype.ext
  apply LinearMap.ext
  intro f
  rw [RealContragredient.dualLie_apply_apply, toKDual_apply_apply, toKDual_apply_apply]
  exact flip_lie hP Y f h

/-- If `P(·, h) = 0` only for `h = 0`, then `h ↦ P(·, h)` is injective. -/
theorem toKDual_injective (hP : IsRealStandardInvariantPairing n ds es P)
    (hsep : ∀ h : realStandardKFinite n es, h ≠ 0 → ∃ f, P f h ≠ 0) :
    Function.Injective (toKDual hP) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro h hh
  rw [Submodule.mem_bot]
  by_contra h0
  obtain ⟨f, hf⟩ := hsep h h0
  apply hf
  rw [← toKDual_apply_apply hP, LinearMap.mem_ker.1 hh]
  rfl

/-- The range of `h ↦ P(·, h)` is a `(𝔤, K)`-submodule of the finite dual. -/
theorem range_toKDual_rep (hP : IsRealStandardInvariantPairing n ds es P)
    (k : Matrix.unitaryGroup (Fin n) ℝ) :
    ∀ w ∈ LinearMap.range (toKDual hP),
      kDualRep (realStandardRep n ds) k w ∈ LinearMap.range (toKDual hP) := by
  rintro _ ⟨h, rfl⟩
  exact ⟨_, toKDual_rep hP k h⟩

theorem range_toKDual_lie (hP : IsRealStandardInvariantPairing n ds es P)
    (Y : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) :
    ∀ w ∈ LinearMap.range (toKDual hP),
      RealContragredient.dualLie (isRealGKModule_realStandardModule n ds) Y w ∈
        LinearMap.range (toKDual hP) := by
  rintro _ ⟨h, rfl⟩
  exact ⟨_, toKDual_lie hP Y h⟩

end Pairing

/-! ## Intertwiners between real standard modules -/

/-- A linear map between `O(n)`-finite real standard modules that commutes with right
translations and with the right derivatives along real matrices is an
`IsRealStandardIntertwiner` map. -/
theorem isRealStandardIntertwiner_of_map {n : ℕ} {es es' : List RealBlock}
    {T : realStandardKFinite n es →ₗ[ℂ] realStandardKFinite n es'}
    (hK : ∀ (k : Matrix.unitaryGroup (Fin n) ℝ) (f : realStandardKFinite n es),
      T (realStandardRep n es k f) = realStandardRep n es' k (T f))
    (hL : ∀ (X : Matrix (Fin n) (Fin n) ℝ) (f : realStandardKFinite n es),
      T (realStandardLie n es (1 ⊗ₜ X) f) = realStandardLie n es' (1 ⊗ₜ X) (T f)) :
    IsRealStandardIntertwiner n (realStandardRep n es') (realStandardLie n es') es T := by
  have hid := isRealStandardIntertwiner_id n es
  refine ⟨fun k f => ?_, fun X f => ?_⟩
  · obtain ⟨hf, he⟩ := hid.1 k f
    refine ⟨hf, ?_⟩
    rw [LinearMap.id_apply, LinearMap.id_apply] at he
    rw [he, hK]
  · obtain ⟨hf, he⟩ := hid.2 X f
    refine ⟨hf, ?_⟩
    rw [LinearMap.id_apply, LinearMap.id_apply] at he
    rw [he, hL]

end RealStandardPairingReduction

open RealStandardPairingReduction in
/-- Duality and factor invariance imply the local pairing premise. -/
theorem realStandardPairingPairLReduction : RealStandardPairingPairLReductionStatement := by
  intro hD hU n ds dds hds hdds hirr hirr' P hP hP0 xs
  set ds' := ds.map RealLocalJacquet.dualBlock with hds'_def
  have hds' : realRank ds' = n := (RealLocalJacquet.realRank_map_dualBlock ds).trans hds
  obtain ⟨Q, hQ0, hQsep⟩ := hD n ds hds hirr
  have hQ : IsRealStandardInvariantPairing n ds ds' Q := hQ0
  have hgk := isRealGKModule_realStandardModule n ds
  have hirrD := RealContragredient.isIrreducible_kDual hgk hirr (realStandardAdmissible n ds)
  -- `h ↦ Q(·, h)` is a bijection of `I(ds')` onto the finite dual of `I(ds)`.
  have hinj := toKDual_injective hQ hQsep
  have hsurj : Function.Surjective (toKDual hQ) := by
    rcases hirrD.2 _ (range_toKDual_rep hQ) (range_toKDual_lie hQ) with h | h
    · exfalso
      have := realStandardNontrivial n ds' hds'
      obtain ⟨x, hx⟩ := exists_ne (0 : realStandardKFinite n ds')
      apply hx
      apply hinj
      rw [map_zero]
      exact (Submodule.mem_bot ℂ).1 (h ▸ LinearMap.mem_range_self _ x)
    · exact LinearMap.range_eq_top.1 h
  let E := LinearEquiv.ofBijective (toKDual hQ) ⟨hinj, hsurj⟩
  have hE : ∀ x, E x = toKDual hQ x := fun _ => rfl
  -- `I(ds')` is irreducible, being isomorphic to the finite dual of `I(ds)`.
  have hirrD' : IsIrreducibleGKModule (realStandardRep n ds') (realStandardLie n ds') := by
    refine ⟨realStandardNontrivial n ds' hds', fun W hWK hWL => ?_⟩
    have hmapK : ∀ (k : Matrix.unitaryGroup (Fin n) ℝ),
        ∀ w ∈ W.map (toKDual hQ), kDualRep (realStandardRep n ds) k w ∈ W.map (toKDual hQ) := by
      rintro k _ ⟨h, hh, rfl⟩
      exact ⟨_, hWK k h hh, toKDual_rep hQ k h⟩
    have hmapL : ∀ (Y : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ),
        ∀ w ∈ W.map (toKDual hQ), RealContragredient.dualLie hgk Y w ∈ W.map (toKDual hQ) := by
      rintro Y _ ⟨h, hh, rfl⟩
      exact ⟨_, hWL Y h hh, toKDual_lie hQ Y h⟩
    rcases hirrD.2 _ hmapK hmapL with h | h
    · left
      rw [← Submodule.comap_map_eq_of_injective hinj W, h, Submodule.comap_bot,
        LinearMap.ker_eq_bot.2 hinj]
    · right
      rw [← Submodule.comap_map_eq_of_injective hinj W, h, Submodule.comap_top]
  -- The nonzero intertwiner `I(dds) → I(ds')`: `h ↦ Q⁻¹(P(·, h))`.
  let T : realStandardKFinite n dds →ₗ[ℂ] realStandardKFinite n ds' :=
    E.symm.toLinearMap ∘ₗ toKDual hP
  have hT : IsRealStandardIntertwiner n (realStandardRep n ds') (realStandardLie n ds') dds T := by
    refine isRealStandardIntertwiner_of_map (fun k f => ?_) (fun X f => ?_)
    · change E.symm (toKDual hP (realStandardRep n dds k f)) =
        realStandardRep n ds' k (E.symm (toKDual hP f))
      rw [LinearEquiv.symm_apply_eq, hE, toKDual_rep, toKDual_rep, ← hE,
        LinearEquiv.apply_symm_apply]
    · change E.symm (toKDual hP (realStandardLie n dds (1 ⊗ₜ X) f)) =
        realStandardLie n ds' (1 ⊗ₜ X) (E.symm (toKDual hP f))
      rw [LinearEquiv.symm_apply_eq, hE, toKDual_lie, toKDual_lie, ← hE,
        LinearEquiv.apply_symm_apply]
  have hT0 : T ≠ 0 := by
    intro hT0
    apply hP0
    apply LinearMap.ext₂
    intro f h
    have h1 : E.symm (toKDual hP h) = 0 := LinearMap.congr_fun hT0 h
    rw [LinearEquiv.map_eq_zero_iff] at h1
    rw [← toKDual_apply_apply hP, h1]
    rfl
  exact hU n dds ds' hdds hds' hirr' hirrD' T hT hT0 xs

end Langlands.Global.RankinSelbergGlobal
