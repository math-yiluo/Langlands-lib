import Langlands.Representation.Archimedean.InversePoleJetSqueeze

/-!
# Proof of the jet squeeze for an intertwiner with a finite inverse pole

This module proves `Langlands.Archimedean.InversePoleJetSqueezeStatement`
(Bernstein–Krötz, *Smooth Fréchet globalizations of Harish-Chandra modules*, §10.1,
Lemma 10.3 and the comparisons before Proposition 10.4) by computing with representatives
modulo the submodules `powerImage`.

The clauses that do not involve `J` have the following individual dependencies. The
intrinsic description of `squeezeDomain`, the chain of submodules and the image identity
for `jetRaise` follow from the induced maps on representatives and use no further
hypothesis. The bijectivity of `jetMulToSub` uses regularity of `s` on the carrier in
question (`U` or `W`), and the bijectivity of `rangeToSubquotient` uses regularity on `U`.
The injectivity of `jetRaise` and of `rangeRaise` uses regularity on `W` and `1 ≤ k`. The
inverse `J` up to `s ^ k` gives the surjectivity of `squeezeMap` (from
`I (J w) = s ^ k • w`) and its kernel (from `J (I u) = s ^ k • u`, cancellation of `s ^ k`
on `U`, and `I (J w) = s ^ k • w`), and with them the bijectivity of
`squeezeQuotientMap`.
-/

noncomputable section

universe uR uA uU uW

set_option autoImplicit false

namespace Langlands.Archimedean

namespace JetSqueeze

variable {R : Type*} [CommRing R] {𝔄 : Type*} [Ring 𝔄] [Algebra R 𝔄]

section Carrier

variable {U : Type*} [AddCommGroup U] [Module R U] [Module 𝔄 U] [IsScalarTower R 𝔄 U]

/-- Membership in `s ^ j U`. -/
theorem mem_powerImage {s : R} {j : ℕ} {u : U} :
    u ∈ powerImage 𝔄 U s j ↔ ∃ v : U, s ^ j • v = u := by
  rw [powerImage, LinearMap.mem_range]
  rfl

/-- `s ^ l U ≤ s ^ j U` when `j ≤ l`. -/
theorem powerImage_antitone (s : R) {j l : ℕ} (h : j ≤ l) :
    powerImage 𝔄 U s l ≤ powerImage 𝔄 U s j :=
  fun _ hx => powerImage_le_comap_id 𝔄 U s h hx

/-- The class of `u` in `U_l` lies in `s ^ j U / s ^ l U` exactly when `u ∈ s ^ j U`, for
`j ≤ l`. -/
theorem mk_mem_jetSub (s : R) {j l : ℕ} (h : j ≤ l) (u : U) :
    (Submodule.Quotient.mk u : Jet 𝔄 U s l) ∈ jetSub 𝔄 U s j l ↔
      u ∈ powerImage 𝔄 U s j := by
  constructor
  · rintro ⟨v, hv, hvu⟩
    have hd : v - u ∈ powerImage 𝔄 U s j :=
      powerImage_antitone s h ((Submodule.Quotient.eq _).mp hvu)
    simpa using sub_mem hv hd
  · intro hu
    exact ⟨u, hu, rfl⟩

/-- Cancellation of a power of a regular element: `s ^ m • u = s ^ (m + n) • v` implies
`u = s ^ n • v`. -/
theorem eq_smul_of_pow_smul_eq {s : R} (hs : IsSMulRegular U s) {m n : ℕ} {u v : U}
    (h : s ^ m • u = s ^ (m + n) • v) : u = s ^ n • v := by
  apply hs.pow m
  change s ^ m • u = s ^ m • s ^ n • v
  rw [h, smul_smul, ← pow_add]

/-- If `s` is regular on `U`, multiplication by `s ^ m` from `U_j` to `U_(m + j)` is
injective. -/
theorem jetMul_injective {s : R} (hs : IsSMulRegular U s) (m : ℕ) {j l : ℕ}
    (h : l ≤ m + j) (hl : m + j ≤ l) : Function.Injective (jetMul 𝔄 U s m h) := by
  obtain rfl : l = m + j := le_antisymm h hl
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [jetMul, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, mem_powerImage] at hx
  obtain ⟨v, hv⟩ := hx
  rw [Submodule.Quotient.mk_eq_zero, mem_powerImage]
  exact ⟨v, (eq_smul_of_pow_smul_eq hs (by simpa using hv.symm)).symm⟩

/-- If `s` is regular on `U`, multiplication by `s ^ k` is a bijection from `U_k` onto
`s ^ k U / s ^ (2k) U`. -/
theorem jetMulToSub_bijective {s : R} (hs : IsSMulRegular U s) (k : ℕ) :
    Function.Bijective (jetMulToSub 𝔄 U s k) := by
  refine ⟨fun x y hxy => ?_, ?_⟩
  · exact jetMul_injective hs k (j := k) (l := 2 * k) (by omega) (by omega)
      (congrArg Subtype.val hxy)
  · rintro ⟨_, u, hu, rfl⟩
    obtain ⟨v, rfl⟩ := mem_powerImage.mp hu
    exact ⟨Submodule.Quotient.mk v, rfl⟩

/-- If `s` is regular on `U` and `1 ≤ k`, multiplication by `s ^ (k - 1)` from `U_1` to
`U_k` is injective. -/
theorem jetRaise_injective {s : R} (hs : IsSMulRegular U s) {k : ℕ} (hk : 1 ≤ k) :
    Function.Injective (jetRaise 𝔄 U s k) :=
  jetMul_injective hs (k - 1) _ (by omega)

end Carrier

section Map

variable {U : Type*} [AddCommGroup U] [Module R U] [Module 𝔄 U] [IsScalarTower R 𝔄 U]
  {W : Type*} [AddCommGroup W] [Module R W] [Module 𝔄 W] [IsScalarTower R 𝔄 W]
  (s : R) (k : ℕ) (I : U →ₗ[𝔄] W)

/-- The class of `u` in `U_(2k)` lies in `squeezeDomain s k I` exactly when
`I u ∈ s ^ k W`. -/
theorem mk_mem_squeezeDomain (u : U) :
    (Submodule.Quotient.mk u : Jet 𝔄 U s (2 * k)) ∈ squeezeDomain s k I ↔
      I u ∈ powerImage 𝔄 W s k := by
  rw [squeezeDomain, Submodule.mem_comap, jetMap, Submodule.mapQ_apply]
  exact mk_mem_jetSub s (by omega) (I u)

/-- `squeezeDomain s k I` is the preimage of `ker I_k` under the jet projection
`U_(2k) → U_k`. -/
theorem squeezeDomain_eq_comap :
    squeezeDomain s k I =
      (LinearMap.ker (jetMap s k I)).comap (jetProj 𝔄 U s (by omega : k ≤ 2 * k)) := by
  ext x
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [mk_mem_squeezeDomain, Submodule.mem_comap, LinearMap.mem_ker, jetProj,
    Submodule.mapQ_apply, LinearMap.id_apply, jetMap, Submodule.mapQ_apply,
    Submodule.Quotient.mk_eq_zero]

/-- `squeezeKernel s k I ≤ s ^ k U / s ^ (2k) U`. -/
theorem squeezeKernel_le_jetSub : squeezeKernel s k I ≤ jetSub 𝔄 U s k (2 * k) := by
  rintro _ ⟨x, -, rfl⟩
  exact jetMul_mem_jetSub 𝔄 U s k x

/-- `s ^ k U / s ^ (2k) U ≤ squeezeDomain s k I`. -/
theorem jetSub_le_squeezeDomain : jetSub 𝔄 U s k (2 * k) ≤ squeezeDomain s k I := by
  rintro _ ⟨u, hu, rfl⟩
  obtain ⟨v, rfl⟩ := mem_powerImage.mp hu
  rw [Submodule.mkQ_apply, mk_mem_squeezeDomain, mem_powerImage]
  exact ⟨I v, (LinearMap.map_smul_of_tower I (s ^ k) v).symm⟩

/-- The image of `range I_1` under multiplication by `s ^ (k - 1)` on `W_1` is the image
under `I_k` of `s ^ (k - 1) U / s ^ k U`. -/
theorem map_range_jetRaise :
    (LinearMap.range (jetMap s 1 I)).map (jetRaise 𝔄 W s k) =
      (jetSub 𝔄 U s (k - 1) k).map (jetMap s k I) := by
  ext y
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact ⟨jetRaise 𝔄 U s k (Submodule.Quotient.mk u), ⟨s ^ (k - 1) • u, ⟨u, rfl⟩, rfl⟩,
      jetMap_jetMul s I (k - 1) _ _⟩
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    obtain ⟨v, rfl⟩ := mem_powerImage.mp hu
    exact ⟨jetMap s 1 I (Submodule.Quotient.mk v), ⟨_, rfl⟩,
      (jetMap_jetMul s I (k - 1) _ (Submodule.Quotient.mk v)).symm⟩

section Inverse

variable {s k I} (J : W →ₗ[R] U)

/-- If `I (J w) = s ^ k • w` for all `w`, the restriction of `I_(2k)` to `squeezeDomain` is
onto `s ^ k W / s ^ (2k) W`. -/
theorem squeezeMap_surjective (hIJ : ∀ w : W, I (J w) = s ^ k • w) :
    Function.Surjective (squeezeMap s k I) := by
  rintro ⟨_, w, hw, rfl⟩
  obtain ⟨v, rfl⟩ := mem_powerImage.mp hw
  have hmem : (Submodule.Quotient.mk (J v) : Jet 𝔄 U s (2 * k)) ∈ squeezeDomain s k I := by
    rw [mk_mem_squeezeDomain, hIJ, mem_powerImage]
    exact ⟨v, rfl⟩
  refine ⟨⟨_, hmem⟩, Subtype.ext ?_⟩
  change (Submodule.Quotient.mk (I (J v)) : Jet 𝔄 W s (2 * k)) =
    Submodule.Quotient.mk (s ^ k • v)
  rw [hIJ]

/-- If `s` is regular on `U`, `J (I u) = s ^ k • u` for all `u` and `I (J w) = s ^ k • w` for
all `w`, the kernel of the restriction of `I_(2k)` to `squeezeDomain`, mapped into `U_(2k)`
by the subtype inclusion, is `squeezeKernel s k I`. -/
theorem map_ker_squeezeMap (hU : IsSMulRegular U s) (hJI : ∀ u : U, J (I u) = s ^ k • u)
    (hIJ : ∀ w : W, I (J w) = s ^ k • w) :
    (LinearMap.ker (squeezeMap s k I)).map (squeezeDomain s k I).subtype =
      squeezeKernel s k I := by
  apply le_antisymm
  · rintro _ ⟨⟨x, hxA⟩, hx, rfl⟩
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have h0 : (Submodule.Quotient.mk (I u) : Jet 𝔄 W s (2 * k)) = 0 :=
      congrArg Subtype.val (LinearMap.mem_ker.mp hx)
    rw [Submodule.Quotient.mk_eq_zero, mem_powerImage] at h0
    obtain ⟨w, hw⟩ := h0
    have hu : u = s ^ k • J w := by
      apply eq_smul_of_pow_smul_eq hU (m := k)
      rw [← hJI u, ← hw, map_smul, ← two_mul]
    change (Submodule.Quotient.mk u : Jet 𝔄 U s (2 * k)) ∈ squeezeKernel s k I
    rw [hu]
    refine ⟨Submodule.Quotient.mk (J w), ?_, rfl⟩
    change jetMap s k I (Submodule.Quotient.mk (J w)) = 0
    rw [jetMap, Submodule.mapQ_apply, hIJ, Submodule.Quotient.mk_eq_zero, mem_powerImage]
    exact ⟨w, rfl⟩
  · intro x hx
    have hxA : x ∈ squeezeDomain s k I :=
      jetSub_le_squeezeDomain s k I (squeezeKernel_le_jetSub s k I hx)
    exact ⟨⟨x, hxA⟩, squeezeKernel_comap_le_ker s k I (x := ⟨x, hxA⟩) hx, rfl⟩

/-- Under the hypotheses of `map_ker_squeezeMap`, the map from `squeezeDomain` modulo
`squeezeKernel` to `s ^ k W / s ^ (2k) W` is bijective. -/
theorem squeezeQuotientMap_bijective (hU : IsSMulRegular U s)
    (hJI : ∀ u : U, J (I u) = s ^ k • u) (hIJ : ∀ w : W, I (J w) = s ^ k • w) :
    Function.Bijective (squeezeQuotientMap s k I) := by
  refine ⟨?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot]
    refine Submodule.ker_liftQ_eq_bot _ _ _ fun x hx => ?_
    rw [Submodule.mem_comap, ← map_ker_squeezeMap J hU hJI hIJ]
    exact Submodule.mem_map_of_mem hx
  · intro y
    obtain ⟨x, hx⟩ := squeezeMap_surjective J hIJ y
    exact ⟨Submodule.Quotient.mk x, hx⟩

end Inverse

/-- If `s` is regular on `U`, the map from `range I_k` to `(s ^ k U / s ^ (2k) U)` modulo
`squeezeKernel` sending `I_k x` to the class of `s ^ k x` is bijective. -/
theorem rangeToSubquotient_bijective (hU : IsSMulRegular U s) :
    Function.Bijective (rangeToSubquotient s k I) := by
  have hmapQ : Function.Bijective
      (Submodule.mapQ _ _ (jetMulToSub 𝔄 U s k) (ker_le_comap_jetMulToSub s k I)) := by
    refine ⟨?_, ?_⟩
    · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro y hy
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hy
      obtain ⟨z, hz, hzx⟩ := hy
      have hzx' : z = x :=
        jetMul_injective hU k (j := k) (l := 2 * k) (by omega) (by omega) hzx
      rw [Submodule.Quotient.mk_eq_zero, ← hzx']
      exact hz
    · intro y
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      obtain ⟨x, rfl⟩ := (jetMulToSub_bijective hU k).2 z
      exact ⟨Submodule.Quotient.mk x, rfl⟩
  rw [rangeToSubquotient, LinearMap.coe_comp]
  exact hmapQ.comp (LinearEquiv.bijective _)

end Map

end JetSqueeze

open JetSqueeze

/-- **Jet squeeze for an intertwiner with a finite inverse pole** (Bernstein–Krötz,
Lemma 10.3 and the comparisons before Proposition 10.4). -/
theorem inversePoleJetSqueeze : InversePoleJetSqueezeStatement.{uR, uA, uU, uW} := by
  intro R _ 𝔄 _ _ U _ _ _ _ W _ _ _ _ s k I J hk hU hW hJI hIJ
  refine ⟨squeezeDomain_eq_comap s k I, squeezeMap_surjective J hIJ,
    map_ker_squeezeMap J hU hJI hIJ, squeezeKernel_le_jetSub s k I,
    jetSub_le_squeezeDomain s k I, jetMulToSub_bijective hU k,
    rangeToSubquotient_bijective s k I hU, squeezeQuotientMap_bijective J hU hJI hIJ,
    jetMulToSub_bijective hW k, jetRaise_injective hW hk, ?_, map_range_jetRaise s k I⟩
  intro x y hxy
  exact Subtype.ext (jetRaise_injective hW hk (congrArg Subtype.val hxy))

end Langlands.Archimedean
