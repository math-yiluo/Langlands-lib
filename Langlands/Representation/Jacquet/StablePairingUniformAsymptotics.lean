import Langlands.Representation.Jacquet.StablePairingAsymptotics
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.CoefficientIndependence

/-!
# Uniform asymptotics of stable pairings

The asymptotic formula `ℓ(ρ(a) v) = b [ℓ] [ρ(a) v]` of
`StablePairingAsymptotics` holds for every element `a` whose inverse conjugates
`K ∩ N` into `K`, whose compression on `K`-fixed vectors commutes with compression
by `g⁻¹`, and which conjugates a finite subset of `Nbar` into `K`; `a` need not
commute with `M`. Compressions commute under Casselman's multiplicativity
conditions for one Iwahori factorization. For finitely many pairing data sharing a
good subgroup, a single depth threshold works for all of them: this is the
abstract form of Waldspurger's Proposition I.4.3. Finally, the constant term
`m ↦ b [ℓ] (J_δ(m) [v])` of a coefficient satisfies the defining asymptotic
property of Waldspurger's Proposition I.6.2, and it lies in `A(π)` for the normalized
action `π` on the opposite quotient, which is admissible when `ρ` is and the opposite
quotient has an Iwahori contraction basis.
-/

noncomputable section

namespace Langlands.Jacquet

open scoped NNReal

universe uG uV uι

section Commute

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- An operator commuting with compression preserves its stable image. -/
theorem mem_stableImage_of_commute (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G)
    {T : Module.End ℂ (fixedVectors ρ K.toSubgroup)}
    (hT : Commute T (compressedAction ρ hρ K hK g))
    {t : fixedVectors ρ K.toSubgroup} (ht : t ∈ stableImage ρ hρ K hK g) :
    T t ∈ stableImage ρ hρ K hK g := by
  rw [mem_stableImage] at ht ⊢
  intro r
  obtain ⟨w, rfl⟩ := ht r
  exact ⟨T w, (LinearMap.congr_fun (hT.pow_right r).eq w).symm⟩

/-- Casselman's commutation of compressions: for an Iwahori factorization
`K = (K ∩ Nbar)(K ∩ M)(K ∩ N)` and two commuting elements `a`, `c` each of which
conjugates `K ∩ N` into `K` and whose inverses conjugate `K ∩ Nbar` and `K ∩ M`
into `K`, the compressions by `a` and by `c` commute. -/
theorem compressedAction_commute_of_factor (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (N M Nbar : Subgroup G)
    (hfactor : ∀ k ∈ K, ∃ l ∈ K.toSubgroup ⊓ Nbar, ∃ m ∈ K.toSubgroup ⊓ M,
      ∃ u ∈ K.toSubgroup ⊓ N, k = l * m * u)
    {a c : G} (hac : a * c = c * a)
    (ha_up : ∀ u ∈ K.toSubgroup ⊓ N, a * u * a⁻¹ ∈ K)
    (ha_low : ∀ l ∈ K.toSubgroup ⊓ Nbar, a⁻¹ * l * a ∈ K)
    (ha_mid : ∀ m ∈ K.toSubgroup ⊓ M, a⁻¹ * m * a ∈ K)
    (hc_up : ∀ u ∈ K.toSubgroup ⊓ N, c * u * c⁻¹ ∈ K)
    (hc_low : ∀ l ∈ K.toSubgroup ⊓ Nbar, c⁻¹ * l * c ∈ K)
    (hc_mid : ∀ m ∈ K.toSubgroup ⊓ M, c⁻¹ * m * c ∈ K) :
    Commute (compressedAction ρ hρ K hK a) (compressedAction ρ hρ K hK c) := by
  change _ * _ = _ * _
  rw [← compressedAction_mul_of_factor ρ hρ K hK N M Nbar hfactor a c ha_up hc_low hc_mid,
    ← compressedAction_mul_of_factor ρ hρ K hK N M Nbar hfactor c a hc_up ha_low ha_mid, hac]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The normalized action agrees with the unnormalized one at elements where the character
is trivial. -/
theorem normalizedActionOfModulus_apply_of_eq_one (ρ : Representation ℂ G V) (N M : Subgroup G)
    (hMN : M ≤ Subgroup.normalizer N) (δ : M →* ℝ≥0ˣ) {m : M} (hm : δ m = 1)
    (y : Coinvariants ρ N) :
    normalizedActionOfModulus ρ N M hMN δ m y = action ρ N M hMN m y := by
  obtain ⟨v, rfl⟩ := mk_surjective ρ N y
  rw [normalizedActionOfModulus_mk, action_mk, hm]
  simp

omit [IsTopologicalGroup G] in
/-- If the unnormalized action on the coinvariants is admissible and `δ` has open kernel, the
normalized action is admissible. -/
theorem isAdmissible_normalizedActionOfModulus (ρ : Representation ℂ G V) (N M : Subgroup G)
    (hMN : M ≤ Subgroup.normalizer N) (δ : M →* ℝ≥0ˣ) (hδ : IsOpen (δ.ker : Set M))
    (hρ : IsSmooth ρ) (h : IsAdmissible (action ρ N M hMN)) :
    IsAdmissible (normalizedActionOfModulus ρ N M hMN δ) := by
  refine ⟨isSmooth_normalizedActionOfModulus ρ N M hMN δ hδ hρ, fun L => ?_⟩
  let Lδ : OpenSubgroup M := L ⊓ { toSubgroup := δ.ker, isOpen' := hδ }
  have hle : fixedVectors (normalizedActionOfModulus ρ N M hMN δ) L.toSubgroup ≤
      fixedVectors (action ρ N M hMN) Lδ.toSubgroup := by
    intro y hy k
    have hk := OpenSubgroup.mem_inf.mp k.property
    have h1 : δ k = 1 := hk.2
    have h2 := hy ⟨k, hk.1⟩
    change action ρ N M hMN k y = y
    rw [← normalizedActionOfModulus_apply_of_eq_one ρ N M hMN δ h1]
    exact h2
  have := h.2 Lδ
  exact Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)

end Commute

namespace StablePairingData

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {D : StablePairingData G}
variable {ρ : Representation ℂ G V} {hρ : IsSmooth ρ}
variable {b : Coinvariants (smoothContragredient ρ) D.N →ₗ[ℂ] Coinvariants ρ D.Nbar →ₗ[ℂ] ℂ}

/-- The functional `b [ℓ]` of a stable pairing is invariant under `K ∩ M` when `ℓ`
is fixed by `K`. -/
theorem IsStablePairing.apply_action_of_mem (hA : D.Admits ρ hρ)
    (hb : D.IsStablePairing ρ hρ b) {K : OpenSubgroup G} {ℓ : SmoothDual ρ}
    (hℓ : ℓ ∈ fixedVectors (smoothContragredient ρ) K.toSubgroup)
    (m : D.M) (hm : (m : G) ∈ K) (y : Coinvariants ρ D.Nbar) :
    b (Jacquet.mk (smoothContragredient ρ) D.N ℓ) (action ρ D.Nbar D.M D.hMNbar m y) =
      b (Jacquet.mk (smoothContragredient ρ) D.N ℓ) y := by
  have h := hb.map_action hA m⁻¹ (Jacquet.mk (smoothContragredient ρ) D.N ℓ)
    (action ρ D.Nbar D.M D.hMNbar m y)
  have h₁ : action (smoothContragredient ρ) D.N D.M D.hMN m⁻¹
      (Jacquet.mk (smoothContragredient ρ) D.N ℓ) =
      Jacquet.mk (smoothContragredient ρ) D.N ℓ := by
    rw [action_mk]
    exact congrArg _ (apply_eq_of_mem_fixedVectors _ hℓ (K.inv_mem hm))
  have h₂ : action ρ D.Nbar D.M D.hMNbar m⁻¹ (action ρ D.Nbar D.M D.hMNbar m y) = y := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [h₁, h₂] at h
  exact h.symm

/-- For a good `K`, a `K`-fixed `ℓ` and a vector `u` fixed by `K ∩ N`, the pairing
of `[ℓ]` with the class of the `K`-average of `u` equals its pairing with `[u]`. -/
theorem IsStablePairing.apply_mk_averageMap (hA : D.Admits ρ hρ)
    (hb : D.IsStablePairing ρ hρ b) (K : OpenSubgroup G) (hK : D.Good K)
    {ℓ : SmoothDual ρ} (hℓ : ℓ ∈ fixedVectors (smoothContragredient ρ) K.toSubgroup)
    {u : V} (hu : ∀ x ∈ K, x ∈ D.N → ρ x u = u) :
    b (Jacquet.mk (smoothContragredient ρ) D.N ℓ)
        (Jacquet.mk ρ D.Nbar (Compact.averageMap ρ hρ K (D.isCompact K hK) u)) =
      b (Jacquet.mk (smoothContragredient ρ) D.N ℓ) (Jacquet.mk ρ D.Nbar u) := by
  apply map_averageMap_of_forall_eq ρ hρ K _
    ((b (Jacquet.mk (smoothContragredient ρ) D.N ℓ)).comp (Jacquet.mk ρ D.Nbar)) u
  intro k
  obtain ⟨l, -, hlN, m, hmK, hmM, x, hxK, hxN, hk⟩ := D.factor K hK k k.property
  change b _ (Jacquet.mk ρ D.Nbar (ρ (k : G) u)) = _
  rw [hk, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hu x hxK hxN,
    mk_apply_subgroup ρ D.Nbar ⟨l, hlN⟩]
  have e : Jacquet.mk ρ D.Nbar (ρ m u) =
      action ρ D.Nbar D.M D.hMNbar ⟨m, hmM⟩ (Jacquet.mk ρ D.Nbar u) :=
    (action_mk ρ D.Nbar D.M D.hMNbar ⟨m, hmM⟩ u).symm
  rw [e]
  exact hb.apply_action_of_mem hA hℓ ⟨m, hmM⟩ hmK _

/-- **Asymptotics without commutation with `M`.** For a good `K` fixing `v` and
`ℓ`, there is a finite subset `F` of `Nbar` such that `ℓ(ρ(a) v) = b [ℓ] [ρ(a) v]`
for every `a` whose inverse conjugates `K ∩ N` into `K`, whose compression on
`K`-fixed vectors commutes with compression by `g⁻¹`, and which conjugates `F`
into `K`. -/
theorem IsStablePairing.exists_finset_asymptotics_of_commute (hA : D.Admits ρ hρ)
    (hb : D.IsStablePairing ρ hρ b) (K : OpenSubgroup G) (hK : D.Good K)
    {v : V} (hv : v ∈ fixedVectors ρ K.toSubgroup)
    {ℓ : SmoothDual ρ} (hℓ : ℓ ∈ fixedVectors (smoothContragredient ρ) K.toSubgroup) :
    ∃ F : Finset G, (F : Set G) ⊆ D.Nbar ∧
      ∀ a : G, (∀ u ∈ K, u ∈ D.N → a⁻¹ * u * a ∈ K) →
        Commute (compressedAction ρ hρ K (D.isCompact K hK) a)
          (compressedAction ρ hρ K (D.isCompact K hK) D.g⁻¹) →
        (∀ n ∈ F, a * n * a⁻¹ ∈ K) →
          smoothDualPairing ρ ℓ (ρ a v) =
            b (Jacquet.mk (smoothContragredient ρ) D.N ℓ) (Jacquet.mk ρ D.Nbar (ρ a v)) := by
  obtain ⟨t, ht, hmk⟩ := D.exists_stable_mk_eq hA hK ⟨v, hv⟩
  have hrel : v - (t : V) ∈ relations ρ D.Nbar := by
    rw [← mk_eq_zero, map_sub, hmk, sub_self]
  obtain ⟨F, hF, hFzero⟩ :=
    exists_finset_averageMap_apply_eq_zero ρ hρ D.Nbar K (D.isCompact K hK) hrel
  refine ⟨F, hF, fun a hup hc haF => ?_⟩
  have havg : Compact.averageMap ρ hρ K (D.isCompact K hK) (ρ a v) =
      (compressedAction ρ hρ K (D.isCompact K hK) a t : V) := by
    have h0 := hFzero a haF
    rw [map_sub, map_sub, sub_eq_zero] at h0
    exact h0
  have hst := mem_stableImage_of_commute ρ hρ K (D.isCompact K hK) D.g⁻¹ hc ht
  have e := hb K hK ⟨ℓ, hℓ⟩ _ hst
  have hu : ∀ x ∈ K, x ∈ D.N → ρ x (ρ a v) = ρ a v := by
    intro x hx hxN
    calc ρ x (ρ a v) = ρ a (ρ (a⁻¹ * x * a) v) := by
          simp only [← Module.End.mul_apply, ← map_mul]
          congr 1
          group
      _ = ρ a v := by rw [apply_eq_of_mem_fixedVectors ρ hv (hup x hx hxN)]
  rw [← smoothDualPairing_averageMap ρ hρ K (D.isCompact K hK) hℓ (ρ a v),
    ← hb.apply_mk_averageMap hA K hK hℓ hu, havg]
  exact e.symm

/-- The class of `ρ(m) v` for `m ∈ M`, paired by `b`, in terms of an action
normalized by a character `δ`: `b x [ρ(m) v] = δ(m)^{1/2} b x (J_δ(m) [v])`. -/
theorem apply_mk_eq_sqrt_mul_normalized (δ : D.M →* ℝ≥0ˣ)
    (x : Coinvariants (smoothContragredient ρ) D.N) (m : D.M) (v : V) :
    b x (Jacquet.mk ρ D.Nbar (ρ m v)) =
      ((NNReal.sqrt (δ m : ℝ≥0) : ℝ) : ℂ) *
        b x (normalizedActionOfModulus ρ D.Nbar D.M D.hMNbar δ m (Jacquet.mk ρ D.Nbar v)) := by
  have hs : (((NNReal.sqrt (δ m : ℝ≥0) : ℝ) : ℂ)) ≠ 0 := by
    simp [(δ m).ne_zero]
  rw [normalizedActionOfModulus_mk, map_smul, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hs,
    one_mul]

variable (D) in
/-- The constant term along the data `D` of the coefficient `x ↦ ℓ(ρ(x) v)`,
relative to a bilinear form `b` and a character `δ` of `M`: the function
`m ↦ b [ℓ] (J_δ(m) [v])` on `M`, where `J_δ` is the action on the opposite quotient
normalized by `δ^{-1/2}`. -/
def coefficientConstantTerm (ρ : Representation ℂ G V)
    (b : Coinvariants (smoothContragredient ρ) D.N →ₗ[ℂ] Coinvariants ρ D.Nbar →ₗ[ℂ] ℂ)
    (δ : D.M →* ℝ≥0ˣ) (ℓ : SmoothDual ρ) (v : V) : D.M → ℂ :=
  fun m => b (Jacquet.mk (smoothContragredient ρ) D.N ℓ)
    (normalizedActionOfModulus ρ D.Nbar D.M D.hMNbar δ m (Jacquet.mk ρ D.Nbar v))

/-- **Existence part of Waldspurger's Proposition I.6.2, abstract form.** If `b`
has the asymptotic property, then for every `m ∈ M` there are a good `K` and a
finite subset `F` of `Nbar` such that
`δ(m a)^{-1/2} ℓ(ρ(m a) v) = f_P(m a)` for every contracting `a ∈ M` with
`a F a⁻¹ ⊆ K`, where `f_P` is `coefficientConstantTerm`. -/
theorem HasAsymptotics.exists_coefficientConstantTerm (hρ : IsSmooth ρ)
    (hb : D.HasAsymptotics ρ b) (δ : D.M →* ℝ≥0ˣ) (ℓ : SmoothDual ρ) (v : V) (m : D.M) :
    ∃ K : OpenSubgroup G, D.Good K ∧ ∃ F : Finset G, (F : Set G) ⊆ D.Nbar ∧
      ∀ a : D.M, D.IsContractingElement a → (∀ n ∈ F, (a : G) * n * (a : G)⁻¹ ∈ K) →
        (((NNReal.sqrt (δ (m * a) : ℝ≥0) : ℝ) : ℂ))⁻¹ *
            smoothDualPairing ρ ℓ (ρ ((m * a : D.M) : G) v) =
          D.coefficientConstantTerm ρ b δ ℓ v (m * a) := by
  obtain ⟨U₁, hU₁⟩ := hρ (ρ m v)
  obtain ⟨U₂, hU₂⟩ := isSmooth_smoothContragredient ρ ℓ
  obtain ⟨K, hK, hK₁, hK₂⟩ := D.exists_good_le_inf U₁ U₂
  obtain ⟨F, hF, h⟩ := hb.normalized δ K hK (mem_fixedVectors_of_le ρ hK₁ hU₁)
    (mem_fixedVectors_of_le _ hK₂ hU₂)
  refine ⟨K, hK, F, hF, fun a ha haF => ?_⟩
  have hma : (m : G) * a = a * m := ha.1 m m.property
  have hcomm : m * a = a * m := Subtype.ext hma
  have hρma : ρ ((m * a : D.M) : G) v = ρ a (ρ m v) := by
    change ρ ((m : G) * a) v = _
    rw [hma, map_mul, Module.End.mul_apply]
  have hJ : normalizedActionOfModulus ρ D.Nbar D.M D.hMNbar δ a
      (Jacquet.mk ρ D.Nbar (ρ m v)) =
      ((NNReal.sqrt (δ m : ℝ≥0) : ℝ) : ℂ) •
        normalizedActionOfModulus ρ D.Nbar D.M D.hMNbar δ (m * a) (Jacquet.mk ρ D.Nbar v) := by
    have hs : (((NNReal.sqrt (δ m : ℝ≥0) : ℝ) : ℂ)) ≠ 0 := by
      simp [(δ m).ne_zero]
    have e : Jacquet.mk ρ D.Nbar (ρ m v) = ((NNReal.sqrt (δ m : ℝ≥0) : ℝ) : ℂ) •
        normalizedActionOfModulus ρ D.Nbar D.M D.hMNbar δ m (Jacquet.mk ρ D.Nbar v) := by
      rw [normalizedActionOfModulus_mk, smul_smul, mul_inv_cancel₀ hs, one_smul]
    rw [e, map_smul, hcomm, map_mul, Module.End.mul_apply]
  have hsqrt : ((NNReal.sqrt (δ (m * a) : ℝ≥0) : ℝ) : ℂ) =
      ((NNReal.sqrt (δ m : ℝ≥0) : ℝ) : ℂ) * ((NNReal.sqrt (δ a : ℝ≥0) : ℝ) : ℂ) := by
    rw [map_mul, Units.val_mul, NNReal.sqrt_mul, NNReal.coe_mul, Complex.ofReal_mul]
  have hs' : ((NNReal.sqrt (δ (m * a) : ℝ≥0) : ℝ) : ℂ) ≠ 0 := by
    simp
  rw [hρma, h a ha haF, hJ, map_smul, smul_eq_mul, inv_mul_eq_iff_eq_mul₀ hs', hsqrt]
  unfold coefficientConstantTerm
  ring

/-- For `δ` with open kernel, each functional `b x` of a stable pairing is a smooth functional
for the normalized action on the opposite quotient. -/
theorem IsStablePairing.mem_smoothVectors_normalized (hA : D.Admits ρ hρ)
    (hb : D.IsStablePairing ρ hρ b) (δ : D.M →* ℝ≥0ˣ) (hδ : IsOpen (δ.ker : Set D.M))
    (x : Coinvariants (smoothContragredient ρ) D.N) :
    b x ∈ smoothVectors (normalizedActionOfModulus ρ D.Nbar D.M D.hMNbar δ).dual := by
  obtain ⟨U, hU⟩ := hb.exists_open_invariant hA x
  have hc : Continuous (D.M.subtype : D.M →* G) := continuous_subtype_val
  refine ⟨U.comap D.M.subtype hc ⊓ { toSubgroup := δ.ker, isOpen' := hδ }, ?_⟩
  intro h
  obtain ⟨hhU, hhker⟩ := OpenSubgroup.mem_inf.mp h.property
  apply LinearMap.ext
  intro y
  change b x (normalizedActionOfModulus ρ D.Nbar D.M D.hMNbar δ (h : D.M)⁻¹ y) = b x y
  have h1 : δ ((h : D.M)⁻¹) = 1 := by
    rw [map_inv, MonoidHom.mem_ker.mp hhker, inv_one]
  rw [normalizedActionOfModulus_apply_of_eq_one _ _ _ _ _ h1]
  exact hU ((h : D.M)⁻¹) (U.inv_mem (OpenSubgroup.mem_comap.mp hhU)) y

/-- For `δ` with open kernel, the constant term `coefficientConstantTerm` of a coefficient is a
coefficient of the normalized action on the opposite quotient, i.e. it lies in Waldspurger's
`A(π)` (`coefficientFunctionSpace`) of that smooth representation of `M`. -/
theorem IsStablePairing.coefficientConstantTerm_mem_coefficientFunctionSpace
    (hA : D.Admits ρ hρ) (hb : D.IsStablePairing ρ hρ b) (δ : D.M →* ℝ≥0ˣ)
    (hδ : IsOpen (δ.ker : Set D.M)) (ℓ : SmoothDual ρ) (v : V) :
    D.coefficientConstantTerm ρ b δ ℓ v ∈
      HarishChandraSchwartz.coefficientFunctionSpace
        (SmoothRep.of (normalizedActionOfModulus ρ D.Nbar D.M D.hMNbar δ)
          (isSmooth_normalizedActionOfModulus ρ D.Nbar D.M D.hMNbar δ hδ hρ)) := by
  have h := HarishChandraSchwartz.matrixCoefficient_mem_coefficientFunctionSpace
    (SmoothRep.of (normalizedActionOfModulus ρ D.Nbar D.M D.hMNbar δ)
      (isSmooth_normalizedActionOfModulus ρ D.Nbar D.M D.hMNbar δ hδ hρ))
    ⟨b (Jacquet.mk (smoothContragredient ρ) D.N ℓ),
      hb.mem_smoothVectors_normalized hA δ hδ _⟩ (Jacquet.mk ρ D.Nbar v)
  convert h using 1
  funext m
  rfl

/-- **`f_P ∈ A(M)`, abstract form.** If moreover `ρ` is admissible and the opposite quotient
has an Iwahori contraction basis (`HasIwahoriContractionBasis Nbar M N`), the constant term lies
in `A(π)` for an admissible smooth representation `π` of `M`. -/
theorem IsStablePairing.exists_admissible_coefficientConstantTerm (hA : D.Admits ρ hρ)
    (hb : D.IsStablePairing ρ hρ b) (δ : D.M →* ℝ≥0ˣ) (hδ : IsOpen (δ.ker : Set D.M))
    (hadm : IsAdmissible ρ) (hbasis : HasIwahoriContractionBasis D.Nbar D.M D.N)
    (ℓ : SmoothDual ρ) (v : V) :
    ∃ B : SmoothRep.{0, uG, uV} ℂ D.M, IsAdmissible B.representation ∧
      D.coefficientConstantTerm ρ b δ ℓ v ∈ HarishChandraSchwartz.coefficientFunctionSpace B :=
  ⟨SmoothRep.of (normalizedActionOfModulus ρ D.Nbar D.M D.hMNbar δ)
      (isSmooth_normalizedActionOfModulus ρ D.Nbar D.M D.hMNbar δ hδ hρ),
    isAdmissible_normalizedActionOfModulus ρ D.Nbar D.M D.hMNbar δ hδ hρ
      (isAdmissible_action_of_iwahoriContraction ρ hadm D.Nbar D.M D.N D.hMNbar hbasis),
    hb.coefficientConstantTerm_mem_coefficientFunctionSpace hA δ hδ ℓ v⟩

end StablePairingData

section Uniform

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- A real function `depth` on a set `A` *controls conjugation of `Nbar` into `K`*
if for every finite subset `F` of `Nbar` there is a threshold `T` with
`a F a⁻¹ ⊆ K` for every `a ∈ A` with `T < depth a`. -/
def DepthControls (Nbar : Subgroup G) (K : OpenSubgroup G) (A : Set G)
    (depth : G → ℝ) : Prop :=
  ∀ F : Finset G, (F : Set G) ⊆ Nbar →
    ∃ T : ℝ, ∀ a ∈ A, T < depth a → ∀ n ∈ F, a * n * a⁻¹ ∈ K

/-- **Abstract form of Waldspurger's Proposition I.4.3.** Let `D i` be finitely
many pairing data with stable pairings `b i`, sharing a good subgroup `K` that
fixes `v` and `ℓ`. Let `A` be a set of elements whose inverses conjugate each
`K ∩ (D i).N` into `K` and whose compressions commute with compression by each
`(D i).g⁻¹`, and let `depth i` control conjugation of `(D i).Nbar` into `K` on
`A` (`DepthControls`). Then there is one threshold `T` such that
`ℓ(ρ(a) v) = b i [ℓ] [ρ(a) v]` for all `i` and all `a ∈ A` with `T < depth i a`. -/
theorem exists_uniform_asymptotics {ι : Type uι} [Finite ι]
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ) (D : ι → StablePairingData G)
    (b : ∀ i, Coinvariants (smoothContragredient ρ) (D i).N →ₗ[ℂ]
      Coinvariants ρ (D i).Nbar →ₗ[ℂ] ℂ)
    (hA : ∀ i, (D i).Admits ρ hρ) (hb : ∀ i, (D i).IsStablePairing ρ hρ (b i))
    (K : OpenSubgroup G) (hK : ∀ i, (D i).Good K)
    {v : V} (hv : v ∈ fixedVectors ρ K.toSubgroup)
    {ℓ : SmoothDual ρ} (hℓ : ℓ ∈ fixedVectors (smoothContragredient ρ) K.toSubgroup)
    (A : Set G) (depth : ι → G → ℝ)
    (hdeep : ∀ i, DepthControls (D i).Nbar K A (depth i))
    (hup : ∀ i, ∀ a ∈ A, ∀ u ∈ K, u ∈ (D i).N → a⁻¹ * u * a ∈ K)
    (hcomm : ∀ i, ∀ a ∈ A,
      Commute (compressedAction ρ hρ K ((D i).isCompact K (hK i)) a)
        (compressedAction ρ hρ K ((D i).isCompact K (hK i)) (D i).g⁻¹)) :
    ∃ T : ℝ, ∀ i, ∀ a ∈ A, T < depth i a →
      smoothDualPairing ρ ℓ (ρ a v) =
        b i (Jacquet.mk (smoothContragredient ρ) (D i).N ℓ)
          (Jacquet.mk ρ (D i).Nbar (ρ a v)) := by
  classical
  have := Fintype.ofFinite ι
  have hF : ∀ i, ∃ F : Finset G, (F : Set G) ⊆ (D i).Nbar ∧
      ∀ a : G, (∀ u ∈ K, u ∈ (D i).N → a⁻¹ * u * a ∈ K) →
        Commute (compressedAction ρ hρ K ((D i).isCompact K (hK i)) a)
          (compressedAction ρ hρ K ((D i).isCompact K (hK i)) (D i).g⁻¹) →
        (∀ n ∈ F, a * n * a⁻¹ ∈ K) →
          smoothDualPairing ρ ℓ (ρ a v) =
            b i (Jacquet.mk (smoothContragredient ρ) (D i).N ℓ)
              (Jacquet.mk ρ (D i).Nbar (ρ a v)) :=
    fun i => (hb i).exists_finset_asymptotics_of_commute (hA i) K (hK i) hv hℓ
  choose F hFN hFeq using hF
  have hT : ∀ i, ∃ T : ℝ, ∀ a ∈ A, T < depth i a → ∀ n ∈ F i, a * n * a⁻¹ ∈ K :=
    fun i => hdeep i (F i) (hFN i)
  choose T hTdeep using hT
  refine ⟨∑ i, |T i|, fun i a ha hdepth => ?_⟩
  have hle : T i ≤ ∑ j, |T j| :=
    (le_abs_self (T i)).trans
      (Finset.single_le_sum (f := fun j => |T j|) (fun j _ => abs_nonneg (T j))
        (Finset.mem_univ i))
  exact hFeq i a (hup i a ha) (hcomm i a ha) (hTdeep i a ha (hle.trans_lt hdepth))

/-- **Normalized form of the abstract Proposition I.4.3.** Under the hypotheses of
`exists_uniform_asymptotics`, if moreover every element of `A` lies in every
`(D i).M` and `δ i` are characters of the `(D i).M`, then there is one threshold `T`
such that `ℓ(ρ(a) v) = (δ i)(a)^{1/2} b i [ℓ] (J_{δ i}(a) [v])` for all `i` and all
`a ∈ A` with `T < depth i a`, where `J_{δ i}` is the action on the opposite
quotient normalized by `(δ i)^{-1/2}`. -/
theorem exists_uniform_normalized_asymptotics {ι : Type uι} [Finite ι]
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ) (D : ι → StablePairingData G)
    (b : ∀ i, Coinvariants (smoothContragredient ρ) (D i).N →ₗ[ℂ]
      Coinvariants ρ (D i).Nbar →ₗ[ℂ] ℂ)
    (hA : ∀ i, (D i).Admits ρ hρ) (hb : ∀ i, (D i).IsStablePairing ρ hρ (b i))
    (δ : ∀ i, (D i).M →* ℝ≥0ˣ)
    (K : OpenSubgroup G) (hK : ∀ i, (D i).Good K)
    {v : V} (hv : v ∈ fixedVectors ρ K.toSubgroup)
    {ℓ : SmoothDual ρ} (hℓ : ℓ ∈ fixedVectors (smoothContragredient ρ) K.toSubgroup)
    (A : Set G) (hAM : ∀ i, ∀ a ∈ A, a ∈ (D i).M) (depth : ι → G → ℝ)
    (hdeep : ∀ i, DepthControls (D i).Nbar K A (depth i))
    (hup : ∀ i, ∀ a ∈ A, ∀ u ∈ K, u ∈ (D i).N → a⁻¹ * u * a ∈ K)
    (hcomm : ∀ i, ∀ a ∈ A,
      Commute (compressedAction ρ hρ K ((D i).isCompact K (hK i)) a)
        (compressedAction ρ hρ K ((D i).isCompact K (hK i)) (D i).g⁻¹)) :
    ∃ T : ℝ, ∀ i, ∀ a (ha : a ∈ A), T < depth i a →
      smoothDualPairing ρ ℓ (ρ a v) =
        ((NNReal.sqrt (δ i ⟨a, hAM i a ha⟩ : ℝ≥0) : ℝ) : ℂ) *
          b i (Jacquet.mk (smoothContragredient ρ) (D i).N ℓ)
            (normalizedActionOfModulus ρ (D i).Nbar (D i).M (D i).hMNbar (δ i)
              ⟨a, hAM i a ha⟩ (Jacquet.mk ρ (D i).Nbar v)) := by
  obtain ⟨T, hT⟩ := exists_uniform_asymptotics ρ hρ D b hA hb K hK hv hℓ A depth hdeep
    hup hcomm
  refine ⟨T, fun i a ha hdepth => ?_⟩
  rw [hT i a ha hdepth]
  exact StablePairingData.apply_mk_eq_sqrt_mul_normalized (δ i) _ ⟨a, hAM i a ha⟩ v

end Uniform

end Langlands.Jacquet
