import Langlands.Representation.Jacquet.StablePairingVanishing
import Langlands.Representation.Jacquet.IwahoriContractionAdmissibility
import Langlands.Representation.Jacquet.Normalized

/-!
# Asymptotics of the stable pairing

For supplied `StablePairingData` and a smooth representation satisfying `Admits`,
the stable pairing `b` of `StablePairingProof` computes the matrix coefficients
`ℓ(ρ(a) v)` for every sufficiently contracting element `a`: this is the asymptotic
formula of Casselman's canonical pairing (Waldspurger, Théorème I.4.1, after
Casselman), in an abstract form with explicit hypotheses.

*Contracting* elements (`IsContractingElement`) commute with `M` and with the
contracting element `g` of the data, and on every good subgroup `K` conjugation
by `a` maps `K ∩ Nbar` into `K` and conjugation by `a⁻¹` maps `K ∩ N` into `K`.
For a good `K` fixing `v` and `ℓ` there is a finite subset `F` of `Nbar` such that
`ℓ(ρ(a) v) = b [ℓ] [ρ(a) v]` whenever `a` is contracting and `a F a⁻¹ ⊆ K`.
Along the powers of `g⁻¹` the formula holds from some power on, without any
condition on `Nbar`.
-/

noncomputable section

namespace Langlands.Jacquet

open scoped NNReal

universe uG uV

section Relations

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- A vector in the span of the coinvariant relations of `N` is killed by the
`K`-average after translation by any `a` that conjugates a fixed finite subset
of `N` into `K`. -/
theorem exists_finset_averageMap_apply_eq_zero (ρ : Representation ℂ G V)
    (hρ : IsSmooth ρ) (N : Subgroup G) (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    {w : V} (hw : w ∈ relations ρ N) :
    ∃ F : Finset G, (F : Set G) ⊆ N ∧
      ∀ a : G, (∀ n ∈ F, a * n * a⁻¹ ∈ K) →
        Compact.averageMap ρ hρ K hK (ρ a w) = 0 := by
  classical
  rw [relations_eq_span] at hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨n, v⟩, rfl⟩ := hx
    refine ⟨{(n : G)}, by simp, fun a ha => ?_⟩
    have hn := ha n (Finset.mem_singleton_self _)
    have e : ρ a (ρ n v) = ρ (a * n * a⁻¹) (ρ a v) := by
      simp only [← Module.End.mul_apply, ← map_mul]
      congr 1
      group
    rw [map_sub, map_sub, e, averageMap_apply_of_mem ρ hρ K hK hn, sub_self]
  | zero => exact ⟨∅, by simp, fun a _ => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨F₁, hF₁, h₁⟩ := hx
    obtain ⟨F₂, hF₂, h₂⟩ := hy
    refine ⟨F₁ ∪ F₂, by rw [Finset.coe_union]; exact Set.union_subset hF₁ hF₂,
      fun a ha => ?_⟩
    rw [map_add, map_add, h₁ a (fun n hn => ha n (Finset.mem_union_left _ hn)),
      h₂ a (fun n hn => ha n (Finset.mem_union_right _ hn)), add_zero]
  | smul c x _ hx =>
    obtain ⟨F, hF, h⟩ := hx
    exact ⟨F, hF, fun a ha => by rw [map_smul, map_smul, h a ha, smul_zero]⟩

end Relations

namespace StablePairingData

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

variable (D : StablePairingData G)

/-- An element `a` is *contracting* for the data `D` if it commutes with `M` and
with `g`, and for every good `K` conjugation by `a` maps `K ∩ Nbar` into `K` and
conjugation by `a⁻¹` maps `K ∩ N` into `K`. -/
def IsContractingElement (a : G) : Prop :=
  (∀ m ∈ D.M, m * a = a * m) ∧ a * D.g = D.g * a ∧
    (∀ K, D.Good K → ∀ l ∈ K, l ∈ D.Nbar → a * l * a⁻¹ ∈ K) ∧
    (∀ K, D.Good K → ∀ u ∈ K, u ∈ D.N → a⁻¹ * u * a ∈ K)

/-- The inverse of the contracting element of the data is contracting. -/
theorem isContractingElement_inv : D.IsContractingElement D.g⁻¹ := by
  refine ⟨fun m hm => by simpa using D.commute_pow m hm 1, by group, ?_, ?_⟩
  · intro K hK l hl hlN
    simpa using D.lower_conj K hK l hl hlN
  · intro K hK u hu huN
    simpa using D.upper_conj K hK u hu huN 1

/-- A good subgroup also factors in the order `N M Nbar`. -/
theorem factor_swap (K : OpenSubgroup G) (hK : D.Good K) :
    ∀ k ∈ K, ∃ l ∈ K.toSubgroup ⊓ D.N, ∃ m ∈ K.toSubgroup ⊓ D.M,
      ∃ u ∈ K.toSubgroup ⊓ D.Nbar, k = l * m * u := by
  intro k hk
  obtain ⟨l, hlK, hlN, m, hmK, hmM, u, huK, huN, hkf⟩ := D.factor K hK k⁻¹ (K.inv_mem hk)
  refine ⟨u⁻¹, Subgroup.mem_inf.mpr ⟨K.inv_mem huK, D.N.inv_mem huN⟩,
    m⁻¹, Subgroup.mem_inf.mpr ⟨K.inv_mem hmK, D.M.inv_mem hmM⟩,
    l⁻¹, Subgroup.mem_inf.mpr ⟨K.inv_mem hlK, D.Nbar.inv_mem hlN⟩, ?_⟩
  rw [← inv_inv k, hkf]
  group

/-- Compression by an element `a` that commutes with `M` and `g`, conjugates
`K ∩ Nbar` into `K` and whose inverse conjugates `K ∩ N` into `K` commutes with
compression by `g⁻¹`. -/
theorem compressedAction_commute (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : D.Good K) {a : G}
    (hM : ∀ m ∈ D.M, m * a = a * m) (hg : a * D.g = D.g * a)
    (hlow : ∀ l ∈ K, l ∈ D.Nbar → a * l * a⁻¹ ∈ K)
    (hup : ∀ u ∈ K, u ∈ D.N → a⁻¹ * u * a ∈ K) :
    Commute (compressedAction ρ hρ K (D.isCompact K hK) a)
      (compressedAction ρ hρ K (D.isCompact K hK) D.g⁻¹) := by
  have hag : a * D.g⁻¹ = D.g⁻¹ * a := by
    rw [mul_inv_eq_iff_eq_mul, mul_assoc, hg, ← mul_assoc, inv_mul_cancel, one_mul]
  have hgN : ∀ u ∈ K.toSubgroup ⊓ D.N, D.g⁻¹⁻¹ * u * D.g⁻¹ ∈ K := by
    intro u hu
    have h := D.upper_conj K hK u (Subgroup.mem_inf.mp hu).1 (Subgroup.mem_inf.mp hu).2 1
    simpa using h
  have hgM : ∀ m ∈ K.toSubgroup ⊓ D.M, D.g⁻¹⁻¹ * m * D.g⁻¹ ∈ K := by
    intro m hm
    have hc : D.g⁻¹⁻¹ * m * D.g⁻¹ = m := by
      rw [inv_inv, ← D.commute m (Subgroup.mem_inf.mp hm).2, mul_assoc, mul_inv_cancel,
        mul_one]
    rw [hc]
    exact (Subgroup.mem_inf.mp hm).1
  have hgNbar : ∀ l ∈ K.toSubgroup ⊓ D.Nbar, D.g⁻¹ * l * D.g⁻¹⁻¹ ∈ K := by
    intro l hl
    have h := D.lower_conj K hK l (Subgroup.mem_inf.mp hl).1 (Subgroup.mem_inf.mp hl).2
    simpa using h
  have haM : ∀ m ∈ K.toSubgroup ⊓ D.M, a⁻¹ * m * a ∈ K := by
    intro m hm
    have hc : a⁻¹ * m * a = m := by
      rw [mul_assoc, hM m (Subgroup.mem_inf.mp hm).2, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [hc]
    exact (Subgroup.mem_inf.mp hm).1
  have e₁ := compressedAction_mul_of_factor ρ hρ K (D.isCompact K hK) D.Nbar D.M D.N
    (D.factor_swap K hK) a D.g⁻¹
    (fun l hl => hlow l (Subgroup.mem_inf.mp hl).1 (Subgroup.mem_inf.mp hl).2) hgN hgM
  have e₂ := compressedAction_mul_of_factor ρ hρ K (D.isCompact K hK) D.Nbar D.M D.N
    (D.factor_swap K hK) D.g⁻¹ a hgNbar
    (fun u hu => hup u (Subgroup.mem_inf.mp hu).1 (Subgroup.mem_inf.mp hu).2) haM
  change _ * _ = _ * _
  rw [← e₁, ← e₂, hag]

/-- Such a compression preserves the stable image of compression by `g⁻¹`. -/
theorem compressedAction_mem_stableImage_inv (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : D.Good K) {a : G}
    (hM : ∀ m ∈ D.M, m * a = a * m) (hg : a * D.g = D.g * a)
    (hlow : ∀ l ∈ K, l ∈ D.Nbar → a * l * a⁻¹ ∈ K)
    (hup : ∀ u ∈ K, u ∈ D.N → a⁻¹ * u * a ∈ K)
    {t : fixedVectors ρ K.toSubgroup}
    (ht : t ∈ stableImage ρ hρ K (D.isCompact K hK) D.g⁻¹) :
    compressedAction ρ hρ K (D.isCompact K hK) a t ∈
      stableImage ρ hρ K (D.isCompact K hK) D.g⁻¹ := by
  have hc := D.compressedAction_commute ρ hρ K hK hM hg hlow hup
  rw [mem_stableImage] at ht ⊢
  intro r
  obtain ⟨w, rfl⟩ := ht r
  exact ⟨compressedAction ρ hρ K (D.isCompact K hK) a w,
    (LinearMap.congr_fun (hc.pow_right r).eq w).symm⟩

/-- For a vector `v` fixed by a good `K` and an element `a` commuting with `M`
whose inverse conjugates `K ∩ N` into `K`, the `K`-average of `ρ(a) v` has the
same opposite class as `ρ(a) v`. -/
theorem mk_averageMap_apply (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : D.Good K) {a : G}
    (hM : ∀ m ∈ D.M, m * a = a * m)
    (hup : ∀ u ∈ K, u ∈ D.N → a⁻¹ * u * a ∈ K)
    {v : V} (hv : v ∈ fixedVectors ρ K.toSubgroup) :
    Jacquet.mk ρ D.Nbar (Compact.averageMap ρ hρ K (D.isCompact K hK) (ρ a v)) =
      Jacquet.mk ρ D.Nbar (ρ a v) := by
  apply map_averageMap_of_forall_eq ρ hρ K _ (Jacquet.mk ρ D.Nbar) (ρ a v)
  intro k
  obtain ⟨l, -, hlN, m, hmK, hmM, u, huK, huN, hk⟩ := D.factor K hK k k.property
  have hu : ρ u (ρ a v) = ρ a v := by
    calc ρ u (ρ a v) = ρ a (ρ (a⁻¹ * u * a) v) := by
          simp only [← Module.End.mul_apply, ← map_mul]
          congr 1
          group
      _ = ρ a v := by rw [apply_eq_of_mem_fixedVectors ρ hv (hup u huK huN)]
  have hm : ρ m (ρ a v) = ρ a v := by
    calc ρ m (ρ a v) = ρ a (ρ m v) := by
          simp only [← Module.End.mul_apply, ← map_mul, hM m hmM]
      _ = ρ a v := by rw [apply_eq_of_mem_fixedVectors ρ hv hmK]
  rw [hk, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hu, hm]
  exact mk_apply_subgroup ρ D.Nbar ⟨l, hlN⟩ _

variable {D}
variable {ρ : Representation ℂ G V} {hρ : IsSmooth ρ}
variable {b : Coinvariants (smoothContragredient ρ) D.N →ₗ[ℂ] Coinvariants ρ D.Nbar →ₗ[ℂ] ℂ}

/-- **Asymptotics on a good subgroup.** For a good `K` fixing `v` and `ℓ`, there is
a finite subset `F` of `Nbar` such that `ℓ(ρ(a) v) = b [ℓ] [ρ(a) v]` for every `a`
commuting with `M` and `g`, conjugating `K ∩ Nbar` and `F` into `K`, and whose
inverse conjugates `K ∩ N` into `K`. -/
theorem IsStablePairing.exists_finset_asymptotics (hA : D.Admits ρ hρ)
    (hb : D.IsStablePairing ρ hρ b) (K : OpenSubgroup G) (hK : D.Good K)
    {v : V} (hv : v ∈ fixedVectors ρ K.toSubgroup)
    {ℓ : SmoothDual ρ} (hℓ : ℓ ∈ fixedVectors (smoothContragredient ρ) K.toSubgroup) :
    ∃ F : Finset G, (F : Set G) ⊆ D.Nbar ∧
      ∀ a : G, (∀ m ∈ D.M, m * a = a * m) → a * D.g = D.g * a →
        (∀ l ∈ K, l ∈ D.Nbar → a * l * a⁻¹ ∈ K) →
        (∀ u ∈ K, u ∈ D.N → a⁻¹ * u * a ∈ K) →
        (∀ n ∈ F, a * n * a⁻¹ ∈ K) →
          smoothDualPairing ρ ℓ (ρ a v) =
            b (Jacquet.mk (smoothContragredient ρ) D.N ℓ) (Jacquet.mk ρ D.Nbar (ρ a v)) := by
  obtain ⟨t, ht, hmk⟩ := D.exists_stable_mk_eq hA hK ⟨v, hv⟩
  have hrel : v - (t : V) ∈ relations ρ D.Nbar := by
    rw [← mk_eq_zero, map_sub, hmk, sub_self]
  obtain ⟨F, hF, hFzero⟩ :=
    exists_finset_averageMap_apply_eq_zero ρ hρ D.Nbar K (D.isCompact K hK) hrel
  refine ⟨F, hF, fun a hM hg hlow hup haF => ?_⟩
  have havg : Compact.averageMap ρ hρ K (D.isCompact K hK) (ρ a v) =
      (compressedAction ρ hρ K (D.isCompact K hK) a t : V) := by
    have h0 := hFzero a haF
    rw [map_sub, map_sub, sub_eq_zero] at h0
    exact h0
  have hst := D.compressedAction_mem_stableImage_inv ρ hρ K hK hM hg hlow hup ht
  have e := hb K hK ⟨ℓ, hℓ⟩ _ hst
  rw [← smoothDualPairing_averageMap ρ hρ K (D.isCompact K hK) hℓ (ρ a v),
    ← D.mk_averageMap_apply ρ hρ K hK hM hup hv, havg]
  exact e.symm

/-- **Asymptotics along the powers of `g⁻¹`.** For every vector `v` and smooth
functional `ℓ`, `ℓ(ρ(g⁻ʳ) v) = b [ℓ] [ρ(g⁻ʳ) v]` for all sufficiently large `r`. -/
theorem IsStablePairing.exists_pow_asymptotics (hA : D.Admits ρ hρ)
    (hb : D.IsStablePairing ρ hρ b) (v : V) (ℓ : SmoothDual ρ) :
    ∃ r₀ : ℕ, ∀ r : ℕ, r₀ ≤ r →
      smoothDualPairing ρ ℓ (ρ (D.g⁻¹ ^ r) v) =
        b (Jacquet.mk (smoothContragredient ρ) D.N ℓ)
          (Jacquet.mk ρ D.Nbar (ρ (D.g⁻¹ ^ r) v)) := by
  obtain ⟨U₁, hU₁⟩ := hρ v
  obtain ⟨U₂, hU₂⟩ := isSmooth_smoothContragredient ρ ℓ
  obtain ⟨K, hK, hK₁, hK₂⟩ := D.exists_good_le_inf U₁ U₂
  have hv : v ∈ fixedVectors ρ K.toSubgroup := mem_fixedVectors_of_le ρ hK₁ hU₁
  have hℓ : ℓ ∈ fixedVectors (smoothContragredient ρ) K.toSubgroup :=
    mem_fixedVectors_of_le _ hK₂ hU₂
  set C := compressedAction ρ hρ K (D.isCompact K hK) D.g⁻¹ with hC
  obtain ⟨t, ht, hmk⟩ := D.exists_stable_mk_eq hA hK ⟨v, hv⟩
  have hker : (⟨v, hv⟩ : fixedVectors ρ K.toSubgroup) - t ∈
      LinearMap.ker (fixedJacquetMap ρ D.Nbar D.M D.hMNbar K.toSubgroup) := by
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero]
    exact Subtype.ext hmk.symm
  have hpk := hA.lower_kernel K hK hker
  have hmono : Monotone fun r : ℕ => LinearMap.ker (C ^ r) := by
    intro r s hrs x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [← Nat.sub_add_cancel hrs, pow_add, Module.End.mul_apply, hx, map_zero]
  obtain ⟨r₀, hr₀⟩ := (Submodule.mem_iSup_of_directed _ hmono.directed_le).mp hpk
  refine ⟨r₀, fun r hr => ?_⟩
  have hCr : (C ^ r) ⟨v, hv⟩ = (C ^ r) t := by
    have h0 := hmono hr hr₀
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at h0
    exact h0
  have hstr : ∀ n : ℕ, (C ^ n) t ∈ stableImage ρ hρ K (D.isCompact K hK) D.g⁻¹ := by
    intro n
    induction n with
    | zero => simpa using ht
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply]
      exact compressedAction_mem_stableImage ρ hρ K _ D.g⁻¹ _ ih
  have hM : ∀ m ∈ D.M, m * D.g⁻¹ ^ r = D.g⁻¹ ^ r * m := fun m hm => D.commute_pow m hm r
  have hup : ∀ u ∈ K, u ∈ D.N → (D.g⁻¹ ^ r)⁻¹ * u * D.g⁻¹ ^ r ∈ K := by
    intro u hu huN
    rw [inv_pow, inv_inv]
    exact D.upper_conj K hK u hu huN r
  have e₁ : ((C ^ r) ⟨v, hv⟩ : V) =
      Compact.averageMap ρ hρ K (D.isCompact K hK) (ρ (D.g⁻¹ ^ r) v) :=
    D.compressedAction_inv_pow_apply ρ hρ K hK r ⟨v, hv⟩
  rw [← smoothDualPairing_averageMap ρ hρ K (D.isCompact K hK) hℓ,
    ← D.mk_averageMap_apply ρ hρ K hK hM hup hv, ← e₁, hCr]
  exact (hb K hK ⟨ℓ, hℓ⟩ _ (hstr r)).symm

variable (D) in
/-- The asymptotic property of a bilinear form `b` on the upper quotient of the
smooth dual and the opposite quotient: for every good `K` and every `K`-fixed
vector `v` and smooth functional `ℓ`, there is a finite subset `F` of `Nbar` such
that `ℓ(ρ(a) v) = b [ℓ] [ρ(a) v]` for every contracting `a` with `a F a⁻¹ ⊆ K`. -/
def HasAsymptotics (ρ : Representation ℂ G V)
    (b : Coinvariants (smoothContragredient ρ) D.N →ₗ[ℂ] Coinvariants ρ D.Nbar →ₗ[ℂ] ℂ) :
    Prop :=
  ∀ K : OpenSubgroup G, D.Good K →
    ∀ v ∈ fixedVectors ρ K.toSubgroup,
      ∀ ℓ ∈ fixedVectors (smoothContragredient ρ) K.toSubgroup,
        ∃ F : Finset G, (F : Set G) ⊆ D.Nbar ∧
          ∀ a : G, D.IsContractingElement a → (∀ n ∈ F, a * n * a⁻¹ ∈ K) →
            smoothDualPairing ρ ℓ (ρ a v) =
              b (Jacquet.mk (smoothContragredient ρ) D.N ℓ) (Jacquet.mk ρ D.Nbar (ρ a v))

/-- A stable pairing has the asymptotic property. -/
theorem IsStablePairing.hasAsymptotics (hA : D.Admits ρ hρ)
    (hb : D.IsStablePairing ρ hρ b) : D.HasAsymptotics ρ b := by
  intro K hK v hv ℓ hℓ
  obtain ⟨F, hF, h⟩ := hb.exists_finset_asymptotics hA K hK hv hℓ
  exact ⟨F, hF, fun a ha haF => h a ha.1 ha.2.1 (ha.2.2.1 K hK) (ha.2.2.2 K hK) haF⟩

/-- Every vector and smooth functional are fixed by a common good subgroup, so the
asymptotic property gives, for each pair `(v, ℓ)`, a good `K` and a finite subset
`F` of `Nbar` controlling the formula. -/
theorem HasAsymptotics.exists (hρ : IsSmooth ρ) (hb : D.HasAsymptotics ρ b) (v : V)
    (ℓ : SmoothDual ρ) :
    ∃ K : OpenSubgroup G, D.Good K ∧ ∃ F : Finset G, (F : Set G) ⊆ D.Nbar ∧
      ∀ a : G, D.IsContractingElement a → (∀ n ∈ F, a * n * a⁻¹ ∈ K) →
        smoothDualPairing ρ ℓ (ρ a v) =
          b (Jacquet.mk (smoothContragredient ρ) D.N ℓ) (Jacquet.mk ρ D.Nbar (ρ a v)) := by
  obtain ⟨U₁, hU₁⟩ := hρ v
  obtain ⟨U₂, hU₂⟩ := isSmooth_smoothContragredient ρ ℓ
  obtain ⟨K, hK, hK₁, hK₂⟩ := D.exists_good_le_inf U₁ U₂
  exact ⟨K, hK, hb K hK v (mem_fixedVectors_of_le ρ hK₁ hU₁) ℓ
    (mem_fixedVectors_of_le _ hK₂ hU₂)⟩

/-- **Normalized form.** For a character `δ : M → ℝ≥0ˣ` and a contracting `a` in
`M`, the asymptotic property reads
`ℓ(ρ(a) v) = δ(a)^{1/2} b [ℓ] (J_δ(a) [v])`, where `J_δ` is the action on the
opposite quotient normalized by `δ^{-1/2}`. -/
theorem HasAsymptotics.normalized (hb : D.HasAsymptotics ρ b) (δ : D.M →* ℝ≥0ˣ)
    (K : OpenSubgroup G) (hK : D.Good K) {v : V} (hv : v ∈ fixedVectors ρ K.toSubgroup)
    {ℓ : SmoothDual ρ} (hℓ : ℓ ∈ fixedVectors (smoothContragredient ρ) K.toSubgroup) :
    ∃ F : Finset G, (F : Set G) ⊆ D.Nbar ∧
      ∀ a : D.M, D.IsContractingElement a → (∀ n ∈ F, (a : G) * n * (a : G)⁻¹ ∈ K) →
        smoothDualPairing ρ ℓ (ρ a v) =
          ((NNReal.sqrt (δ a : ℝ≥0) : ℝ) : ℂ) *
            b (Jacquet.mk (smoothContragredient ρ) D.N ℓ)
              (normalizedActionOfModulus ρ D.Nbar D.M D.hMNbar δ a (Jacquet.mk ρ D.Nbar v)) := by
  obtain ⟨F, hF, h⟩ := hb K hK v hv ℓ hℓ
  refine ⟨F, hF, fun a ha haF => ?_⟩
  have hs : (((NNReal.sqrt (δ a : ℝ≥0) : ℝ) : ℂ)) ≠ 0 := by
    simp [(δ a).ne_zero]
  rw [normalizedActionOfModulus_mk, map_smul, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hs,
    one_mul]
  exact h a ha haF

/-- **Abstract form of Waldspurger's Théorème I.4.1 (Casselman).** Under `Admits`,
there is a bilinear form on the upper quotient of the smooth dual and the opposite
quotient which is nondegenerate on both sides, invariant under `M`, and has the
asymptotic property. -/
theorem exists_nondegenerate_invariant_hasAsymptotics (hA : D.Admits ρ hρ) :
    ∃ b : Coinvariants (smoothContragredient ρ) D.N →ₗ[ℂ] Coinvariants ρ D.Nbar →ₗ[ℂ] ℂ,
      Function.Injective b ∧ Function.Injective b.flip ∧
        (∀ (m : D.M) (x : Coinvariants (smoothContragredient ρ) D.N)
          (y : Coinvariants ρ D.Nbar),
          b (action (smoothContragredient ρ) D.N D.M D.hMN m x)
            (action ρ D.Nbar D.M D.hMNbar m y) = b x y) ∧
        D.HasAsymptotics ρ b := by
  obtain ⟨b, hb⟩ := D.exists_isStablePairing hA
  exact ⟨b, hb.injective hA, hb.flip_injective hA, hb.map_action hA,
    hb.hasAsymptotics hA⟩

end StablePairingData

end Langlands.Jacquet
