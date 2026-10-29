import Langlands.Representation.Compact.OrbitMeanTranslation
import Langlands.Representation.Compact.ProjectionProof
import Langlands.Representation.Jacquet.Localization
import Langlands.Representation.Twist.SmoothProof
import Langlands.Representation.Whittaker.Algebraic

/-!
# Character-twisted averaging over compact open subgroups

For a smooth complex representation `ρ` of a topological group `G`, a subgroup `N`
and a character `χ` of `N` with open kernel, averaging the twisted restriction
`n ↦ χ(n)⁻¹ ρ(n)` over a compact open subgroup `H` of `N` is a linear projection
`P_H`. It fixes every `χ`-equivariant linear form, it differs from the identity by
an element of the character relations `ρ(n) v - χ(n) v`, and it kills every
relation with `n ∈ H`. Along an increasing exhaustion of `N` by compact open
subgroups, every relation is eventually killed. These facts give the extension of
an equivariant form from an `N`-stable subspace and, under uniqueness of
equivariant forms, the spanning of the whole space by the relations and the
subspace.
-/

noncomputable section

namespace Langlands.Jacquet.Localization

open Compact Whittaker

universe uG uG' uV

section Orbit

variable {H : Type uG'} [Group H]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (π : Representation ℂ H V) (v : V)

/-- The orbit mean as a normalized finite sum of orbit points. -/
theorem orbitMean_eq_smul_sum [Fintype (orbit π v)] :
    orbitMean π v = (Fintype.card (orbit π v) : ℂ)⁻¹ • ∑ x : orbit π v, x.val := by
  rw [orbitMean_eq_finiteMean]
  rfl

/-- The orbit mean lies in every submodule containing the orbit. -/
theorem orbitMean_mem [Finite (orbit π v)] (S : Submodule ℂ V) (hS : ∀ g, π g v ∈ S) :
    orbitMean π v ∈ S := by
  classical
  let := Fintype.ofFinite (orbit π v)
  rw [orbitMean_eq_smul_sum]
  refine S.smul_mem _ (S.sum_mem fun x _ => ?_)
  obtain ⟨g, hg⟩ := x.property
  rw [← hg]
  exact hS g

/-- A linear form constant on the orbit takes the same value on the orbit mean. -/
theorem apply_orbitMean [Finite (orbit π v)] (ℓ : V →ₗ[ℂ] ℂ) (hℓ : ∀ g, ℓ (π g v) = ℓ v) :
    ℓ (orbitMean π v) = ℓ v := by
  classical
  let := Fintype.ofFinite (orbit π v)
  have hcard : (Fintype.card (orbit π v) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hval (x : orbit π v) : ℓ x.val = ℓ v := by
    obtain ⟨g, hg⟩ := x.property
    rw [← hg]
    exact hℓ g
  rw [orbitMean_eq_smul_sum, map_smul, map_sum]
  simp only [hval, Finset.sum_const, Finset.card_univ, smul_eq_mul, nsmul_eq_mul]
  field_simp

/-- If every difference `v - π(g) v` lies in `S`, so does `v` minus its orbit mean. -/
theorem sub_orbitMean_mem [Finite (orbit π v)] (S : Submodule ℂ V)
    (hS : ∀ g, v - π g v ∈ S) : v - orbitMean π v ∈ S := by
  classical
  let := Fintype.ofFinite (orbit π v)
  have hcard : (Fintype.card (orbit π v) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hv : v = (Fintype.card (orbit π v) : ℂ)⁻¹ • ∑ _x : orbit π v, v := by
    rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
      inv_mul_cancel₀ hcard, one_smul]
  have he : v - orbitMean π v =
      (Fintype.card (orbit π v) : ℂ)⁻¹ • ∑ x : orbit π v, (v - x.val) := by
    rw [orbitMean_eq_smul_sum, Finset.sum_sub_distrib, smul_sub, ← hv]
  rw [he]
  refine S.smul_mem _ (S.sum_mem fun x _ => ?_)
  obtain ⟨g, hg⟩ := x.property
  rw [← hg]
  exact hS g

/-- The orbit of a translate is the same orbit. -/
theorem orbit_apply (g : H) : orbit π (π g v) = orbit π v := by
  ext w
  constructor
  · rintro ⟨h, rfl⟩
    refine ⟨h * g, ?_⟩
    change π (h * g) v = π h (π g v)
    rw [map_mul, Module.End.mul_apply]
  · rintro ⟨h, rfl⟩
    refine ⟨h * g⁻¹, ?_⟩
    change π (h * g⁻¹) (π g v) = π h v
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]

/-- The orbit mean is the normalized sum over cosets of any finite-index subgroup
fixing the vector, using arbitrary coset representatives. -/
theorem orbitMean_eq_quotient_sum (K : Subgroup H) [Fintype (H ⧸ K)]
    (hv : ∀ k ∈ K, π k v = v) [Finite (orbit π v)] :
    orbitMean π v =
      (Fintype.card (H ⧸ K) : ℂ)⁻¹ • ∑ c : H ⧸ K, π (Quotient.out c) v := by
  classical
  let := Fintype.ofFinite (orbit π v)
  have hrep (a b : H) (hab : (QuotientGroup.mk a : H ⧸ K) = QuotientGroup.mk b) :
      π a v = π b v := by
    have hk : a⁻¹ * b ∈ K := QuotientGroup.eq.mp hab
    calc π a v = π a (π (a⁻¹ * b) v) := by rw [hv _ hk]
      _ = π b v := by rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
  let f : (H ⧸ K) →[H] orbit π v :=
    { toFun := fun c => ⟨π (Quotient.out c) v, ⟨Quotient.out c, rfl⟩⟩
      map_smul' := by
        intro g c
        apply Subtype.ext
        change π (Quotient.out (g • c)) v = π g (π (Quotient.out c) v)
        rw [← Module.End.mul_apply, ← map_mul]
        apply hrep
        rw [QuotientGroup.out_eq']
        conv_lhs => rw [← QuotientGroup.out_eq' c]
        rfl }
  have hcomp := finiteMean_comp f (fun x : orbit π v => x.val)
  rw [orbitMean_eq_finiteMean, ← hcomp]
  rfl

end Orbit

section Averaging

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (ρ : Representation ℂ G V) (N : Subgroup G) (χ : N →* ℂˣ)

/-- The restriction of `ρ` to `N`, twisted by `χ⁻¹`: `n ↦ χ(n)⁻¹ ρ(n)`. -/
def twistedRestriction : Representation ℂ N V :=
  twist χ⁻¹ (ρ.comp N.subtype)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem twistedRestriction_apply (n : N) (v : V) :
    twistedRestriction ρ N χ n v = (χ n : ℂ)⁻¹ • ρ n v := by
  change ((χ⁻¹ n : ℂˣ) : ℂ) • ρ n v = _
  rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val]

variable {ρ N χ}

omit [IsTopologicalGroup G] in
/-- The twisted restriction of a smooth representation by a character with open
kernel is smooth. -/
theorem isSmooth_twistedRestriction (hρ : IsSmooth ρ) (hχ : IsOpen (χ.ker : Set N)) :
    IsSmooth (twistedRestriction ρ N χ) := by
  have hker : ((χ⁻¹).ker : Set N) = χ.ker := by
    ext n
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.inv_apply, inv_eq_one]
  have hres : IsSmooth (ρ.comp N.subtype) := by
    intro v
    obtain ⟨K, hK⟩ := hρ v
    refine ⟨K.comap N.subtype continuous_subtype_val, ?_⟩
    intro k
    exact hK ⟨(k.val : G), k.property⟩
  exact (isSmooth_twist_iff χ⁻¹ (ρ.comp N.subtype) (by rw [hker]; exact hχ)).mpr hres

variable (hρ : IsSmooth ρ) (hχ : IsOpen (χ.ker : Set N))

/-- The twisted average `P_H` over a compact open subgroup `H` of `N`. -/
def characterAverage (H : OpenSubgroup N) (hH : IsCompact (H : Set N)) : V →ₗ[ℂ] V :=
  averageMap (twistedRestriction ρ N χ) (isSmooth_twistedRestriction hρ hχ) H hH

section Fixed

variable (H : OpenSubgroup N) (hH : IsCompact (H : Set N))

include hρ hχ hH in
theorem finite_orbit_twistedRestriction (v : V) :
    Finite (orbit ((twistedRestriction ρ N χ).comp H.toSubgroup.subtype) v) :=
  finite_orbit_of_smooth _ (isSmooth_twistedRestriction hρ hχ) H hH v

theorem characterAverage_eq_orbitMean (v : V) :
    characterAverage hρ hχ H hH v =
      orbitMean ((twistedRestriction ρ N χ).comp H.toSubgroup.subtype) v :=
  rfl

/-- `P_H` preserves every `ρ(N)`-stable submodule. -/
theorem characterAverage_mem (S : Submodule ℂ V) (hS : ∀ (n : N) (v : V), v ∈ S → ρ n v ∈ S)
    {v : V} (hv : v ∈ S) : characterAverage hρ hχ H hH v ∈ S := by
  let := finite_orbit_twistedRestriction hρ hχ H hH v
  rw [characterAverage_eq_orbitMean]
  refine orbitMean_mem _ v S fun h => ?_
  change twistedRestriction ρ N χ h v ∈ S
  rw [twistedRestriction_apply]
  exact S.smul_mem _ (hS h v hv)

/-- A linear form which is `χ`-equivariant on the orbit of `v` is unchanged by `P_H`. -/
theorem apply_characterAverage (ℓ : V →ₗ[ℂ] ℂ) (v : V)
    (hℓ : ∀ n ∈ H, ℓ (ρ n v) = χ n * ℓ v) :
    ℓ (characterAverage hρ hχ H hH v) = ℓ v := by
  let := finite_orbit_twistedRestriction hρ hχ H hH v
  rw [characterAverage_eq_orbitMean]
  refine apply_orbitMean _ v ℓ fun h => ?_
  change ℓ (twistedRestriction ρ N χ h v) = ℓ v
  rw [twistedRestriction_apply, map_smul, hℓ h h.property, smul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ (Units.ne_zero _), one_mul]

/-- Every `χ`-equivariant linear form is unchanged by `P_H`. -/
theorem functional_characterAverage (ℓ : functionals N χ ρ) (v : V) :
    ℓ.val (characterAverage hρ hχ H hH v) = ℓ.val v :=
  apply_characterAverage hρ hχ H hH ℓ.val v fun n _ => ℓ.property n v

/-- `v - P_H v` is a character relation. -/
theorem sub_characterAverage_mem (v : V) :
    v - characterAverage hρ hχ H hH v ∈ relations ρ N χ := by
  let := finite_orbit_twistedRestriction hρ hχ H hH v
  rw [characterAverage_eq_orbitMean]
  refine sub_orbitMean_mem _ v _ fun h => ?_
  change v - twistedRestriction ρ N χ h v ∈ relations ρ N χ
  rw [twistedRestriction_apply]
  have hrel := sub_mem_relations ρ N χ h v
  have he : v - (χ h : ℂ)⁻¹ • ρ h v =
      -((χ h : ℂ)⁻¹ • (ρ h v - (χ h : ℂ) • v)) := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul, neg_sub]
  rw [he]
  exact (relations ρ N χ).neg_mem ((relations ρ N χ).smul_mem _ hrel)

/-- `P_H` kills each relation `ρ(n) w - χ(n) w` with `n ∈ H`. -/
theorem characterAverage_relation {n : N} (hn : n ∈ H) (w : V) :
    characterAverage hρ hχ H hH (ρ n w - (χ n : ℂ) • w) = 0 := by
  let π := (twistedRestriction ρ N χ).comp H.toSubgroup.subtype
  have htr : ρ n w = (χ n : ℂ) • π ⟨n, hn⟩ w := by
    change ρ n w = (χ n : ℂ) • twistedRestriction ρ N χ n w
    rw [twistedRestriction_apply, smul_smul, mul_inv_cancel₀ (Units.ne_zero _), one_smul]
  have hinv : characterAverage hρ hχ H hH (π ⟨n, hn⟩ w) = characterAverage hρ hχ H hH w := by
    rw [characterAverage_eq_orbitMean, characterAverage_eq_orbitMean]
    exact Compact.orbitMean_apply π ⟨n, hn⟩ w
  rw [map_sub, htr, map_smul, map_smul, hinv, sub_self]

/-- `P_H` is the normalized sum of `χ(c)⁻¹ ρ(c) v` over coset representatives of any
finite-index subgroup of `H` fixing `v` under the twisted action. -/
theorem characterAverage_eq_quotient_sum (v : V) (K : Subgroup H) [Fintype (H ⧸ K)]
    (hv : ∀ k ∈ K, (χ (k : N) : ℂ)⁻¹ • ρ ((k : N) : G) v = v) :
    characterAverage hρ hχ H hH v =
      (Fintype.card (H ⧸ K) : ℂ)⁻¹ • ∑ c : H ⧸ K,
        (χ ((Quotient.out c : H) : N) : ℂ)⁻¹ • ρ (((Quotient.out c : H) : N) : G) v := by
  let := finite_orbit_twistedRestriction hρ hχ H hH v
  rw [characterAverage_eq_orbitMean, orbitMean_eq_quotient_sum _ v K]
  · refine congrArg _ (Finset.sum_congr rfl fun c _ => ?_)
    change twistedRestriction ρ N χ ((Quotient.out c : H) : N) v = _
    rw [twistedRestriction_apply]
  · intro k hk
    change twistedRestriction ρ N χ (k : N) v = v
    rw [twistedRestriction_apply]
    exact hv k hk

end Fixed

section Exhaustion

variable (S : ℕ → OpenSubgroup N) (hS : ∀ k, IsCompact (S k : Set N))
variable (hmono : Monotone S) (hcover : ∀ n : N, ∃ k, n ∈ S k)

include hρ hχ hS hmono hcover in
/-- Along an increasing compact open exhaustion of `N`, every character relation is
eventually killed by the averages. -/
theorem eventually_characterAverage_eq_zero {r : V} (hr : r ∈ relations ρ N χ) :
    ∃ k₀, ∀ k, k₀ ≤ k → characterAverage hρ hχ (S k) (hS k) r = 0 := by
  induction hr using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨n, w⟩, rfl⟩ := hx
    obtain ⟨k₀, hk₀⟩ := hcover n
    exact ⟨k₀, fun k hk => characterAverage_relation hρ hχ (S k) (hS k) (hmono hk hk₀) w⟩
  | zero => exact ⟨0, fun k _ => map_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨max a b, fun k hk => ?_⟩
    rw [map_add, ha k (le_of_max_le_left hk), hb k (le_of_max_le_right hk), add_zero]
  | smul c x _ hx =>
    obtain ⟨a, ha⟩ := hx
    exact ⟨a, fun k hk => by rw [map_smul, ha k hk, smul_zero]⟩

variable (V' : Submodule ℂ V) (hV' : ∀ (n : N) (v : V), v ∈ V' → ρ n v ∈ V')
variable (J' : V' →ₗ[ℂ] ℂ)
variable (hJ' : ∀ (n : N) (v : V'), J' ⟨ρ n v, hV' n v v.property⟩ = χ n * J' v)

include hρ hχ hS hmono hcover hJ' in
/-- An equivariant form on an `N`-stable subspace vanishes on the relations lying in
that subspace. -/
theorem apply_eq_zero_of_mem_relations {v : V} (hv : v ∈ V') (hr : v ∈ relations ρ N χ) :
    J' ⟨v, hv⟩ = 0 := by
  obtain ⟨k₀, hk₀⟩ := eventually_characterAverage_eq_zero hρ hχ S hS hmono hcover hr
  obtain ⟨ℓ, hℓ⟩ := LinearMap.exists_extend J'
  have hℓv (w : V) (hw : w ∈ V') : ℓ w = J' ⟨w, hw⟩ := by
    rw [← hℓ]
    rfl
  have h := apply_characterAverage hρ hχ (S k₀) (hS k₀) ℓ v (fun n _ => by
    rw [hℓv _ (hV' n v hv), hℓv _ hv]
    exact hJ' n ⟨v, hv⟩)
  rw [hk₀ k₀ le_rfl, map_zero, hℓv _ hv] at h
  exact h.symm

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- A form on `V'` vanishing on the relations in `V'` is the restriction of an
equivariant form on the whole space. -/
theorem exists_functional_extension
    (hvan : ∀ (v : V) (hv : v ∈ V'), v ∈ relations ρ N χ → J' ⟨v, hv⟩ = 0) :
    ∃ J : functionals N χ ρ, ∀ v : V', J.val v = J' v := by
  let R := relations ρ N χ
  let q : V' →ₗ[ℂ] V ⧸ R := R.mkQ ∘ₗ V'.subtype
  have hker : LinearMap.ker q ≤ LinearMap.ker J' := by
    intro v hv
    have hvR : (v : V) ∈ R := (Submodule.Quotient.mk_eq_zero R).mp hv
    exact hvan v v.property hvR
  let J₁ : (V' ⧸ LinearMap.ker q) →ₗ[ℂ] ℂ := (LinearMap.ker q).liftQ J' hker
  let J₂ : LinearMap.range q →ₗ[ℂ] ℂ := J₁ ∘ₗ q.quotKerEquivRange.symm.toLinearMap
  obtain ⟨J₃, hJ₃⟩ := LinearMap.exists_extend J₂
  let J : V →ₗ[ℂ] ℂ := J₃ ∘ₗ R.mkQ
  have hJR : ∀ r ∈ R, J r = 0 := by
    intro r hr
    change J₃ (R.mkQ r) = 0
    rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero R).mpr hr, map_zero]
  refine ⟨⟨J, fun n v => ?_⟩, fun v => ?_⟩
  · have h := hJR _ (sub_mem_relations ρ N χ n v)
    rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at h
    exact h
  · change J₃ (R.mkQ v) = J' v
    have h1 : R.mkQ (v : V) = q v := rfl
    have h2 := congrArg (fun f => f ⟨q v, LinearMap.mem_range_self q v⟩) hJ₃
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype] at h2
    rw [h1, h2]
    change J₁ (q.quotKerEquivRange.symm ⟨q v, _⟩) = J' v
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    rfl

include hρ hχ hS hmono hcover hJ' in
/-- Under uniqueness of equivariant forms up to scalars, the relations and a stable
subspace carrying a nonzero equivariant form span the whole space. -/
theorem relations_sup_eq_top
    (huniq : ∀ φ ψ : functionals N χ ρ, ψ.val ≠ 0 → ∃ c : ℂ, φ = c • ψ)
    (hJ'0 : J' ≠ 0) : relations ρ N χ ⊔ V' = ⊤ := by
  obtain ⟨J, hJ⟩ := exists_functional_extension V' J'
    (fun v hv hr => apply_eq_zero_of_mem_relations hρ hχ S hS hmono hcover V' hV' J' hJ' hv hr)
  by_contra htop
  obtain ⟨φ, hφ0, hφ⟩ :=
    Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr htop)
  have hφR : ∀ r ∈ relations ρ N χ, φ r = 0 := fun r hr => hφ (Submodule.mem_sup_left hr)
  have hφV : ∀ v ∈ V', φ v = 0 := fun v hv => hφ (Submodule.mem_sup_right hv)
  let φ' : functionals N χ ρ := ⟨φ, fun n v => by
    have h := hφR _ (sub_mem_relations ρ N χ n v)
    rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at h
    exact h⟩
  obtain ⟨w, hw⟩ : ∃ w : V', J' w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hJ'0 (LinearMap.ext hcon)
  have hJ0 : J.val ≠ 0 := by
    intro h0
    apply hw
    rw [← hJ w, h0, LinearMap.zero_apply]
  obtain ⟨c, hc⟩ := huniq φ' J hJ0
  have hcw : c * J' w = 0 := by
    have h := congrArg (fun f : functionals N χ ρ => f.val (w : V)) hc
    simp only [Submodule.coe_smul, LinearMap.smul_apply, smul_eq_mul] at h
    rw [← hJ w, ← h]
    exact hφV w w.property
  have hc0 : c = 0 := (mul_eq_zero.mp hcw).resolve_right hw
  apply hφ0
  have h := congrArg Subtype.val hc
  rw [hc0, zero_smul] at h
  exact h

include hρ hχ hS hmono hcover hV' in
/-- If the relations and a stable subspace span the whole space, every vector is
eventually averaged into the subspace. -/
theorem eventually_characterAverage_mem (htop : relations ρ N χ ⊔ V' = ⊤) (F : V) :
    ∃ k₀, ∀ k, k₀ ≤ k → characterAverage hρ hχ (S k) (hS k) F ∈ V' := by
  have hF : F ∈ relations ρ N χ ⊔ V' := by rw [htop]; exact Submodule.mem_top
  obtain ⟨r, hr, v, hv, rfl⟩ := Submodule.mem_sup.mp hF
  obtain ⟨k₀, hk₀⟩ := eventually_characterAverage_eq_zero hρ hχ S hS hmono hcover hr
  refine ⟨k₀, fun k hk => ?_⟩
  rw [map_add, hk₀ k hk, zero_add]
  exact characterAverage_mem hρ hχ (S k) (hS k) V' hV' hv

end Exhaustion

end Averaging

end Langlands.Jacquet.Localization
