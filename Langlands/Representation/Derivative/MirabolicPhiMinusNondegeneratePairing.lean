import Langlands.Representation.Derivative.MirabolicMinusPairingTransferProof
import Langlands.Representation.Derivative.MinusVanishing
import Langlands.Representation.Compact.ProjectionProof
import Langlands.Group.GL.MirabolicProjection

/-!
# Nondegenerate pairings through normalized `Φ⁻`

Let `A`, `B` be smooth representations of `P_(m+2)` and `β` a pairing with covariance
`|det|` that is nondegenerate in `A`. Restrict `β` to the radical relations
`A(V) = span {u a - a}`, whose radical coefficients have compact support, and integrate
it against `θ_ψ⁻¹` along the radical. The resulting form on `Φ⁻ A(V) × Φ⁻ B` is
nondegenerate in the first variable: a vector in its left kernel has vanishing twisted
radical integrals against every character near `θ_ψ`, so its `θ_ψ`-average over a large
radical box has vanishing integrals against all nontrivial characters, and the published
finite Fourier lemma kills the average. Finally `Φ⁻ A(V) ≅ Φ⁻ A`, and the normalizing twists
turn covariance `|det|^2` into `|det|`. See the paired Markdown.
-/

noncomputable section

namespace Langlands.Derivative.Mirabolic

open GeneralLinear GeneralLinear.Mirabolic HarmonicAnalysis RankinSelberg Topology MeasureTheory
open Jacquet.Localization
open scoped Matrix NNReal

universe uF uV uW

/-! ### The radical relations as a subrepresentation -/

section Radical

variable {K : Type uF} [Field K] {m : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (ρ : Representation ℂ (mirabolic (m + 1) K) V)

/-- The radical relations `span {ρ u v - v}` are stable under the whole mirabolic group. -/
theorem radicalRelations_stable (g : mirabolic (m + 1) K) :
    relations ρ (radical (m + 1) K) 1 ≤
      (relations ρ (radical (m + 1) K) 1).comap (ρ g) := by
  apply Submodule.span_le.2
  rintro _ ⟨⟨u, v⟩, rfl⟩
  let u' : radical (m + 1) K :=
    ⟨g * u * g⁻¹, (radical_normal (n := m + 1) (F := K)).conj_mem u u.property g⟩
  have h := sub_mem_relations ρ (radical (m + 1) K) 1 u' (ρ g v)
  simp only [MonoidHom.one_apply, Units.val_one, one_smul] at h ⊢
  have hg : g * (u : mirabolic (m + 1) K) = (u' : mirabolic (m + 1) K) * g := by
    change _ = g * u * g⁻¹ * g
    group
  have e : ρ g (ρ u v - v) = ρ u' (ρ g v) - ρ g v := by
    rw [map_sub, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, hg]
  rw [SetLike.mem_coe, Submodule.mem_comap, e]
  exact h

/-- `A(V)`: the representation of the mirabolic group on the radical relations. -/
def radicalPart : Representation ℂ (mirabolic (m + 1) K) (relations ρ (radical (m + 1) K) 1) :=
  ρ.subrepresentation _ (radicalRelations_stable ρ)

theorem radicalPart_apply (g : mirabolic (m + 1) K) (x : relations ρ (radical (m + 1) K) 1) :
    ((radicalPart ρ g x : relations ρ (radical (m + 1) K) 1) : V) = ρ g x := rfl

end Radical

section Smooth

variable {G : Type*} [Group G] [TopologicalSpace G] {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- A stable submodule of a smooth representation is smooth. -/
theorem isSmooth_subrepresentation (ρ : Representation ℂ G V) (S : Submodule ℂ V)
    (hS : ∀ g, S ≤ S.comap (ρ g)) (hρ : IsSmooth ρ) : IsSmooth (ρ.subrepresentation S hS) := by
  intro x
  obtain ⟨H, hH⟩ := hρ x
  refine ⟨H, (Representation.mem_invariants _ x).mpr fun h => Subtype.ext ?_⟩
  exact (Representation.mem_invariants _ (x : V)).mp hH h

end Smooth

/-! ### Compact support on the radical relations -/

section Support

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData) {m : ℕ}
variable {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable (ξ : Representation ℂ (mirabolic (m + 1) F.Carrier) V)
  (ξ' : Representation ℂ (mirabolic (m + 1) F.Carrier) W) (β : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (s : ℂ)

/-- Radical coefficients of vectors in the radical relations have compact support. -/
theorem exists_coefficient_support_of_mem
    (hβ : ∀ (g : mirabolic (m + 1) F.Carrier) (v : V) (w : W),
      β (ξ g v) (ξ' g w) = determinantWeight (normalizedAbsoluteValue T) g.val (-s) * β v w) :
    letI := T.topology
    IsSmooth ξ → IsSmooth ξ' →
      ∀ v ∈ relations ξ (radical (m + 1) F.Carrier) 1, ∀ w : W,
        ∃ N : ℤ, ∀ c ∉ latticeBox T (m + 1) N,
          β (ξ (radicalElement c : mirabolic (m + 1) F.Carrier) v) w = 0 := by
  let := T.topology
  intro hs hs' v hv w
  let S : Submodule ℂ V :=
    { carrier := {v | ∃ N : ℤ, ∀ c ∉ latticeBox T (m + 1) N,
        β (ξ (radicalElement c : mirabolic (m + 1) F.Carrier) v) w = 0}
      add_mem' := by
        rintro a b ⟨N₁, h₁⟩ ⟨N₂, h₂⟩
        refine ⟨max N₁ N₂, fun c hc => ?_⟩
        have hc₁ : c ∉ latticeBox T (m + 1) N₁ :=
          fun h => hc (latticeBox_mono T (le_max_left _ _) h)
        have hc₂ : c ∉ latticeBox T (m + 1) N₂ :=
          fun h => hc (latticeBox_mono T (le_max_right _ _) h)
        rw [map_add, map_add, LinearMap.add_apply, h₁ c hc₁, h₂ c hc₂, add_zero]
      zero_mem' := ⟨0, fun c _ => by rw [map_zero, map_zero, LinearMap.zero_apply]⟩
      smul_mem' := by
        rintro a b ⟨N, h⟩
        exact ⟨N, fun c hc => by
          rw [map_smul, map_smul, LinearMap.smul_apply, h c hc, smul_zero]⟩ }
  have hle : relations ξ (radical (m + 1) F.Carrier) 1 ≤ S := by
    apply Submodule.span_le.2
    rintro _ ⟨⟨u, x⟩, rfl⟩
    obtain ⟨d, rfl⟩ : ∃ d, radicalElement d = u := ⟨_, radicalElement_coordinates u⟩
    obtain ⟨H, hHo, hH⟩ := exists_open_subgroup_coefficient T ξ ξ' β s hβ hs hs' x w
    obtain ⟨N, hN⟩ := exists_mulVec_eq_add T (H : Set (Langlands.GeneralLinear (m + 1) F.Carrier))
      hHo H.one_mem d
    refine ⟨N, fun c hc => ?_⟩
    obtain ⟨h, hh, hhc⟩ := hN c hc
    change β (ξ (radicalElement c : mirabolic (m + 1) F.Carrier)
      (ξ (radicalElement d : mirabolic (m + 1) F.Carrier) x -
        (((1 : radical (m + 1) F.Carrier →* ℂˣ) (radicalElement d) : ℂˣ) : ℂ) • x)) w = 0
    rw [MonoidHom.one_apply, Units.val_one, one_smul, map_sub, rep_radicalElement_mul, map_sub,
      LinearMap.sub_apply, ← hhc, hH h hh c, sub_self]
  exact hle hv

/-- Near the identity, `GL_(m+1)` realizes every small perturbation `c ↦ c_last + r ⬝ c`
of the last coordinate. -/
theorem exists_lastRow_perturbation (H : Set (Langlands.GeneralLinear (m + 1) F.Carrier)) :
    letI := T.topology
    IsOpen H → (1 : Langlands.GeneralLinear (m + 1) F.Carrier) ∈ H →
      ∃ n₀ : ℤ, ∀ r ∈ latticeBox T (m + 1) n₀, ∃ h ∈ H, ∀ c : Fin (m + 1) → F.Carrier,
        (h.val *ᵥ c) (Fin.last m) = c (Fin.last m) + r ⬝ᵥ c := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have : T2Space F.Carrier := T.fieldT2
  intro hH h1
  let φ : (Fin (m + 1) → F.Carrier) → Matrix (Fin (m + 1)) (Fin (m + 1)) F.Carrier :=
    fun r => 1 + Matrix.vecMulVec (Pi.single (Fin.last m) 1) r
  have hφ : Continuous φ :=
    continuous_const.add (continuous_const.matrix_vecMulVec continuous_id)
  have hO : IsOpen (Units.val '' H) :=
    (isOpenEmbedding_generalLinear_val (m + 1)).isOpenMap _ hH
  have hmem : φ ⁻¹' (Units.val '' H) ∈ 𝓝 (0 : Fin (m + 1) → F.Carrier) := by
    apply (hO.preimage hφ).mem_nhds
    refine ⟨1, h1, ?_⟩
    simp [φ]
  obtain ⟨n₀, hn₀⟩ := exists_latticeBox_subset T hmem
  refine ⟨n₀, fun r hr => ?_⟩
  obtain ⟨h, hH', hh⟩ := hn₀ hr
  refine ⟨h, hH', fun c => ?_⟩
  rw [hh]
  simp [φ, Matrix.add_mulVec, Matrix.vecMulVec_mulVec]

end Support

/-! ### Twisted radical integrals against coordinate characters -/

section Twisted

variable {K : Type uF} [Field K] [TopologicalSpace K] [IsTopologicalRing K] {m : ℕ}
variable [MeasurableSpace (Fin (m + 1) → K)] [BorelSpace (Fin (m + 1) → K)]
variable (μ : Measure (Fin (m + 1) → K)) [μ.IsAddHaarMeasure]
variable (ψ : UnitaryAdditiveCharacter K)
variable {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable (ξ : Representation ℂ (mirabolic (m + 1) K) V) (β : V →ₗ[ℂ] W →ₗ[ℂ] ℂ)

/-- `J_y(v, w) = ∫ ψ(-(y ⬝ c)) β(ξ(u c) v, w) dc`. -/
def twistedIntegral (y : Fin (m + 1) → K) (v : V) (w : W) : ℂ :=
  ∫ c, ψ.complex (-(y ⬝ᵥ c)) * β (ξ (radicalElement c : mirabolic (m + 1) K) v) w ∂μ

theorem integrable_twistedIntegrand
    (hcont : ∀ v w, Continuous fun c : Fin (m + 1) → K =>
      β (ξ (radicalElement c : mirabolic (m + 1) K) v) w)
    (hcpt : ∀ v w, HasCompactSupport fun c : Fin (m + 1) → K =>
      β (ξ (radicalElement c : mirabolic (m + 1) K) v) w)
    (y : Fin (m + 1) → K) (v : V) (w : W) :
    Integrable (fun c : Fin (m + 1) → K =>
      ψ.complex (-(y ⬝ᵥ c)) * β (ξ (radicalElement c : mirabolic (m + 1) K) v) w) μ :=
  ((ψ.continuous_complex.comp (continuous_const.dotProduct continuous_id).neg).mul
    (hcont v w)).integrable_of_hasCompactSupport
    ((hcpt v w).mul_left (f := fun c : Fin (m + 1) → K => ψ.complex (-(y ⬝ᵥ c))))

/-- The twisted integral as a linear form in the first vector. -/
def twistedFunctional
    (hcont : ∀ v w, Continuous fun c : Fin (m + 1) → K =>
      β (ξ (radicalElement c : mirabolic (m + 1) K) v) w)
    (hcpt : ∀ v w, HasCompactSupport fun c : Fin (m + 1) → K =>
      β (ξ (radicalElement c : mirabolic (m + 1) K) v) w)
    (y : Fin (m + 1) → K) (w : W) : V →ₗ[ℂ] ℂ where
  toFun v := twistedIntegral μ ψ ξ β y v w
  map_add' v₁ v₂ := by
    unfold twistedIntegral
    simp only [map_add, LinearMap.add_apply, mul_add]
    exact integral_add (integrable_twistedIntegrand μ ψ ξ β hcont hcpt y v₁ w)
      (integrable_twistedIntegrand μ ψ ξ β hcont hcpt y v₂ w)
  map_smul' a v := by
    unfold twistedIntegral
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [← integral_const_mul]
    congr 1
    funext c
    ring

theorem twistedFunctional_apply
    (hcont : ∀ v w, Continuous fun c : Fin (m + 1) → K =>
      β (ξ (radicalElement c : mirabolic (m + 1) K) v) w)
    (hcpt : ∀ v w, HasCompactSupport fun c : Fin (m + 1) → K =>
      β (ξ (radicalElement c : mirabolic (m + 1) K) v) w)
    (y : Fin (m + 1) → K) (w : W) (v : V) :
    twistedFunctional μ ψ ξ β hcont hcpt y w v = twistedIntegral μ ψ ξ β y v w := rfl

/-- Translating `v` by `u(d)` multiplies `J_y` by `ψ(y ⬝ d)`. -/
theorem twistedIntegral_radical (y d : Fin (m + 1) → K) (v : V) (w : W) :
    twistedIntegral μ ψ ξ β y (ξ (radicalElement d : mirabolic (m + 1) K) v) w =
      ψ.complex (y ⬝ᵥ d) * twistedIntegral μ ψ ξ β y v w := by
  unfold twistedIntegral
  rw [← integral_add_right_eq_self (μ := μ) (fun c : Fin (m + 1) → K =>
      ψ.complex (-(y ⬝ᵥ c)) * β (ξ (radicalElement c : mirabolic (m + 1) K) v) w) d,
    ← integral_const_mul]
  congr 1
  funext c
  have hψ : ψ.complex (-(y ⬝ᵥ c)) =
      ψ.complex (y ⬝ᵥ d) * ψ.complex (-(y ⬝ᵥ (c + d))) := by
    rw [← AddChar.map_add_eq_mul, dotProduct_add]
    congr 1
    ring
  rw [rep_radicalElement_mul, hψ]
  ring

end Twisted

/-! ### The left kernel of the transfer integral -/

section Kernel

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData) {m : ℕ}
variable {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- If `β` is nondegenerate in `v` and has compactly supported radical coefficients, a
vector `v` whose transfer integrals `∫ ψ(-c_last) β(ξ(u c) v, w) dc` vanish for every `w`
lies in the `θ_ψ`-relations. -/
theorem mem_relations_of_transferIntegral_eq_zero
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (ξ : Representation ℂ (mirabolic (m + 1) F.Carrier) V)
    (ξ' : Representation ℂ (mirabolic (m + 1) F.Carrier) W) (β : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (s : ℂ)
    (hβ : ∀ (g : mirabolic (m + 1) F.Carrier) (v : V) (w : W),
      β (ξ g v) (ξ' g w) = determinantWeight (normalizedAbsoluteValue T) g.val (-s) * β v w)
    (hnd : ∀ v : V, (∀ w : W, β v w = 0) → v = 0) :
    letI := T.topology
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    haveI : BorelSpace F.Carrier := ⟨rfl⟩
    haveI : SecondCountableTopology F.Carrier := T.secondCountableTopology
    ∀ (μ : Measure (Fin (m + 1) → F.Carrier)) [μ.IsAddHaarMeasure],
      IsSmooth ξ → IsSmooth ξ' →
      (∀ (v : V) (w : W), ∃ N : ℤ, ∀ c ∉ latticeBox T (m + 1) N,
        β (ξ (radicalElement c : mirabolic (m + 1) F.Carrier) v) w = 0) →
      ∀ v : V, (∀ w : W, transferIntegral μ ψ ξ β v w = 0) →
        v ∈ relations ξ (radical (m + 1) F.Carrier) (T.mirabolicTheta ψ m) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have : T2Space F.Carrier := T.fieldT2
  have := T.generalLinearTopologicalGroup (m + 1 + 1)
  let : MeasurableSpace F.Carrier := borel F.Carrier
  have : BorelSpace F.Carrier := ⟨rfl⟩
  have : SecondCountableTopology F.Carrier := T.secondCountableTopology
  intro μ _ hs hs' hsupp v hv
  let abv := normalizedAbsoluteValue T
  -- Haar scaling on the radical coordinates.
  have hχ (a : F.Carrier) (ha : a ≠ 0) :
      (Measure.addHaar : Measure F.Carrier).map (fun x => a * x) =
        (T.normalizedAbsHom a)⁻¹ • Measure.addHaar :=
    HarmonicAnalysis.padicScalarHaarScaling F T Measure.addHaar (Units.mk0 a ha)
  have hscale : ∀ k : Langlands.GeneralLinear (m + 1) F.Carrier,
      μ.map (fun x => k.val *ᵥ x) = (T.normalizedAbsHom (Matrix.det k.val))⁻¹ • μ := by
    intro k
    have h := HarmonicAnalysis.haarMeasure_map_matrix (Measure.addHaar : Measure F.Carrier)
      T.normalizedAbsHom hχ μ (EqualRankFrobenius.det_ne_zero k)
    have e : (fun x => k.val *ᵥ x) = ⇑(Matrix.toLin' k.val) := by
      funext x
      rw [Matrix.toLin'_apply]
    rw [e, h]
  have habv : ∀ a, (T.normalizedAbsHom a : ℝ) = abv a := fun _ => rfl
  -- Continuity and compact support of the radical coefficients.
  have hcont : ∀ v w, Continuous fun c : Fin (m + 1) → F.Carrier =>
      β (ξ (radicalElement c : mirabolic (m + 1) F.Carrier) v) w := by
    intro v w
    obtain ⟨l, hl⟩ := exists_latticeBox_fixes T ξ hs v
    exact continuous_of_forall_add_eq ((isOpen_latticeBox T (m + 1) l).mem_nhds (zero_mem _))
      fun c d hd => by rw [← rep_radicalElement_mul, hl d hd]
  have hcpt : ∀ v w, HasCompactSupport fun c : Fin (m + 1) → F.Carrier =>
      β (ξ (radicalElement c : mirabolic (m + 1) F.Carrier) v) w := by
    intro v w
    obtain ⟨N, hN⟩ := hsupp v w
    exact HasCompactSupport.intro (isCompact_latticeBox T (m + 1) N) hN
  set θ := T.mirabolicTheta ψ m with hθdef
  have hθ : IsOpen (θ.ker : Set (radical (m + 1) F.Carrier)) := T.mirabolicTheta_isOpen_ker ψ m
  have hθu : ∀ d : Fin (m + 1) → F.Carrier,
      (θ (radicalElement d) : ℂ) = ψ.complex (d (Fin.last m)) :=
    fun d => theta_radicalElement ψ m d
  let e : Fin (m + 1) → F.Carrier := Pi.single (Fin.last m) 1
  have he : ∀ c : Fin (m + 1) → F.Carrier, e ⬝ᵥ c = c (Fin.last m) := fun c => by
    simp [e, single_dotProduct]
  -- The twisted integrals of `v` vanish for characters near `θ_ψ`.
  obtain ⟨K₁, hK₁⟩ := hs v
  have hfix : ∀ k ∈ K₁, ξ k v = v := fun k hk =>
    (Representation.mem_invariants _ v).mp hK₁ ⟨k, hk⟩
  obtain ⟨n₀, hn₀⟩ := exists_lastRow_perturbation T
    (levi ⁻¹' (K₁ : Set (mirabolic (m + 1) F.Carrier)))
    (K₁.isOpen.preimage continuous_levi) (by simp)
  have hJv : ∀ (w : W) (y : Fin (m + 1) → F.Carrier), y - e ∈ latticeBox T (m + 1) n₀ →
      twistedIntegral μ ψ ξ β y v w = 0 := by
    intro w y hy
    obtain ⟨h, hh, hhc⟩ := hn₀ (y - e) hy
    have hval := transferIntegral_levi μ ψ ξ ξ' β abv T.normalizedAbsHom habv hscale s hβ hcont
      h v w
    rw [hfix _ hh, hv] at hval
    have hint : ∫ c, ψ.complex (-((h.val *ᵥ c) (Fin.last m))) *
          β (ξ (radicalElement c : mirabolic (m + 1) F.Carrier) v) w ∂μ =
        twistedIntegral μ ψ ξ β y v w := by
      unfold twistedIntegral
      congr 1
      funext c
      rw [hhc c, sub_dotProduct, he, add_sub_cancel]
    rw [hint] at hval
    have hne : determinantWeight abv h (-s) * (abv (Matrix.det h.val) : ℂ) ≠ 0 := by
      refine mul_ne_zero ?_ ?_
      · rw [determinantWeight, Complex.cpow_ne_zero_iff]
        exact Or.inl (Complex.ofReal_ne_zero.mpr (EqualRankFrobenius.abv_det_ne_zero abv h))
      · exact Complex.ofReal_ne_zero.mpr (EqualRankFrobenius.abv_det_ne_zero abv h)
    exact (mul_eq_zero.mp hval.symm).resolve_left hne
  -- The `θ_ψ`-average of `v` over a large radical box.
  let M : ℤ := T.additiveConductor ψ - n₀
  have hM : T.additiveConductor ψ - M = n₀ := by simp [M]
  let H := radicalBox T m M
  have hH := isCompact_radicalBox T m M
  set x := characterAverage hs hθ H hH v with hxdef
  have hxinv : ∀ d ∈ latticeBox T (m + 1) M,
      ξ (radicalElement d : mirabolic (m + 1) F.Carrier) x = ψ.complex (d (Fin.last m)) • x := by
    intro d hd
    have hmem := Compact.averageMap_mem_fixedVectors (twistedRestriction ξ _ θ)
      (isSmooth_twistedRestriction hs hθ) H hH v
    have hu : radicalElement d ∈ H := by
      rw [mem_radicalBox, radicalCoordinates_element]
      exact hd
    have h1 : twistedRestriction ξ _ θ (radicalElement d) x = x :=
      (Representation.mem_invariants _ _).mp hmem ⟨_, hu⟩
    rw [twistedRestriction_apply] at h1
    calc ξ (radicalElement d : mirabolic (m + 1) F.Carrier) x =
          (θ (radicalElement d) : ℂ) • ((θ (radicalElement d) : ℂ)⁻¹ •
            ξ (radicalElement d : mirabolic (m + 1) F.Carrier) x) := by
          rw [smul_smul, mul_inv_cancel₀ (Units.ne_zero _), one_smul]
      _ = _ := by rw [h1, hθu]
  have hx0 : x = 0 := by
    apply hnd
    intro w
    obtain ⟨l, hl⟩ := exists_latticeBox_fixes T ξ hs x
    obtain ⟨N, hN⟩ := hsupp x w
    by_contra hxw
    obtain ⟨y, -, hy⟩ := exists_integral_character_ne_zero T ψ μ
      (fun c => β (ξ (radicalElement c : mirabolic (m + 1) F.Carrier) x) w) l N
      (fun c d hd => by
        show β (ξ (radicalElement (c + d) : mirabolic (m + 1) F.Carrier) x) w =
          β (ξ (radicalElement c : mirabolic (m + 1) F.Carrier) x) w
        rw [← rep_radicalElement_mul, hl d hd]) hN
      (by
        show β (ξ (radicalElement (0 : Fin (m + 1) → F.Carrier) :
          mirabolic (m + 1) F.Carrier) x) w ≠ 0
        rw [rep_radicalElement_zero]
        exact hxw)
    apply hy
    change twistedIntegral μ ψ ξ β y x w = 0
    by_cases hye : y - e ∈ latticeBox T (m + 1) (T.additiveConductor ψ - M)
    · -- On the box, `J_y` is `θ_ψ`-equivariant, so averaging does not change it.
      have h := apply_characterAverage hs hθ H hH (twistedFunctional μ ψ ξ β hcont hcpt y w) v
        (fun n hn => by
          obtain ⟨d, rfl⟩ : ∃ d, radicalElement d = n := ⟨_, radicalElement_coordinates n⟩
          have hd : d ∈ latticeBox T (m + 1) M := by
            rw [mem_radicalBox, radicalCoordinates_element] at hn
            exact hn
          rw [twistedFunctional_apply, twistedFunctional_apply, twistedIntegral_radical, hθu]
          congr 1
          have h1 := character_dotProduct_eq_one T ψ hye hd
          rw [show y = (y - e) + e by abel, add_dotProduct, AddChar.map_add_eq_mul,
            UnitaryAdditiveCharacter.complex_apply ψ ((y - e) ⬝ᵥ d), h1, Circle.coe_one,
            one_mul, he])
      rw [twistedFunctional_apply, twistedFunctional_apply] at h
      rw [h]
      apply hJv w y
      rw [← hM]
      exact hye
    · -- Off the box, `θ_ψ` and the character of `y` differ on the box, killing `J_y(x)`.
      obtain ⟨d, hd, hψd⟩ : ∃ d ∈ latticeBox T (m + 1) M, ψ (d ⬝ᵥ (y - e)) ≠ 1 := by
        by_contra hcon
        push Not at hcon
        exact hye (mem_latticeBox_of_forall_character_eq_one T ψ hcon)
      have h1 := twistedIntegral_radical μ ψ ξ β y d x w
      have hlin : twistedIntegral μ ψ ξ β y (ψ.complex (d (Fin.last m)) • x) w =
          ψ.complex (d (Fin.last m)) * twistedIntegral μ ψ ξ β y x w :=
        (twistedFunctional μ ψ ξ β hcont hcpt y w).map_smul _ x
      have hsplit : ψ.complex (y ⬝ᵥ d) =
          ψ.complex ((y - e) ⬝ᵥ d) * ψ.complex (d (Fin.last m)) := by
        rw [← AddChar.map_add_eq_mul, sub_dotProduct, he, sub_add_cancel]
      rw [hxinv d hd, hlin, hsplit] at h1
      by_contra hJ
      have ha : ψ.complex (d (Fin.last m)) ≠ 0 := by
        rw [UnitaryAdditiveCharacter.complex_apply]
        exact Circle.coe_ne_zero _
      have h2 : ψ.complex ((y - e) ⬝ᵥ d) * ψ.complex (d (Fin.last m)) =
          1 * ψ.complex (d (Fin.last m)) := by
        rw [one_mul]
        exact (mul_right_cancel₀ hJ h1).symm
      have h3 := mul_right_cancel₀ ha h2
      apply hψd
      rw [dotProduct_comm]
      rw [UnitaryAdditiveCharacter.complex_apply] at h3
      exact Circle.coe_eq_one.mp h3
  have hrel := sub_characterAverage_mem hs hθ H hH v
  rw [← hxdef, hx0, sub_zero] at hrel
  exact hrel

end Kernel

/-! ### The descended transfer pairing -/

section Pairing

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData) {m : ℕ}
variable {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- A covariant pairing, nondegenerate in `v`, whose radical coefficients have compact
support, gives a pairing of the `θ_ψ`-coinvariants with covariance `|det|^(1 - s)` under the
successor action that is nondegenerate in the first variable. -/
theorem exists_transferPairing_nondegenerate
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (ξ : Representation ℂ (mirabolic (m + 1) F.Carrier) V)
    (ξ' : Representation ℂ (mirabolic (m + 1) F.Carrier) W) (β : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (s : ℂ)
    (hβ : ∀ (g : mirabolic (m + 1) F.Carrier) (v : V) (w : W),
      β (ξ g v) (ξ' g w) = determinantWeight (normalizedAbsoluteValue T) g.val (-s) * β v w)
    (hnd : ∀ v : V, (∀ w : W, β v w = 0) → v = 0) :
    letI := T.topology
    IsSmooth ξ → IsSmooth ξ' →
      (∀ (v : V) (w : W), ∃ N : ℤ, ∀ c ∉ latticeBox T (m + 1) N,
        β (ξ (radicalElement c : mirabolic (m + 1) F.Carrier) v) w = 0) →
      ∃ B : Coinvariants ξ (radical (m + 1) F.Carrier) (T.mirabolicTheta ψ m) →ₗ[ℂ]
          Coinvariants ξ' (radical (m + 1) F.Carrier) (T.mirabolicTheta ψ m) →ₗ[ℂ] ℂ,
        (∀ (h : mirabolic m F.Carrier) (v : V) (w : W),
          B (mk ξ _ (T.mirabolicTheta ψ m) (ξ (successor h) v))
              (mk ξ' _ (T.mirabolicTheta ψ m) (ξ' (successor h) w)) =
            determinantWeight (normalizedAbsoluteValue T) h.val (-(s - 1)) *
              B (mk ξ _ (T.mirabolicTheta ψ m) v) (mk ξ' _ (T.mirabolicTheta ψ m) w)) ∧
        ∀ x, (∀ y, B x y = 0) → x = 0 := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have : T2Space F.Carrier := T.fieldT2
  have : SecondCountableTopology F.Carrier := T.secondCountableTopology
  let : MeasurableSpace F.Carrier := borel F.Carrier
  have : BorelSpace F.Carrier := ⟨rfl⟩
  intro hs hs' hsupp
  let abv := normalizedAbsoluteValue T
  let μ : Measure (Fin (m + 1) → F.Carrier) := Measure.addHaar
  have hβu : ∀ (d : Fin (m + 1) → F.Carrier) (v : V) (w : W),
      β (ξ (radicalElement d : mirabolic (m + 1) F.Carrier) v)
        (ξ' (radicalElement d : mirabolic (m + 1) F.Carrier) w) = β v w := by
    intro d v w
    rw [hβ, determinantWeight_radicalElement, one_mul]
  -- Haar scaling on the radical coordinates.
  have hχ (a : F.Carrier) (ha : a ≠ 0) :
      (Measure.addHaar : Measure F.Carrier).map (fun x => a * x) =
        (T.normalizedAbsHom a)⁻¹ • Measure.addHaar :=
    HarmonicAnalysis.padicScalarHaarScaling F T Measure.addHaar (Units.mk0 a ha)
  have hscale : ∀ k : Langlands.GeneralLinear (m + 1) F.Carrier,
      μ.map (fun x => k.val *ᵥ x) = (T.normalizedAbsHom (Matrix.det k.val))⁻¹ • μ := by
    intro k
    have h := HarmonicAnalysis.haarMeasure_map_matrix (Measure.addHaar : Measure F.Carrier)
      T.normalizedAbsHom hχ μ (EqualRankFrobenius.det_ne_zero k)
    have e : (fun x => k.val *ᵥ x) = ⇑(Matrix.toLin' k.val) := by
      funext x
      rw [Matrix.toLin'_apply]
    rw [e, h]
  have habv : ∀ a, (T.normalizedAbsHom a : ℝ) = abv a := fun _ => rfl
  have hcont : ∀ v w, Continuous fun c : Fin (m + 1) → F.Carrier =>
      β (ξ (radicalElement c : mirabolic (m + 1) F.Carrier) v) w := by
    intro v w
    obtain ⟨l, hl⟩ := exists_latticeBox_fixes T ξ hs v
    exact continuous_of_forall_add_eq ((isOpen_latticeBox T (m + 1) l).mem_nhds (zero_mem _))
      fun c d hd => by rw [← rep_radicalElement_mul, hl d hd]
  have hcpt : ∀ v w, HasCompactSupport fun c : Fin (m + 1) → F.Carrier =>
      β (ξ (radicalElement c : mirabolic (m + 1) F.Carrier) v) w := by
    intro v w
    obtain ⟨N, hN⟩ := hsupp v w
    exact HasCompactSupport.intro (isCompact_latticeBox T (m + 1) N) hN
  -- The transferred form before descent.
  let ε : mirabolic (m + 1) F.Carrier := levi (-1 : Langlands.GeneralLinear (m + 1) F.Carrier)
  let B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ := (transferForm μ ψ ξ β hcont hcpt).compl₂ (ξ' ε)
  have hB : ∀ v w, B v w = transferIntegral μ ψ ξ β v (ξ' ε w) := fun _ _ => rfl
  have hBl : ∀ (d : Fin (m + 1) → F.Carrier) v w,
      B (ξ (radicalElement d : mirabolic (m + 1) F.Carrier) v) w =
        ψ.complex (d (Fin.last m)) * B v w := by
    intro d v w
    rw [hB, hB, transferIntegral_radical_left]
  have hBr : ∀ (d : Fin (m + 1) → F.Carrier) v w,
      B v (ξ' (radicalElement d : mirabolic (m + 1) F.Carrier) w) =
        ψ.complex (d (Fin.last m)) * B v w := by
    intro d v w
    rw [hB, hB, ← Module.End.mul_apply, ← map_mul, levi_neg_one_mul_radicalElement, map_mul,
      Module.End.mul_apply, transferIntegral_radical_right μ ψ ξ ξ' β hβu,
      transferIntegral_radical_left]
  -- Descent to the coinvariants.
  let Θ := T.mirabolicTheta ψ m
  have hΘ : ∀ u : Mirabolic.radical (m + 1) F.Carrier,
      ∃ d : Fin (m + 1) → F.Carrier, radicalElement d = u ∧
        (Θ u : ℂ) = ψ.complex (d (Fin.last m)) := by
    intro u
    refine ⟨radicalCoordinates u, radicalElement_coordinates u, ?_⟩
    rw [← theta_radicalElement ψ m (radicalCoordinates u), radicalElement_coordinates u]
    rfl
  let B₂ := lift ξ' (Mirabolic.radical (m + 1) F.Carrier) Θ B.flip
    (fun u w => by
      obtain ⟨d, rfl, hd⟩ := hΘ u
      ext v
      rw [LinearMap.smul_apply, LinearMap.flip_apply, LinearMap.flip_apply, hd, smul_eq_mul]
      exact hBr d v w)
  let B₄ := lift ξ (Mirabolic.radical (m + 1) F.Carrier) Θ B₂.flip
    (fun u v => by
      obtain ⟨d, rfl, hd⟩ := hΘ u
      apply hom_ext
      ext w
      change B (ξ (radicalElement d : mirabolic (m + 1) F.Carrier) v) w = (Θ _ : ℂ) • B v w
      rw [hd, smul_eq_mul]
      exact hBl d v w)
  have hB₄ : ∀ v w, B₄ (mk ξ _ Θ v) (mk ξ' _ Θ w) = B v w := fun _ _ => rfl
  refine ⟨B₄, ?_, ?_⟩
  · -- Covariance under the smaller mirabolic group.
    intro h v w
    change B (ξ (successor h) v) (ξ' (successor h) w) =
      determinantWeight abv h.val (-(s - 1)) * B v w
    have hε : ξ' ε (ξ' (successor h) w) = ξ' (successor h) (ξ' ε w) := by
      rw [← Module.End.mul_apply, ← map_mul, show ε * successor h = successor h * ε from
        levi_neg_one_commute _, map_mul, Module.End.mul_apply]
    rw [hB, hB, hε, show successor h = levi (h : Langlands.GeneralLinear (m + 1) F.Carrier) from
      rfl, transferIntegral_levi μ ψ ξ ξ' β abv T.normalizedAbsHom habv hscale s hβ hcont]
    simp only [mulVec_last]
    rw [neg_sub, EqualRankFrobenius.determinantWeight_one_sub]
    unfold transferIntegral
    ring
  · -- Nondegeneracy in the first variable.
    intro x hx
    obtain ⟨v, rfl⟩ := mk_surjective ξ _ Θ x
    rw [mk_eq_zero]
    refine mem_relations_of_transferIntegral_eq_zero T ψ ξ ξ' β s hβ hnd μ hs hs' hsupp v
      (fun w => ?_)
    have h := hx (mk ξ' _ Θ (ξ' ε⁻¹ w))
    rw [hB₄, hB, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Module.End.one_apply] at h
    exact h

end Pairing

/-! ### Normalized `Φ⁻` -/

section Normalized

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- `c • (c • (d X)) = x X` when `c c d = x`. -/
theorem smul_smul_eq_of_eq (c d x X Y : ℂ) (hY : Y = d * X) (hx : c * c * d = x) :
    c • (c • Y) = x * X := by
  rw [hY, ← hx, smul_eq_mul, smul_eq_mul]
  ring

/-- The determinant norm `|det g|` as the determinant weight of exponent `1`. -/
theorem determinantNorm_eq_determinantWeight (T : F.TopologicalData) {n : ℕ}
    (g : GeneralLinear n F.Carrier) :
    ((((T.determinantNorm n) g : ℝ≥0) : ℝ) : ℂ) =
      determinantWeight (normalizedAbsoluteValue T) g (-(-1)) := by
  rw [neg_neg, determinantWeight, Complex.cpow_one, T.determinantNorm_coe]
  rfl

/-- The two normalizing twists `|det h|^(-1/2)` turn covariance `|det h|^2` into `|det h|`. -/
theorem phiMinusCharacter_mul_mul_determinantWeight (T : F.TopologicalData) {m : ℕ}
    (h : mirabolic m F.Carrier) :
    (realPowerCharacter ((T.determinantNorm (m + 1)).comp (mirabolic m F.Carrier).subtype)
        (-(1 / 2 : ℝ)) h : ℂ) *
      (realPowerCharacter ((T.determinantNorm (m + 1)).comp (mirabolic m F.Carrier).subtype)
        (-(1 / 2 : ℝ)) h : ℂ) *
      determinantWeight (normalizedAbsoluteValue T) h.val (-((-1 : ℂ) - 1)) =
    ((((T.determinantNorm (m + 1)) h.val : ℝ≥0) : ℝ) : ℂ) := by
  set x : ℝ := (((T.determinantNorm (m + 1)) h.val : ℝ≥0) : ℝ) with hxdef
  have hx : 0 < x := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero _))
  have hbase : normalizedAbsoluteValue T (Matrix.det h.val.val) = x := by
    rw [hxdef, T.determinantNorm_coe]
    rfl
  have hw : determinantWeight (normalizedAbsoluteValue T) h.val (-((-1 : ℂ) - 1)) =
      ((x ^ (2 : ℝ) : ℝ) : ℂ) := by
    rw [determinantWeight, hbase, Complex.ofReal_cpow hx.le]
    norm_num
  rw [coe_realPowerCharacter, MonoidHom.comp_apply, Subgroup.coe_subtype, ← hxdef, hw,
    ← Complex.ofReal_mul, ← Complex.ofReal_mul]
  congr 1
  rw [← Real.rpow_add hx, ← Real.rpow_add hx]
  norm_num

end Normalized

/-! ### Comparison of `Φ⁻ A(V)` with `Φ⁻ A` -/

section Comparison

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData) {m : ℕ}
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
variable (ρ : Representation ℂ (mirabolic (m + 1) F.Carrier) V)

/-- The map `Φ⁻ A(V) → Φ⁻ A` induced by the inclusion `A(V) ⊆ A`. -/
def radicalPartMap :
    Coinvariants (radicalPart ρ) (radical (m + 1) F.Carrier) (T.mirabolicTheta ψ m) →ₗ[ℂ]
      Coinvariants ρ (radical (m + 1) F.Carrier) (T.mirabolicTheta ψ m) :=
  lift (radicalPart ρ) _ _ (mk ρ _ _ ∘ₗ (relations ρ (radical (m + 1) F.Carrier) 1).subtype)
    (fun u x => mk_apply_subgroup ρ _ _ u x)

theorem radicalPartMap_mk (x : relations ρ (radical (m + 1) F.Carrier) 1) :
    radicalPartMap T ψ ρ (mk (radicalPart ρ) _ _ x) =
      mk ρ _ (T.mirabolicTheta ψ m) (x : V) := rfl

/-- Every class of `Φ⁻ A` comes from `A(V)`: `[a] = (θ(u₀) - 1)⁻¹ [u₀ a - a]`. -/
theorem exists_mk_radicalRelations_eq (v : V) :
    ∃ x : relations ρ (radical (m + 1) F.Carrier) 1,
      mk ρ _ (T.mirabolicTheta ψ m) (x : V) = mk ρ _ (T.mirabolicTheta ψ m) v := by
  let := T.topology
  obtain ⟨t, ht⟩ : ∃ t : F.Carrier, ψ t ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact ψ.nontrivial (DFunLike.ext _ _ fun t => by rw [AddChar.one_apply]; exact hcon t)
  let u₀ : radical (m + 1) F.Carrier := radicalElement (Pi.single (Fin.last m) t)
  have hθ₀ : (T.mirabolicTheta ψ m u₀ : ℂ) = ψ.complex t := by
    have h := theta_radicalElement ψ m (Pi.single (Fin.last m) t)
    rw [Pi.single_eq_same] at h
    exact h
  have hne : (T.mirabolicTheta ψ m u₀ : ℂ) - 1 ≠ 0 := by
    rw [hθ₀, sub_ne_zero, UnitaryAdditiveCharacter.complex_apply]
    exact fun h => ht (Circle.coe_eq_one.mp h)
  have hz : ρ u₀ v - v ∈ relations ρ (radical (m + 1) F.Carrier) 1 := by
    have h := sub_mem_relations ρ (radical (m + 1) F.Carrier) 1 u₀ v
    simpa using h
  refine ⟨((T.mirabolicTheta ψ m u₀ : ℂ) - 1)⁻¹ • ⟨ρ u₀ v - v, hz⟩, ?_⟩
  change mk ρ _ _ (((T.mirabolicTheta ψ m u₀ : ℂ) - 1)⁻¹ • (ρ u₀ v - v)) = mk ρ _ _ v
  rw [map_smul, map_sub, mk_apply_subgroup,
    show (T.mirabolicTheta ψ m u₀ : ℂ) • mk ρ _ (T.mirabolicTheta ψ m) v -
        mk ρ _ (T.mirabolicTheta ψ m) v =
      ((T.mirabolicTheta ψ m u₀ : ℂ) - 1) • mk ρ _ (T.mirabolicTheta ψ m) v by
      rw [sub_smul, one_smul],
    smul_smul, inv_mul_cancel₀ hne, one_smul]

theorem radicalPartMap_surjective : Function.Surjective (radicalPartMap T ψ ρ) := by
  intro a
  obtain ⟨v, rfl⟩ := mk_surjective ρ _ _ a
  obtain ⟨x, hx⟩ := exists_mk_radicalRelations_eq T ψ ρ v
  exact ⟨mk (radicalPart ρ) _ _ x, hx⟩

/-- A vector of `A(V)` that is a `θ_ψ`-relation in `A` is a `θ_ψ`-relation in `A(V)`:
equivariant forms on `A(V)` vanish on such vectors. -/
theorem radicalPartMap_injective :
    letI := T.topology
    IsSmooth ρ → Function.Injective (radicalPartMap T ψ ρ) := by
  let := T.topology
  have := T.generalLinearTopologicalGroup (m + 1 + 1)
  intro hρ
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro y hy
  obtain ⟨x, rfl⟩ := mk_surjective (radicalPart ρ) _ _ y
  rw [radicalPartMap_mk, mk_eq_zero] at hy
  rw [← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro f
  have hV' : ∀ (n : radical (m + 1) F.Carrier) (v : V),
      v ∈ relations ρ (radical (m + 1) F.Carrier) 1 →
        ρ n v ∈ relations ρ (radical (m + 1) F.Carrier) 1 :=
    fun n v hv => radicalRelations_stable ρ n hv
  have hcover : ∀ n : radical (m + 1) F.Carrier, ∃ k : ℕ, n ∈ radicalBox T m k := by
    intro n
    obtain ⟨M, hM⟩ := exists_mem_latticeBox T (radicalCoordinates n)
    exact ⟨M.toNat, radicalBox_mono T m (Int.self_le_toNat M) hM⟩
  exact apply_eq_zero_of_mem_relations hρ (T.mirabolicTheta_isOpen_ker ψ m)
    (fun k : ℕ => radicalBox T m k) (fun k => isCompact_radicalBox T m k)
    (fun j k hjk => radicalBox_mono T m (Nat.cast_le.mpr hjk)) hcover _ hV'
    (f ∘ₗ mk (radicalPart ρ) _ _) (fun n v => by
      change f (mk (radicalPart ρ) _ _ (radicalPart ρ n v)) =
        (T.mirabolicTheta ψ m n : ℂ) * f (mk (radicalPart ρ) _ _ v)
      rw [mk_apply_subgroup, map_smul, smul_eq_mul]) x.property hy

end Comparison

/-! ### Transport of a pairing along a bijection in the first variable -/

section Transport

variable {X : Type*} {X' : Type*} {Y : Type*} [AddCommGroup X] [Module ℂ X]
  [AddCommGroup X'] [Module ℂ X'] [AddCommGroup Y] [Module ℂ Y]

/-- A bilinear form transported along a linear bijection `ι` of the first variable keeps
nondegeneracy in the first variable. -/
theorem exists_transport_left (ι : X →ₗ[ℂ] X') (hι : Function.Bijective ι)
    (B : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ) :
    ∃ γ : X' →ₗ[ℂ] Y →ₗ[ℂ] ℂ, (∀ x y, γ (ι x) y = B x y) ∧
      ((∀ x, (∀ y, B x y = 0) → x = 0) → ∀ x', (∀ y, γ x' y = 0) → x' = 0) := by
  let e := LinearEquiv.ofBijective ι hι
  refine ⟨B ∘ₗ e.symm.toLinearMap, fun x y => ?_, fun hB x' hx' => ?_⟩
  · change B (e.symm (e x)) y = B x y
    rw [e.symm_apply_apply]
  · have h0 : e.symm x' = 0 := hB _ hx'
    rw [← e.apply_symm_apply x', h0, map_zero]

end Transport

/-! ### The pairing of `θ_ψ`-coinvariants -/

section Coinvariant

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData) {m : ℕ}
variable {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- Covariance under the successor action passes from `Φ⁻ A(V)` to `Φ⁻ A`. -/
theorem radicalPartMap_covariance (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (ρ : Representation ℂ (mirabolic (m + 1) F.Carrier) V)
    (σ : Representation ℂ (mirabolic (m + 1) F.Carrier) W)
    (γ : Coinvariants ρ (radical (m + 1) F.Carrier) (T.mirabolicTheta ψ m) →ₗ[ℂ]
      Coinvariants σ (radical (m + 1) F.Carrier) (T.mirabolicTheta ψ m) →ₗ[ℂ] ℂ)
    (B : Coinvariants (radicalPart ρ) (radical (m + 1) F.Carrier) (T.mirabolicTheta ψ m) →ₗ[ℂ]
      Coinvariants σ (radical (m + 1) F.Carrier) (T.mirabolicTheta ψ m) →ₗ[ℂ] ℂ)
    (d : mirabolic m F.Carrier → ℂ)
    (hγ : ∀ x y, γ (radicalPartMap T ψ ρ x) y = B x y)
    (hB : ∀ (h : mirabolic m F.Carrier) (x : relations ρ (radical (m + 1) F.Carrier) 1) (w : W),
      B (mk (radicalPart ρ) _ (T.mirabolicTheta ψ m) (radicalPart ρ (successor h) x))
          (mk σ _ (T.mirabolicTheta ψ m) (σ (successor h) w)) =
        d h * B (mk (radicalPart ρ) _ (T.mirabolicTheta ψ m) x) (mk σ _ (T.mirabolicTheta ψ m) w))
    (h : mirabolic m F.Carrier) (v : V) (w : W) :
    γ (mk ρ _ (T.mirabolicTheta ψ m) (ρ (successor h) v))
        (mk σ _ (T.mirabolicTheta ψ m) (σ (successor h) w)) =
      d h * γ (mk ρ _ (T.mirabolicTheta ψ m) v) (mk σ _ (T.mirabolicTheta ψ m) w) := by
  let := T.topology
  obtain ⟨x₀, hx⟩ := exists_mk_radicalRelations_eq T ψ ρ v
  have hsx : mk ρ _ (T.mirabolicTheta ψ m) (ρ (successor h) v) =
      radicalPartMap T ψ ρ (mk (radicalPart ρ) _ (T.mirabolicTheta ψ m)
        (radicalPart ρ (successor h) x₀)) := by
    rw [radicalPartMap_mk, mk_eq_iff, radicalPart_apply, ← map_sub]
    exact relations_stable ρ _ _ (successorSubgroup m F.Carrier)
      successorSubgroup_le_normalizer (theta_isInvariant ψ m) ⟨successor h, h, rfl⟩
      ((mk_eq_iff ρ _ _ _ _).mp hx.symm)
  have hv : mk ρ _ (T.mirabolicTheta ψ m) v =
      radicalPartMap T ψ ρ (mk (radicalPart ρ) _ (T.mirabolicTheta ψ m) x₀) := hx.symm
  rw [hsx, hv, hγ, hγ]
  exact hB h x₀ w

/-- A pairing of `A` and `B` with covariance `|det|`, nondegenerate in `A`, gives a pairing
of the `θ_ψ`-coinvariants with covariance `|det|^2` under the successor action that is
nondegenerate in the first variable. -/
theorem exists_coinvariantPairing_nondegenerate
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (ρ : Representation ℂ (mirabolic (m + 1) F.Carrier) V)
    (σ : Representation ℂ (mirabolic (m + 1) F.Carrier) W) (β : V →ₗ[ℂ] W →ₗ[ℂ] ℂ)
    (hβ : ∀ (g : mirabolic (m + 1) F.Carrier) (v : V) (w : W),
      β (ρ g v) (σ g w) = determinantWeight (normalizedAbsoluteValue T) g.val (-(-1)) * β v w)
    (hnd : ∀ v : V, (∀ w : W, β v w = 0) → v = 0) :
    letI := T.topology
    IsSmooth ρ → IsSmooth σ →
      ∃ γ : Coinvariants ρ (radical (m + 1) F.Carrier) (T.mirabolicTheta ψ m) →ₗ[ℂ]
          Coinvariants σ (radical (m + 1) F.Carrier) (T.mirabolicTheta ψ m) →ₗ[ℂ] ℂ,
        (∀ (h : mirabolic m F.Carrier) (v : V) (w : W),
          γ ((realPowerCharacter ((T.determinantNorm (m + 1)).comp
                (mirabolic m F.Carrier).subtype) (-(1 / 2 : ℝ)) h : ℂ) •
                mk ρ _ (T.mirabolicTheta ψ m) (ρ (successor h) v))
              ((realPowerCharacter ((T.determinantNorm (m + 1)).comp
                (mirabolic m F.Carrier).subtype) (-(1 / 2 : ℝ)) h : ℂ) •
                mk σ _ (T.mirabolicTheta ψ m) (σ (successor h) w)) =
            ((((T.determinantNorm (m + 1)) h.val : ℝ≥0) : ℝ) : ℂ) *
              γ (mk ρ _ (T.mirabolicTheta ψ m) v) (mk σ _ (T.mirabolicTheta ψ m) w)) ∧
        ∀ x, (∀ y, γ x y = 0) → x = 0 := by
  let := T.topology
  intro hρ hσ
  -- The radical relations `A(V)` and the restricted pairing.
  let A₀ := relations ρ (radical (m + 1) F.Carrier) 1
  have hξ : IsSmooth (radicalPart ρ) :=
    isSmooth_subrepresentation ρ A₀ (radicalRelations_stable ρ) hρ
  let β₀ : A₀ →ₗ[ℂ] W →ₗ[ℂ] ℂ := β ∘ₗ A₀.subtype
  have hβ₀ : ∀ (g : mirabolic (m + 1) F.Carrier) (x : A₀) (w : W),
      β₀ (radicalPart ρ g x) (σ g w) =
        determinantWeight (normalizedAbsoluteValue T) g.val (-(-1)) * β₀ x w :=
    fun g x w => hβ g x w
  have hsupp₀ : ∀ (x : A₀) (w : W), ∃ N : ℤ, ∀ c ∉ latticeBox T (m + 1) N,
      β₀ (radicalPart ρ (radicalElement c : mirabolic (m + 1) F.Carrier) x) w = 0 :=
    fun x w => exists_coefficient_support_of_mem T ρ σ β (-1) hβ hρ hσ x x.property w
  have hnd₀ : ∀ x : A₀, (∀ w : W, β₀ x w = 0) → x = 0 :=
    fun x hx => Subtype.ext (hnd x hx)
  have hex :=
    exists_transferPairing_nondegenerate T ψ (radicalPart ρ) σ β₀ (-1) hβ₀ hnd₀ hξ hσ hsupp₀
  have hcov := hex.choose_spec.1
  have hleft := hex.choose_spec.2
  -- Transport along `Φ⁻ A(V) ≅ Φ⁻ A`.
  have htr := exists_transport_left (radicalPartMap T ψ ρ)
    ⟨radicalPartMap_injective T ψ ρ hρ, radicalPartMap_surjective T ψ ρ⟩ hex.choose
  have hγ := htr.choose_spec.1
  have hcov' := radicalPartMap_covariance T ψ ρ σ htr.choose hex.choose
    (fun h => determinantWeight (normalizedAbsoluteValue T) h.val (-((-1 : ℂ) - 1))) hγ hcov
  refine ⟨htr.choose, fun h v w => ?_, htr.choose_spec.2 hleft⟩
  refine (LinearMap.map_smul₂ _ _ _ _).trans ?_
  refine (congrArg (HSMul.hSMul _) (LinearMap.map_smul _ _ _)).trans ?_
  exact smul_smul_eq_of_eq _ _ _ _ _ (hcov' h v w)
    (phiMinusCharacter_mul_mul_determinantWeight T h)

end Coinvariant

/-- BZ77 §3: a pairing of smooth representations `A`, `B` of `P_(m+2)` with covariance
`|det|` that is nondegenerate in `A` gives a pairing of the normalized `Φ⁻ A` and `Φ⁻ B`
with covariance `|det|` that is nondegenerate in `Φ⁻ A`. -/
theorem phiMinus_nondegeneratePairing {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
    (T : F.TopologicalData) (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (m : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + 1) F.Carrier))
      (B : SmoothRep.{0, uF, uW} ℂ (mirabolic (m + 1) F.Carrier))
      (β : InvariantBilinear.forms A.representation B.representation
        (fun g => ((((T.determinantNorm (m + 1 + 1)) g.val : ℝ≥0) : ℝ) : ℂ))),
      (∀ v : A, (∀ w : B, β.val v w = 0) → v = 0) →
      ∃ γ : InvariantBilinear.forms ((phiMinus T ψ m).obj A).representation
          ((phiMinus T ψ m).obj B).representation
          (fun h => ((((T.determinantNorm (m + 1)) h.val : ℝ≥0) : ℝ) : ℂ)),
        ∀ v : (phiMinus T ψ m).obj A, (∀ w : (phiMinus T ψ m).obj B, γ.val v w = 0) →
          v = 0 := by
  let := T.topology
  intro A B β hnd
  have hβ : ∀ (g : mirabolic (m + 1) F.Carrier) (v : A) (w : B),
      β.val (A.representation g v) (B.representation g w) =
        determinantWeight (normalizedAbsoluteValue T) g.val (-(-1)) * β.val v w := by
    intro g v w
    rw [β.property g v w]
    congr 1
    exact determinantNorm_eq_determinantWeight T g.val
  have hex := exists_coinvariantPairing_nondegenerate T ψ A.representation
    B.representation β.val hβ hnd A.isSmooth B.isSmooth
  have hcov := hex.choose_spec.1
  refine ⟨⟨hex.choose, ?_⟩, hex.choose_spec.2⟩
  -- Covariance: two twists `|det|^(-1/2)` against `|det|^2`.
  intro h a b
  have key : ∀ (v : A) (w : B),
      hex.choose (((phiMinus T ψ m).obj A).representation h (phiMinusQuotient T ψ m A v))
          (((phiMinus T ψ m).obj B).representation h (phiMinusQuotient T ψ m B w)) =
        ((((T.determinantNorm (m + 1)) h.val : ℝ≥0) : ℝ) : ℂ) *
          hex.choose (phiMinusQuotient T ψ m A v) (phiMinusQuotient T ψ m B w) := by
    intro v w
    exact hcov h v w
  rw [← (phiMinusQuotient_surjective T ψ m A a).choose_spec,
    ← (phiMinusQuotient_surjective T ψ m B b).choose_spec]
  exact key _ _

end Langlands.Derivative.Mirabolic
