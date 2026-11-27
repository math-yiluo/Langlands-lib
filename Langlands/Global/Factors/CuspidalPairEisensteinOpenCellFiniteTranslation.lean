import Langlands.Global.Factors.CuspidalPairEisensteinSemilocalCutoff
import Langlands.Global.FiniteAdelicGL.OpenSubgroupInduction
import Langlands.Representation.Twist.ContinuousCharacterProof

/-! # Translating the open-cell integrand by small finite adelic matrices

Let `Z` be an adelic `(t + 1) × (r + 1)` matrix with archimedean component `0` and integral
components at every finite place. This module proves that the open-cell integrand is unchanged
by the translation `Y ↦ Y + Z` when the section is invariant under `u'(Z)` and the additive
character is trivial on the corner entry `Z_(t,0)`, and gives sufficient conditions for both:

* `exists_finiteBox_eq_one`: a continuous additive character of `𝔸` is trivial on the finite
  adeles integral at every place and of valuation `< |a_v|_v` at the places `v` of a finite set;
* `mul_invariant_of_components`: a function right invariant under an open subgroup `J` of
  `GL_n(𝔸_f)` and under `GL_n(𝒪_v)` for `v ∉ S₁` is right invariant under every matrix with
  archimedean component `1`, integral components, and component in `J` at the places of `S₁`;
* `exists_ball_openCellUnipotent_mem`: for an open subgroup `J`, the matrices `u'(y)` placed at
  `v` lie in `J` for all local `y` with entries in a small ball.

See the paired Markdown. -/

noncomputable section

set_option autoImplicit false

universe u

namespace Langlands.Global.CuspidalPairEisenstein.FiniteTranslation

open scoped _root_.Topology
open NumberField Automorphic AdelicBlockParabolic PrimitiveAdelicHeight OpenCellCutoff Oneplace
  OpenCellExhaustion SemilocalCutoff

variable {F : Type u} [Field F] [NumberField F] {r t : ℕ}

section Character

/-- **Continuous additive characters are trivial on a small box of finite adeles.** For a
continuous additive character `ψ` of `𝔸` there are a finite set `T_ψ` of finite places and
nonzero `a_v` with `|a_v|_v ≤ 1` such that `ψ(x) = 1` for every adele `x` with archimedean component `0`, integral
components at every finite place and `|x_v|_v < |a_v|_v` for `v ∈ T_ψ`. -/
theorem exists_finiteBox_eq_one (ψ : AddChar (Adeles F) ℂ) (hψ : Continuous ψ) :
    ∃ (Tψ : Finset (FinitePlace F)) (a : ∀ v : FinitePlace F, FiniteCompletion F v),
      (∀ v, a v ≠ 0 ∧ Valued.v (a v) ≤ 1) ∧
      ∀ x : Adeles F, x.1 = 0 → (∀ v, x.2 v ∈ v.adicCompletionIntegers F) →
        (∀ v ∈ Tψ, Valued.v (x.2 v) < Valued.v (a v)) → ψ x = 1 := by
  classical
  let ι : FiniteAdeles F → Adeles F := fun y => (0, y)
  have hι : Continuous ι := continuous_const.prodMk continuous_id
  let O : Set (FiniteAdeles F) := {y | ‖ψ (ι y) - 1‖ < (1 / 2 : ℝ)}
  have hO : O ∈ 𝓝 (0 : FiniteAdeles F) := by
    refine (isOpen_lt ((hψ.comp hι).sub continuous_const).norm continuous_const).mem_nhds ?_
    change ‖ψ (0, 0) - 1‖ < (1 / 2 : ℝ)
    rw [show ((0, 0) : Adeles F) = 0 from rfl, AddChar.map_zero_eq_one, sub_self, norm_zero]
    norm_num
  let A : ∀ v : FinitePlace F, Set (FiniteCompletion F v) := fun v =>
    (v.adicCompletionIntegers F : Set (FiniteCompletion F v))
  let st : (∀ v : FinitePlace F, A v) → FiniteAdeles F :=
    RestrictedProduct.structureMap (FiniteCompletion F) A Filter.cofinite
  have hst : Continuous st :=
    (RestrictedProduct.isEmbedding_structureMap (R := FiniteCompletion F) (A := A)
      (𝓕 := Filter.cofinite)).continuous
  have hst0 : st 0 = 0 := rfl
  have hO' : st ⁻¹' O ∈ 𝓝 (0 : ∀ v : FinitePlace F, A v) := by
    refine hst.continuousAt.preimage_mem_nhds ?_
    rw [hst0]
    exact hO
  rw [nhds_pi, Filter.mem_pi'] at hO'
  obtain ⟨I, u, hu, hIs⟩ := hO'
  have hball : ∀ v : FinitePlace F, ∃ a : FiniteCompletion F v, a ≠ 0 ∧ Valued.v a ≤ 1 ∧
      ∀ y : A v, Valued.v (y : FiniteCompletion F v) < Valued.v a → y ∈ u v := by
    intro v
    obtain ⟨w, hw, hwu⟩ := (mem_nhds_subtype (A v) 0 (u v)).mp (hu v)
    obtain ⟨a, ha0, ha1, hsub⟩ := exists_ball_subset hw
    exact ⟨a, ha0, ha1, fun y hy => hwu (hsub hy)⟩
  choose a ha0 ha1 ha using hball
  refine ⟨I, a, fun v => ⟨ha0 v, ha1 v⟩, fun x hx1 hxint hxT => ?_⟩
  have key : ∀ y : FiniteAdeles F, (∀ v, y v ∈ v.adicCompletionIntegers F) →
      (∀ v ∈ I, Valued.v (y v) < Valued.v (a v)) → y ∈ O := by
    intro y hyint hyT
    let z : ∀ v : FinitePlace F, A v := fun v => ⟨y v, hyint v⟩
    have hz : st z = y := rfl
    rw [← hz]
    exact hIs fun v hv => ha v (z v) (hyT v hv)
  have hx : x = ι x.2 := Prod.ext hx1 rfl
  rw [hx]
  apply Langlands.complex_eq_one_of_forall_norm_pow_sub_one_lt
  intro n
  rw [← AddChar.map_nsmul_eq_pow]
  have e : n • ι x.2 = ι (n • x.2) := Prod.ext (by simp [ι]) rfl
  rw [e]
  refine key (n • x.2) (fun v => ?_) (fun v hv => ?_)
  · exact (v.adicCompletionIntegers F).toSubring.nsmul_mem (hxint v) n
  · have hne : Valued.v (a v) ≠ 0 := (Valuation.ne_zero_iff _).mpr (ha0 v)
    exact (Valued.v.ltAddSubgroup (Units.mk0 _ hne)).nsmul_mem (hxT v hv) n

end Character

section Invariance

/-- **Invariance under matrices with small finite components.** Let `φ` be right invariant
under an open subgroup `J` of `GL_n(𝔸_f)` and under `GL_n(𝒪_v)`, placed at `v`, for every
finite place `v ∉ S₁`. Then `φ` is right invariant under every adelic matrix `a` with
archimedean component `1`, integral components at every finite place, and component in `J`
(placed at `v`) at every `v ∈ S₁`. -/
theorem mul_invariant_of_components {n : ℕ} {φ : AdelicGL F n → ℂ}
    (J : OpenSubgroup (FiniteAdelicGL F n))
    (hJ : ∀ (j : J) (g : AdelicGL F n), φ (g * AdelicGL.ofFinite F n j.val) = φ g)
    {S₁ : Finset (FinitePlace F)}
    (hsph : ∀ v ∉ S₁, ∀ k ∈ FiniteAdelicGL.localIntegral F n v, ∀ g : AdelicGL F n,
      φ (g * AdelicGL.ofFinite F n (FiniteAdelicGL.localInclusion F n v k)) = φ g)
    {a : AdelicGL F n} (ha : AdelicGL.infinite F n a = 1)
    (hint : ∀ v, comp F n v a ∈ FiniteAdelicGL.localIntegral F n v)
    (hS₁ : ∀ v ∈ S₁, FiniteAdelicGL.localInclusion F n v (comp F n v a) ∈ J)
    (g : AdelicGL F n) : φ (g * a) = φ g := by
  classical
  obtain ⟨T, hT⟩ := FiniteAdelicGL.exists_finset_forall_mem J
  suffices key : ∀ T' : Finset (FinitePlace F), ∀ a : AdelicGL F n,
      AdelicGL.infinite F n a = 1 →
      (∀ v, comp F n v a ∈ FiniteAdelicGL.localIntegral F n v) →
      (∀ v ∈ S₁, FiniteAdelicGL.localInclusion F n v (comp F n v a) ∈ J) →
      (∀ v ∈ T, v ∉ T' → comp F n v a = 1) → ∀ g, φ (g * a) = φ g from
    key T a ha hint hS₁ (fun v hv hv' => absurd hv hv') g
  intro T'
  induction T' using Finset.induction_on with
  | empty =>
    intro a ha hint _ hT1 g
    have hmem : AdelicGL.finite F n a ∈ J :=
      hT _ (fun v hv => hT1 v hv (Finset.notMem_empty v)) (fun v => hint v)
    have e : a = AdelicGL.ofFinite F n (AdelicGL.finite F n a) := by
      refine adelic_ext ?_ fun w => ?_
      · rw [ha, RankinSelbergGlobal.LocalPointFactorization.infinite_ofFinite]
      · change _ = FiniteAdelicGL.localProjection F n w
          (AdelicGL.finite F n (AdelicGL.ofFinite F n (AdelicGL.finite F n a)))
        rw [RankinSelbergGlobal.LocalPointFactorization.finite_ofFinite]
        rfl
    rw [e]
    exact hJ ⟨_, hmem⟩ g
  | insert w T' hw ih =>
    intro a ha hint hS₁ hT1 g
    set x := comp F n w a with hx
    set a' := (adelicAt F n w x)⁻¹ * a with ha'
    have hsplit : a = adelicAt F n w x * a' := by rw [ha', mul_inv_cancel_left]
    have hcomp : ∀ v, comp F n v a' = if v = w then 1 else comp F n v a := by
      intro v
      rw [ha', map_mul, map_inv]
      split_ifs with hvw
      · subst hvw
        rw [comp_adelicAt, inv_mul_cancel]
      · rw [comp_adelicAt_of_ne n hvw, inv_one, one_mul]
    have h' := ih a'
      (by rw [ha', map_mul, map_inv, infinite_adelicAt, inv_one, one_mul, ha])
      (fun v => by
        rw [hcomp]
        split_ifs
        exacts [one_mem _, hint v])
      (fun v hv => by
        rw [hcomp]
        split_ifs
        · rw [map_one]
          exact one_mem _
        · exact hS₁ v hv)
      (fun v hv hv' => by
        rw [hcomp]
        split_ifs with hvw
        · rfl
        · exact hT1 v hv (by simp [hvw, hv']))
    rw [hsplit, ← mul_assoc, h' (g * adelicAt F n w x)]
    by_cases hwS : w ∈ S₁
    · exact hJ ⟨_, hS₁ w hwS⟩ g
    · exact hsph w hwS x (hint w) g

/-- For an open subgroup `J` of `GL_(r+t+2)(𝔸_f)` and a finite place `v`, the matrices `u'(y)`
placed at `v` lie in `J` for every local `y` with entries in a ball `{x | |x|_v < |a|_v}`,
`a ≠ 0`, `|a|_v ≤ 1`. -/
theorem exists_ball_openCellUnipotent_mem (J : OpenSubgroup (FiniteAdelicGL F (r + t + 2)))
    (v : FinitePlace F) :
    ∃ a : FiniteCompletion F v, a ≠ 0 ∧ Valued.v a ≤ 1 ∧
      ∀ y : Matrix (Fin (t + 1)) (Fin (r + 1)) (FiniteCompletion F v),
        (∀ i j, Valued.v (y i j) < Valued.v a) →
        FiniteAdelicGL.localInclusion F (r + t + 2) v (GeneralLinear.reindex (blockEquiv r t)
          (Shahidi.intertwiningUnipotent (r + 1) (t + 1) (FiniteCompletion F v) y)) ∈ J := by
  let f : Matrix (Fin (t + 1)) (Fin (r + 1)) (FiniteCompletion F v) →
      FiniteAdelicGL F (r + t + 2) := fun y =>
    FiniteAdelicGL.localInclusion F (r + t + 2) v (GeneralLinear.reindex (blockEquiv r t)
      (Shahidi.intertwiningUnipotent (r + 1) (t + 1) (FiniteCompletion F v) y))
  have hc : Continuous f :=
    (FiniteAdelicGL.localInclusion F (r + t + 2) v).continuous.comp
      ((GeneralLinear.reindexContinuous (R := FiniteCompletion F v) (blockEquiv r t)).continuous.comp
        (Shahidi.continuous_intertwiningUnipotent (r + 1) (t + 1) (FiniteCompletion F v)))
  have h0 : f 0 = 1 := by
    simp only [f, Shahidi.intertwiningUnipotent_zero, map_one]
  have hmem : f ⁻¹' (J : Set (FiniteAdelicGL F (r + t + 2))) ∈
      𝓝 (0 : Matrix (Fin (t + 1)) (Fin (r + 1)) (FiniteCompletion F v)) := by
    refine hc.continuousAt.preimage_mem_nhds ?_
    rw [h0]
    exact J.isOpen.mem_nhds J.one_mem
  obtain ⟨a, ha0, ha1, hsub⟩ := exists_matrix_ball_subset hmem
  exact ⟨a, ha0, ha1, fun y hy => hsub hy⟩

end Invariance

section Translation

/-- The archimedean component of `u'(Z)` is `1` when `Z` has archimedean component `0`. -/
theorem infinite_openCellUnipotent {Z : Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)}
    (hZ : ∀ i j, (Z i j).1 = 0) :
    AdelicGL.infinite F (r + t + 2) (openCellUnipotent F r t Z) = 1 := by
  rw [show AdelicGL.infinite F (r + t + 2) (openCellUnipotent F r t Z) =
      GeneralLinear.reindex (blockEquiv r t)
        (Shahidi.intertwiningUnipotent (r + 1) (t + 1) (InfiniteAdeleRing F)
          (Z.map (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeles F)))) from
    (map_reindex _ _ _).trans (congrArg _ (map_intertwiningUnipotent _ _ _ _))]
  have h0 : Z.map (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeles F)) = 0 := by
    funext i j
    exact hZ i j
  rw [h0, Shahidi.intertwiningUnipotent_zero, map_one]

/-- The component of `u'(Z)` at `v` is integral when `Z_v` is integral. -/
theorem comp_openCellUnipotent_mem {Z : Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)}
    {v : FinitePlace F} (hZ : ∀ i j, matrixComponent v Z i j ∈ v.adicCompletionIntegers F) :
    comp F (r + t + 2) v (openCellUnipotent F r t Z) ∈
      FiniteAdelicGL.localIntegral F (r + t + 2) v := by
  rw [comp_openCellUnipotent]
  exact reindex_mem_localIntegral v (intertwiningUnipotent_mem_integralGroup
    (CompletionPadic.padicField v) r t _
      (fun i j => (mem_adicCompletionIntegers_iff_canonical v _).1 (hZ i j)))

/-- `u'(Z)` lies in the standard maximal compact subgroup when `Z` has archimedean component
`0` and integral components at every finite place. -/
theorem openCellUnipotent_mem_standardCompact
    {Z : Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)} (hZ : ∀ i j, (Z i j).1 = 0)
    (hint : ∀ v i j, matrixComponent v Z i j ∈ v.adicCompletionIntegers F) :
    openCellUnipotent F r t Z ∈ standardCompact F (r + t + 2) := by
  rw [mem_standardCompact_iff]
  refine ⟨?_, ?_⟩
  · rw [infinite_openCellUnipotent hZ]
    exact one_mem _
  · rw [FiniteAdelicGL.mem_standardIntegral_iff_local]
    exact fun v => comp_openCellUnipotent_mem (hint v)

/-- **Translation invariance of the open-cell integrand.** If the twisted section `φ · H^s`
is right invariant under `u'(Z)` and `ψ(Z_(t,0)) = 1`, the open-cell integrand at `Y + Z` equals
the integrand at `Y`. -/
theorem openCellIntegrand_add_of_invariant (ψ : AddChar (Adeles F) ℂ)
    (φ : AdelicGL F (r + t + 2) → ℂ) (s : ℂ) (Y Z : Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F))
    (hφ : ∀ g, twisted φ s (g * openCellUnipotent F r t Z) = twisted φ s g)
    (hψ : ψ (Z (Fin.last t) 0) = 1) :
    openCellIntegrand ψ φ s (Y + Z) = openCellIntegrand ψ φ s Y := by
  rw [openCellIntegrand_eq, openCellIntegrand_eq, openCellUnipotent_add, ← mul_assoc,
    leviWhittaker_mul_right_of_invariant _ _ _ _ hφ, Matrix.add_apply,
    AddChar.map_add_eq_mul, hψ, mul_one]

/-- The twisted section `φ · H^s` is right invariant under `u'(Z)` for `Z` with archimedean
component `0`, integral components, and `u'(Z_v)` in `J` at the places of `S₁`, when `φ` is
right invariant under `J` and spherical outside `S₁`. -/
theorem twisted_mul_openCellUnipotent {φ : AdelicGL F (r + t + 2) → ℂ}
    (J : OpenSubgroup (FiniteAdelicGL F (r + t + 2)))
    (hJ : ∀ (j : J) (g : AdelicGL F (r + t + 2)),
      φ (g * AdelicGL.ofFinite F (r + t + 2) j.val) = φ g)
    {S₁ : Finset (FinitePlace F)} (hsph : IsSphericalOutside F r t S₁ φ) (s : ℂ)
    {Z : Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)} (hZ : ∀ i j, (Z i j).1 = 0)
    (hint : ∀ v i j, matrixComponent v Z i j ∈ v.adicCompletionIntegers F)
    (hS₁ : ∀ v ∈ S₁, FiniteAdelicGL.localInclusion F (r + t + 2) v
      (comp F (r + t + 2) v (openCellUnipotent F r t Z)) ∈ J)
    (g : AdelicGL F (r + t + 2)) :
    twisted φ s (g * openCellUnipotent F r t Z) = twisted φ s g := by
  unfold twisted
  rw [heightPower_mul_compact s g _ (openCellUnipotent_mem_standardCompact hZ hint),
    mul_invariant_of_components J hJ hsph (infinite_openCellUnipotent hZ)
      (fun v => comp_openCellUnipotent_mem (hint v)) hS₁ g]

end Translation

end Langlands.Global.CuspidalPairEisenstein.FiniteTranslation
