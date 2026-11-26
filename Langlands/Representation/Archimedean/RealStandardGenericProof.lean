import Langlands.Representation.Archimedean.RealCharacterStandardGeneric
import Langlands.Representation.Archimedean.RealTailKernelGrowth
import Langlands.Representation.Archimedean.RealIrreducibleStandardGenericStatement
import Langlands.Representation.Archimedean.RealStandardCentralGrowth
import Langlands.Representation.Archimedean.RealWhittakerMaximallyFaithfulProof
import Langlands.Representation.Archimedean.BGChaseReps
import Langlands.Representation.Archimedean.RealExponentDeformation
import Langlands.Representation.Archimedean.RealStandardNontrivialProof
import Langlands.Global.RankinSelberg.RealCanonicalWhittakerComparison

/-! # Real standard modules are generic -/

noncomputable section

open scoped TensorProduct Matrix Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean Langlands.Algebra.UniversalEnveloping

namespace RealStandardGeneric

/-! ## Descending a Whittaker functional along a surjective intertwiner -/

section Descent

variable {n : ℕ} {ds es : List RealBlock}

/-- A nonzero Whittaker functional on the source of a surjective intertwiner of standard
modules that vanishes on its kernel descends to a nonzero Whittaker functional on the
target. -/
theorem isRealGeneric_of_surjective
    (T : kFiniteFunctions (realStandardModule n es) (unitaryCompact ℝ n) →ₗ[ℂ]
      kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n))
    (hT : Function.Surjective T)
    (hI : IsRealStandardIntertwiner n (realStandardRep n ds) (realStandardLie n ds) es T)
    (ℓ : kFiniteFunctions (realStandardModule n es) (unitaryCompact ℝ n) →ₗ[ℂ] ℂ)
    (hℓ0 : ℓ ≠ 0) (a : Fin n → ℝ) (ha : ∀ i : Fin n, (i : ℕ) + 1 < n → a i ≠ 0)
    (hW : ∀ X : Matrix (Fin n) (Fin n) ℝ, (∀ i j : Fin n, (j : ℕ) ≤ i → X i j = 0) →
      ∀ v, ℓ (realStandardLie n es (1 ⊗ₜ X) v) =
        (Complex.I * ((∑ i : Fin n, ∑ j : Fin n,
          if (j : ℕ) = i + 1 then a i * X i j else 0 : ℝ) : ℂ)) * ℓ v)
    (hker : ∀ v, T v = 0 → ℓ v = 0) :
    IsRealGenericGKModule n (realStandardLie n ds) := by
  have hle : LinearMap.ker T ≤ LinearMap.ker ℓ := fun v hv => hker v hv
  let ℓ' := ((LinearMap.ker T).liftQ ℓ hle).comp
    (T.quotKerEquivOfSurjective hT).symm.toLinearMap
  have hℓ' : ∀ v, ℓ' (T v) = ℓ v := by
    intro v
    have h : (T.quotKerEquivOfSurjective hT).symm (T v) = Submodule.Quotient.mk v := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    simp only [ℓ', LinearMap.comp_apply, LinearEquiv.coe_coe, h, Submodule.liftQ_apply]
  refine ⟨ℓ', fun h0 => hℓ0 (LinearMap.ext fun v => ?_), a, ha, fun X hX w => ?_⟩
  · rw [← hℓ' v, h0, LinearMap.zero_apply, LinearMap.zero_apply]
  · obtain ⟨v, rfl⟩ := hT w
    rw [← hI.map_realStandardLie, hℓ', hℓ', hW X hX v]

set_option backward.isDefEq.respectTransparency false in
/-- Equal standard modules have the same Whittaker functionals. -/
theorem isRealGeneric_of_module_eq (h : realStandardModule n es = realStandardModule n ds)
    (hes : IsRealGenericGKModule n (realStandardLie n es)) :
    IsRealGenericGKModule n (realStandardLie n ds) := by
  have hK : kFiniteFunctions (realStandardModule n es) (unitaryCompact ℝ n) =
      kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n) := by rw [h]
  obtain ⟨e, he⟩ := exists_linearEquiv_coe_eq hK
  obtain ⟨ℓ, hℓ0, a, ha, hW⟩ := hes
  refine ⟨ℓ ∘ₗ e.symm.toLinearMap, fun h0 => hℓ0 (LinearMap.ext fun v => ?_), a, ha,
    fun X hX w => ?_⟩
  · have := LinearMap.congr_fun h0 (e v)
    simpa using this
  · have hc : e.symm (realStandardLie n ds (1 ⊗ₜ X) w) =
        realStandardLie n es (1 ⊗ₜ X) (e.symm w) := by
      apply Subtype.ext
      have h1 := he (e.symm (realStandardLie n ds (1 ⊗ₜ X) w))
      rw [LinearEquiv.apply_symm_apply] at h1
      have h3 : ((realStandardLie n ds (1 ⊗ₜ X) w : kFiniteFunctions (realStandardModule n ds)
          (unitaryCompact ℝ n)) : Langlands.GeneralLinear n ℝ → ℂ) =
          rightDerivative (matrixModel ℝ n) X (w : Langlands.GeneralLinear n ℝ → ℂ) :=
            kFiniteLie_one_tmul_apply_coe _ _ _ _ X w
      have h4 : ((realStandardLie n es (1 ⊗ₜ X) (e.symm w) : kFiniteFunctions
          (realStandardModule n es) (unitaryCompact ℝ n)) : Langlands.GeneralLinear n ℝ → ℂ) =
          rightDerivative (matrixModel ℝ n) X
            ((e.symm w : kFiniteFunctions (realStandardModule n es) (unitaryCompact ℝ n)) :
              Langlands.GeneralLinear n ℝ → ℂ) :=
        kFiniteLie_one_tmul_apply_coe _ _ _ _ X (e.symm w)
      have h2 := he (e.symm w)
      rw [LinearEquiv.apply_symm_apply] at h2
      rw [← h1, h3, h4, h2]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hc, hW X hX]

end Descent

/-! ## Kostant's theorem on a stable subspace -/

section Restrict

variable {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Let `K` be a subspace stable under a representation `π` with an infinitesimal character,
and let `ℓ` be a Whittaker functional on `K` for a nondegenerate character that is nonzero on
`K`. Every element of `U(𝔤)` annihilating `K` lies in the ideal generated by the central
elements annihilating `V`. -/
theorem mem_span_center_of_whittaker_on
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V) (K : Submodule ℂ V)
    (hK : ∀ Y, ∀ w ∈ K, π Y w ∈ K) (hinf : HasInfinitesimalCharacter π) (ℓ : V →ₗ[ℂ] ℂ)
    {w₀ : V} (hw₀ : w₀ ∈ K) (hℓw₀ : ℓ w₀ ≠ 0)
    (a : Fin n → ℝ) (ha : ∀ i : Fin n, (i : ℕ) + 1 < n → a i ≠ 0)
    (hW : ∀ X : Matrix (Fin n) (Fin n) ℝ, (∀ i j : Fin n, (j : ℕ) ≤ i → X i j = 0) →
      ∀ w ∈ K, ℓ (π (1 ⊗ₜ X) w) =
        (Complex.I * ((∑ i : Fin n, ∑ j : Fin n,
          if (j : ℕ) = i + 1 then a i * X i j else 0 : ℝ) : ℂ)) * ℓ w)
    (u : UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ))
    (hu : ∀ w ∈ K, envelopingAction π u w = 0) :
    u ∈ Ideal.span {z | z ∈ Subalgebra.center ℂ
      (UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ)) ∧
        envelopingAction π z = 0} := by
  let πK := BGChase.restrictLie π K hK
  have hsub : ∀ u (w : K), ((envelopingAction πK u w : K) : V) = envelopingAction π u w :=
    fun u w => envelopingAction_intertwine πK π K.subtype (fun _ _ => rfl) u w
  have hinfK : HasInfinitesimalCharacter πK := by
    intro z hz
    obtain ⟨c0, hc0⟩ := hinf z hz
    refine ⟨c0, LinearMap.ext fun w => Subtype.ext ?_⟩
    rw [hsub, hc0]
    rfl
  have hgenK : IsRealGenericGKModule n πK := by
    refine ⟨ℓ ∘ₗ K.subtype, fun h0 => hℓw₀ ?_, a, ha, fun X hX w => hW X hX w w.2⟩
    simpa using LinearMap.congr_fun h0 ⟨w₀, hw₀⟩
  have hmf := Kostant.realWhittakerMaximallyFaithful n K πK hinfK hgenK
  have hu' : envelopingAction πK u = 0 := LinearMap.ext fun w => Subtype.ext (by
    rw [hsub]
    exact hu w w.2)
  refine Ideal.span_mono ?_ (hmf u hu')
  rintro z ⟨hzc, hz⟩
  refine ⟨hzc, ?_⟩
  obtain ⟨c0, hc0⟩ := hinf z hzc
  have hw : envelopingAction π z w₀ = 0 := by
    rw [← hsub z ⟨w₀, hw₀⟩, hz]
    rfl
  rw [hc0] at hw ⊢
  have hw₀0 : w₀ ≠ 0 := fun h => hℓw₀ (by rw [h, map_zero])
  have hc : c0 = 0 := by
    rw [Module.algebraMap_end_apply] at hw
    exact (smul_eq_zero.mp hw).resolve_right hw₀0
  rw [hc, map_zero]

end Restrict

/-! ## Slowly growing kernels carry no Whittaker functional -/

section SlowKernel

open RealStandardCentralGrowth RealLinkedQuotientGrowth

variable {n : ℕ} {cs es : List RealBlock}

/-- Let `T` be an intertwiner of real standard modules whose kernel grows slowly: the
operators of degree `≤ k` of `U(𝔤)` restricted to `ker T` span a space of dimension
`O((k + 1)^(n (n - 1) - 1))`, and `n ≥ 2`. Then every Whittaker functional for a
nondegenerate character on the source vanishes on `ker T`. -/
theorem whittaker_eq_zero_of_slowKernel
    (T : kFiniteFunctions (realStandardModule n cs) (unitaryCompact ℝ n) →ₗ[ℂ]
      kFiniteFunctions (realStandardModule n es) (unitaryCompact ℝ n))
    (hI : IsRealStandardIntertwiner n (realStandardRep n es) (realStandardLie n es) cs T)
    (hN : 2 ≤ n) (C : ℝ)
    (hC : ∀ k : ℕ,
      (Module.finrank ℂ ((degreeFiltration ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) k).map
        (LinearMap.lcomp ℂ _ (LinearMap.ker T).subtype ∘ₗ
          (envelopingAction (realStandardLie n cs)).toLinearMap)) : ℝ) ≤
        C * ((k : ℝ) + 1) ^ (n * (n - 1) - 1))
    (ℓ : kFiniteFunctions (realStandardModule n cs) (unitaryCompact ℝ n) →ₗ[ℂ] ℂ)
    (a : Fin n → ℝ) (ha : ∀ i : Fin n, (i : ℕ) + 1 < n → a i ≠ 0)
    (hW : ∀ X : Matrix (Fin n) (Fin n) ℝ, (∀ i j : Fin n, (j : ℕ) ≤ i → X i j = 0) →
      ∀ v, ℓ (realStandardLie n cs (1 ⊗ₜ X) v) =
        (Complex.I * ((∑ i : Fin n, ∑ j : Fin n,
          if (j : ℕ) = i + 1 then a i * X i j else 0 : ℝ) : ℂ)) * ℓ v)
    (v : kFiniteFunctions (realStandardModule n cs) (unitaryCompact ℝ n)) (hv : T v = 0) :
    ℓ v = 0 := by
  by_contra hℓv
  have hKX : ∀ Y, ∀ w ∈ LinearMap.ker T, realStandardLie n cs Y w ∈ LinearMap.ker T :=
    fun Y w hw => by
      rw [LinearMap.mem_ker, hI.map_realStandardLie, LinearMap.mem_ker.mp hw, map_zero]
  have hv0 : v ≠ 0 := fun h0 => hℓv (by rw [h0, map_zero])
  obtain ⟨c0, hc0, hlow⟩ := realStandardCentralGrowth n cs ⟨v, hv0⟩
  have hspan : ∀ u, (LinearMap.lcomp ℂ _ (LinearMap.ker T).subtype ∘ₗ
      (envelopingAction (realStandardLie n cs)).toLinearMap) u = 0 →
        u ∈ realStandardCentralIdeal n cs := fun u hTu =>
    mem_span_center_of_whittaker_on (realStandardLie n cs) (LinearMap.ker T) hKX
      (realStandardLie_hasInfinitesimalCharacter n cs) ℓ (LinearMap.mem_ker.mpr hv) hℓv a ha
      (fun X hX w _ => hW X hX w) u fun w hw => by
        have h1 := LinearMap.congr_fun hTu ⟨w, hw⟩
        simp only [LinearMap.comp_apply, LinearMap.lcomp_apply, LinearMap.zero_apply,
          Submodule.subtype_apply, AlgHom.toLinearMap_apply] at h1
        exact h1
  have hlow' := fun k => hlow k (LinearMap.lcomp ℂ _ (LinearMap.ker T).subtype ∘ₗ
    (envelopingAction (realStandardLie n cs)).toLinearMap) fun u _ hu => hspan u hu
  exact not_forall_le hc0 (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)))
    hlow' hC (fun k => le_of_eq (by congr 1))

end SlowKernel

/-! ## Genericity of all real standard modules -/

section Main

open RealInducedCharacter RealBlockFrobeniusMap RealTailKernel

/-- A real standard module of rank zero is generic. -/
theorem isRealGeneric_rankZero (ds : List RealBlock) (hr : realRank ds = 0) :
    IsRealGenericGKModule 0 (realStandardLie 0 ds) := by
  have := realStandardNontrivial 0 ds hr
  obtain ⟨v, hv⟩ := exists_ne (0 : kFiniteFunctions (realStandardModule 0 ds)
    (unitaryCompact ℝ 0))
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ (kFiniteFunctions (realStandardModule 0 ds)
      (unitaryCompact ℝ 0)), φ v ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hv ((Module.forall_dual_apply_eq_zero_iff ℂ v).1 h)
  refine ⟨φ, fun h0 => hφ (by rw [h0, LinearMap.zero_apply]), fun _ => 0,
    fun i => Fin.elim0 i, fun X _ w => ?_⟩
  have hX : X = 0 := Subsingleton.elim _ _
  simp [hX]

open Langlands.Global.RankinSelbergGlobal.RealPrincipalSeries in
/-- A list of real character blocks gives a generic standard module. -/
theorem isRealGeneric_characters (n : ℕ) (cs : List RealCharacterData)
    (hr : realRank (cs.map RealBlock.character) = n) :
    IsRealGenericGKModule n (realStandardLie n (cs.map RealBlock.character)) := by
  rcases n with _ | r
  · exact isRealGeneric_rankZero _ hr
  · obtain ⟨p, z, he⟩ :=
      exists_characterList_of_map_character cs hr
    rw [he]
    exact isRealGeneric_characterList r p z

/-- The parity `(|m| + 1) mod 2` of the second character of the ascending pair of an
induction block of weight `m` whose first character is even. -/
def tailParity (d : ComplexCharacterData) : Fin 2 :=
  ⟨(d.weight.natAbs + 1) % 2, Nat.mod_lt _ (by norm_num)⟩

theorem tailParity_spec (d : ComplexCharacterData) :
    ((tailParity d).val + (0 : Fin 2).val) % 2 = (d.weight.natAbs + 1) % 2 := by
  simp [tailParity]

/-- The inductive step: a list of character blocks followed by an arbitrary list. -/
theorem isRealGeneric_append :
    ∀ (ds : List RealBlock) (cs : List RealCharacterData) (n : ℕ),
      realRank (cs.map RealBlock.character ++ ds) = n →
        IsRealGenericGKModule n (realStandardLie n (cs.map RealBlock.character ++ ds))
  | [], cs, n, hr => by
    rw [List.append_nil] at hr ⊢
    exact isRealGeneric_characters n cs hr
  | .character c :: ds, cs, n, hr => by
    have he : cs.map RealBlock.character ++ RealBlock.character c :: ds =
        (cs ++ [c]).map RealBlock.character ++ ds := by simp
    rw [he] at hr ⊢
    exact isRealGeneric_append ds (cs ++ [c]) n hr
  | .induced d :: ds, cs, n, hr => by
    by_cases hw : d.weight = 0
    · have hmod := realStandardModule_append_expand n (cs.map RealBlock.character) ds
        (.induced d)
      simp only [realBlockExpand, hw, ↓reduceIte] at hmod
      let cs' := cs ++ [RealJacquetFrobenius.charData 1 d.exponent,
        RealJacquetFrobenius.charData 0 d.exponent]
      have he : cs.map RealBlock.character ++ [RealBlock.character
          (RealJacquetFrobenius.charData 1 d.exponent), RealBlock.character
          (RealJacquetFrobenius.charData 0 d.exponent)] ++ ds =
          cs'.map RealBlock.character ++ ds := by simp [cs']
      rw [he] at hmod
      have hr' : realRank (cs'.map RealBlock.character ++ ds) = n := by
        rw [← hr]
        simp only [cs', List.map_append, realRank_append, List.map_cons, List.map_nil,
          realRank_cons, realRank_nil, RealBlock.rank]
        omega
      exact isRealGeneric_of_module_eq hmod.symm (isRealGeneric_append ds cs' n hr')
    · have hl : 0 < d.weight.natAbs := Int.natAbs_pos.mpr hw
      set pre := cs.map RealBlock.character with hpre
      have hn : realRank (pre ++ [RealBlock.induced d] ++ ds) = n := by simpa using hr
      have hs := tailParity_spec d
      let cs' := cs ++ [cb d 0, ca d (tailParity d)]
      have he : tailList pre ds d (tailParity d) 0 = cs'.map RealBlock.character ++ ds := by
        simp [tailList, cs', pre]
      have hr' : realRank (cs'.map RealBlock.character ++ ds) = n := by
        rw [← he]
        exact realRank_tail_mid hn
      have hgen := isRealGeneric_append ds cs' n hr'
      rw [← he] at hgen
      obtain ⟨ℓ, hℓ0, a, ha, hW⟩ := hgen
      have hI := RealExponentDeformation.isRealStandardIntertwiner_of_modulo_bot
        (modulo_tail hn hl hs)
      have hN : 2 ≤ n := by have := (data_tail hn hl hs).lt; omega
      obtain ⟨C, hC⟩ := tailKernel_growth hn hl hs
      have hgoal := isRealGeneric_of_surjective _ (tail_surjective hn hl hs) hI ℓ hℓ0 a ha hW
        (fun v hv => whittaker_eq_zero_of_slowKernel _ hI hN C hC ℓ a ha hW v hv)
      have he2 : pre ++ RealBlock.induced d :: ds = pre ++ [RealBlock.induced d] ++ ds := by
        simp
      rw [he2]
      exact hgoal

end Main

end RealStandardGeneric

open RealStandardGeneric in
/-- **Every real standard module is generic.** The `O(n)`-finite functions of the standard
module of any list of real blocks of rank `n` carry a nonzero Whittaker functional for a
nondegenerate unitary character. -/
theorem isRealGeneric_realStandardLie (n : ℕ) (ds : List RealBlock) (hr : realRank ds = n) :
    IsRealGenericGKModule n (realStandardLie n ds) := by
  have h := isRealGeneric_append ds [] n (by simpa using hr)
  rwa [List.map_nil, List.nil_append] at h

/-- **Irreducible real standard modules are generic**, as a special case of
`isRealGeneric_realStandardLie`. -/
theorem realIrreducibleStandardGeneric : RealIrreducibleStandardGenericStatement :=
  fun n ds hr _ => isRealGeneric_realStandardLie n ds hr

end Langlands.Archimedean
