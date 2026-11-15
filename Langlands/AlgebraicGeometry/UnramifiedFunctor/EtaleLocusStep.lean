import Langlands.AlgebraicGeometry.UnramifiedFunctor.EtaleLocusCaseA

/-! # The inductive step of the case of a non-nilpotent prime

With the notation of `EtaleLocusCaseA`: if `c` is an Artin–Rees constant for `𝔍 ⊆ R'` and
`I` (so that `𝔍 ∩ I^m ⊆ I 𝔍` for `m ≥ c + 1`), then for `n ≥ c` vanishing of `𝔍` in the stalk
at level `n` implies vanishing at level `n + 1` (`van_succ`). -/

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite IsLocalRing

noncomputable section

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor

namespace EtaleLocus

variable {R : CommRingCat.{u}} {F : (Over (Spec R))ᵒᵖ ⥤ Type v}
  {R' : Type u} [CommRing R'] [Algebra R R'] {𝔍 : Ideal R'} [IsNoetherianRing R']
  (I : Ideal R')

/-- The inductive step: `VanN n w` implies `VanN (n + 1) w` for `n ≥ c`. -/
theorem van_succ (Lvs : ∀ n : ℕ, Level F (Ideal.Quotient.mk (I ^ (n + 1))))
    (ξ : F.obj (op (chart R R' 𝔍))) (w : Spec (CommRingCat.of (R' ⧸ 𝔍)))
    [Fact (I ≤ primeOf 𝔍 w)] (c : ℕ) (hAR : ∀ m ≥ c + 1, 𝔍 ⊓ I ^ m ≤ I * 𝔍) (n : ℕ)
    (hn : c ≤ n) (hv : VanN 𝔍 I Lvs ξ n w) : VanN 𝔍 I Lvs ξ (n + 1) w := by
  have hw : I ≤ primeOf 𝔍 w := Fact.out
  have : IsLocallyNoetherian (Lvs (n + 1)).X :=
    LocallyOfFiniteType.isLocallyNoetherian (Lvs (n + 1)).q
  -- notation for the two levels
  let d := nDatum R 𝔍 I n w
  let d' := nDatum R 𝔍 I (n + 1) w
  have hψ'θ' : ∀ r : R', (d'.ψ ξ (Lvs (n + 1))).hom ((d'.θ ξ (Lvs (n + 1))).hom
      (Ideal.Quotient.mk _ r)) = Ideal.Quotient.mk _ (algebraMap R' (Ow 𝔍 w) r) :=
    fun r => d'.ψ_θ_apply ξ _ _
  -- the extension `θt : O_w → Λ'`
  have hunit : ∀ s : (primeOf 𝔍 w).primeCompl, IsUnit (((d'.θ ξ (Lvs (n + 1))).hom.comp
      (Ideal.Quotient.mk (I ^ (n + 1 + 1)))) s) := by
    intro s
    apply isUnit_of_map_unit (d'.ψ ξ (Lvs (n + 1))).hom
    rw [RingHom.comp_apply, hψ'θ']
    exact (IsLocalization.map_units (Ow 𝔍 w) s).map _
  obtain ⟨θt, hθtdef⟩ : ∃ θt : Ow 𝔍 w →+* (Lvs (n + 1)).X.presheaf.stalk (d'.pt ξ (Lvs (n + 1))),
      θt = IsLocalization.lift (M := (primeOf 𝔍 w).primeCompl) (S := Ow 𝔍 w) hunit :=
    ⟨_, rfl⟩
  have hθtcomp : θt.comp (algebraMap R' (Ow 𝔍 w)) =
      (d'.θ ξ (Lvs (n + 1))).hom.comp (Ideal.Quotient.mk (I ^ (n + 1 + 1))) := by
    rw [hθtdef]
    exact IsLocalization.lift_comp hunit
  have hθt : ∀ r, θt (algebraMap R' (Ow 𝔍 w) r) =
      (d'.θ ξ (Lvs (n + 1))).hom (Ideal.Quotient.mk _ r) := fun r => RingHom.congr_fun hθtcomp r
  have hψθt : (d'.ψ ξ (Lvs (n + 1))).hom.comp θt = Ideal.Quotient.mk _ := by
    apply ringHom_ext_Ow w
    ext r
    simp only [RingHom.comp_apply]
    rw [hθt]
    exact hψ'θ' r
  -- the ideal `J' = I^(n+1) Λ'`
  obtain ⟨J', hJ'⟩ : ∃ J' : Ideal ((Lvs (n + 1)).X.presheaf.stalk (d'.pt ξ (Lvs (n + 1)))),
      J' = (I ^ (n + 1)).map ((d'.θ ξ (Lvs (n + 1))).hom.comp (Ideal.Quotient.mk _)) :=
    ⟨_, rfl⟩
  have hmkloc : IsLocalHom (Ideal.Quotient.mk
      ((𝔍 ⊔ I ^ (n + 1 + 1)).map (algebraMap R' (Ow 𝔍 w)))) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have hJ'max : J' ≤ maximalIdeal _ := by
    rw [hJ', Ideal.map_le_iff_le_comap]
    intro i hi
    rw [Ideal.mem_comap, RingHom.comp_apply, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have h1 := hu.map (d'.ψ ξ (Lvs (n + 1))).hom
    rw [hψ'θ'] at h1
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (Ow 𝔍 w) (primeOf 𝔍 w) i).1
      (isUnit_of_map_unit _ _ h1) (hw (Ideal.pow_le_self n.succ_ne_zero hi))
  have : Nontrivial ((Lvs (n + 1)).X.presheaf.stalk (d'.pt ξ (Lvs (n + 1))) ⧸ J') :=
    Ideal.Quotient.nontrivial_iff.2 (ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top hJ'max)
  have : IsLocalRing ((Lvs (n + 1)).X.presheaf.stalk (d'.pt ξ (Lvs (n + 1))) ⧸ J') :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J') Ideal.Quotient.mk_surjective
  -- the map `δb : R'/I^(n+1) → Λ'/J'`
  have hδb0 : ∀ a ∈ I ^ (n + 1), ((Ideal.Quotient.mk J').comp ((d'.θ ξ (Lvs (n + 1))).hom.comp
      (Ideal.Quotient.mk (I ^ (n + 1 + 1))))) a = 0 := by
    intro a ha
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, hJ']
    exact Ideal.mem_map_of_mem _ ha
  let δb : R' ⧸ I ^ (n + 1) →+* (Lvs (n + 1)).X.presheaf.stalk (d'.pt ξ (Lvs (n + 1))) ⧸ J' :=
    Ideal.Quotient.lift _ _ hδb0
  -- the element on `Spec (Λ'/J')` from level `n + 1`
  let t' : Spec (CommRingCat.of ((Lvs (n + 1)).X.presheaf.stalk (d'.pt ξ (Lvs (n + 1))) ⧸ J')) ⟶
      Spec (CommRingCat.of (R' ⧸ I ^ (n + 1 + 1))) :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J')) ≫ Spec.map (d'.θ ξ (Lvs (n + 1)))
  have ht' : t' ≫ levelMap R (Ideal.Quotient.mk (I ^ (n + 1 + 1))) =
      (Over.mk (Spec.map (CommRingCat.ofHom δb) ≫ levelMap R (Ideal.Quotient.mk (I ^ (n + 1))))).hom := by
    change (Spec.map _ ≫ Spec.map _) ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    simp only [← Spec.map_comp]
    rfl
  have ha' : (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J')) ≫
      (Lvs (n + 1)).X.fromSpecStalk (d'.pt ξ (Lvs (n + 1)))) ≫ (Lvs (n + 1)).q = t' := by
    rw [Category.assoc, ← specMap_structMap]
    rfl
  let a' : Over.mk t' ⟶ Over.mk (Lvs (n + 1)).q := Over.homMk _ ha'
  let z := Charts.elemEquiv (levelMap R (Ideal.Quotient.mk (I ^ (n + 1 + 1)))) (Lvs (n + 1)).e
    (Over.mk (Spec.map (CommRingCat.ofHom δb) ≫ levelMap R (Ideal.Quotient.mk (I ^ (n + 1))))) t'
    ht' a'
  -- the map `π : Λ'/J' → L_n`
  have h𝔟 : (𝔍 ⊔ I ^ (n + 1 + 1)).map (algebraMap R' (Ow 𝔍 w)) ≤
      (𝔍 ⊔ I ^ (n + 1)).map (algebraMap R' (Ow 𝔍 w)) :=
    Ideal.map_mono (sup_le_sup_left (Ideal.pow_le_pow_right (by omega)) _)
  let κ : Ln 𝔍 I (n + 1) w →+* Ln 𝔍 I n w := Ideal.Quotient.factor h𝔟
  have hπ0 : ∀ a ∈ J', (κ.comp (d'.ψ ξ (Lvs (n + 1))).hom) a = 0 := by
    have : J' ≤ RingHom.ker (κ.comp (d'.ψ ξ (Lvs (n + 1))).hom) := by
      rw [hJ', Ideal.map_le_iff_le_comap]
      intro i hi
      rw [Ideal.mem_comap, RingHom.mem_ker, RingHom.comp_apply, RingHom.comp_apply, hψ'θ']
      change Ideal.Quotient.mk _ (algebraMap R' (Ow 𝔍 w) i) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_map_of_mem _ (Ideal.mem_sup_right hi)
    exact fun a ha => this ha
  let π : (Lvs (n + 1)).X.presheaf.stalk (d'.pt ξ (Lvs (n + 1))) ⧸ J' →+* Ln 𝔍 I n w :=
    Ideal.Quotient.lift J' _ hπ0
  have hπsurj : Function.Surjective π := by
    intro l
    obtain ⟨o, rfl⟩ := Ideal.Quotient.mk_surjective l
    obtain ⟨b, hb⟩ := d'.ψ_surjective ξ (Lvs (n + 1)) (Ideal.Quotient.mk _ o)
    exact ⟨Ideal.Quotient.mk J' b, by
      change κ ((d'.ψ ξ (Lvs (n + 1))).hom b) = _
      rw [hb]
      rfl⟩
  have : IsLocalHom π := IsLocalHom.of_surjective π hπsurj
  have hπδ : π.comp δb = d.δ := by
    apply Ideal.Quotient.ringHom_ext
    ext r
    change κ ((d'.ψ ξ (Lvs (n + 1))).hom ((d'.θ ξ (Lvs (n + 1))).hom (Ideal.Quotient.mk _ r))) = _
    rw [hψ'θ']
    rfl
  -- comparison of the elements on `Spec L_n`
  have hk₂ : Spec.map (CommRingCat.ofHom π) ≫
      (Over.mk (Spec.map (CommRingCat.ofHom δb) ≫ levelMap R (Ideal.Quotient.mk (I ^ (n + 1))))).hom =
      d.f := by
    change Spec.map (CommRingCat.ofHom π) ≫ Spec.map (CommRingCat.ofHom δb) ≫ _ = _
    rw [← Category.assoc, specMap_ofHom_comp, hπδ, d.hT]
  let k₂ : Over.mk d.f ⟶ Over.mk (Spec.map (CommRingCat.ofHom δb) ≫
      levelMap R (Ideal.Quotient.mk (I ^ (n + 1)))) :=
    Over.homMk (Spec.map (CommRingCat.ofHom π)) hk₂
  have ht₁ : (k₂.left ≫ t') ≫ levelMap R (Ideal.Quotient.mk (I ^ (n + 1 + 1))) =
      (Over.mk d.f).hom := by
    rw [Category.assoc, ht']
    exact Over.w k₂
  have e1 := elemEquiv_naturality' (levelMap R (Ideal.Quotient.mk (I ^ (n + 1 + 1))))
    (Lvs (n + 1)).e k₂ (k₂.left ≫ t') t' ht₁ ht' rfl a'
  have hk₃ : Spec.map (CommRingCat.ofHom κ) ≫ d'.f = d.f := by
    change Spec.map (CommRingCat.ofHom κ) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R' (Ln 𝔍 I (n + 1) w))) ≫ baseMap R R' =
      Spec.map (CommRingCat.ofHom (algebraMap R' (Ln 𝔍 I n w))) ≫ baseMap R R'
    rw [← Category.assoc, specMap_ofHom_comp]
    rfl
  let k₃ : Over.mk d.f ⟶ Over.mk d'.f := Over.homMk (Spec.map (CommRingCat.ofHom κ)) hk₃
  have ht₃ : (Spec.map (CommRingCat.ofHom κ) ≫ Spec.map (CommRingCat.ofHom d'.δ)) ≫
      levelMap R (Ideal.Quotient.mk (I ^ (n + 1 + 1))) = (Over.mk d.f).hom := by
    rw [Category.assoc, d'.hT]
    exact hk₃
  have e2 := d'.map_ζ ξ (Lvs (n + 1)) k₃ _ ht₃ rfl
  have e3 : F.map k₃.op (d'.ζ ξ) = d.ζ ξ := by
    have hk : k₃ ≫ homU d'.ℓ d'.f d'.hf = homU d.ℓ d.f d.hf := by
      ext1
      change Spec.map (CommRingCat.ofHom κ) ≫ Spec.map (CommRingCat.ofHom d'.ℓ) =
        Spec.map (CommRingCat.ofHom d.ℓ)
      rw [specMap_ofHom_comp]
      congr 2
      apply Ideal.Quotient.ringHom_ext
      ext r
      rfl
    rw [LocalDatum.ζ, LocalDatum.ζ, ← Functor.map_comp_apply, ← op_comp, hk]
  have e4 : Charts.elemEquiv (levelMap R (Ideal.Quotient.mk (I ^ (n + 1 + 1)))) (Lvs (n + 1)).e
      (Over.mk d.f) (k₂.left ≫ t') ht₁ ((Over.homMk k₂.left rfl : Over.mk _ ⟶ Over.mk t') ≫ a') =
      Charts.elemEquiv (levelMap R (Ideal.Quotient.mk (I ^ (n + 1 + 1)))) (Lvs (n + 1)).e
      (Over.mk d.f) _ ht₃ ((Over.homMk k₃.left rfl :
        Over.mk _ ⟶ Over.mk (Spec.map (CommRingCat.ofHom d'.δ))) ≫ d'.mor ξ (Lvs (n + 1))) := by
    apply elemEquiv_congr
    change Spec.map (CommRingCat.ofHom π) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J')) ≫
        (Lvs (n + 1)).X.fromSpecStalk (d'.pt ξ (Lvs (n + 1))) =
      Spec.map (CommRingCat.ofHom κ) ≫ (d'.mor ξ (Lvs (n + 1))).left
    rw [LocalDatum.mor_left, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
    congr 2
  have hz : F.map k₂.op z = d.ζ ξ := e1.trans (e4.trans (e2.symm.trans e3))
  have hkt : k₂.left ≫ Spec.map (CommRingCat.ofHom δb) = Spec.map (CommRingCat.ofHom d.δ) := by
    change Spec.map (CommRingCat.ofHom π) ≫ Spec.map (CommRingCat.ofHom δb) = _
    rw [specMap_ofHom_comp, hπδ]
  have hleft := d.left_of_map_eq ξ (Lvs n) (Spec.map (CommRingCat.ofHom δb)) rfl z k₂ hkt hz
  have hpt := d.pt_eq_of ξ (Lvs n) _ π hleft
  obtain ⟨χ, -, -, hχ⟩ := exists_stalkHom (Lvs n).q _ δb (Over.w _) _ hpt
  -- `θ'(𝔍) ⊆ J'`
  have hJ : ∀ j ∈ 𝔍, (d'.θ ξ (Lvs (n + 1))).hom (Ideal.Quotient.mk _ j) ∈ J' := by
    intro j hj
    have e : χ.hom ((d.θ ξ (Lvs n)).hom (Ideal.Quotient.mk _ j)) =
        δb (Ideal.Quotient.mk _ j) := congrArg (fun φ => φ.hom (Ideal.Quotient.mk _ j)) hχ
    rw [hv j hj, map_zero] at e
    exact Ideal.Quotient.eq_zero_iff_mem.1 e.symm
  -- the kernel of `ψ'` and surjectivity of `θt`
  have hK' := d'.ker_ψ_le ξ (Lvs (n + 1))
  have h𝔍J' : Ideal.map ((d'.θ ξ (Lvs (n + 1))).hom.comp (Ideal.Quotient.mk _)) 𝔍 ≤ J' :=
    Ideal.map_le_iff_le_comap.2 fun j hj => hJ j hj
  have hmap : ((I ^ (n + 1)).map (algebraMap R' (Ow 𝔍 w))).map θt = J' := by
    rw [Ideal.map_map, hθtcomp, hJ']
  have hJ'2 : J' ^ 2 = ⊥ := by
    rw [hJ', ← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker]
    intro i hi
    have hi' : i ∈ I ^ (n + 1 + 1) := by
      rw [← pow_mul] at hi
      exact Ideal.pow_le_pow_right (by omega) hi
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 hi', map_zero]
  have hsurj : Function.Surjective θt := by
    refine surjective_of_isNilpotent_map θt ((I ^ (n + 1)).map (algebraMap R' (Ow 𝔍 w)))
      (by rw [hmap]; exact ⟨2, hJ'2⟩) fun b => ?_
    obtain ⟨o, ho⟩ := Ideal.Quotient.mk_surjective ((d'.ψ ξ (Lvs (n + 1))).hom b)
    refine ⟨o, ?_⟩
    rw [hmap]
    apply h𝔍J'
    apply hK'
    rw [RingHom.mem_ker, map_sub, ← RingHom.comp_apply _ θt, hψθt, ho, sub_self]
  -- the kernel `Q` of `θt`
  have hQ1 : (I ^ (n + 1 + 1)).map (algebraMap R' (Ow 𝔍 w)) ≤ RingHom.ker θt := by
    rw [Ideal.map_le_iff_le_comap]
    intro i hi
    rw [Ideal.mem_comap, RingHom.mem_ker, hθt, Ideal.Quotient.eq_zero_iff_mem.2 hi, map_zero]
  have hQ2 : RingHom.ker θt ≤ 𝔍.map (algebraMap R' (Ow 𝔍 w)) ⊔
      (I ^ (n + 1 + 1)).map (algebraMap R' (Ow 𝔍 w)) := by
    intro o ho
    have : Ideal.Quotient.mk ((𝔍 ⊔ I ^ (n + 1 + 1)).map (algebraMap R' (Ow 𝔍 w))) o = 0 := by
      rw [← hψθt, RingHom.comp_apply, RingHom.mem_ker.1 ho, map_zero]
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.map_sup] at this
    exact this
  have h𝔍 : 𝔍.map (algebraMap R' (Ow 𝔍 w)) ≤
      RingHom.ker θt ⊔ (I ^ (n + 1)).map (algebraMap R' (Ow 𝔍 w)) := by
    rw [Ideal.map_le_iff_le_comap]
    intro j hj
    have h1 : θt (algebraMap R' (Ow 𝔍 w) j) ∈
        ((I ^ (n + 1)).map (algebraMap R' (Ow 𝔍 w))).map θt := by
      rw [hmap, hθt]
      exact hJ j hj
    obtain ⟨x, hx, hxe⟩ := (Ideal.mem_map_iff_of_surjective θt hsurj).1 h1
    rw [Ideal.mem_comap]
    refine Submodule.mem_sup.2 ⟨algebraMap R' (Ow 𝔍 w) j - x, ?_, x, hx, sub_add_cancel _ _⟩
    rw [RingHom.mem_ker, map_sub, hxe, sub_self]
  -- Artin–Rees in `O_w`
  have hAR' : 𝔍.map (algebraMap R' (Ow 𝔍 w)) ⊓ (I ^ (n + 1)).map (algebraMap R' (Ow 𝔍 w)) ≤
      I.map (algebraMap R' (Ow 𝔍 w)) * 𝔍.map (algebraMap R' (Ow 𝔍 w)) := by
    rw [← IsLocalization.map_inf (primeOf 𝔍 w).primeCompl, ← Ideal.map_mul]
    exact Ideal.map_mono (hAR (n + 1) (by omega))
  have hle : 𝔍.map (algebraMap R' (Ow 𝔍 w)) ≤
      RingHom.ker θt ⊔ I.map (algebraMap R' (Ow 𝔍 w)) • 𝔍.map (algebraMap R' (Ow 𝔍 w)) := by
    intro x hx
    obtain ⟨q, hq, a, ha, rfl⟩ := Submodule.mem_sup.1 (h𝔍 hx)
    obtain ⟨j', hj', b, hb, hqe⟩ := Submodule.mem_sup.1 (hQ2 hq)
    have hb𝔦 : b ∈ (I ^ (n + 1)).map (algebraMap R' (Ow 𝔍 w)) :=
      Ideal.map_mono (Ideal.pow_le_pow_right (by omega)) hb
    have hab : a + b ∈ 𝔍.map (algebraMap R' (Ow 𝔍 w)) ⊓
        (I ^ (n + 1)).map (algebraMap R' (Ow 𝔍 w)) := by
      refine ⟨?_, add_mem ha hb𝔦⟩
      have : a + b = (q + a) - j' := by rw [← hqe]; ring
      rw [this]
      exact sub_mem hx hj'
    have hsplit : q + a = (q - b) + (a + b) := by ring
    rw [hsplit]
    refine Submodule.add_mem_sup (sub_mem hq (hQ1 hb)) ?_
    rw [Ideal.smul_eq_mul]
    exact hAR' hab
  have hIjac : I.map (algebraMap R' (Ow 𝔍 w)) ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top,
      ← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.map_mono hw
  have hfinal : 𝔍.map (algebraMap R' (Ow 𝔍 w)) ≤ RingHom.ker θt :=
    Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _) hIjac hle
  intro j hj
  have := hfinal (Ideal.mem_map_of_mem _ hj)
  rw [RingHom.mem_ker, hθt] at this
  exact this

end EtaleLocus

end Langlands.AlgebraicGeometry.UnramifiedFunctor
