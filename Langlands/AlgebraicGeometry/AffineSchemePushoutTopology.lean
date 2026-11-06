import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import Mathlib.RingTheory.LocalRing.Pullback
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.Category.TopCat.Limits.Pullbacks

open CategoryTheory Limits Topology PrimeSpectrum

universe u

namespace Langlands.AlgebraicGeometry.AffineSchemePushout

variable {B C D : Type u} [CommRing B] [CommRing C] [CommRing D]
  (f : B →+* D) (g : C →+* D)

/-- Away from the kernel of the second projection, a prime lifts to the first factor. -/
theorem exists_comap_pullbackFst_eq
    (p : PrimeSpectrum (f.pullback g))
    (h : ¬ RingHom.ker (f.pullbackSnd g) ≤ p.asIdeal) :
    ∃ q : PrimeSpectrum B, comap (f.pullbackFst g) q = p := by
  classical
  obtain ⟨t, ht, htp⟩ := SetLike.not_le_iff_exists.mp h
  have htC : t.val.2 = 0 := ht
  have htB : f t.val.1 = 0 := by
    have he : f t.val.1 = g t.val.2 := t.property
    rw [htC, map_zero] at he
    exact he
  let m : B → f.pullback g := fun b ↦ ⟨(t.val.1 * b, 0), by simp [htB]⟩
  have m_one : m 1 = t := by
    apply Subtype.ext
    exact Prod.ext (mul_one _) htC.symm
  have m_mul (b c : B) : m (b * c) * t = m b * m c := by
    apply Subtype.ext
    apply Prod.ext <;> simp [m, htC]
    ring
  have m_proj (x : f.pullback g) : m ((f.pullbackFst g) x) = t * x := by
    apply Subtype.ext
    apply Prod.ext <;> simp [m, htC]
  let q : Ideal B :=
    { carrier := {b | m b ∈ p.asIdeal}
      zero_mem' := by
        change m 0 ∈ p.asIdeal
        have he : m 0 = 0 := by apply Subtype.ext; simp [m]
        rw [he]
        exact p.asIdeal.zero_mem
      add_mem' := by
        intro b c hb hc
        change m (b + c) ∈ p.asIdeal
        have he : m (b + c) = m b + m c := by
          apply Subtype.ext
          apply Prod.ext <;> simp [m, mul_add]
        exact he ▸ p.asIdeal.add_mem hb hc
      smul_mem' := by
        intro b c hc
        change m (b * c) ∈ p.asIdeal
        have he : m (b * c) * t ∈ p.asIdeal := by
          rw [m_mul]
          exact p.asIdeal.mul_mem_left _ hc
        exact (p.isPrime.mem_or_mem he).resolve_right htp }
  have hq : q.IsPrime :=
    { ne_top' := by
        intro he
        have hm : m 1 ∈ p.asIdeal := (show (1 : B) ∈ q from he ▸ Submodule.mem_top)
        exact htp (m_one ▸ hm)
      mem_or_mem' := by
        intro b c hbc
        change m (b * c) ∈ p.asIdeal at hbc
        have he : m b * m c ∈ p.asIdeal := by
          rw [← m_mul]
          exact p.asIdeal.mul_mem_right _ hbc
        exact p.isPrime.mem_or_mem he }
  refine ⟨⟨q, hq⟩, ?_⟩
  apply PrimeSpectrum.ext
  apply Ideal.ext
  intro x
  change m ((f.pullbackFst g) x) ∈ p.asIdeal ↔ x ∈ p.asIdeal
  rw [m_proj]
  exact ⟨fun hx ↦ (p.isPrime.mem_or_mem hx).resolve_left htp,
    fun hx ↦ p.asIdeal.mul_mem_left _ hx⟩

/-- The spectra of the two factors jointly cover the spectrum of the pullback. -/
theorem jointly_surjective_comap_pullback
    (hf : Function.Surjective f) (p : PrimeSpectrum (f.pullback g)) :
    (∃ q : PrimeSpectrum B, comap (f.pullbackFst g) q = p) ∨
      (∃ q : PrimeSpectrum C, comap (f.pullbackSnd g) q = p) := by
  classical
  by_cases h : RingHom.ker (f.pullbackSnd g) ≤ p.asIdeal
  · right
    have hp : p ∈ Set.range (comap (f.pullbackSnd g)) := by
      rw [range_comap_of_surjective C _ (f.surjective_pullbackSnd_of_surjective g hf)]
      exact h
    exact hp
  · exact Or.inl (exists_comap_pullbackFst_eq f g p h)

/-- The topology of the pullback spectrum is final for the two projection spectra. -/
theorem isOpen_iff_comap_pullback (hf : Function.Surjective f)
    (s : Set (PrimeSpectrum (f.pullback g))) :
    IsOpen s ↔
      IsOpen (comap (f.pullbackFst g) ⁻¹' s) ∧
      IsOpen (comap (f.pullbackSnd g) ⁻¹' s) := by
  classical
  refine ⟨fun hs ↦ ⟨hs.preimage (continuous_comap _), hs.preimage (continuous_comap _)⟩, ?_⟩
  rintro ⟨hB, hC⟩
  have hcomm (q : PrimeSpectrum D) :
      comap (f.pullbackFst g) (comap f q) =
        comap (f.pullbackSnd g) (comap g q) := by
    rw [← comap_comp_apply, RingHom.pullback_comm_sq, comap_comp_apply]
  apply isTopologicalBasis_basic_opens.isOpen_iff.mpr
  intro p hp
  by_cases hk : RingHom.ker (f.pullbackSnd g) ≤ p.asIdeal
  · have hpr : p ∈ Set.range (comap (f.pullbackSnd g)) := by
      rw [range_comap_of_surjective C _ (f.surjective_pullbackSnd_of_surjective g hf)]
      exact hk
    obtain ⟨qC, rfl⟩ := hpr
    obtain ⟨_, ⟨c, rfl⟩, hc, hcU⟩ :=
      isTopologicalBasis_basic_opens.isOpen_iff.mp hC qC hp
    obtain ⟨I, hI⟩ := (isClosed_iff_zeroLocus_ideal _).mp hB.isClosed_compl
    have hrad : g c ∈ (I.map f).radical := by
      rw [← vanishingIdeal_zeroLocus_eq_radical, mem_vanishingIdeal]
      intro q hq
      have hqB : comap (f.pullbackFst g) (comap f q) ∉ s := by
        change comap f q ∈ (comap (f.pullbackFst g) ⁻¹' s)ᶜ
        rw [hI]
        intro b hb
        exact hq (Ideal.mem_map_of_mem f hb)
      have hqC : comap g q ∉ comap (f.pullbackSnd g) ⁻¹' s := by
        change comap (f.pullbackSnd g) (comap g q) ∉ s
        rwa [← hcomm]
      by_contra hgc
      exact hqC (hcU hgc)
    obtain ⟨n, hn⟩ := hrad
    have hn' : g c ^ (n + 1) ∈ I.map f := by
      rw [pow_succ]
      exact (I.map f).mul_mem_right _ hn
    obtain ⟨b, hb, hbc⟩ := (Ideal.mem_map_iff_of_surjective f hf).mp hn'
    let a : f.pullback g := ⟨(b, c ^ (n + 1)), by simpa using hbc⟩
    refine ⟨basicOpen a, ⟨a, rfl⟩, ?_, ?_⟩
    · change c ^ (n + 1) ∉ qC.asIdeal
      exact (le_basicOpen_pow c (n + 1)) hc
    · intro p hp
      rcases jointly_surjective_comap_pullback f g hf p with ⟨qB, rfl⟩ | ⟨qC, rfl⟩
      · by_contra hnot
        have hz : qB ∈ zeroLocus (I : Set B) := hI ▸ hnot
        exact hp (hz hb)
      · exact hcU (by
          change qC ∈ basicOpen (c ^ (n + 1)) at hp
          rwa [basicOpen_pow _ _ (Nat.succ_pos n)] at hp)
  · obtain ⟨t, ht, htp⟩ := SetLike.not_le_iff_exists.mp hk
    obtain ⟨qB, rfl⟩ := exists_comap_pullbackFst_eq f g p hk
    obtain ⟨_, ⟨b, rfl⟩, hb, hbU⟩ :=
      isTopologicalBasis_basic_opens.isOpen_iff.mp hB qB hp
    have htC : t.val.2 = 0 := ht
    have htB : f t.val.1 = 0 := by
      have he : f t.val.1 = g t.val.2 := t.property
      rw [htC, map_zero] at he
      exact he
    let a : f.pullback g := ⟨(t.val.1 * b, 0), by simp [htB]⟩
    refine ⟨basicOpen a, ⟨a, rfl⟩, ?_, ?_⟩
    · change t.val.1 * b ∉ qB.asIdeal
      exact fun he ↦ (qB.isPrime.mem_or_mem he).elim htp hb
    · intro p hp
      rcases jointly_surjective_comap_pullback f g hf p with ⟨qB, rfl⟩ | ⟨qC, rfl⟩
      · exact hbU (fun h ↦ hp (qB.asIdeal.mul_mem_left t.val.1 h))
      · exact False.elim (hp qC.asIdeal.zero_mem)

/-- The disjoint union of the two spectra maps onto the pullback spectrum by a quotient map. -/
theorem isQuotientMap_comap_pullback (hf : Function.Surjective f) :
    IsQuotientMap (Sum.elim (comap (f.pullbackFst g)) (comap (f.pullbackSnd g))) := by
  rw [isQuotientMap_iff]
  refine ⟨?_, ?_⟩
  · rw [isCoinducing_iff]
    intro s
    rw [isOpen_iff_comap_pullback f g hf, isOpen_sum_iff]
    rfl
  · intro p
    rcases jointly_surjective_comap_pullback f g hf p with ⟨q, hq⟩ | ⟨q, hq⟩
    · exact ⟨Sum.inl q, hq⟩
    · exact ⟨Sum.inr q, hq⟩

/-- Two primes in different factors with equal contractions come from a common prime. -/
theorem exists_comap_eq_of_comap_pullback_eq (hf : Function.Surjective f)
    (qB : PrimeSpectrum B) (qC : PrimeSpectrum C)
    (h : comap (f.pullbackFst g) qB = comap (f.pullbackSnd g) qC) :
    ∃ q : PrimeSpectrum D, comap f q = qB ∧ comap g q = qC := by
  have hk : RingHom.ker f ≤ qB.asIdeal := by
    intro b hb
    let a : f.pullback g := ⟨(b, 0), by simpa using hb⟩
    change a ∈ (comap (f.pullbackFst g) qB).asIdeal
    rw [h]
    exact qC.asIdeal.zero_mem
  have hq : qB ∈ Set.range (comap f) := by
    rw [range_comap_of_surjective D f hf]
    exact hk
  obtain ⟨q, rfl⟩ := hq
  refine ⟨q, rfl, ?_⟩
  apply comap_injective_of_surjective (f.pullbackSnd g)
    (f.surjective_pullbackSnd_of_surjective g hf)
  rw [← comap_comp_apply, ← RingHom.pullback_comm_sq, comap_comp_apply]
  exact h

/-- The first spectrum map is injective outside the image of the second factor. -/
theorem eq_of_comap_pullbackFst_eq (q₁ q₂ : PrimeSpectrum B)
    (h : comap (f.pullbackFst g) q₁ = comap (f.pullbackFst g) q₂)
    (hk : ¬ RingHom.ker (f.pullbackSnd g) ≤
      (comap (f.pullbackFst g) q₁).asIdeal) : q₁ = q₂ := by
  classical
  obtain ⟨t, ht, ht₁⟩ := SetLike.not_le_iff_exists.mp hk
  have htC : t.val.2 = 0 := ht
  have htB : f t.val.1 = 0 := by
    have he : f t.val.1 = g t.val.2 := t.property
    rw [htC, map_zero] at he
    exact he
  have ht₂ : t.val.1 ∉ q₂.asIdeal := by
    change t ∉ (comap (f.pullbackFst g) q₂).asIdeal
    rwa [← h]
  apply PrimeSpectrum.ext
  apply Ideal.ext
  intro b
  let a : f.pullback g := ⟨(t.val.1 * b, 0), by simp [htB]⟩
  have ha : t.val.1 * b ∈ q₁.asIdeal ↔ t.val.1 * b ∈ q₂.asIdeal := by
    change a ∈ (comap (f.pullbackFst g) q₁).asIdeal ↔
      a ∈ (comap (f.pullbackFst g) q₂).asIdeal
    rw [h]
  exact ⟨fun hb ↦ (q₂.isPrime.mem_or_mem (ha.mp (q₁.asIdeal.mul_mem_left _ hb))).resolve_left ht₂,
    fun hb ↦ (q₁.isPrime.mem_or_mem (ha.mpr (q₂.asIdeal.mul_mem_left _ hb))).resolve_left ht₁⟩

/-- Compatible functions on the factor spectra are constant on the fibers downstairs. -/
theorem factorsThrough_comap_pullback (hf : Function.Surjective f)
    {X : Type*} (m : PrimeSpectrum B → X) (n : PrimeSpectrum C → X)
    (h : m ∘ comap f = n ∘ comap g) :
    (Sum.elim m n).FactorsThrough
      (Sum.elim (comap (f.pullbackFst g)) (comap (f.pullbackSnd g))) := by
  classical
  have hcross (qB : PrimeSpectrum B) (qC : PrimeSpectrum C)
      (he : comap (f.pullbackFst g) qB = comap (f.pullbackSnd g) qC) :
      m qB = n qC := by
    obtain ⟨q, rfl, rfl⟩ := exists_comap_eq_of_comap_pullback_eq f g hf qB qC he
    exact congrFun h q
  intro x y hxy
  cases x with
  | inl q₁ =>
    cases y with
    | inl q₂ =>
      change comap (f.pullbackFst g) q₁ = comap (f.pullbackFst g) q₂ at hxy
      change m q₁ = m q₂
      by_cases hk : RingHom.ker (f.pullbackSnd g) ≤
          (comap (f.pullbackFst g) q₁).asIdeal
      · have hq : comap (f.pullbackFst g) q₁ ∈ Set.range (comap (f.pullbackSnd g)) := by
          rw [range_comap_of_surjective C _ (f.surjective_pullbackSnd_of_surjective g hf)]
          exact hk
        obtain ⟨qC, hqC⟩ := hq
        exact (hcross q₁ qC hqC.symm).trans (hcross q₂ qC (hxy.symm.trans hqC.symm)).symm
      · exact congrArg m (eq_of_comap_pullbackFst_eq f g q₁ q₂ hxy hk)
    | inr qC => exact hcross q₁ qC hxy
  | inr qC =>
    cases y with
    | inl qB => exact (hcross qB qC hxy.symm).symm
    | inr qC' =>
      exact congrArg n (comap_injective_of_surjective (f.pullbackSnd g)
        (f.surjective_pullbackSnd_of_surjective g hf) hxy)

/-- The projection spectra form a cocone over the common spectrum. -/
def comapPullbackCocone :
    PushoutCocone
      (TopCat.ofHom ⟨comap f, continuous_comap f⟩)
      (TopCat.ofHom ⟨comap g, continuous_comap g⟩) :=
  PushoutCocone.mk
    (TopCat.ofHom ⟨comap (f.pullbackFst g), continuous_comap _⟩)
    (TopCat.ofHom ⟨comap (f.pullbackSnd g), continuous_comap _⟩) (by
      apply TopCat.ext
      intro q
      change comap (f.pullbackFst g) (comap f q) =
        comap (f.pullbackSnd g) (comap g q)
      rw [← comap_comp_apply, RingHom.pullback_comm_sq, comap_comp_apply])

/-- Continuous compatible maps descend uniquely along the projection spectra. -/
noncomputable def comapPullbackCoconeIsColimit (hf : Function.Surjective f) :
    IsColimit (comapPullbackCocone f g) := by
  classical
  apply PushoutCocone.isColimitAux'
  intro s
  let Q := Sum.elim (comap (f.pullbackFst g)) (comap (f.pullbackSnd g))
  have hQ : IsQuotientMap Q := isQuotientMap_comap_pullback f g hf
  let M := Sum.elim (s.inl : PrimeSpectrum B → s.pt) (s.inr : PrimeSpectrum C → s.pt)
  have hM : M.FactorsThrough Q := factorsThrough_comap_pullback f g hf s.inl s.inr (by
    funext q
    exact ConcreteCategory.congr_hom s.condition q)
  let d : PrimeSpectrum (f.pullback g) → s.pt :=
    fun p ↦ M (Classical.choose (hQ.surjective p))
  have hd (x) : d (Q x) = M x := hM (Classical.choose_spec (hQ.surjective (Q x)))
  have hcont : Continuous d := hQ.continuous_iff.mpr (by
    have he : d ∘ Q = M := funext hd
    rw [he]
    exact s.inl.hom.continuous.sumElim s.inr.hom.continuous)
  refine ⟨TopCat.ofHom ⟨d, hcont⟩, ?_, ?_, ?_⟩
  · ext q
    exact hd (Sum.inl q)
  · ext q
    exact hd (Sum.inr q)
  · intro m hmB hmC
    ext p
    obtain ⟨x, rfl⟩ := hQ.surjective p
    change m (Q x) = d (Q x)
    rw [hd]
    cases x with
    | inl q => exact ConcreteCategory.congr_hom hmB q
    | inr q => exact ConcreteCategory.congr_hom hmC q

/-- With a surjective first ring map, the spectrum square is a pushout in `TopCat`. -/
theorem isPushout_comap_pullback (hf : Function.Surjective f) :
    IsPushout
      (TopCat.ofHom ⟨comap f, continuous_comap f⟩)
      (TopCat.ofHom ⟨comap g, continuous_comap g⟩)
      (TopCat.ofHom ⟨comap (f.pullbackFst g), continuous_comap _⟩)
      (TopCat.ofHom ⟨comap (f.pullbackSnd g), continuous_comap _⟩) where
  w := (comapPullbackCocone f g).condition
  isColimit' := ⟨comapPullbackCoconeIsColimit f g hf⟩

end Langlands.AlgebraicGeometry.AffineSchemePushout
