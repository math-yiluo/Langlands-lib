import Langlands.Algebra.FinitePresentationStages
import Langlands.Algebra.FinitePresentationStageFlatness
import Langlands.Algebra.NoetherianFlatLocusOpen
import Mathlib.RingTheory.Spectrum.Prime.Topology

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

/-! # Flat finitely presented models from pointwise flat stages -/

open TensorProduct

namespace Langlands.Algebra.FlatFinitePresentationModel

open FinitePresentationStages

/-- Flatness of a localization at a prime only depends on the prime ideal. -/
theorem flat_atPrime_of_eq {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {I J : Ideal S} [I.IsPrime] [J.IsPrime] (e : I = J)
    [Module.Flat R (Localization.AtPrime I)] : Module.Flat R (Localization.AtPrime J) := by
  subst e
  assumption

variable {A B ι σ : Type*} [CommRing A] [CommRing B] [Algebra A B]
  (P : Algebra.Presentation A B ι σ)

/-- The primes `Q` of `B` at which the stage `t` is flat: the localization of `model P t` at the
prime `Q ∩ model P t` is flat over `base P t`. -/
def flatSet (t : Finset A) : Set (PrimeSpectrum B) :=
  {Q | Module.Flat (base P t) (Localization.AtPrime (Q.asIdeal.comap (toB P t)))}

theorem mem_flatSet {t : Finset A} {Q : PrimeSpectrum B} :
    Q ∈ flatSet P t ↔
      Module.Flat (base P t) (Localization.AtPrime (Q.asIdeal.comap (toB P t))) :=
  Iff.rfl

/-- The flat sets increase with the stage. -/
theorem flatSet_mono {t t' : Finset A} (h : t ⊆ t') : flatSet P t ⊆ flatSet P t' := by
  intro Q hQ
  have : Module.Flat (base P t) (Localization.AtPrime (Q.asIdeal.comap (toB P t))) := hQ
  have : Module.Flat (base P t)
      (Localization.AtPrime ((Q.asIdeal.comap (toB P t')).comap (trans P h))) :=
    flat_atPrime_of_eq (comap_trans_comap_toB P h Q.asIdeal).symm
  exact flat_localization_trans P h _ this

theorem directed_flatSet : Directed (· ⊆ ·) (flatSet P) := by
  classical
  intro t t'
  exact ⟨t ∪ t', flatSet_mono P Finset.subset_union_left,
    flatSet_mono P Finset.subset_union_right⟩

/-- Each flat set is open: it is the preimage of the open flat locus of `model P t` over the
Noetherian ring `base P t`. -/
theorem isOpen_flatSet [Finite ι] [Finite σ] (t : Finset A) : IsOpen (flatSet P t) :=
  (Module.Flat.isOpen_setOf_flat_localization_atPrime (A := base P t) (B := model P t)).preimage
    (PrimeSpectrum.continuous_comap (toB P t).toRingHom)

/-- Composition of transitions as ring homomorphisms. -/
theorem trans_comp {t t' t'' : Finset A} (h₁ : t ⊆ t') (h₂ : t' ⊆ t'') :
    (trans P h₂).comp (trans P h₁) = trans P (h₁.trans h₂) :=
  RingHom.ext fun x => trans_trans h₁ h₂ x

theorem trans_mem_map_trans {t t' t'' : Finset A} (h₁ : t ⊆ t') (h₂ : t' ⊆ t'')
    {J : Ideal (model P t)} {x : model P t'} (hx : x ∈ J.map (trans P h₁)) :
    trans P h₂ x ∈ J.map (trans P (h₁.trans h₂)) := by
  rw [← trans_comp P h₁ h₂, ← Ideal.map_map]
  exact Ideal.mem_map_of_mem _ hx

/-- An element of the extension of an ideal `J` of a stage to `B` comes from the extension of
`J` to some later stage. -/
theorem exists_mem_map_trans {t : Finset A} (J : Ideal (model P t)) {b : B}
    (hb : b ∈ J.map (toB P t)) :
    ∃ t', ∃ h : t ⊆ t', ∃ x ∈ J.map (trans P h), toB P t' x = b := by
  classical
  induction hb using Submodule.span_induction with
  | mem b hb =>
    obtain ⟨j, hj, rfl⟩ := hb
    exact ⟨t, subset_refl t, trans P (subset_refl t) j, Ideal.mem_map_of_mem _ hj,
      toB_trans _ _⟩
  | zero => exact ⟨t, subset_refl t, 0, zero_mem _, map_zero _⟩
  | add b c _ _ hb hc =>
    obtain ⟨t₁, h₁, x, hx, rfl⟩ := hb
    obtain ⟨t₂, h₂, y, hy, rfl⟩ := hc
    have hx' := trans_mem_map_trans P h₁ (Finset.subset_union_left (s₂ := t₂)) hx
    have hy' := trans_mem_map_trans P h₂ (Finset.subset_union_right (s₁ := t₁)) hy
    refine ⟨t₁ ∪ t₂, h₁.trans Finset.subset_union_left, _, add_mem hx' hy', ?_⟩
    rw [map_add, toB_trans, toB_trans]
  | smul c b _ hb =>
    obtain ⟨t₁, h₁, x, hx, rfl⟩ := hb
    obtain ⟨t₂, h₁₂, y, rfl⟩ := exists_lift P t₁ c
    have hx' := trans_mem_map_trans P h₁ h₁₂ hx
    refine ⟨t₂, h₁.trans h₁₂, y * trans P h₁₂ x, Ideal.mul_mem_left _ _ hx', ?_⟩
    rw [map_mul, toB_trans, smul_eq_mul]

/-- If an ideal of a stage generates the unit ideal of `B`, it generates the unit ideal of some
later stage. -/
theorem exists_map_trans_eq_top [Finite σ] {t : Finset A} (J : Ideal (model P t))
    (hJ : J.map (toB P t) = ⊤) : ∃ t', ∃ h : t ⊆ t', J.map (trans P h) = ⊤ := by
  obtain ⟨t', h, x, hx, hx1⟩ := exists_mem_map_trans P J (hJ ▸ Submodule.mem_top (x := 1))
  obtain ⟨t'', h', hzero⟩ := exists_trans_eq_zero P (x - 1) (by rw [map_sub, hx1, map_one,
    sub_self])
  refine ⟨t'', h.trans h', (Ideal.eq_top_iff_one _).mpr ?_⟩
  rw [map_sub, map_one, sub_eq_zero] at hzero
  exact hzero ▸ trans_mem_map_trans P h h' hx

/-- A stage lying in every flat set is flat at every prime of the stage under a prime of `B`. -/
theorem flat_of_univ_subset_flatSet {t : Finset A} (ht : Set.univ ⊆ flatSet P t) (Q : Ideal B)
    [hQ : Q.IsPrime] : Module.Flat (base P t) (Localization.AtPrime (Q.comap (toB P t))) :=
  ht (Set.mem_univ (PrimeSpectrum.mk Q hQ))

/-- The flat locus of a stage is the complement of the zero locus of an ideal. -/
theorem exists_ideal_flat_iff [Finite ι] [Finite σ] (t : Finset A) :
    ∃ J : Ideal (model P t), ∀ q : PrimeSpectrum (model P t),
      Module.Flat (base P t) (Localization.AtPrime q.asIdeal) ↔ ¬ J ≤ q.asIdeal := by
  obtain ⟨J, hJ⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).mp
    (Module.Flat.isOpen_setOf_flat_localization_atPrime (A := base P t) (B := model P t)).isClosed_compl
  refine ⟨J, fun q => ?_⟩
  have h := Set.ext_iff.mp hJ q
  rw [Set.mem_compl_iff, Set.mem_ofPred_eq, PrimeSpectrum.mem_zeroLocus,
    SetLike.coe_subset_coe] at h
  rw [← h, not_not]

/-- If a stage lies in every flat set, then an ideal cutting out its non-flat locus generates
the unit ideal of `B`. -/
theorem map_toB_eq_top {t : Finset A} (ht : Set.univ ⊆ flatSet P t) (J : Ideal (model P t))
    (hJ : ∀ q : PrimeSpectrum (model P t),
      Module.Flat (base P t) (Localization.AtPrime q.asIdeal) → ¬ J ≤ q.asIdeal) :
    J.map (toB P t) = ⊤ := by
  refine Classical.byContradiction fun hne => ?_
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  exact hJ (PrimeSpectrum.mk (M.comap (toB P t)) inferInstance)
    (flat_of_univ_subset_flatSet P ht M) (Ideal.map_le_iff_le_comap.mp hle)

/-- If an ideal cutting out the non-flat locus of a stage generates the unit ideal of a later
stage, then that later stage is flat. -/
theorem flat_of_map_trans_eq_top {t t' : Finset A} (h : t ⊆ t') (J : Ideal (model P t))
    (hJ : ∀ q : PrimeSpectrum (model P t),
      ¬ J ≤ q.asIdeal → Module.Flat (base P t) (Localization.AtPrime q.asIdeal))
    (htop : J.map (trans P h) = ⊤) : Module.Flat (base P t') (model P t') := by
  refine Module.flat_of_isLocalized_maximal (model P t') (model P t')
    (fun M _ => Localization.AtPrime M) (fun M _ => Algebra.linearMap _ _) fun M hM => ?_
  refine flat_localization_trans P h M (hJ (PrimeSpectrum.mk (M.comap (trans P h)) inferInstance)
    fun hle => hM.ne_top ?_)
  rw [eq_top_iff, ← htop]
  exact Ideal.map_le_iff_le_comap.mpr hle

/-- **Glue for Stacks 10.168.1(1).** If every prime of `B` lies in the flat set of some stage,
then some stage model is flat over its base ring. -/
theorem exists_flat_model_of_forall_mem_flatSet [Finite ι] [Finite σ]
    (hstage : ∀ Q : PrimeSpectrum B, ∃ t, Q ∈ flatSet P t) :
    ∃ t, Module.Flat (base P t) (model P t) := by
  -- One stage is flat at every prime of `B`.
  obtain ⟨t₁, ht₁⟩ := isCompact_univ.elim_directed_cover (flatSet P) (isOpen_flatSet P)
    (fun Q _ => Set.mem_iUnion.mpr (hstage Q)) (directed_flatSet P)
  -- The non-flat locus of `model P t₁` is cut out by an ideal `J`, which generates the unit
  -- ideal of `B`, hence of a later stage; that stage is flat everywhere.
  obtain ⟨J, hJ⟩ := exists_ideal_flat_iff P t₁
  obtain ⟨t₂, h, htop⟩ := exists_map_trans_eq_top P J
    (map_toB_eq_top P ht₁ J fun q => (hJ q).mp)
  exact ⟨t₂, flat_of_map_trans_eq_top P h J (fun q => (hJ q).mpr) htop⟩

universe u in
/-- A finitely presented algebra all of whose primes lie in flat sets of the stages of its
standard presentation has a flat finitely presented model over a subring of finite type
over `ℤ`. -/
theorem exists_flat_model_of_forall_mem_flatSet_ofFinitePresentation (A B : Type u)
    [CommRing A] [CommRing B] [Algebra A B] [Algebra.FinitePresentation A B]
    (hstage : ∀ Q : PrimeSpectrum B,
      ∃ t, Q ∈ flatSet (Algebra.Presentation.ofFinitePresentation A B) t) :
    ∃ (A₀ : Subalgebra ℤ A) (B₀ : Type u) (_ : CommRing B₀) (_ : Algebra A₀ B₀),
      Algebra.FiniteType ℤ A₀ ∧ Algebra.FinitePresentation A₀ B₀ ∧ Module.Flat A₀ B₀ ∧
        Nonempty (A ⊗[A₀] B₀ ≃ₐ[A] B) := by
  obtain ⟨t, ht⟩ := exists_flat_model_of_forall_mem_flatSet _ hstage
  exact ⟨base _ t, model _ t, inferInstance, inferInstance, inferInstance, inferInstance, ht,
    nonempty_tensor_model _ t⟩

end Langlands.Algebra.FlatFinitePresentationModel

namespace Langlands.Algebra

open FinitePresentationStages FlatFinitePresentationModel

universe u in
/-- **Stacks 10.168.1(1)** (Tag 02JO), case `M = S`. A flat finitely presented algebra has a
flat finitely presented model over a subring of finite type over `ℤ`. -/
theorem exists_flat_finitePresentation_model (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] : Algebra.FinitePresentation A B → Module.Flat A B →
      ∃ (A₀ : Subalgebra ℤ A) (B₀ : Type u) (_ : CommRing B₀) (_ : Algebra A₀ B₀),
        Algebra.FiniteType ℤ A₀ ∧ Algebra.FinitePresentation A₀ B₀ ∧ Module.Flat A₀ B₀ ∧
          Nonempty (A ⊗[A₀] B₀ ≃ₐ[A] B) := by
  intro _ _
  exact exists_flat_model_of_forall_mem_flatSet_ofFinitePresentation A B fun Q ↦
    exists_flat_stage _ Q.asIdeal

end Langlands.Algebra
