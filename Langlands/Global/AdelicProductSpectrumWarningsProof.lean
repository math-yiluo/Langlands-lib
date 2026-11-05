import Langlands.Global.AdelicProductSpectrumWarningsStatement
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

/-! # Proof of the support warnings for spectra of products and adelic levels -/

noncomputable section

universe u

open CategoryTheory Filter Polynomial
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

section General

/-- A factor point is the literal pullback of a prime ideal. -/
theorem productSpectrum_mem_range_iff {A C : Type u} [CommRing A] [CommRing C]
    (q : A →+* C) (z : PrimeSpectrum A) :
    z ∈ Set.range (Spec.map (CommRingCat.ofHom q)) ↔
      ∃ x : PrimeSpectrum C, PrimeSpectrum.comap q x = z := Iff.rfl

/-- The range of the morphism induced by a surjection is the zero locus of its kernel. -/
theorem productSpectrum_mem_range_iff_ker_le {A C : Type u} [CommRing A] [CommRing C]
    (q : A →+* C) (hq : Function.Surjective q) (z : PrimeSpectrum A) :
    z ∈ Set.range (Spec.map (CommRingCat.ofHom q)) ↔ RingHom.ker q ≤ z.asIdeal := by
  rw [productSpectrum_mem_range_iff]
  change z ∈ Set.range (PrimeSpectrum.comap q) ↔ _
  rw [range_comap_of_surjective _ q hq]
  exact Iff.rfl

/-- If a factor morphism factors through a closed subscheme, the ring map kills its ideal. -/
theorem productSpectrum_eq_zero_of_factor {A C : Type u} [CommRing A] [CommRing C]
    (I : Ideal A) (q : A →+* C)
    (h : ∃ f : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of (A ⧸ I)),
      f ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) =
        Spec.map (CommRingCat.ofHom q)) {a : A} (ha : a ∈ I) : q a = 0 := by
  obtain ⟨f, hf⟩ := h
  have hg : CommRingCat.ofHom (Ideal.Quotient.mk I) ≫ Spec.preimage f =
      CommRingCat.ofHom q := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, hf]
  have := congrArg (fun g => g.hom a) hg
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply,
    Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero] at this
  exact this.symm

/-- Infinitely many disjoint nonempty open sets have a noncompact union. -/
theorem not_isCompact_iUnion_of_pairwise_disjoint {X : Type*} [TopologicalSpace X]
    {ι : Type*} (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hd : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hne : {i | (U i).Nonempty}.Infinite) : ¬ IsCompact (⋃ i, U i) := by
  intro hK
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover U hU subset_rfl
  obtain ⟨j, hj, hjt⟩ := (hne.sdiff t.finite_toSet).nonempty
  obtain ⟨z, hz⟩ := hj
  have hz' := ht (Set.mem_iUnion.2 ⟨j, hz⟩)
  simp only [Set.mem_iUnion] at hz'
  obtain ⟨i, hi, hzi⟩ := hz'
  have hij : i ≠ j := fun h => hjt (h ▸ hi)
  exact Set.disjoint_left.1 (hd hij) hzi hz

variable {ι : Type u} {A : Type u} [CommRing A] {B : ι → Type u} [∀ i, CommRing (B i)]
  (e : A ≃+* ∀ i, B i) (p : ∀ i, A →+* B i) (hp : ∀ i a, p i a = e a i)

include hp

theorem productSpectrum_p_surjective (i : ι) : Function.Surjective (p i) := by
  classical
  intro b
  exact ⟨e.symm (Pi.single i b), by rw [hp, RingEquiv.apply_symm_apply, Pi.single_eq_same]⟩

theorem productSpectrum_p_idem (i j : ι) [DecidableEq ι] :
    p j (e.symm (Pi.single i 1)) = if j = i then 1 else 0 := by
  rw [hp, RingEquiv.apply_symm_apply]
  by_cases h : j = i
  · subst h; simp
  · simp [h]

theorem productSpectrum_isOpenImmersion (i : ι) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (p i))) := by
  have h : CommRingCat.ofHom (p i) =
      e.toCommRingCatIso.hom ≫ CommRingCat.ofHom (Pi.evalRingHom B i) := by
    ext a
    exact hp i a
  rw [h, Spec.map_comp]
  infer_instance

theorem productSpectrum_disjoint :
    Pairwise (fun i j => Disjoint (Set.range (Spec.map (CommRingCat.ofHom (p i))))
      (Set.range (Spec.map (CommRingCat.ofHom (p j))))) := by
  classical
  intro i j hij
  rw [Set.disjoint_left]
  rintro z ⟨x, rfl⟩ ⟨y, hy⟩
  have h1 : e.symm (Pi.single i 1) ∈ (PrimeSpectrum.comap (p j) y).asIdeal := by
    change p j (e.symm (Pi.single i 1)) ∈ y.asIdeal
    rw [productSpectrum_p_idem e p hp]
    simp [Ne.symm hij]
  rw [show PrimeSpectrum.comap (p j) y = PrimeSpectrum.comap (p i) x from hy] at h1
  change p i (e.symm (Pi.single i 1)) ∈ x.asIdeal at h1
  rw [productSpectrum_p_idem e p hp] at h1
  simp only [ite_true] at h1
  exact x.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)

omit hp in
theorem productSpectrum_range_nonempty (i : ι) [Nontrivial (B i)] :
    (Set.range (Spec.map (CommRingCat.ofHom (p i)))).Nonempty := by
  obtain ⟨x⟩ := (inferInstance : Nonempty (PrimeSpectrum (B i)))
  exact ⟨_, x, rfl⟩

theorem productSpectrum_finite_support_of_mem_span [DecidableEq ι] {y : A}
    (hy : y ∈ Ideal.span (Set.range fun i => e.symm (Pi.single i (1 : B i)))) :
    {j | p j y ≠ 0}.Finite := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    refine (Set.finite_singleton i).subset fun j hj => ?_
    by_contra h
    have hji : j ≠ i := fun h' => h (Set.mem_singleton_iff.2 h')
    exact hj (by rw [productSpectrum_p_idem e p hp]; simp [hji])
  | zero => simp
  | add x y _ _ hx hy =>
    refine (hx.union hy).subset fun j hj => ?_
    by_contra h
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at h
    exact hj (by rw [map_add, h.1, h.2, add_zero])
  | smul a x _ hx =>
    refine hx.subset fun j hj => ?_
    by_contra h
    simp only [Set.mem_ofPred_eq, not_not] at h
    exact hj (by rw [smul_eq_mul, map_mul, h, mul_zero])

theorem productSpectrum_iUnion_ne_univ (hinf : {i | Nontrivial (B i)}.Infinite) :
    (⋃ i, Set.range (Spec.map (CommRingCat.ofHom (p i)))) ≠ Set.univ := by
  classical
  let J : Ideal A := Ideal.span (Set.range fun i => e.symm (Pi.single i (1 : B i)))
  have hJ : J ≠ ⊤ := by
    rw [Ne, Ideal.eq_top_iff_one]
    intro h1
    apply hinf
    refine (productSpectrum_finite_support_of_mem_span e p hp h1).subset fun j hj => ?_
    have : Nontrivial (B j) := hj
    simp
  obtain ⟨m, hm, hJm⟩ := Ideal.exists_le_maximal J hJ
  intro h
  have hP : (⟨m, hm.isPrime⟩ : PrimeSpectrum A) ∈
      (⋃ i, Set.range (Spec.map (CommRingCat.ofHom (p i)))) := by
    rw [h]; trivial
  obtain ⟨i, x, hx⟩ := Set.mem_iUnion.1 hP
  have h1 : e.symm (Pi.single i 1) ∈ (PrimeSpectrum.comap (p i) x).asIdeal := by
    rw [show PrimeSpectrum.comap (p i) x = ⟨m, hm.isPrime⟩ from hx]
    exact hJm (Ideal.subset_span ⟨i, rfl⟩)
  change p i (e.symm (Pi.single i 1)) ∈ x.asIdeal at h1
  rw [productSpectrum_p_idem e p hp] at h1
  simp only [ite_true] at h1
  exact x.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)

theorem productSpectrum_iUnion_eq_univ (hfin : {i | Nontrivial (B i)}.Finite) :
    (⋃ i, Set.range (Spec.map (CommRingCat.ofHom (p i)))) = Set.univ := by
  classical
  refine Set.eq_univ_of_forall fun z => ?_
  let T := hfin.toFinset
  have hsum : ∑ i ∈ T, e.symm (Pi.single i (1 : B i)) = 1 := by
    apply e.injective
    rw [map_sum, map_one]
    funext j
    rw [Finset.sum_apply]
    by_cases hj : j ∈ T
    · rw [Finset.sum_eq_single j (fun b _ hb => by
          rw [RingEquiv.apply_symm_apply, Pi.single_eq_of_ne (Ne.symm hb)])
        (fun h => absurd hj h), RingEquiv.apply_symm_apply, Pi.single_eq_same, Pi.one_apply]
    · have : ¬ Nontrivial (B j) := fun h => hj (hfin.mem_toFinset.2 h)
      have : Subsingleton (B j) := not_nontrivial_iff_subsingleton.mp this
      exact Subsingleton.elim _ _
  obtain ⟨i, -, hi⟩ : ∃ i ∈ T, e.symm (Pi.single i (1 : B i)) ∉ z.asIdeal := by
    by_contra! h
    exact z.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
      (hsum ▸ Ideal.sum_mem _ fun i hi => h i hi))
  refine Set.mem_iUnion.2 ⟨i, ?_⟩
  refine (productSpectrum_mem_range_iff_ker_le _ (productSpectrum_p_surjective e p hp i) z).2 ?_
  intro a ha
  have h0 : a * e.symm (Pi.single i 1) = 0 := by
    apply e.injective
    rw [map_mul, RingEquiv.apply_symm_apply, map_zero]
    funext j
    by_cases hj : j = i
    · subst hj
      rw [Pi.mul_apply, Pi.single_eq_same, mul_one, Pi.zero_apply, ← hp]
      exact ha
    · rw [Pi.mul_apply, Pi.single_eq_of_ne hj, mul_zero, Pi.zero_apply]
  have hmem : a * e.symm (Pi.single i 1) ∈ z.asIdeal := h0 ▸ zero_mem _
  exact (z.isPrime.mem_or_mem hmem).resolve_right hi

theorem productSpectrum_dense (I : Ideal A)
    (h : ∀ i, ∃ f : Spec (CommRingCat.of (B i)) ⟶ Spec (CommRingCat.of (A ⧸ I)),
      f ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) =
        Spec.map (CommRingCat.ofHom (p i))) : I = ⊥ := by
  rw [eq_bot_iff]
  intro a ha
  rw [Ideal.mem_bot]
  apply e.injective
  funext i
  rw [map_zero, Pi.zero_apply, ← hp]
  exact productSpectrum_eq_zero_of_factor I (p i) (h i) ha

omit hp in
theorem productSpectrum_isOpen (i : ι) [IsOpenImmersion (Spec.map (CommRingCat.ofHom (p i)))] :
    IsOpen (Set.range (Spec.map (CommRingCat.ofHom (p i)))) :=
  IsOpenImmersion.isOpen_range _

theorem productSpectrum_not_isCompact (hinf : {i | Nontrivial (B i)}.Infinite) :
    ¬ IsCompact (⋃ i, Set.range (Spec.map (CommRingCat.ofHom (p i)))) := by
  refine not_isCompact_iUnion_of_pairwise_disjoint _ (fun i => ?_)
    (productSpectrum_disjoint e p hp) (hinf.mono fun i hi => ?_)
  · have := productSpectrum_isOpenImmersion e p hp i
    exact productSpectrum_isOpen p i
  · have : Nontrivial (B i) := hi
    exact productSpectrum_range_nonempty p i

section Local

variable [∀ i, IsLocalRing (B i)]

theorem productSpectrum_mem_span_iff
    (hϖ : ∀ᶠ i in cofinite, ∃ ϖ : B i, Irreducible ϖ ∧
      IsLocalRing.maximalIdeal (B i) = Ideal.span {ϖ}) (a : A) :
    a ∈ Ideal.span {b : A | ∀ᶠ j in cofinite, Irreducible (p j b)} ↔
      ∀ᶠ j in cofinite, p j a ∈ IsLocalRing.maximalIdeal (B j) := by
  classical
  constructor
  · intro ha
    induction ha using Submodule.span_induction with
    | mem x hx =>
      exact (show ∀ᶠ j in cofinite, Irreducible (p j x) from hx).mono fun j hj =>
        (IsLocalRing.mem_maximalIdeal _).2 hj.not_isUnit
    | zero => exact Eventually.of_forall fun j => by rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy =>
      exact (hx.and hy).mono fun j hj => by rw [map_add]; exact add_mem hj.1 hj.2
    | smul c x _ hx =>
      exact hx.mono fun j hj => by
        rw [smul_eq_mul, map_mul]; exact Ideal.mul_mem_left _ _ hj
  · intro ha
    have key : ∀ j, ∃ β γ : B j, p j a = γ * β ∧
        ((p j a ∈ IsLocalRing.maximalIdeal (B j) ∧ ∃ ϖ : B j, Irreducible ϖ ∧
          IsLocalRing.maximalIdeal (B j) = Ideal.span {ϖ}) → Irreducible β) := by
      intro j
      by_cases hj : p j a ∈ IsLocalRing.maximalIdeal (B j) ∧ ∃ ϖ : B j, Irreducible ϖ ∧
          IsLocalRing.maximalIdeal (B j) = Ideal.span {ϖ}
      · obtain ⟨ha', ϖ, hϖi, hm⟩ := hj
        rw [hm] at ha'
        obtain ⟨γ, hγ⟩ := Ideal.mem_span_singleton'.1 ha'
        exact ⟨ϖ, γ, hγ.symm, fun _ => hϖi⟩
      · exact ⟨1, p j a, (mul_one _).symm, fun h => absurd h hj⟩
    choose β γ hβγ hβ using key
    have hb : e.symm β ∈ {b : A | ∀ᶠ j in cofinite, Irreducible (p j b)} :=
      (ha.and hϖ).mono fun j hj => by
        rw [hp, RingEquiv.apply_symm_apply]; exact hβ j hj
    have hab : a = e.symm γ * e.symm β := by
      apply e.injective
      funext j
      rw [map_mul, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, Pi.mul_apply,
        ← hp]
      exact hβγ j
    rw [hab]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span hb)

theorem productSpectrum_map_eq_top
    (hϖ : ∀ᶠ i in cofinite, ∃ ϖ : B i, Irreducible ϖ ∧
      IsLocalRing.maximalIdeal (B i) = Ideal.span {ϖ}) (i : ι) :
    (Ideal.span {b : A | ∀ᶠ j in cofinite, Irreducible (p j b)}).map (p i) = ⊤ := by
  classical
  have key : ∀ j, ∃ β : B j, (∃ ϖ : B j, Irreducible ϖ ∧
      IsLocalRing.maximalIdeal (B j) = Ideal.span {ϖ}) → Irreducible β := by
    intro j
    by_cases hj : ∃ ϖ : B j, Irreducible ϖ ∧ IsLocalRing.maximalIdeal (B j) = Ideal.span {ϖ}
    · obtain ⟨ϖ, hϖi, -⟩ := hj
      exact ⟨ϖ, fun _ => hϖi⟩
    · exact ⟨1, fun h => absurd h hj⟩
  choose β hβ using key
  let b : A := e.symm (Function.update β i 1)
  have hb : b ∈ {b : A | ∀ᶠ j in cofinite, Irreducible (p j b)} :=
    (hϖ.and (eventually_cofinite_ne i)).mono fun j hj => by
      change Irreducible (p j (e.symm (Function.update β i 1)))
      rw [hp, RingEquiv.apply_symm_apply, Function.update_of_ne hj.2]
      exact hβ j hj.1
  rw [Ideal.eq_top_iff_one]
  have : p i b = 1 := by
    change p i (e.symm (Function.update β i 1)) = 1
    rw [hp, RingEquiv.apply_symm_apply, Function.update_self]
  rw [← this]
  exact Ideal.mem_map_of_mem _ (Ideal.subset_span hb)

theorem productSpectrum_not_fg [Infinite ι]
    (hϖ : ∀ᶠ i in cofinite, ∃ ϖ : B i, Irreducible ϖ ∧
      IsLocalRing.maximalIdeal (B i) = Ideal.span {ϖ}) :
    ¬ (Ideal.span {b : A | ∀ᶠ j in cofinite, Irreducible (p j b)}).FG := by
  rintro ⟨s, hs⟩
  have hev : ∀ x ∈ s, ∀ᶠ j in cofinite, p j x ∈ IsLocalRing.maximalIdeal (B j) := by
    intro x hx
    refine (productSpectrum_mem_span_iff e p hp hϖ x).1 ?_
    rw [← hs]
    exact Submodule.subset_span hx
  obtain ⟨j, hj⟩ := ((Filter.eventually_all_finset s).2 hev).exists
  have htop := productSpectrum_map_eq_top e p hp hϖ j
  rw [← hs] at htop
  change Ideal.map (p j) (Ideal.span (s : Set A)) = ⊤ at htop
  rw [Ideal.map_span] at htop
  have hle : Ideal.span (p j '' (s : Set A)) ≤ IsLocalRing.maximalIdeal (B j) := by
    rw [Ideal.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact hj x hx
  rw [htop] at hle
  exact (IsLocalRing.maximalIdeal.isMaximal (B j)).ne_top (top_le_iff.mp hle)

/-- All local warnings for a ring presented as an infinite product of local rings. -/
theorem localFactorSpectrumWarnings_of_ringEquiv [Infinite ι]
    (hϖ : ∀ᶠ i in cofinite, ∃ ϖ : B i, Irreducible ϖ ∧
      IsLocalRing.maximalIdeal (B i) = Ideal.span {ϖ}) :
    LocalFactorSpectrumWarnings A B p := by
  have hinf : {i | Nontrivial (B i)}.Infinite := by
    rw [Set.eq_univ_of_forall fun i => (inferInstance : Nontrivial (B i))]
    exact Set.infinite_univ
  exact ⟨productSpectrum_isOpenImmersion e p hp, productSpectrum_disjoint e p hp,
    fun i => productSpectrum_range_nonempty p i,
    productSpectrum_iUnion_ne_univ e p hp hinf, productSpectrum_not_isCompact e p hp hinf,
    productSpectrum_dense e p hp, productSpectrum_mem_span_iff e p hp hϖ,
    productSpectrum_not_fg e p hp hϖ, productSpectrum_map_eq_top e p hp hϖ⟩

end Local

end General

theorem productFactorSpectrum : ProductFactorSpectrumStatement.{u} := by
  intro ι R _
  have hp : ∀ i a, Pi.evalRingHom R i a = (RingEquiv.refl (∀ i, R i)) a i := fun _ _ => rfl
  exact ⟨productSpectrum_isOpenImmersion _ _ hp, productSpectrum_disjoint _ _ hp,
    ⟨fun h => by
      by_contra hinf
      exact productSpectrum_iUnion_ne_univ _ _ hp hinf h,
      productSpectrum_iUnion_eq_univ _ _ hp⟩,
    productSpectrum_not_isCompact _ _ hp, productSpectrum_dense _ _ hp⟩

theorem localProductSpectrumWarnings : LocalProductSpectrumWarningsStatement.{u} := by
  intro ι _ R _ _ hϖ
  exact localFactorSpectrumWarnings_of_ringEquiv (RingEquiv.refl (∀ i, R i)) _
    (fun _ _ => rfl) hϖ

/-- `X ^ (n + 1)` does not divide `X ^ m` when `m ≤ n`. -/
theorem moretBailly_not_dvd (k : Type u) [Field k] {m n : ℕ} (h : m ≤ n) :
    ¬ (X : k[X]) ^ (n + 1) ∣ X ^ m := by
  intro hd
  have := Polynomial.natDegree_le_of_dvd hd (pow_ne_zero _ Polynomial.X_ne_zero)
  rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_X_pow] at this
  omega

/-- A componentwise nilpotent, globally non-nilpotent element gives the support warning. -/
theorem closedSubschemeSupportWarning_of {ι : Type} (R : ι → Type u) [∀ i, CommRing (R i)]
    (r : ∀ i, R i) (N : Set ι) (h1 : ∀ i, IsNilpotent (r i)) (h2 : ∀ i ∈ N, r i ≠ 0)
    (h3 : ¬ IsNilpotent r) : ClosedSubschemeSupportWarning R r N := by
  have hrange : ∀ z : PrimeSpectrum (∀ i, R i),
      z ∈ Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {r})))) ↔
        r ∈ z.asIdeal := by
    intro z
    rw [productSpectrum_mem_range_iff_ker_le _ Ideal.Quotient.mk_surjective, Ideal.mk_ker,
      Ideal.span_singleton_le_iff_mem]
  have hsub : ∀ i, Set.range (Spec.map (CommRingCat.ofHom (Pi.evalRingHom R i))) ⊆
      Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {r})))) := by
    rintro i _ ⟨x, rfl⟩
    refine (hrange _).2 ?_
    change r i ∈ x.asIdeal
    obtain ⟨m, hm⟩ := h1 i
    exact x.isPrime.mem_of_pow_mem m (hm ▸ zero_mem _)
  have hne : Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {r})))) ≠
      Set.univ := by
    intro h
    apply h3
    have hall : ∀ z : PrimeSpectrum (∀ i, R i), r ∈ z.asIdeal := fun z =>
      (hrange z).1 (h ▸ Set.mem_univ _)
    rw [← mem_nilradical, nilradical_eq_sInf, Submodule.mem_sInf]
    intro P hP
    exact hall ⟨P, hP⟩
  refine ⟨hsub, ?_, h3, hne, ?_⟩
  · rintro i hi h
    exact h2 i hi (productSpectrum_eq_zero_of_factor _ (Pi.evalRingHom R i) h
      (Ideal.mem_span_singleton_self r))
  · intro h
    apply hne
    apply Set.eq_univ_of_univ_subset
    rw [← h]
    apply closure_minimal (Set.iUnion_subset hsub)
    have := IsClosedImmersion.spec_of_surjective
      (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {r}))) Ideal.Quotient.mk_surjective
    exact (Scheme.Hom.isClosedEmbedding _).isClosed_range

theorem moretBaillyDiagonal : MoretBaillyDiagonalStatement.{u} := by
  intro k _
  refine closedSubschemeSupportWarning_of _ _ _ (fun n => ⟨n + 1, ?_⟩) (fun n hn h0 => ?_) ?_
  · rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self _
  · rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h0
    exact moretBailly_not_dvd k (m := 1) hn (by simpa using h0)
  · rintro ⟨m, hm⟩
    have := congrFun hm m
    rw [Pi.pow_apply, Pi.zero_apply, ← map_pow, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_span_singleton] at this
    exact moretBailly_not_dvd k le_rfl this

end Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

theorem numberFieldLevelSpectrumWarnings : NumberFieldLevelSpectrumWarningsStatement.{u} := by
  intro K _ _ S
  have := numberField_finitePlaces_infinite K
  have : Infinite {v : FinitePlace K // v ∉ S} :=
    (S.finite_toSet.infinite_compl).to_subtype
  have hϖ : ∀ᶠ i in cofinite, ∃ ϖ : NumberFieldLevelFactor K S i, Irreducible ϖ ∧
      IsLocalRing.maximalIdeal (NumberFieldLevelFactor K S i) = Ideal.span {ϖ} := by
    let f : InfinitePlace K ⊕ {v : FinitePlace K // v ∈ S} → NumberFieldLevelFactorIndex K S :=
      Sum.elim Sum.inl (Sum.inr ∘ Sum.inl)
    refine Filter.eventually_cofinite.2 ((Set.finite_range f).subset ?_)
    intro i hi
    rcases i with v | v | v
    · exact ⟨Sum.inl v, rfl⟩
    · exact ⟨Sum.inr v, rfl⟩
    · exfalso
      apply hi
      obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (v.1.adicCompletionIntegers K)
      exact ⟨ϖ, hϖ, (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ⟩
  exact localFactorSpectrumWarnings_of_ringEquiv (numberFieldLevelFactorRingEquiv K S) _
    (fun _ _ => rfl) hϖ

theorem curvePlaceLevelSpectrumWarnings : CurvePlaceLevelSpectrumWarningsStatement.{u} := by
  intro k F _ _ _ _ _ _ S
  have := functionField_places_infinite k F
  have : Infinite {v : AlgebraicCurve.Place k F // v ∉ S} :=
    (S.finite_toSet.infinite_compl).to_subtype
  have hϖ : ∀ᶠ i in cofinite, ∃ ϖ : CurvePlaceLevelFactor k F S i, Irreducible ϖ ∧
      IsLocalRing.maximalIdeal (CurvePlaceLevelFactor k F S i) = Ideal.span {ϖ} := by
    refine Filter.eventually_cofinite.2 ((Set.finite_range
      (Sum.inl : {v : AlgebraicCurve.Place k F // v ∈ S} → CurvePlaceLevelFactorIndex k F S)).subset ?_)
    intro i hi
    rcases i with v | v
    · exact ⟨v, rfl⟩
    · exfalso
      apply hi
      obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (curvePlaceCompletionIntegers v.1)
      exact ⟨ϖ, hϖ, (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ⟩
  exact localFactorSpectrumWarnings_of_ringEquiv (curvePlaceLevelFactorRingEquiv k F S) _
    (fun _ _ => rfl) hϖ

/-- Conrad's product-spectrum warnings, Moret-Bailly's example and both adelic levels. -/
theorem adelicProductSpectrumWarnings : AdelicProductSpectrumWarningsStatement.{u} :=
  ⟨productFactorSpectrum, localProductSpectrumWarnings, moretBaillyDiagonal,
    numberFieldLevelSpectrumWarnings, curvePlaceLevelSpectrumWarnings⟩

end Langlands.Global
