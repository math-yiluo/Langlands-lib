import Langlands.GroupScheme.KostantRosenlicht.Hopf

/-! # Translation-stable subalgebras of a unipotent coordinate algebra -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology

namespace Langlands.GroupScheme.KostantRosenlicht

open AffineLinearEmbedding

/-- Two `K`-points with the same kernel are equal. -/
theorem algHom_eq_of_ker_eq {K : Type*} [Field K] {A : Type*} [CommRing A] [Algebra K A]
    {χ ψ : A →ₐ[K] K} (h : RingHom.ker χ = RingHom.ker ψ) : χ = ψ := by
  ext a
  have ha : a - algebraMap K A (χ a) ∈ RingHom.ker ψ := by
    rw [← h, RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self_apply, sub_self]
  rw [RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self_apply, sub_eq_zero] at ha
  exact ha.symm

variable {k : Type u} [Field k] [IsAlgClosed k]
  {F : CommAlgCat.{u} (CommRingCat.of k) ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} (CommRingCat.of k)} (e : (F ⋙ forget GrpCat).CorepresentableBy B)
  [Algebra.FiniteType (CommRingCat.of k) B]

omit [IsAlgClosed k] in
/-- A `k`-point of a subalgebra whose kernel is the contraction of a prime of `B` is the
restriction of a `k`-point of `B`. -/
theorem exists_comp_val_eq [IsAlgClosed k] {C : Subalgebra (CommRingCat.of k) B}
    (y : C →ₐ[CommRingCat.of k] CommRingCat.of k)
    (hy : ∃ P : PrimeSpectrum B, Ideal.comap C.val P.asIdeal = RingHom.ker y) :
    ∃ χ : B →ₐ[CommRingCat.of k] CommRingCat.of k, χ.comp C.val = y := by
  obtain ⟨P, hP⟩ := hy
  obtain ⟨M, hM, hPM⟩ := Ideal.exists_le_maximal P.asIdeal P.2.ne_top
  obtain ⟨χ, hχ⟩ := exists_algHom_ker_eq (k := CommRingCat.of k) M
  refine ⟨χ, algHom_eq_of_ker_eq ?_⟩
  have hmax : (RingHom.ker y).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective y fun c => ⟨algebraMap _ C c, y.commutes c⟩
  have hcomap : RingHom.ker (χ.comp C.val) = Ideal.comap C.val M := by
    ext c
    rw [RingHom.mem_ker, AlgHom.comp_apply, ← RingHom.mem_ker, hχ, Ideal.mem_comap]
  rw [hcomap]
  refine (hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_).symm
  rw [← hP]
  exact Ideal.comap_mono hPM

variable [IsReduced B]

/-- A finitely generated subalgebra of the coordinate algebra of a unipotent group which is
stable under right translations by `k`-points: every prime of the subalgebra lies under a prime
of `B`. -/
theorem range_comap_val_eq_univ (hU : IsUnipotent (Corepresented.groupScheme F e))
    (C : Subalgebra (CommRingCat.of k) B) [Algebra.FiniteType (CommRingCat.of k) C]
    (hC : ∀ v, ∀ c ∈ C, charTranslate e v c ∈ C) :
    Set.range (PrimeSpectrum.comap C.val.toRingHom) = Set.univ := by
  set Y := Set.range (PrimeSpectrum.comap C.val.toRingHom) with hYdef
  have : Nontrivial C := ((counit e).comp C.val).toRingHom.domain_nontrivial
  have : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing (CommRingCat.of k) C
  -- Chevalley: `Y` is constructible, and so is its complement.
  have hfp : C.val.toRingHom.FinitePresentation := by
    refine RingHom.FinitePresentation.of_finiteType.mp
      (RingHom.FiniteType.of_comp_finiteType (f := algebraMap (CommRingCat.of k) C) ?_)
    have hcomp : C.val.toRingHom.comp (algebraMap (CommRingCat.of k) C) =
        algebraMap (CommRingCat.of k) B := RingHom.ext fun _ => rfl
    rw [hcomp, RingHom.finiteType_algebraMap]
    infer_instance
  have hYc : IsConstructible Yᶜ := (PrimeSpectrum.isConstructible_range_comap hfp).compl
  obtain ⟨S, _, g, hg⟩ := PrimeSpectrum.exists_range_eq_of_isConstructible hYc
  -- `g` is not injective: otherwise a minimal prime of `C` would lie in both `Y` and `Yᶜ`.
  obtain ⟨f, hf0, hgf⟩ : ∃ f : C, f ≠ 0 ∧ g f = 0 := by
    by_contra! h
    have hinj : Function.Injective g :=
      (injective_iff_map_eq_zero g).mpr fun a ha => by_contra fun hne => h a hne ha
    obtain ⟨M, hM⟩ := Ideal.exists_maximal C
    obtain ⟨p, hp, -⟩ := Ideal.exists_minimalPrimes_le (I := ⊥) (J := M) bot_le
    have : p.IsPrime := hp.1.1
    obtain ⟨q, hq, hqp⟩ := Ideal.exists_comap_eq_of_mem_minimalPrimes_of_injective hinj p hp
    obtain ⟨q', hq', hq'p⟩ := Ideal.exists_comap_eq_of_mem_minimalPrimes_of_injective
      (f := C.val.toRingHom) Subtype.val_injective p hp
    have h1 : (⟨p, this⟩ : PrimeSpectrum C) ∈ Yᶜ := by
      rw [← hg]
      exact ⟨⟨q, hq⟩, PrimeSpectrum.ext hqp⟩
    exact h1 ⟨⟨q', hq'⟩, PrimeSpectrum.ext hq'p⟩
  -- The `k`-points of `C` that are not restrictions of `k`-points of `B`.
  set Zc : Set (C →ₐ[CommRingCat.of k] CommRingCat.of k) :=
    {y | ∀ χ : B →ₐ[CommRingCat.of k] CommRingCat.of k, χ.comp C.val ≠ y} with hZc
  have hZf : ∀ y ∈ Zc, y f = 0 := by
    intro y hy
    have hyY : (⟨RingHom.ker y, RingHom.ker_isPrime y⟩ : PrimeSpectrum C) ∈ Yᶜ := by
      rintro ⟨P, hP⟩
      obtain ⟨χ, hχ⟩ := exists_comp_val_eq y ⟨P, congrArg PrimeSpectrum.asIdeal hP⟩
      exact hy χ hχ
    rw [← hg] at hyY
    obtain ⟨Q, hQ⟩ := hyY
    have hfQ : f ∈ (PrimeSpectrum.comap g Q).asIdeal := by
      rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, hgf]
      exact Q.asIdeal.zero_mem
    rw [hQ] at hfQ
    exact hfQ
  -- Right translations of `C`.
  let τ : (B →ₐ[CommRingCat.of k] CommRingCat.of k) → (C →ₐ[CommRingCat.of k] C) :=
    fun v => ((charTranslate e v).comp C.val).codRestrict C fun c => hC v c c.2
  have hτ : ∀ v (c : C), τ v (τ (charInv e v) c) = c := fun v c =>
    Subtype.ext (charTranslate_charTranslate_charInv e v c)
  have hZτ : ∀ v, ∀ y ∈ Zc, y.comp (τ v) ∈ Zc := by
    intro v y hy χ hχ
    apply hy (χ.comp (charTranslate e (charInv e v)))
    ext c
    have := congrArg (fun z : C →ₐ[CommRingCat.of k] CommRingCat.of k => z (τ (charInv e v) c)) hχ
    simp only [AlgHom.comp_apply, hτ] at this
    exact this
  -- The subspace of functions in `C` vanishing on `Zc`.
  let J : Submodule (CommRingCat.of k) C :=
    { carrier := {c | ∀ y ∈ Zc, y c = 0}
      add_mem' := fun ha hb y hy => by rw [map_add, ha y hy, hb y hy, add_zero]
      zero_mem' := fun y _ => map_zero y
      smul_mem' := fun r c hc y hy => by rw [map_smul, hc y hy, smul_zero] }
  let W : Submodule (CommRingCat.of k) B := J.map C.val.toLinearMap
  have hW : ∀ v, ∀ w ∈ W, charTranslate e v w ∈ W := by
    rintro v _ ⟨c, hc, rfl⟩
    exact ⟨τ v c, fun y hy => hc _ (hZτ v y hy), rfl⟩
  have hWne : W ≠ ⊥ := by
    rw [Submodule.ne_bot_iff]
    exact ⟨f, ⟨f, hZf, rfl⟩, fun h => hf0 (Subtype.ext h)⟩
  obtain ⟨c, hc, hc1⟩ := one_mem_of_rightAct_mem e hU
    (fun m w hw => rightAct_mem_of_charTranslate_mem e hW m hw) hWne
  have hc1' : c = 1 := Subtype.ext hc1
  have hZ : ∀ y, y ∉ Zc := fun y hy => by
    have := hc y hy
    rw [hc1', map_one] at this
    exact one_ne_zero this
  -- Hence `Yᶜ` has no closed points, so it is empty.
  have : IsJacobsonRing C := isJacobsonRing_of_finiteType (A := CommRingCat.of k)
  refine Set.compl_empty_iff.mp (eq_empty_of_isConstructible hYc fun x hx hmax => hx ?_)
  obtain ⟨y, hy⟩ := exists_algHom_ker_eq (k := CommRingCat.of k) x.asIdeal
  have hy' := hZ y
  simp only [hZc, Set.mem_ofPred_eq, not_forall, not_not] at hy'
  obtain ⟨χ, hχ⟩ := hy'
  refine ⟨⟨RingHom.ker χ, RingHom.ker_isPrime χ⟩, PrimeSpectrum.ext ?_⟩
  rw [PrimeSpectrum.comap_asIdeal, ← hy, ← hχ]
  ext c
  rw [Ideal.mem_comap, RingHom.mem_ker, RingHom.mem_ker]
  rfl

/-- **Kostant–Rosenlicht, algebraic form.** If `φ : A → B` is a map of finitely generated
`k`-algebras into the coordinate algebra of a unipotent group whose image is stable under right
translations by `k`-points, then the image of `Spec B → Spec A` is the closed set cut out by the
kernel of `φ`. -/
theorem range_comap_eq_zeroLocus (hU : IsUnipotent (Corepresented.groupScheme F e))
    {A : Type*} [CommRing A] [Algebra (CommRingCat.of k) A]
    [Algebra.FiniteType (CommRingCat.of k) A] (φ : A →ₐ[CommRingCat.of k] B)
    (hφ : ∀ v a, ∃ a', charTranslate e v (φ a) = φ a') :
    Set.range (PrimeSpectrum.comap φ.toRingHom) = PrimeSpectrum.zeroLocus (RingHom.ker φ) := by
  have : Algebra.FiniteType (CommRingCat.of k) φ.range :=
    Algebra.FiniteType.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  have hC : ∀ v, ∀ c ∈ φ.range, charTranslate e v c ∈ φ.range := by
    rintro v _ ⟨a, rfl⟩
    obtain ⟨a', ha'⟩ := hφ v a
    exact ⟨a', ha'.symm⟩
  have hφ' : φ.toRingHom = φ.range.val.toRingHom.comp φ.rangeRestrict.toRingHom :=
    RingHom.ext fun _ => rfl
  rw [hφ', PrimeSpectrum.comap_comp, Set.range_comp, range_comap_val_eq_univ e hU _ hC,
    Set.image_univ, range_comap_of_surjective _ _ φ.rangeRestrict_surjective]
  exact congrArg _ (congrArg _ φ.ker_rangeRestrict)

end Langlands.GroupScheme.KostantRosenlicht
