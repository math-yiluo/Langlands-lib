import Langlands.AlgebraicGeometry.LangWeil.Slicing.Bridges
import Langlands.AlgebraicGeometry.LangWeil.Slicing.Dimension
import Langlands.AlgebraicGeometry.LangWeil.Slicing.GenericImage
import Langlands.AlgebraicGeometry.AffineChartPoints
import Langlands.AlgebraicGeometry.SchemePureDimensionProof
import Langlands.Algebra.GenericIrreducibilityReduction

/-!
# Reduction of the uniform Lang–Weil estimate to affine families over integral bases
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.LangWeil.Slicing

open SchemeFiberGeometry

/-- **Ring-level interface.** The uniform Lang–Weil estimate in fibre dimension `e` for affine
families `Spec A → Spec R` over integral bases of finite type over `ℤ`, whose base changes to
fields away from `r₀ = 0` have prime nilradical and dimension `e`: away from some `r = 0`, the
number of `κ`-points is `(#κ) ^ e` up to an error `C (#κ) ^ (e - 1/2)`. -/
def AffineFamilyLangWeil (e : ℕ) : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [Algebra.FiniteType ℤ R] (A : Type u) [CommRing A]
    [Algebra R A] [Algebra.FiniteType R A] (r₀ : R), r₀ ≠ 0 →
    (∀ (K : Type u) [Field K] [Algebra R K], algebraMap R K r₀ ≠ 0 →
      (nilradical (K ⊗[R] A)).IsPrime ∧ ringKrullDim (K ⊗[R] A) = e) →
    ∃ r : R, r ≠ 0 ∧ ∃ C : ℝ, 0 < C ∧ ∀ (κ : Type u) [Field κ] [Finite κ] [Algebra R κ],
      algebraMap R κ r ≠ 0 →
        |(Nat.card (A →ₐ[R] κ) : ℝ) - (Nat.card κ : ℝ) ^ e| ≤
          C * (Nat.card κ : ℝ) ^ ((e : ℝ) - 1 / 2)

section RingLevel

/-- Algebra maps from an algebra of finite type to a finite ring form a finite set. -/
theorem finite_algHom_of_finiteType (R₀ B κ : Type*) [CommRing R₀] [CommRing B] [Algebra R₀ B]
    [Algebra.FiniteType R₀ B] [CommRing κ] [Algebra R₀ κ] [Finite κ] :
    Finite (B →ₐ[R₀] κ) := by
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := R₀) (A := B)
  exact Finite.of_injective (fun φ : B →ₐ[R₀] κ => fun x : (s : Set B) => φ x)
    fun φ ψ h => AlgHom.ext_of_adjoin_eq_top hs fun x hx => congrFun h ⟨x, hx⟩

/-- If no prime of `A` lies over the zero ideal of the domain `R`, some nonzero element of `R`
becomes nilpotent in `A`. -/
theorem exists_ne_zero_isNilpotent_of_forall_comap_ne {R A : Type*} [CommRing R] [IsDomain R]
    [CommRing A] [Algebra R A]
    (h : ∀ Q : Ideal A, Q.IsPrime → Q.comap (algebraMap R A) ≠ ⊥) :
    ∃ c : R, c ≠ 0 ∧ IsNilpotent (algebraMap R A c) := by
  by_contra hc
  push Not at hc
  let M : Submonoid A := (nonZeroDivisors R).map (algebraMap R A)
  have hdisj : Disjoint ((⊥ : Ideal A) : Set A) M := by
    rw [Set.disjoint_left]
    rintro _ hx ⟨c, hc0, rfl⟩
    exact hc c (nonZeroDivisors.ne_zero hc0) ⟨1, by simpa using hx⟩
  obtain ⟨Q, hQ, -, hQM⟩ := Ideal.exists_le_prime_disjoint ⊥ M hdisj
  refine h Q hQ (eq_bot_iff.mpr fun x hx => ?_)
  by_contra hx0
  exact Set.disjoint_left.mp hQM hx ⟨x, mem_nonZeroDivisors_of_ne_zero hx0, rfl⟩

/-- A ring receiving a surjection from a ring of finite type over `ℤ` is of finite type over
`ℤ`. -/
theorem finiteType_int_of_surjective {R R' : Type*} [CommRing R] [CommRing R']
    [Algebra.FiniteType ℤ R] (g : R →+* R') (hg : Function.Surjective g) :
    Algebra.FiniteType ℤ R' := by
  rw [← RingHom.finiteType_algebraMap,
    show algebraMap ℤ R' = g.comp (algebraMap ℤ R) from RingHom.ext_int _ _]
  exact (RingHom.FiniteType.of_surjective g hg).comp
    (RingHom.finiteType_algebraMap.mpr inferInstance)

variable {R₀ : Type u} [CommRing R₀] (𝔭 : Ideal R₀) [𝔭.IsPrime]
  (B : Type u) [CommRing B] [Algebra R₀ B]

/-- The `R₀ ⧸ 𝔭`-algebra structure of an `R₀`-algebra in which `𝔭` vanishes. -/
noncomputable abbrev quotientAlgebra (K : Type*) [CommRing K] [Algebra R₀ K]
    (h : 𝔭 ≤ RingHom.ker (algebraMap R₀ K)) : Algebra (R₀ ⧸ 𝔭) K :=
  (Ideal.Quotient.lift 𝔭 (algebraMap R₀ K) fun _ ha => h ha).toAlgebra

omit [𝔭.IsPrime] in
theorem quotientAlgebra_isScalarTower (K : Type*) [CommRing K] [Algebra R₀ K]
    (h : 𝔭 ≤ RingHom.ker (algebraMap R₀ K)) :
    letI := quotientAlgebra 𝔭 K h
    IsScalarTower R₀ (R₀ ⧸ 𝔭) K :=
  letI := quotientAlgebra 𝔭 K h
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- **Chevalley near a prime.** If a prime of `B` lies over `𝔭`, then for some `r ∉ 𝔭` every
field `K` over `R₀ ⧸ 𝔭` in which `r` does not vanish gives a nonzero `K ⊗[R₀] B`. -/
theorem exists_not_mem_forall_nontrivial [IsNoetherianRing R₀] [Algebra.FiniteType R₀ B]
    (P : Ideal B) [P.IsPrime] (hP : P.comap (algebraMap R₀ B) = 𝔭) :
    ∃ r : R₀, r ∉ 𝔭 ∧ ∀ (K : Type u) [Field K] [Algebra R₀ K],
      𝔭 ≤ RingHom.ker (algebraMap R₀ K) → algebraMap R₀ K r ≠ 0 → Nontrivial (K ⊗[R₀] B) := by
  have hle : 𝔭 ≤ RingHom.ker (algebraMap R₀ (B ⧸ P)) := by
    intro x hx
    rw [RingHom.mem_ker, IsScalarTower.algebraMap_apply R₀ B (B ⧸ P),
      Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_comap, hP]
    exact hx
  let := quotientAlgebra 𝔭 (B ⧸ P) hle
  have := quotientAlgebra_isScalarTower 𝔭 (B ⧸ P) hle
  let φ : (R₀ ⧸ 𝔭) ⊗[R₀] B →ₐ[R₀ ⧸ 𝔭] B ⧸ P :=
    Algebra.TensorProduct.liftEquivRight R₀ (R₀ ⧸ 𝔭) B (B ⧸ P) (Ideal.Quotient.mkₐ R₀ P)
  have hQ : (RingHom.ker φ).comap (algebraMap (R₀ ⧸ 𝔭) ((R₀ ⧸ 𝔭) ⊗[R₀] B)) = ⊥ := by
    refine eq_bot_iff.mpr fun x hx => ?_
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes] at hx
    change (Ideal.Quotient.mk P (algebraMap R₀ B x)) = 0 at hx
    rw [Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_comap, hP] at hx
    exact (Ideal.Quotient.eq_zero_iff_mem.mpr hx : _)
  have : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  obtain ⟨r, hr, hK⟩ := exists_ne_zero_forall_nontrivial_tensor (R := R₀ ⧸ 𝔭) (RingHom.ker φ) hQ
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
  refine ⟨r, fun h => hr (Ideal.Quotient.eq_zero_iff_mem.mpr h), fun K _ _ hK𝔭 hrK => ?_⟩
  let := quotientAlgebra 𝔭 K hK𝔭
  have := quotientAlgebra_isScalarTower 𝔭 K hK𝔭
  have := hK K hrK
  exact (Algebra.TensorProduct.cancelBaseChange R₀ (R₀ ⧸ 𝔭) K K B).injective.nontrivial

/-- If no prime of `B` lies over `𝔭`, then for some `r ∉ 𝔭` every field `K` over `R₀ ⧸ 𝔭` in
which `r` does not vanish gives `K ⊗[R₀] B = 0`. -/
theorem exists_not_mem_forall_subsingleton
    (hP : ∀ P : Ideal B, P.IsPrime → P.comap (algebraMap R₀ B) ≠ 𝔭) :
    ∃ r : R₀, r ∉ 𝔭 ∧ ∀ (K : Type u) [Field K] [Algebra R₀ K],
      𝔭 ≤ RingHom.ker (algebraMap R₀ K) → algebraMap R₀ K r ≠ 0 →
        Subsingleton (K ⊗[R₀] B) := by
  have hQ : ∀ Q : Ideal ((R₀ ⧸ 𝔭) ⊗[R₀] B), Q.IsPrime →
      Q.comap (algebraMap (R₀ ⧸ 𝔭) ((R₀ ⧸ 𝔭) ⊗[R₀] B)) ≠ ⊥ := by
    intro Q hQ hQ0
    refine hP (Q.comap (Algebra.TensorProduct.includeRight : B →ₐ[R₀] (R₀ ⧸ 𝔭) ⊗[R₀] B))
      (Ideal.comap_isPrime _ _) ?_
    ext x
    rw [Ideal.mem_comap, Ideal.mem_comap, AlgHom.commutes,
      IsScalarTower.algebraMap_apply R₀ (R₀ ⧸ 𝔭), ← Ideal.mem_comap, hQ0, Ideal.mem_bot,
      Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨c, hc, hnil⟩ := exists_ne_zero_isNilpotent_of_forall_comap_ne hQ
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
  refine ⟨c, fun h => hc (Ideal.Quotient.eq_zero_iff_mem.mpr h), fun K _ _ hK𝔭 hcK => ?_⟩
  let := quotientAlgebra 𝔭 K hK𝔭
  have := quotientAlgebra_isScalarTower 𝔭 K hK𝔭
  by_contra hnt
  rw [not_subsingleton_iff_nontrivial] at hnt
  have hu : IsUnit (algebraMap K (K ⊗[R₀] B) (algebraMap R₀ K c)) := (IsUnit.mk0 _ hcK).map _
  refine hu.not_isNilpotent ?_
  have h := hnil.map
    (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R₀ (R₀ ⧸ 𝔭) K) (AlgHom.id R₀ B))
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.map_tmul] at h
  rw [Algebra.TensorProduct.algebraMap_apply]
  exact h

/-- **Chevalley on a basic open.** If a prime of `B` lies over `𝔭` and avoids `a`, then for some
`r ∉ 𝔭` every field `K` over `R₀ ⧸ 𝔭` in which `r` does not vanish makes `1 ⊗ a` non-nilpotent
in `K ⊗[R₀] B`. -/
theorem exists_not_mem_forall_not_isNilpotent [IsNoetherianRing R₀] [Algebra.FiniteType R₀ B]
    (a : B) (P : Ideal B) [P.IsPrime] (haP : a ∉ P) (hP : P.comap (algebraMap R₀ B) = 𝔭) :
    ∃ r : R₀, r ∉ 𝔭 ∧ ∀ (K : Type u) [Field K] [Algebra R₀ K],
      𝔭 ≤ RingHom.ker (algebraMap R₀ K) → algebraMap R₀ K r ≠ 0 →
        ¬IsNilpotent ((1 : K) ⊗ₜ[R₀] a) := by
  let L := Localization.Away a
  have hdisj : Disjoint (Submonoid.powers a : Set B) P :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime a).mpr haP
  let P' : Ideal L := P.map (algebraMap B L)
  have : P'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint _ L P ‹_› hdisj
  have hP' : P'.comap (algebraMap R₀ L) = 𝔭 := by
    rw [IsScalarTower.algebraMap_eq R₀ B L, ← Ideal.comap_comap]
    change Ideal.comap _ (Ideal.under B P') = 𝔭
    rw [IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers a) L ‹_› hdisj, hP]
  obtain ⟨r, hr, hK⟩ := exists_not_mem_forall_nontrivial 𝔭 L P' hP'
  refine ⟨r, hr, fun K _ _ hK𝔭 hrK hnil => ?_⟩
  have := hK K hK𝔭 hrK
  have hu : IsUnit ((1 : K) ⊗ₜ[R₀] (algebraMap B L a)) :=
    (IsLocalization.Away.algebraMap_isUnit a).map
      (Algebra.TensorProduct.includeRight : L →ₐ[R₀] K ⊗[R₀] L)
  refine hu.not_isNilpotent ?_
  have h := hnil.map (Algebra.TensorProduct.map (AlgHom.id R₀ K) (IsScalarTower.toAlgHom R₀ B L))
  rwa [Algebra.TensorProduct.map_tmul] at h

/-- Killing an element `a` of `B` whose image `1 ⊗ a` in the scalar extension `K ⊗[R₀] B`, a ring
with prime nilradical and dimension `e + 1`, is not nilpotent leaves dimension at most `e`. -/
theorem ringKrullDim_tensor_quotient_le (K : Type*) [Field K] [Algebra R₀ K] (a : B) {e : ℕ}
    (hT : (nilradical (K ⊗[R₀] B)).IsPrime) (hdim : ringKrullDim (K ⊗[R₀] B) = (e + 1 : ℕ))
    (ha : ¬IsNilpotent ((1 : K) ⊗ₜ[R₀] a)) :
    ringKrullDim (K ⊗[R₀] (B ⧸ Ideal.span {a})) ≤ e := by
  let I : Ideal (K ⊗[R₀] B) := Ideal.span {(1 : K) ⊗ₜ[R₀] a}
  have hI : ¬I ≤ nilradical (K ⊗[R₀] B) := by
    rw [Ideal.span_singleton_le_iff_mem, mem_nilradical]
    exact ha
  have h1 := ringKrullDim_quotient_succ_le_of_not_le_nilradical hT hI
  let φ : K ⊗[R₀] B →ₐ[R₀] K ⊗[R₀] (B ⧸ Ideal.span {a}) :=
    Algebra.TensorProduct.map (AlgHom.id R₀ K) (Ideal.Quotient.mkₐ R₀ _)
  have hφ : Function.Surjective φ :=
    Algebra.TensorProduct.map_surjective _ _ Function.surjective_id Ideal.Quotient.mk_surjective
  have h2 : ringKrullDim (K ⊗[R₀] (B ⧸ Ideal.span {a})) ≤ ringKrullDim ((K ⊗[R₀] B) ⧸ I) := by
    refine ringKrullDim_le_of_surjective (Ideal.Quotient.lift I φ.toRingHom fun y hy => ?_)
      (Ideal.Quotient.lift_surjective_of_surjective _ _ hφ)
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    change φ (c * (1 ⊗ₜ[R₀] a)) = 0
    rw [map_mul, Algebra.TensorProduct.map_tmul, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self a),
      TensorProduct.tmul_zero, mul_zero]
  rw [hdim] at h1
  refine h2.trans ?_
  generalize ringKrullDim ((K ⊗[R₀] B) ⧸ I) = d at h1 ⊢
  induction d using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe m =>
    norm_cast at h1 ⊢
    exact (ENat.add_le_add_iff_right ENat.one_ne_top).mp h1

/-- If `K ⊗[R₀] B` vanishes, so does `K ⊗[R₀] (B ⧸ I)`. -/
theorem subsingleton_tensor_quotient (K : Type*) [Field K] [Algebra R₀ K] (I : Ideal B)
    [Subsingleton (K ⊗[R₀] B)] : Subsingleton (K ⊗[R₀] (B ⧸ I)) :=
  (Algebra.TensorProduct.map_surjective (AlgHom.id R₀ K) (Ideal.Quotient.mkₐ R₀ I)
    Function.surjective_id Ideal.Quotient.mk_surjective).subsingleton

/-- Algebra maps killing `a` factor through `B ⧸ (a)`. -/
theorem natCard_algHom_eq_zero_le (κ : Type*) [CommRing κ] [Algebra R₀ κ] [Finite κ]
    [Algebra.FiniteType R₀ B] (a : B) :
    Nat.card {ψ : B →ₐ[R₀] κ // ψ a = 0} ≤ Nat.card (B ⧸ Ideal.span {a} →ₐ[R₀] κ) := by
  have := finite_algHom_of_finiteType R₀ (B ⧸ Ideal.span {a}) κ
  refine Nat.card_le_card_of_surjective
    (fun φ => ⟨φ.comp (Ideal.Quotient.mkₐ R₀ _), ?_⟩) fun ψ => ?_
  · rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self a), map_zero]
  · refine ⟨Ideal.Quotient.liftₐ _ ψ.1 fun y hy => ?_, Subtype.ext (Ideal.Quotient.liftₐ_comp _ _ _)⟩
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    rw [map_mul, ψ.2, mul_zero]

end RingLevel

section ChartFibre

variable {X S : Scheme.{u}} (f : X ⟶ S) {S₀ : S.Opens} (hS₀ : IsAffineOpen S₀)
  (c : Chart S₀ (Over.mk f)) (K : Type u) [Field K] [Algebra Γ(S, S₀) K]

/-- The base change of an affine chart to a field, as an open subscheme of the base change of
the whole scheme. -/
noncomputable def chartPullbackMap :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, S₀) c.Ring)))
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, S₀) K))) ⟶ pullback f (testMap hS₀ K) :=
  pullback.map _ _ _ _ c.fromSpec (𝟙 _) hS₀.fromSpec (c.fromSpec_hom hS₀).symm
    (by simp [testMap])

instance : IsOpenImmersion (chartPullbackMap f hS₀ c K) := by
  unfold chartPullbackMap
  infer_instance

theorem irreducibleSpace_pullback_testMap [GeometricallyIrreducible f] :
    IrreducibleSpace ↥(pullback f (testMap hS₀ K)) :=
  GeometricallyIrreducible.geometrically_irreducibleSpace _ _ _ (.of_hasPullback _ _)

theorem hasPureDimension_pullback_testMap [LocallyOfFiniteType f] {E : ℕ}
    (hdim : ∀ s : S, HasPureDimension (f.fiber s) E) :
    HasPureDimension (pullback f (testMap hS₀ K)) E := by
  let y : Spec (CommRingCat.of K) := IsLocalRing.closedPoint K
  have h := (hasPureDimension_locallyFiniteType_fiberBaseChange_iff
    (IsPullback.of_hasPullback f (testMap hS₀ K)) y E).mpr (hdim _)
  have hpre : (pullback.snd f (testMap hS₀ K)) ⁻¹' {y} = Set.univ := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact Subsingleton.elim _ _
  exact h.of_homeomorph (((pullback.snd f (testMap hS₀ K)).fiberHomeo y).trans
    ((Homeomorph.setCongr hpre).trans (Homeomorph.Set.univ _)))

include hS₀ in
/-- **Fibres of affine charts.** For a geometrically irreducible morphism, locally of finite
type, whose fibres have pure dimension `E`, and an affine chart `U` over an affine open `S₀`,
every nonzero base change `K ⊗ Γ(U)` to a field has prime nilradical and dimension `E`. -/
theorem chart_isPrime_and_dim [GeometricallyIrreducible f] [LocallyOfFiniteType f] {E : ℕ}
    (hdim : ∀ s : S, HasPureDimension (f.fiber s) E)
    [Nontrivial (K ⊗[Γ(S, S₀)] c.Ring)] :
    (nilradical (K ⊗[Γ(S, S₀)] c.Ring)).IsPrime ∧
      ringKrullDim (K ⊗[Γ(S, S₀)] c.Ring) = E := by
  let Q := pullback (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, S₀) c.Ring)))
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, S₀) K)))
  let e : Q ≅ Spec (CommRingCat.of (K ⊗[Γ(S, S₀)] c.Ring)) :=
    pullbackSymmetry _ _ ≪≫ pullbackSpecIso Γ(S, S₀) K c.Ring
  have : Nonempty Q := ⟨e.inv (Nonempty.some inferInstance)⟩
  have : IrreducibleSpace ↥(pullback f (testMap hS₀ K)) :=
    irreducibleSpace_pullback_testMap f hS₀ K
  have hirr : IrreducibleSpace Q := (chartPullbackMap f hS₀ c K).isOpenEmbedding.irreducibleSpace
  have hprime : (nilradical (K ⊗[Γ(S, S₀)] c.Ring)).IsPrime :=
    (irreducibleSpace_pullbackSpec_iff_nilradical_isPrime _ _ _).mp hirr
  refine ⟨hprime, ?_⟩
  have hP := hasPureDimension_pullback_testMap f hS₀ K hdim
  have hcomp := componentOpenDimensionInvariant_locallyOfFiniteType K _
    (pullback.snd f (testMap hS₀ K))
  have hU := hP.open_of_componentOpenDimensionInvariant hcomp
    (chartPullbackMap f hS₀ c K).opensRange
  have hQ : HasPureDimension Q E :=
    (hasPureDimension_iff_of_iso (chartPullbackMap f hS₀ c K).isoOpensRange).mpr hU
  have hR : HasPureRingDimension (K ⊗[Γ(S, S₀)] c.Ring) E :=
    hasPureDimension_spec_iff.mp ((hasPureDimension_iff_of_iso e).mp hQ)
  have hmin : nilradical (K ⊗[Γ(S, S₀)] c.Ring) ∈ minimalPrimes (K ⊗[Γ(S, S₀)] c.Ring) := by
    refine ⟨⟨hprime, bot_le⟩, fun p hp _ => ?_⟩
    have : p.IsPrime := hp.1
    exact nilradical_le_prime p
  rw [← ringKrullDim_quotient_nilradical]
  exact hR _ hmin

end ChartFibre

section Induction

/-- **Noetherian induction over the base.** Let `P κ C` be a property of finite fields `κ` over
a Noetherian ring `R₀` and real constants `C`, monotone in `C`. If for every prime `𝔭` of `R₀`
some `r ∉ 𝔭` and some constant work for all `κ` in which `𝔭` vanishes and `r` does not, then one
constant works for all `κ`. -/
theorem exists_forall_of_forall_isPrime {R₀ : Type u} [CommRing R₀] [IsNoetherianRing R₀]
    (P : ∀ (κ : Type u) [Field κ] [Finite κ] [Algebra R₀ κ], ℝ → Prop)
    (hmono : ∀ (κ : Type u) [Field κ] [Finite κ] [Algebra R₀ κ] (C C' : ℝ), C ≤ C' →
      P κ C → P κ C')
    (hprime : ∀ 𝔭 : Ideal R₀, 𝔭.IsPrime → ∃ r : R₀, r ∉ 𝔭 ∧ ∃ C : ℝ,
      ∀ (κ : Type u) [Field κ] [Finite κ] [Algebra R₀ κ],
        𝔭 ≤ RingHom.ker (algebraMap R₀ κ) → algebraMap R₀ κ r ≠ 0 → P κ C) :
    ∃ C : ℝ, ∀ (κ : Type u) [Field κ] [Finite κ] [Algebra R₀ κ], P κ C := by
  suffices h : ∀ 𝔞 : Ideal R₀, ∃ C : ℝ, ∀ (κ : Type u) [Field κ] [Finite κ] [Algebra R₀ κ],
      𝔞 ≤ RingHom.ker (algebraMap R₀ κ) → P κ C by
    obtain ⟨C, hC⟩ := h ⊥
    exact ⟨C, fun κ _ _ _ => hC κ bot_le⟩
  refine IsNoetherian.induction fun (𝔞 : Ideal R₀) ih => ?_
  by_cases htop : 𝔞 = ⊤
  · refine ⟨0, fun κ _ _ _ h => absurd (h (htop ▸ Submodule.mem_top : (1 : R₀) ∈ 𝔞)) ?_⟩
    rw [RingHom.mem_ker, map_one]
    exact one_ne_zero
  have hlt : ∀ x : R₀, x ∉ 𝔞 → 𝔞 < 𝔞 ⊔ Ideal.span {x} := fun x hx =>
    left_lt_sup.mpr fun h => hx (Ideal.span_singleton_le_iff_mem _ |>.mp h)
  have hle : ∀ (κ : Type u) [Field κ] [Algebra R₀ κ] (x : R₀),
      𝔞 ≤ RingHom.ker (algebraMap R₀ κ) → algebraMap R₀ κ x = 0 →
        𝔞 ⊔ Ideal.span {x} ≤ RingHom.ker (algebraMap R₀ κ) := fun κ _ _ x h hx =>
    sup_le h ((Ideal.span_singleton_le_iff_mem _).mpr hx)
  by_cases hp : 𝔞.IsPrime
  · obtain ⟨r, hr, C₁, h₁⟩ := hprime 𝔞 hp
    obtain ⟨C₂, h₂⟩ := ih _ (hlt r hr)
    refine ⟨max C₁ C₂, fun κ _ _ _ h => ?_⟩
    by_cases hrκ : algebraMap R₀ κ r = 0
    · exact hmono κ _ _ (le_max_right _ _) (h₂ κ (hle κ r h hrκ))
    · exact hmono κ _ _ (le_max_left _ _) (h₁ κ h hrκ)
  · rw [Ideal.isPrime_iff] at hp
    push Not at hp
    obtain ⟨x, y, hxy, hx, hy⟩ := hp htop
    obtain ⟨C₁, h₁⟩ := ih _ (hlt x hx)
    obtain ⟨C₂, h₂⟩ := ih _ (hlt y hy)
    refine ⟨max C₁ C₂, fun κ _ _ _ h => ?_⟩
    have hxyκ : algebraMap R₀ κ x * algebraMap R₀ κ y = 0 := by
      rw [← map_mul]
      exact h hxy
    rcases mul_eq_zero.mp hxyκ with hxκ | hyκ
    · exact hmono κ _ _ (le_max_left _ _) (h₁ κ (hle κ x h hxκ))
    · exact hmono κ _ _ (le_max_right _ _) (h₂ κ (hle κ y h hyκ))

end Induction

section Counting

variable {X S : Scheme.{u}} (f : X ⟶ S) {S₀ : S.Opens} (hS₀ : IsAffineOpen S₀)

/-- The `κ`-points of `X` over the point `testMap hS₀ κ` of `S` are the morphisms
`testObj hS₀ κ ⟶ Over.mk f` over `S`. -/
noncomputable def pointsEquiv (κ : Type u) [CommRing κ] [Algebra Γ(S, S₀) κ] :
    {x : Spec (CommRingCat.of κ) ⟶ X // x ≫ f = testMap hS₀ κ} ≃
      (testObj hS₀ κ ⟶ Over.mk f) where
  toFun x := Over.homMk x.1 x.2
  invFun y := ⟨y.left, Over.w y⟩
  left_inv _ := rfl
  right_inv _ := Over.OverMorphism.ext rfl

/-- The point of a chart given by a prime `y` lies in the basic open of `a` iff `a ∉ y`. -/
theorem fromSpec_mem_basicOpen_iff (c : Chart S₀ (Over.mk f)) (a : Γ(X, c.U))
    (y : Spec Γ(X, c.U)) :
    c.isAffine.fromSpec y ∈ X.basicOpen a ↔ a ∉ (y : PrimeSpectrum Γ(X, c.U)).asIdeal :=
  SetLike.ext_iff.mp (c.isAffine.fromSpec_preimage_basicOpen a) y

/-- The point of a chart defined by `ψ` lies in the basic open of `a` iff `ψ a ≠ 0`. -/
theorem pt_mem_basicOpen_iff (c : Chart S₀ (Over.mk f)) {κ : Type u} [Field κ]
    [Algebra Γ(S, S₀) κ] (ψ : c.Ring →ₐ[Γ(S, S₀)] κ) (a : Γ(X, c.U))
    (z : Spec (CommRingCat.of κ)) :
    (c.pt hS₀ ψ).left z ∈ X.basicOpen a ↔ ψ a ≠ 0 := by
  rw [Chart.pt_left, Scheme.Hom.comp_apply]
  refine (fromSpec_mem_basicOpen_iff f c a _).trans ?_
  change ψ a ∉ (z : PrimeSpectrum κ).asIdeal ↔ _
  have := (z : PrimeSpectrum κ).isPrime
  rw [Ideal.eq_bot_of_prime (z : PrimeSpectrum κ).asIdeal, Ideal.mem_bot]

/-- **Counting through charts.** If the charts `c i` cover the preimage of `S₀` and every basic
open `D(a j)` of `c j` lies in the chart `c j₀`, then the `κ`-points of `X` over `S` number at
least the `κ`-points of `c j₀`, and at most these plus the `κ`-points of the loci `a j = 0`. -/
theorem natCard_bounds {ι : Type*} [Fintype ι] (c : ι → Chart S₀ (Over.mk f))
    (hcov : ∀ x : X, f x ∈ S₀ → ∃ i, x ∈ (c i).U) (j₀ : ι) (a : ∀ j, Γ(X, (c j).U))
    (ha : ∀ j, X.basicOpen (a j) ≤ (c j₀).U)
    [∀ j, Algebra.FiniteType Γ(S, S₀) (c j).Ring]
    (κ : Type u) [Field κ] [Finite κ] [Algebra Γ(S, S₀) κ] :
    Nat.card ((c j₀).Ring →ₐ[Γ(S, S₀)] κ) ≤ Nat.card (testObj hS₀ κ ⟶ Over.mk f) ∧
      Nat.card (testObj hS₀ κ ⟶ Over.mk f) ≤ Nat.card ((c j₀).Ring →ₐ[Γ(S, S₀)] κ) +
        ∑ j, Nat.card {ψ : (c j).Ring →ₐ[Γ(S, S₀)] κ // ψ (a j) = 0} := by
  have := fun j => finite_algHom_of_finiteType Γ(S, S₀) (c j).Ring κ
  let Φ : ((c j₀).Ring →ₐ[Γ(S, S₀)] κ) ⊕
      (Σ j, {ψ : (c j).Ring →ₐ[Γ(S, S₀)] κ // ψ (a j) = 0}) → (testObj hS₀ κ ⟶ Over.mk f) :=
    Sum.elim ((c j₀).pt hS₀) fun p => (c p.1).pt hS₀ p.2.1
  have hΦ : Function.Surjective Φ := by
    intro x
    let z : Spec (CommRingCat.of κ) := IsLocalRing.closedPoint κ
    have hrange : ∀ i, x.left z ∈ (c i).U → Set.range x.left ⊆ (c i).U := by
      rintro i hi _ ⟨w, rfl⟩
      rwa [Subsingleton.elim (α := PrimeSpectrum κ) w z]
    have hw : x.left ≫ f = testMap hS₀ κ := Over.w x
    have hS : f (x.left z) ∈ S₀ := by
      rw [← Scheme.Hom.comp_apply, hw, testMap, Scheme.Hom.comp_apply]
      exact hS₀.range_fromSpec.subset ⟨_, rfl⟩
    obtain ⟨i, hi⟩ := hcov _ hS
    by_cases h₀ : x.left z ∈ (c j₀).U
    · obtain ⟨ψ, rfl⟩ := (c j₀).exists_pt hS₀ x (hrange j₀ h₀)
      exact ⟨Sum.inl ψ, rfl⟩
    · obtain ⟨ψ, rfl⟩ := (c i).exists_pt hS₀ x (hrange i hi)
      refine ⟨Sum.inr ⟨i, ψ, ?_⟩, rfl⟩
      by_contra hψ
      exact h₀ (ha i ((pt_mem_basicOpen_iff f hS₀ (c i) ψ (a i) z).mpr hψ))
  have : Finite (testObj hS₀ κ ⟶ Over.mk f) := Finite.of_surjective Φ hΦ
  refine ⟨Nat.card_le_card_of_injective _ ((c j₀).pt_injective hS₀), ?_⟩
  refine (Nat.card_le_card_of_surjective Φ hΦ).trans ?_
  rw [Nat.card_sum, Nat.card_sigma]

/-- A point of a chart lies over the point of `S₀` given by the prime below it. -/
theorem chart_apply (c : Chart S₀ (Over.mk f)) (y : Spec (CommRingCat.of c.Ring)) :
    f (c.fromSpec y) = hS₀.fromSpec (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(S, S₀) c.Ring)) y) := by
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
  exact congrArg (fun g : Spec (CommRingCat.of c.Ring) ⟶ S => g y) (c.fromSpec_hom hS₀)

/-- A point of a chart over the point of `S₀` given by `𝔭` comes from a prime over `𝔭`. -/
theorem chart_comap_eq (c : Chart S₀ (Over.mk f)) (y : Spec (CommRingCat.of c.Ring))
    (𝔭 : PrimeSpectrum Γ(S, S₀)) (h : f (c.fromSpec y) = hS₀.fromSpec 𝔭) :
    (y : PrimeSpectrum c.Ring).asIdeal.comap (algebraMap Γ(S, S₀) c.Ring) = 𝔭.asIdeal := by
  rw [chart_apply f hS₀] at h
  have h' := hS₀.fromSpec.isOpenEmbedding.injective h
  rw [Spec.map_apply] at h'
  exact congrArg PrimeSpectrum.asIdeal h'

end Counting

section PrimeCase

variable {X S : Scheme.{u}} (f : X ⟶ S) {S₀ : S.Opens} (hS₀ : IsAffineOpen S₀)

include hS₀ in
/-- **Basic opens inside one chart.** Let `x₀` be a point of the chart `c₀` over the point `𝔭`
of `S₀`. For any chart `c` there is `a` with `D(a) ⊆ c₀` and `r ∉ 𝔭` such that, for every field
`K` over `Γ(S₀) ⧸ 𝔭` in which `r` does not vanish, either `K ⊗ Γ(c)` vanishes or `1 ⊗ a` is not
nilpotent in it. -/
theorem exists_basicOpen_le_forall [GeometricallyIrreducible f] [IsNoetherianRing Γ(S, S₀)]
    (c c₀ : Chart S₀ (Over.mk f)) [Algebra.FiniteType Γ(S, S₀) c.Ring]
    (𝔭 : Ideal Γ(S, S₀)) [𝔭.IsPrime] (x₀ : X) (hx₀ : x₀ ∈ c₀.U)
    (hfx₀ : f x₀ = hS₀.fromSpec ⟨𝔭, ‹_›⟩) :
    ∃ a : c.Ring, X.basicOpen (a : Γ(X, c.U)) ≤ c₀.U ∧ ∃ r : Γ(S, S₀), r ∉ 𝔭 ∧
      ∀ (K : Type u) [Field K] [Algebra Γ(S, S₀) K], 𝔭 ≤ RingHom.ker (algebraMap Γ(S, S₀) K) →
        algebraMap Γ(S, S₀) K r ≠ 0 →
          Subsingleton (K ⊗[Γ(S, S₀)] c.Ring) ∨ ¬IsNilpotent ((1 : K) ⊗ₜ[Γ(S, S₀)] a) := by
  by_cases hP : ∃ P : Ideal c.Ring, P.IsPrime ∧ P.comap (algebraMap Γ(S, S₀) c.Ring) = 𝔭
  · obtain ⟨P, hPp, hP⟩ := hP
    let s : S := hS₀.fromSpec ⟨𝔭, ‹_›⟩
    let y : Spec (CommRingCat.of c.Ring) := ⟨P, hPp⟩
    have hy : f (c.fromSpec y) = s := by
      rw [chart_apply f hS₀]
      exact congrArg hS₀.fromSpec (PrimeSpectrum.ext hP)
    have hrange : ∀ x : X, f x = s → ∃ w : f.fiber s, f.fiberι s w = x := fun x hx => by
      have : x ∈ Set.range (f.fiberι s) := by
        rw [Scheme.Hom.range_fiberι]
        exact hx
      exact this
    obtain ⟨w₁, hw₁⟩ := hrange _ hy
    obtain ⟨w₀, hw₀⟩ := hrange x₀ hfx₀
    have hc : c.fromSpec y ∈ c.U := c.range_fromSpec.subset ⟨y, rfl⟩
    obtain ⟨w, hwc, hwc₀⟩ := nonempty_preirreducible_inter (f.fiberι s ⁻¹ᵁ c.U).isOpen
      (f.fiberι s ⁻¹ᵁ c₀.U).isOpen ⟨w₁, show f.fiberι s w₁ ∈ c.U from hw₁ ▸ hc⟩
      ⟨w₀, show f.fiberι s w₀ ∈ c₀.U from hw₀ ▸ hx₀⟩
    have hws : f (f.fiberι s w) = s := by
      have : f.fiberι s w ∈ Set.range (f.fiberι s) := ⟨w, rfl⟩
      rw [Scheme.Hom.range_fiberι] at this
      exact this
    obtain ⟨a, ha, hza⟩ := c.isAffine.exists_basicOpen_le (V := c.U ⊓ c₀.U)
      ⟨f.fiberι s w, hwc, hwc₀⟩ hwc
    have hz : f.fiberι s w ∈ Set.range c.fromSpec := by
      rw [c.range_fromSpec]
      exact hwc
    obtain ⟨y', hy'⟩ := hz
    have : (y' : PrimeSpectrum c.Ring).asIdeal.IsPrime := (y' : PrimeSpectrum c.Ring).isPrime
    have haQ : (a : c.Ring) ∉ (y' : PrimeSpectrum c.Ring).asIdeal :=
      (fromSpec_mem_basicOpen_iff f c a y').mp (by
        change c.fromSpec y' ∈ X.basicOpen a
        rw [hy']
        exact hza)
    have hQ := chart_comap_eq f hS₀ c y' ⟨𝔭, ‹_›⟩ (by rw [hy']; exact hws)
    obtain ⟨r, hr, hK⟩ := exists_not_mem_forall_not_isNilpotent 𝔭 c.Ring (a : c.Ring) _ haQ hQ
    exact ⟨a, ha.trans inf_le_right, r, hr, fun K _ _ h𝔭 hrK => Or.inr (hK K h𝔭 hrK)⟩
  · obtain ⟨r, hr, hK⟩ := exists_not_mem_forall_subsingleton 𝔭 c.Ring
      fun P hPp hPc => hP ⟨P, hPp, hPc⟩
    refine ⟨0, ?_, r, hr, fun K _ _ h𝔭 hrK => Or.inl (hK K h𝔭 hrK)⟩
    exact (X.basicOpen_zero c.U).trans_le bot_le

/-- **The estimate near a prime of the base.** For a family as in the Lang–Weil estimate in
fibre dimension `e + 1` over an affine open `S₀` of finite type over `ℤ`, covered by finitely
many charts of finite type, every prime `𝔭` of `Γ(S₀)` admits `r ∉ 𝔭` and a constant `C` such
that the estimate holds with `C` for all finite fields `κ` in which `𝔭` vanishes and `r` does
not. -/
theorem prime_case (hUB : FamilyPointUpperBoundStatement.{u}) {e : ℕ}
    (hA : AffineFamilyLangWeil.{u} (e + 1)) [GeometricallyIrreducible f] [LocallyOfFiniteType f]
    (hdim : ∀ s : S, HasPureDimension (f.fiber s) (e + 1))
    [Algebra.FiniteType ℤ Γ(S, S₀)] [IsNoetherianRing Γ(S, S₀)]
    {ι : Type*} [Fintype ι] (c : ι → Chart S₀ (Over.mk f))
    (hcov : ∀ x : X, f x ∈ S₀ → ∃ i, x ∈ (c i).U)
    [∀ j, Algebra.FiniteType Γ(S, S₀) (c j).Ring] (𝔭 : Ideal Γ(S, S₀)) [𝔭.IsPrime] :
    ∃ r : Γ(S, S₀), r ∉ 𝔭 ∧ ∃ C : ℝ, ∀ (κ : Type u) [Field κ] [Finite κ]
      [Algebra Γ(S, S₀) κ], 𝔭 ≤ RingHom.ker (algebraMap Γ(S, S₀) κ) →
        algebraMap Γ(S, S₀) κ r ≠ 0 →
          |(Nat.card (testObj hS₀ κ ⟶ Over.mk f) : ℝ) - (Nat.card κ : ℝ) ^ (e + 1)| ≤
            C * (Nat.card κ : ℝ) ^ (((e + 1 : ℕ) : ℝ) - 1 / 2) := by
  -- a point `x₀` of `X` over the point `𝔭` of `S₀`, in the chart `c j₀`
  let s : S := hS₀.fromSpec ⟨𝔭, ‹_›⟩
  obtain ⟨x₀, hx₀⟩ := f.surjective s
  have hs : f x₀ ∈ S₀ := by
    rw [hx₀]
    exact hS₀.range_fromSpec.subset ⟨_, rfl⟩
  obtain ⟨j₀, hj₀⟩ := hcov x₀ hs
  have hj₀' : x₀ ∈ Set.range (c j₀).fromSpec := by
    rw [(c j₀).range_fromSpec]
    exact hj₀
  obtain ⟨y₀, hy₀⟩ := hj₀'
  have : (y₀ : PrimeSpectrum (c j₀).Ring).asIdeal.IsPrime :=
    (y₀ : PrimeSpectrum (c j₀).Ring).isPrime
  have hP₀ := chart_comap_eq f hS₀ (c j₀) y₀ ⟨𝔭, ‹_›⟩ (by rw [hy₀]; exact hx₀)
  -- the basic opens `D(a j)` of the charts `c j` inside `c j₀`
  choose a ha r hr hK using fun j => exists_basicOpen_le_forall f hS₀ (c j) (c j₀) 𝔭 x₀ hj₀ hx₀
  -- the affine estimate for `c j₀` over `Γ(S₀) ⧸ 𝔭`
  obtain ⟨r₁, hr₁, hK₁⟩ := exists_not_mem_forall_nontrivial 𝔭 (c j₀).Ring _ hP₀
  have := finiteType_int_of_surjective (Ideal.Quotient.mk 𝔭) Ideal.Quotient.mk_surjective
  have hfib : ∀ (K : Type u) [Field K] [Algebra (Γ(S, S₀) ⧸ 𝔭) K],
      algebraMap (Γ(S, S₀) ⧸ 𝔭) K (Ideal.Quotient.mk 𝔭 r₁) ≠ 0 →
        (nilradical (K ⊗[Γ(S, S₀) ⧸ 𝔭] ((Γ(S, S₀) ⧸ 𝔭) ⊗[Γ(S, S₀)] (c j₀).Ring))).IsPrime ∧
          ringKrullDim (K ⊗[Γ(S, S₀) ⧸ 𝔭] ((Γ(S, S₀) ⧸ 𝔭) ⊗[Γ(S, S₀)] (c j₀).Ring)) =
            ((e + 1 : ℕ) : WithBot ℕ∞) := by
    intro K _ _ hrK
    let : Algebra Γ(S, S₀) K :=
      ((algebraMap (Γ(S, S₀) ⧸ 𝔭) K).comp (algebraMap Γ(S, S₀) (Γ(S, S₀) ⧸ 𝔭))).toAlgebra
    have : IsScalarTower Γ(S, S₀) (Γ(S, S₀) ⧸ 𝔭) K := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have h𝔭 : 𝔭 ≤ RingHom.ker (algebraMap Γ(S, S₀) K) := fun x hx => by
      rw [RingHom.mem_ker, IsScalarTower.algebraMap_apply Γ(S, S₀) (Γ(S, S₀) ⧸ 𝔭) K,
        Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]
    have := hK₁ K h𝔭 hrK
    obtain ⟨h1, h2⟩ := chart_isPrime_and_dim f hS₀ (c j₀) K hdim
    let ε := (Algebra.TensorProduct.cancelBaseChange Γ(S, S₀) (Γ(S, S₀) ⧸ 𝔭) K K
      (c j₀).Ring).toRingEquiv
    exact ⟨(Langlands.Algebra.GenericIrreducibilityReduction.nilradical_isPrime_iff_of_ringEquiv
      ε).mpr h1,
      (ringKrullDim_eq_of_ringEquiv ε).trans h2⟩
  obtain ⟨r₂, hr₂, C₀, -, hest⟩ := hA (Γ(S, S₀) ⧸ 𝔭)
    ((Γ(S, S₀) ⧸ 𝔭) ⊗[Γ(S, S₀)] (c j₀).Ring) (Ideal.Quotient.mk 𝔭 r₁)
    (fun h => hr₁ (Ideal.Quotient.eq_zero_iff_mem.mp h)) hfib
  obtain ⟨r₂, rfl⟩ := Ideal.Quotient.mk_surjective r₂
  -- the upper bound for the loci `a j = 0`
  have : ∀ j, Algebra.FiniteType Γ(S, S₀) ((c j).Ring ⧸ Ideal.span {(a j : (c j).Ring)}) :=
    fun j => Algebra.FiniteType.of_surjective _ (Ideal.Quotient.mkₐ_surjective _ _)
  choose C' hC' hUB' using fun j =>
    upperBound_ring hUB Γ(S, S₀) ((c j).Ring ⧸ Ideal.span {(a j : (c j).Ring)})
  refine ⟨r₂ * ∏ j, r j, fun hmem => ?_, C₀ + ∑ j, C' j, fun κ _ _ _ h𝔭 hrκ => ?_⟩
  · rcases Ideal.IsPrime.mem_or_mem ‹_› hmem with h | h
    · exact hr₂ (Ideal.Quotient.eq_zero_iff_mem.mpr h)
    · obtain ⟨j, -, hj⟩ := Ideal.IsPrime.prod_mem_iff.mp h
      exact hr j hj
  rw [map_mul, map_prod] at hrκ
  have hr₂κ : algebraMap Γ(S, S₀) κ r₂ ≠ 0 := left_ne_zero_of_mul hrκ
  have hrjκ : ∀ j, algebraMap Γ(S, S₀) κ (r j) ≠ 0 := fun j =>
    Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul hrκ) j (Finset.mem_univ j)
  let := quotientAlgebra 𝔭 κ h𝔭
  have := quotientAlgebra_isScalarTower 𝔭 κ h𝔭
  have hM := hest κ hr₂κ
  rw [← Nat.card_congr (Algebra.TensorProduct.liftEquivRight Γ(S, S₀) (Γ(S, S₀) ⧸ 𝔭)
    (c j₀).Ring κ)] at hM
  have hUBj : ∀ j, (Nat.card {ψ : (c j).Ring →ₐ[Γ(S, S₀)] κ // ψ (a j) = 0} : ℝ) ≤
      C' j * (Nat.card κ : ℝ) ^ e := by
    intro j
    refine le_trans (Nat.cast_le.mpr (natCard_algHom_eq_zero_le (c j).Ring κ (a j)))
      (hUB' j κ e fun p hp => ?_)
    have h𝔭K : 𝔭 ≤ RingHom.ker (algebraMap Γ(S, S₀) p.asIdeal.ResidueField) := by
      rw [Ideal.ker_algebraMap_residueField, hp]
      exact h𝔭
    have hrK : algebraMap Γ(S, S₀) p.asIdeal.ResidueField (r j) ≠ 0 := fun h => by
      have h' : r j ∈ RingHom.ker (algebraMap Γ(S, S₀) p.asIdeal.ResidueField) := h
      rw [Ideal.ker_algebraMap_residueField, hp] at h'
      exact hrjκ j h'
    rcases hK j p.asIdeal.ResidueField h𝔭K hrK with hsub | hnil
    · have := subsingleton_tensor_quotient (R₀ := Γ(S, S₀)) (c j).Ring p.asIdeal.ResidueField
        (Ideal.span {(a j : (c j).Ring)})
      rw [ringKrullDim_eq_bot_of_subsingleton]
      exact bot_le
    · have : Nontrivial (p.asIdeal.ResidueField ⊗[Γ(S, S₀)] (c j).Ring) := by
        by_contra hnt
        rw [not_nontrivial_iff_subsingleton] at hnt
        exact hnil ⟨1, Subsingleton.elim _ _⟩
      obtain ⟨h1, h2⟩ := chart_isPrime_and_dim f hS₀ (c j) p.asIdeal.ResidueField hdim
      exact ringKrullDim_tensor_quotient_le (c j).Ring p.asIdeal.ResidueField (a j) h1 h2 hnil
  obtain ⟨hlo, hhi⟩ := natCard_bounds f hS₀ c hcov j₀ a ha κ
  have hq : (1 : ℝ) ≤ Nat.card κ := Nat.one_le_cast.mpr Nat.card_pos
  have hpow : (Nat.card κ : ℝ) ^ e ≤ (Nat.card κ : ℝ) ^ (((e + 1 : ℕ) : ℝ) - 1 / 2) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hq (by push_cast; linarith)
  have hsum : (∑ j, (Nat.card {ψ : (c j).Ring →ₐ[Γ(S, S₀)] κ // ψ (a j) = 0} : ℝ)) ≤
      (∑ j, C' j) * (Nat.card κ : ℝ) ^ (((e + 1 : ℕ) : ℝ) - 1 / 2) := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun j _ =>
      (hUBj j).trans (mul_le_mul_of_nonneg_left hpow (hC' j).le)
  have hC'0 : 0 ≤ ∑ j, C' j := Finset.sum_nonneg fun j _ => (hC' j).le
  have hT : 0 ≤ (Nat.card κ : ℝ) ^ (((e + 1 : ℕ) : ℝ) - 1 / 2) :=
    Real.rpow_nonneg (by linarith) _
  have hlo' : (Nat.card ((c j₀).Ring →ₐ[Γ(S, S₀)] κ) : ℝ) ≤
      Nat.card (testObj hS₀ κ ⟶ Over.mk f) := by exact_mod_cast hlo
  have hhi' : (Nat.card (testObj hS₀ κ ⟶ Over.mk f) : ℝ) ≤
      Nat.card ((c j₀).Ring →ₐ[Γ(S, S₀)] κ) +
        ∑ j, (Nat.card {ψ : (c j).Ring →ₐ[Γ(S, S₀)] κ // ψ (a j) = 0} : ℝ) := by
    exact_mod_cast hhi
  rw [abs_le] at hM ⊢
  rw [add_mul]
  constructor <;> linarith [mul_nonneg hC'0 hT, hM.1, hM.2]

end PrimeCase

section Global

/-- The sections of a scheme of finite type over `ℤ` on an affine open form a ring of finite
type over `ℤ`. -/
theorem finiteType_int_of_isAffineOpen {S : Scheme.{u}}
    (hS : LocallyOfFiniteType (specULiftZIsTerminal.{u}.from S)) {S₀ : S.Opens}
    (hS₀ : IsAffineOpen S₀) : Algebra.FiniteType ℤ Γ(S, S₀) := by
  have h : hS₀.fromSpec ≫ specULiftZIsTerminal.from S =
      Spec.map (CommRingCat.ofHom ((algebraMap ℤ Γ(S, S₀)).comp
        (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).toRingHom)) :=
    specULiftZIsTerminal.hom_ext _ _
  have hL : LocallyOfFiniteType (hS₀.fromSpec ≫ specULiftZIsTerminal.from S) := inferInstance
  rw [h, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at hL
  exact RingHom.finiteType_algebraMap.mp (RingHom.FiniteType.of_comp_finiteType hL)

/-- **The estimate over an affine open of the base.** Under the hypotheses of the Lang–Weil
estimate in fibre dimension `e + 1`, the affine estimate `AffineFamilyLangWeil (e + 1)` yields
one constant for all `κ`-points of `S` factoring through a fixed affine open `S₀`. -/
theorem affine_open_case (hUB : FamilyPointUpperBoundStatement.{u}) {e : ℕ}
    (hA : AffineFamilyLangWeil.{u} (e + 1)) {X S : Scheme.{u}} (f : X ⟶ S)
    (hS : LocallyOfFiniteType (specULiftZIsTerminal.{u}.from S))
    [LocallyOfFiniteType f] [QuasiCompact f] [GeometricallyIrreducible f]
    (hdim : ∀ s : S, HasPureDimension (f.fiber s) (e + 1)) {S₀ : S.Opens}
    (hS₀ : IsAffineOpen S₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ (κ : Type u) [Field κ] [Finite κ] [Algebra Γ(S, S₀) κ],
      |(Nat.card {x : Spec (CommRingCat.of κ) ⟶ X // x ≫ f = testMap hS₀ κ} : ℝ) -
          (Nat.card κ : ℝ) ^ (e + 1)| ≤
        C * (Nat.card κ : ℝ) ^ (((e + 1 : ℕ) : ℝ) - 1 / 2) := by
  have := finiteType_int_of_isAffineOpen hS hS₀
  have : IsNoetherianRing Γ(S, S₀) := Algebra.FiniteType.isNoetherianRing ℤ _
  -- finitely many affine charts cover the preimage of `S₀`
  obtain ⟨s, hs, hcov⟩ :=
    isCompact_iff_finite_and_eq_biUnion_affineOpens.mp (f.isCompact_preimage hS₀.isCompact)
  have : Fintype s := hs.fintype
  have hle : ∀ i ∈ s, (i : X.Opens) ≤ f ⁻¹ᵁ S₀ := fun i hi => by
    rw [hcov]
    exact le_iSup₂ (f := fun (i : X.affineOpens) (_ : i ∈ s) => (i : X.Opens)) i hi
  let c : s → Chart S₀ (Over.mk f) := fun i => ⟨i.1.1, i.1.2, hle i.1 i.2⟩
  have hcov' : ∀ x : X, f x ∈ S₀ → ∃ i, x ∈ (c i).U := fun x hx => by
    have hx' : x ∈ f ⁻¹ᵁ S₀ := hx
    rw [hcov] at hx'
    simp only [TopologicalSpace.Opens.mem_iSup] at hx'
    obtain ⟨i, hi, hxi⟩ := hx'
    exact ⟨⟨i, hi⟩, hxi⟩
  have : ∀ i, Algebra.FiniteType Γ(S, S₀) (c i).Ring := fun i =>
    HasRingHomProperty.appLE @LocallyOfFiniteType f ‹_› ⟨S₀, hS₀⟩ ⟨_, (c i).isAffine⟩ (c i).le
  -- Noetherian induction on the base
  obtain ⟨C, hC⟩ := exists_forall_of_forall_isPrime (R₀ := Γ(S, S₀))
    (fun κ _ _ _ C => |(Nat.card (testObj hS₀ κ ⟶ Over.mk f) : ℝ) - (Nat.card κ : ℝ) ^ (e + 1)| ≤
      C * (Nat.card κ : ℝ) ^ (((e + 1 : ℕ) : ℝ) - 1 / 2))
    (fun κ _ _ _ C C' hCC' h => h.trans (mul_le_mul_of_nonneg_right hCC'
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)))
    (fun 𝔭 h𝔭 => prime_case f hS₀ hUB hA hdim c hcov' 𝔭)
  refine ⟨max C 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun κ _ _ _ => ?_⟩
  rw [Nat.card_congr (pointsEquiv f hS₀ κ)]
  exact (hC κ).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _))

/-- **Reduction to affine families.** Given the uniform upper bound for point counts, the affine
estimate `AffineFamilyLangWeil (e + 1)` implies the uniform Lang–Weil estimate in fibre
dimension `e + 1`. -/
theorem familyLangWeil_of_affine (hUB : FamilyPointUpperBoundStatement.{u}) (e : ℕ)
    (hA : AffineFamilyLangWeil.{u} (e + 1)) : FamilyLangWeilInDimension.{u} (e + 1) := by
  intro S X f hS hSc hf hqc hgi hdim
  -- a finite affine open cover of `S`
  obtain ⟨s, hs, hcov⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp
    (show IsCompact ((⊤ : S.Opens) : Set S) from isCompact_univ)
  have : Fintype s := hs.fintype
  choose C hC hest using fun i : s => affine_open_case hUB hA f hS hdim i.1.2
  refine ⟨∑ i, C i + 1, add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun i _ => (hC i).le)
    one_pos, fun κ _ _ t => ?_⟩
  -- the point `t` factors through some affine open of the cover
  let z : Spec (CommRingCat.of κ) := IsLocalRing.closedPoint κ
  have hz : t z ∈ (⊤ : S.Opens) := trivial
  rw [hcov] at hz
  simp only [TopologicalSpace.Opens.mem_iSup] at hz
  obtain ⟨i, hi, hzi⟩ := hz
  let j : s := ⟨i, hi⟩
  have hj : IsAffineOpen (j.1 : S.Opens) := j.1.2
  have hrange : Set.range t ⊆ Set.range hj.fromSpec := by
    rintro _ ⟨w, rfl⟩
    rw [Subsingleton.elim (α := PrimeSpectrum κ) w z, IsAffineOpen.range_fromSpec]
    exact hzi
  let g := IsOpenImmersion.lift hj.fromSpec t hrange
  obtain ⟨φ, hφ⟩ := Spec.map_surjective g
  let : Algebra Γ(S, (j.1 : S.Opens)) κ := φ.hom.toAlgebra
  have ht : testMap hj κ = t := by
    change Spec.map (CommRingCat.ofHom φ.hom) ≫ _ = t
    rw [CommRingCat.ofHom_hom, hφ, IsOpenImmersion.lift_fac]
  rw [← ht]
  exact (hest j κ).trans (mul_le_mul_of_nonneg_right
    ((Finset.single_le_sum (fun i _ => (hC i).le) (Finset.mem_univ j)).trans
      (le_add_of_nonneg_right zero_le_one))
    (Real.rpow_nonneg (Nat.cast_nonneg _) _))

end Global

end Langlands.AlgebraicGeometry.LangWeil.Slicing
