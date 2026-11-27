import Langlands.Global.Factors.CuspidalPairEisensteinUnfoldingLevi

/-! # The Levi integral is the Levi Whittaker coefficient

Let `f` be continuous and left invariant under `P(F)`, let `ψ` be a standard additive character
of `𝔸`, and let `g ∈ GL_N(𝔸)`. If `f(diag(B, A) g) conj(ψ_(t+1)(A)) conj(ψ_(r+1)(B))` is
integrable on a fundamental domain of `N_(t+1)(F) × N_(r+1)(F)` for its normalized Haar measure,
then its integral there is the iterated generic Whittaker coefficient `leviWhittaker f g`. The
triviality of `ψ` on `F` makes the integrand invariant under the lattice. See the paired
Markdown. -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open NumberField MeasureTheory Matrix Set

namespace Langlands.Global.CuspidalPairEisenstein.Unfolding

open RankinSelbergGlobal RowEchelon PrimitiveAdelicHeight LeftCosetSpace

section Normalization

variable {X : Type u} [Group X] [TopologicalSpace X] [IsTopologicalGroup X]
  [SecondCountableTopology X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The lattice-normalized Haar measure is `(μ S)⁻¹ • μ` for every Haar measure `μ` and every
measurable strict fundamental domain `S` of finite positive measure. -/
theorem latticeNormalizedHaar_eq (Γ : Subgroup X) (hΓ : IsDiscrete (Γ : Set X))
    (μ : Measure X) [μ.IsHaarMeasure] {S : Set X} (hSm : MeasurableSet S)
    (hS : ∀ x, ∃! c : Γ, (c : X) * x ∈ S) :
    Semidirect.latticeNormalizedHaar Γ hΓ = (μ S)⁻¹ • μ := by
  have : Countable Γ := countable_of_isDiscrete Γ hΓ
  have hk := Measure.isMulLeftInvariant_eq_smul (Measure.haar : Measure X) μ
  have hfd := isFundamentalDomain Γ hΓ (Measure.haar : Measure X)
  have hfdS : IsFundamentalDomain Γ S (Measure.haar : Measure X) :=
    IsFundamentalDomain.mk' hSm.nullMeasurableSet hS
  rw [Semidirect.latticeNormalizedHaar, hfd.measure_eq hfdS, hk]
  have hpos := Measure.haarScalarFactor_pos_of_isHaarMeasure (Measure.haar : Measure X) μ
  exact normalizedAmbientMeasure_smul μ S _ (by exact_mod_cast hpos.ne') ENNReal.coe_ne_top

end Normalization

section LeviIntegral

variable (F : Type u) [Field F] [NumberField F] (r t : ℕ)

set_option synthInstance.maxHeartbeats 400000 in
instance leviLatticeMulAction : MulAction (leviLattice F r t) (LeviPart F r t) :=
  inferInstance

instance leviLatticeSMul : SMul (leviLattice F r t) (LeviPart F r t) :=
  (leviLatticeMulAction F r t).toSMul

/-- The product fundamental domain of `N_(t+1)(F) × N_(r+1)(F)`. -/
abbrev fdProd : Set (LeviPart F r t) := fd₀ F (t + 1) ×ˢ fd₀ F (r + 1)

theorem measurableSet_fdProd : MeasurableSet (fdProd F r t) :=
  (measurableSet_fundamentalDomain _ _).prod (measurableSet_fundamentalDomain _ _)

theorem existsUnique_mem_fdProd (m : LeviPart F r t) :
    ∃! c : leviLattice F r t, (c : LeviPart F r t) * m ∈ fdProd F r t := by
  obtain ⟨c₁, hc₁, hu₁⟩ := fundamentalDomain_unique (Γ₀ F (t + 1)) (isDiscrete_Γ₀ F _) m.1
  obtain ⟨c₂, hc₂, hu₂⟩ := fundamentalDomain_unique (Γ₀ F (r + 1)) (isDiscrete_Γ₀ F _) m.2
  refine ⟨⟨((c₁ : unipotentAdelic F (t + 1)), (c₂ : unipotentAdelic F (r + 1))), c₁.2, c₂.2⟩,
    ⟨hc₁, hc₂⟩, fun c hc => ?_⟩
  have e₁ := hu₁ ⟨(c : LeviPart F r t).1, c.2.1⟩ hc.1
  have e₂ := hu₂ ⟨(c : LeviPart F r t).2, c.2.2⟩ hc.2
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg Subtype.val e₁
  · exact congrArg Subtype.val e₂

/-- The normalized Haar measure of the block diagonal group is the product of Haar measures
divided by the mass of the product fundamental domain. -/
theorem haarM_eq_prod :
    haarM F r t = (((Measure.haar : Measure (unipotentAdelic F (t + 1))).prod
      (Measure.haar : Measure (unipotentAdelic F (r + 1)))) (fdProd F r t))⁻¹ •
      ((Measure.haar : Measure (unipotentAdelic F (t + 1))).prod
        (Measure.haar : Measure (unipotentAdelic F (r + 1)))) :=
  latticeNormalizedHaar_eq _ _ _ (measurableSet_fdProd F r t) (existsUnique_mem_fdProd F r t)

theorem continuous_leviPair :
    Continuous fun p : AdelicGL F (r + 1) × AdelicGL F (t + 1) => leviPair F r t p.1 p.2 :=
  ((blockShape r t).leviEmbeddingContinuous (Adeles F)).continuous.comp
    (Shahidi.twoBlockLeviContinuousEquiv (Nat.succ_pos r) (Nat.succ_pos t) (Adeles F)).symm.continuous

variable {F r t}

/-- Left translation of the first block by a rational upper unitriangular matrix. -/
theorem twisted_leviPair_rational_left {f : AdelicGL F (r + t + 2) → ℂ}
    (hfP : ∀ c0 ∈ (blockShape r t).parabolic F, ∀ x, f (AdelicGL.rational F _ c0 * x) = f x)
    (a : RationalGL F (r + 1)) (b : RationalGL F (t + 1)) (x : AdelicGL F (r + 1))
    (y : AdelicGL F (t + 1)) (g : AdelicGL F (r + t + 2)) :
    f (leviPair F r t (AdelicGL.rational F _ a * x) (AdelicGL.rational F _ b * y) * g) =
      f (leviPair F r t x y * g) := by
  obtain ⟨c0, hc0, hc⟩ := leviPair_rational F r t a b
  rw [leviPair_mul, hc, mul_assoc, hfP c0 hc0]

theorem toMat_mem_rational_of_mem_Γ₀ {n : ℕ} {x : unipotentAdelic F n} (hx : x ∈ Γ₀ F n) :
    ∃ a : RationalGL F n, toMat F n x = AdelicGL.rational F n a := by
  obtain ⟨δ, rfl⟩ := (mem_Γ₀_iff F n x).mp hx
  exact ⟨δ, toMat_ratHom F n δ⟩

/-- The integrand of the Levi integral. -/
def leviIntegrand (f : AdelicGL F (r + t + 2) → ℂ) (ψ : AddChar (Adeles F) ℂ)
    (g : AdelicGL F (r + t + 2)) (m : LeviPart F r t) : ℂ :=
  f (leviPair F r t (toMat F _ m.2) (toMat F _ m.1) * g) *
    starRingEnd ℂ (genericCharacter F t ψ (fun _ => 1) m.1) *
    starRingEnd ℂ (genericCharacter F r ψ (fun _ => 1) m.2)

theorem leviIntegrand_mul {f : AdelicGL F (r + t + 2) → ℂ}
    (hfP : ∀ c0 ∈ (blockShape r t).parabolic F, ∀ x, f (AdelicGL.rational F _ c0 * x) = f x)
    (ψ : AddChar (Adeles F) ℂ) (hψ : ∀ a : F, ψ (algebraMap F (Adeles F) a) = 1)
    (g : AdelicGL F (r + t + 2)) {c : LeviPart F r t} (hc : c ∈ leviLattice F r t)
    (m : LeviPart F r t) : leviIntegrand f ψ g (c * m) = leviIntegrand f ψ g m := by
  obtain ⟨a₁, ha₁⟩ := toMat_mem_rational_of_mem_Γ₀ hc.1
  obtain ⟨a₂, ha₂⟩ := toMat_mem_rational_of_mem_Γ₀ hc.2
  rw [leviIntegrand, leviIntegrand, Prod.fst_mul, Prod.snd_mul, map_mul, map_mul, ha₁, ha₂,
    twisted_leviPair_rational_left hfP,
    RankinSelbergGlobal.Unfolding.genericCharacter_mul F t ψ _ c.1 m.1,
    RankinSelbergGlobal.Unfolding.genericCharacter_mul F r ψ _ c.2 m.2,
    RankinSelbergGlobal.Unfolding.genericCharacter_rational F t ψ hψ _ ⟨c.1, hc.1⟩,
    RankinSelbergGlobal.Unfolding.genericCharacter_rational F r ψ hψ _ ⟨c.2, hc.2⟩, one_mul,
    one_mul]

end LeviIntegral

section Whittaker

open scoped CategoryTheory.MonObj

variable {F : Type u} [Field F] [NumberField F] {r t : ℕ}

local instance leviIntegralSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _

local instance leviIntegralSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

/-- The mass normalizer of `N_n(F) \ N_n(𝔸)` as a real number. -/
abbrev unipotentNormalizer (F : Type u) [Field F] [NumberField F] (n : ℕ) : ℝ :=
  (AdelicSubgroupPoints.quotientMassNormalizer F (Scheme F n) (upperUnipotent F n)).toReal

theorem genericCharacter_mul_rational (ψ : AddChar (Adeles F) ℂ)
    (hψ : ∀ a : F, ψ (algebraMap F (Adeles F) a) = 1) (n : ℕ)
    (k : AdelicSubgroupPoints.rationalSubgroup F (Scheme F (n + 1)) (upperUnipotent F (n + 1)))
    (x : unipotentAdelic F (n + 1)) :
    genericCharacter F n ψ (fun _ => 1) (k * x) = genericCharacter F n ψ (fun _ => 1) x := by
  rw [RankinSelbergGlobal.Unfolding.genericCharacter_mul,
    RankinSelbergGlobal.Unfolding.genericCharacter_rational F n ψ hψ, one_mul]

/-- The inner Whittaker coefficient over the second block as a set integral. -/
theorem innerWhittaker_eq {f : AdelicGL F (r + t + 2) → ℂ} (hfc : Continuous f)
    (hfP : ∀ c0 ∈ (blockShape r t).parabolic F, ∀ x, f (AdelicGL.rational F _ c0 * x) = f x)
    (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ)
    (g : AdelicGL F (r + t + 2)) (X : AdelicGL F (r + 1)) :
    generalLinearWhittakerFunction F t ψ (fun _ => 1)
        (fun y => f (leviPair F r t X (GeneralLinearGroupPoints.adelicEquiv F (t + 1) y) * g)) 1 =
      unipotentNormalizer F (t + 1) • ∫ y in fd₀ F (t + 1),
        f (leviPair F r t X (toMat F _ y) * g) *
          starRingEnd ℂ (genericCharacter F t ψ (fun _ => 1) y) ∂Measure.haar := by
  have hcont : Continuous fun y : Points F (t + 1) =>
      f (leviPair F r t X (GeneralLinearGroupPoints.adelicEquiv F (t + 1) y) * g) :=
    hfc.comp (((continuous_leviPair F r t).comp (continuous_const.prodMk
      (GeneralLinearGroupPoints.adelicHomeomorph F (t + 1)).continuous)).mul continuous_const)
  rw [generalLinearWhittakerFunction, RankinSelbergGlobal.Unfolding.subgroupCharacterCoefficient_eq_setIntegral
    F _ _ _ (RankinSelbergGlobal.Unfolding.continuous_genericCharacter F t ψ hψ.1 _).measurable
    (genericCharacter_mul_rational ψ hψ.2.2.1 t) _ hcont.measurable ?_ 1]
  · simp only [mul_one]
    rfl
  · intro k y
    obtain ⟨a, ha⟩ := toMat_mem_rational_of_mem_Γ₀ k.2
    rw [map_mul]
    have hk : GeneralLinearGroupPoints.adelicEquiv F (t + 1)
        ((k : unipotentAdelic F (t + 1)) : Points F (t + 1)) = AdelicGL.rational F _ a := ha
    rw [hk]
    have := twisted_leviPair_rational_left hfP 1 a X
      (GeneralLinearGroupPoints.adelicEquiv F (t + 1) y) g
    rwa [map_one, one_mul] at this

/-- **The Levi Whittaker coefficient as an iterated set integral.** -/
theorem leviWhittaker_eq {f : AdelicGL F (r + t + 2) → ℂ} (hfc : Continuous f)
    (hfP : ∀ c0 ∈ (blockShape r t).parabolic F, ∀ x, f (AdelicGL.rational F _ c0 * x) = f x)
    (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ)
    (g : AdelicGL F (r + t + 2)) :
    leviWhittaker F r t ψ f g =
      unipotentNormalizer F (r + 1) • ∫ x in fd₀ F (r + 1),
        (unipotentNormalizer F (t + 1) • ∫ y in fd₀ F (t + 1),
          f (leviPair F r t (toMat F _ x) (toMat F _ y) * g) *
            starRingEnd ℂ (genericCharacter F t ψ (fun _ => 1) y) ∂Measure.haar) *
          starRingEnd ℂ (genericCharacter F r ψ (fun _ => 1) x) ∂Measure.haar := by
  obtain ⟨h, hh⟩ : ∃ h : Points F (r + 1) → ℂ, h = fun x =>
      generalLinearWhittakerFunction F t ψ (fun _ => 1)
        (fun y => f (leviPair F r t (GeneralLinearGroupPoints.adelicEquiv F (r + 1) x)
          (GeneralLinearGroupPoints.adelicEquiv F (t + 1) y) * g)) 1 := ⟨_, rfl⟩
  have hh' : ∀ x, h x = unipotentNormalizer F (t + 1) • ∫ y in fd₀ F (t + 1),
      f (leviPair F r t (GeneralLinearGroupPoints.adelicEquiv F (r + 1) x) (toMat F _ y) * g) *
        starRingEnd ℂ (genericCharacter F t ψ (fun _ => 1) y) ∂Measure.haar := fun x => by
    rw [hh]
    exact innerWhittaker_eq hfc hfP ψ hψ g _
  have hG : Continuous fun p : Points F (r + 1) × unipotentAdelic F (t + 1) =>
      f (leviPair F r t (GeneralLinearGroupPoints.adelicEquiv F (r + 1) p.1) (toMat F _ p.2) * g) *
        starRingEnd ℂ (genericCharacter F t ψ (fun _ => 1) p.2) := by
    refine (hfc.comp (((continuous_leviPair F r t).comp
      (((GeneralLinearGroupPoints.adelicHomeomorph F (r + 1)).continuous.comp continuous_fst).prodMk
        ((continuous_toMat F _).comp continuous_snd))).mul continuous_const)).mul ?_
    exact Complex.continuous_conj.comp
      ((RankinSelbergGlobal.Unfolding.continuous_genericCharacter F t ψ hψ.1 _).comp continuous_snd)
  have hhm : Measurable h := by
    have : h = fun x => unipotentNormalizer F (t + 1) • ∫ y, (fun p : Points F (r + 1) ×
        unipotentAdelic F (t + 1) =>
          f (leviPair F r t (GeneralLinearGroupPoints.adelicEquiv F (r + 1) p.1)
            (toMat F _ p.2) * g) * starRingEnd ℂ (genericCharacter F t ψ (fun _ => 1) p.2)) (x, y)
          ∂(Measure.haar.restrict (fd₀ F (t + 1))) := funext hh'
    rw [this]
    exact Measurable.const_smul (hG.measurable.stronglyMeasurable.integral_prod_right'
      (ν := (Measure.haar : Measure (unipotentAdelic F (t + 1))).restrict
        (fd₀ F (t + 1)))).measurable (unipotentNormalizer F (t + 1))
  have hinv : ∀ (k : AdelicSubgroupPoints.rationalSubgroup F (Scheme F (r + 1))
      (upperUnipotent F (r + 1))) (x : Points F (r + 1)),
      h (((k : unipotentAdelic F (r + 1)) : Points F (r + 1)) * x) = h x := by
    intro k x
    obtain ⟨a, ha⟩ := toMat_mem_rational_of_mem_Γ₀ k.2
    have hk : GeneralLinearGroupPoints.adelicEquiv F (r + 1)
        ((k : unipotentAdelic F (r + 1)) : Points F (r + 1)) = AdelicGL.rational F _ a := ha
    have hfun : (fun y : Points F (t + 1) => f (leviPair F r t
        (GeneralLinearGroupPoints.adelicEquiv F (r + 1)
          (((k : unipotentAdelic F (r + 1)) : Points F (r + 1)) * x))
        (GeneralLinearGroupPoints.adelicEquiv F (t + 1) y) * g)) =
        fun y => f (leviPair F r t (GeneralLinearGroupPoints.adelicEquiv F (r + 1) x)
          (GeneralLinearGroupPoints.adelicEquiv F (t + 1) y) * g) := by
      funext y
      rw [map_mul, hk]
      have := twisted_leviPair_rational_left hfP a 1
        (GeneralLinearGroupPoints.adelicEquiv F (r + 1) x)
        (GeneralLinearGroupPoints.adelicEquiv F (t + 1) y) g
      rwa [map_one, one_mul] at this
    rw [hh]
    exact congrArg (fun φ => generalLinearWhittakerFunction F t ψ (fun _ => 1) φ 1) hfun
  have key : leviWhittaker F r t ψ f g = subgroupCharacterCoefficient F (Scheme F (r + 1))
      (upperUnipotent F (r + 1)) (genericCharacter F r ψ fun _ => 1) h 1 := by
    rw [hh]
    rfl
  rw [key, RankinSelbergGlobal.Unfolding.subgroupCharacterCoefficient_eq_setIntegral
    F _ _ _ (RankinSelbergGlobal.Unfolding.continuous_genericCharacter F r ψ hψ.1 _).measurable
    (genericCharacter_mul_rational ψ hψ.2.2.1 r) h hhm hinv 1]
  refine congrArg (fun z : ℂ => unipotentNormalizer F (r + 1) • z) ?_
  refine setIntegral_congr_fun (measurableSet_fundamentalDomain _ _) fun x _ => ?_
  simp only [mul_one]
  rw [hh']
  rfl

theorem haar_fd₀_ne_zero (n : ℕ) :
    (Measure.haar : Measure (unipotentAdelic F n)) (fd₀ F n) ≠ 0 := by
  have := RankinSelbergGlobal.Unfolding.compactSpace_unipotentRationalQuotient F n
  have h := RankinSelbergGlobal.Unfolding.haar_unipotentFundamentalDomain F n
  change (Measure.haar : Measure (unipotentAdelic F n))
    (RankinSelbergGlobal.Unfolding.unipotentFundamentalDomain F n) ≠ 0
  rw [h]
  exact ENNReal.inv_ne_zero.mpr (AdelicSubgroupPoints.quotientMassNormalizer_ne_top _ _ _)

theorem unipotentNormalizer_eq (n : ℕ) :
    unipotentNormalizer F n =
      ((Measure.haar : Measure (unipotentAdelic F n)) (fd₀ F n))⁻¹.toReal := by
  have := RankinSelbergGlobal.Unfolding.compactSpace_unipotentRationalQuotient F n
  have h := RankinSelbergGlobal.Unfolding.haar_unipotentFundamentalDomain F n
  change _ = ((Measure.haar : Measure (unipotentAdelic F n))
    (RankinSelbergGlobal.Unfolding.unipotentFundamentalDomain F n))⁻¹.toReal
  rw [h, inv_inv]

/-- **The Levi integral is the Levi Whittaker coefficient.** -/
theorem setIntegral_fdM_eq_leviWhittaker {f : AdelicGL F (r + t + 2) → ℂ} (hfc : Continuous f)
    (hfP : ∀ c0 ∈ (blockShape r t).parabolic F, ∀ x, f (AdelicGL.rational F _ c0 * x) = f x)
    (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ)
    (g : AdelicGL F (r + t + 2))
    (hint : IntegrableOn (leviIntegrand f ψ g) (fdM F r t) (haarM F r t)) :
    ∫ m in fdM F r t, leviIntegrand f ψ g m ∂haarM F r t = leviWhittaker F r t ψ f g := by
  have hcount : Countable (leviLattice F r t) :=
    countable_of_isDiscrete _ (isDiscrete_leviLattice F r t)
  have hfd1 : IsFundamentalDomain (leviLattice F r t) (fdM F r t) (haarM F r t) :=
    IsFundamentalDomain.mk' (measurableSet_fundamentalDomain _ _).nullMeasurableSet
      (fun m => fundamentalDomain_unique _ _ m)
  have hfd2 : IsFundamentalDomain (leviLattice F r t) (fdProd F r t) (haarM F r t) :=
    IsFundamentalDomain.mk' (measurableSet_fdProd F r t).nullMeasurableSet
      (fun m => existsUnique_mem_fdProd F r t m)
  have hinv : ∀ (c : leviLattice F r t) (m : LeviPart F r t),
      leviIntegrand f ψ g (c • m) = leviIntegrand f ψ g m := fun c m =>
    leviIntegrand_mul hfP ψ hψ.2.2.1 g c.2 m
  have hint2 := (hfd1.integrableOn_iff hfd2 hinv).mp hint
  have hne0 : ((Measure.haar : Measure (unipotentAdelic F (t + 1))).prod
      (Measure.haar : Measure (unipotentAdelic F (r + 1))) (fdProd F r t))⁻¹ ≠ 0 := by
    rw [Measure.prod_prod]
    exact ENNReal.inv_ne_zero.mpr (ENNReal.mul_ne_top (haar_fd₀_ne_top _) (haar_fd₀_ne_top _))
  have hnetop : ((Measure.haar : Measure (unipotentAdelic F (t + 1))).prod
      (Measure.haar : Measure (unipotentAdelic F (r + 1))) (fdProd F r t))⁻¹ ≠ ⊤ := by
    rw [Measure.prod_prod]
    exact ENNReal.inv_ne_top.mpr (mul_ne_zero (haar_fd₀_ne_zero _) (haar_fd₀_ne_zero _))
  have hc : (((Measure.haar : Measure (unipotentAdelic F (t + 1))).prod
      (Measure.haar : Measure (unipotentAdelic F (r + 1)))) (fdProd F r t))⁻¹.toReal =
      unipotentNormalizer F (r + 1) * unipotentNormalizer F (t + 1) := by
    rw [Measure.prod_prod, ENNReal.mul_inv (Or.inr (haar_fd₀_ne_top _))
      (Or.inl (haar_fd₀_ne_top _)), ENNReal.toReal_mul, unipotentNormalizer_eq,
      unipotentNormalizer_eq, mul_comm]
  rw [IntegrableOn, haarM_eq_prod, Measure.restrict_smul, integrable_smul_measure hne0 hnetop,
    fdProd, ← Measure.prod_restrict] at hint2
  rw [hfd1.setIntegral_eq hfd2 hinv, haarM_eq_prod, Measure.restrict_smul, integral_smul_measure,
    fdProd, ← Measure.prod_restrict, integral_prod_symm _ hint2, hc, mul_smul,
    leviWhittaker_eq hfc hfP ψ hψ g]
  refine congrArg (fun z : ℂ => unipotentNormalizer F (r + 1) • z) ?_
  rw [← integral_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [leviIntegrand]
  rw [integral_mul_const, smul_mul_assoc]

end Whittaker

end Langlands.Global.CuspidalPairEisenstein.Unfolding
