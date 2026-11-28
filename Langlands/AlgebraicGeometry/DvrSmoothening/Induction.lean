import Langlands.AlgebraicGeometry.DvrSmoothening.GoodChartStatement
import Langlands.AlgebraicGeometry.DvrSmoothening.Step
import Mathlib.AlgebraicGeometry.QuasiAffine

/-! # The induction on the defect and on the centre -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open scoped TensorProduct

universe u

namespace Langlands.AlgebraicGeometry.DvrSmoothening

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

theorem TestPoint.lift_map {X X₁ : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)} (g : X₁ ⟶ X)
    (P : TestPoint X₁ (g ≫ f)) : (P.map g).lift g P.a rfl = P := by
  cases P
  rfl

/-- Let `g : X₂ ⟶ X` be an isomorphism over a basic open `D(s)` of an affine open `U`, with
`g⁻¹ D(s)` affine. On the chart `g⁻¹ D(s)`, the chart primes of the family of points of `X₂` whose
images under `g` belong to `E` and whose closed points lie over `D(s)` are the extensions of the
chart primes of `E` on `U` not containing `s`. -/
theorem chartPrimes_comp {X X₂ : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [LocallyOfFinitePresentation f] (g : X₂ ⟶ X) [LocallyOfFinitePresentation (g ≫ f)]
    (U : X.affineOpens) (s : Γ(X, U)) [IsIso (g ∣_ X.basicOpen s)]
    (hU₂ : IsAffineOpen (g ⁻¹ᵁ X.basicOpen s)) (h : g ⁻¹ᵁ X.basicOpen s ≤ g ⁻¹ᵁ U)
    (E : TestPoint X f → Prop) :
    letI := (g.appLE U (g ⁻¹ᵁ X.basicOpen s) h).hom.toAlgebra
    (chartPrimes (g ≫ f) (AffineChart.ofAffineOpen ⟨_, hU₂⟩)
        (fun P' => E (P'.map g) ∧ P'.special ∈ g ⁻¹ᵁ X.basicOpen s) :
          Set (Ideal Γ(X₂, g ⁻¹ᵁ X.basicOpen s))) =
      Ideal.map (algebraMap Γ(X, U) Γ(X₂, g ⁻¹ᵁ X.basicOpen s)) ''
        {q : Ideal Γ(X, U) | q ∈ chartPrimes f (AffineChart.ofAffineOpen U) E ∧ s ∉ q} := by
  letI := (g.appLE U (g ⁻¹ᵁ X.basicOpen s) h).hom.toAlgebra
  have hloc : IsLocalization.Away s Γ(X₂, g ⁻¹ᵁ X.basicOpen s) := isLocalization_appLE g U s h
  let U₂ : X₂.affineOpens := ⟨_, hU₂⟩
  -- the prime of a point through `U` avoids `s` exactly when its closed point lies in `D(s)`
  have key : ∀ (P : TestPoint X f) (h₁ : P.special ∈ (AffineChart.ofAffineOpen U).ι.opensRange),
      s ∉ (IsLocalRing.maximalIdeal P.ring).comap ((AffineChart.ofAffineOpen U).pointHom P.a h₁) ↔
        P.special ∈ X.basicOpen s := by
    intro P h₁
    have e1 : ((AffineChart.ofAffineOpen U).liftPoint P.a h₁ (IsLocalRing.closedPoint P.ring) ∈
        U.2.fromSpec ⁻¹ᵁ X.basicOpen s) ↔ P.special ∈ X.basicOpen s := by
      change (AffineChart.ofAffineOpen U).ι _ ∈ X.basicOpen s ↔ _
      rw [AffineChart.ι_liftPoint_closedPoint]
    rw [← e1, U.2.fromSpec_preimage_basicOpen]
    change _ ↔ s ∉ ((AffineChart.ofAffineOpen U).liftPoint P.a h₁
      (IsLocalRing.closedPoint P.ring)).asIdeal
    rw [AffineChart.liftPoint_closedPoint]
  ext q
  constructor
  · rintro ⟨P', ⟨hE, hV⟩, hns, h₂, rfl⟩
    have hV' : g P'.special ∈ X.basicOpen s := hV
    have hUmem : (P'.map g).special ∈ (AffineChart.ofAffineOpen U).ι.opensRange := by
      rw [AffineChart.ofAffineOpen_opensRange]; exact X.basicOpen_le s hV'
    have hns' : (P'.map g).special ∉ f.smoothLocus := fun hs =>
      hns ((mem_smoothLocus_comp_iff f g _ _ hV).mpr hs)
    have hpc := AffineChart.pointHom_comp g U U₂ h P'.a (P'.map g).a rfl h₂ hUmem
    refine ⟨(IsLocalRing.maximalIdeal P'.ring).comap
      ((AffineChart.ofAffineOpen U).pointHom (P'.map g).a hUmem),
      ⟨⟨P'.map g, hE, hns', hUmem, rfl⟩, (key (P'.map g) hUmem).mpr hV'⟩, ?_⟩
    have hK := IsLocalization.map_under (Submonoid.powers s) Γ(X₂, g ⁻¹ᵁ X.basicOpen s)
      ((IsLocalRing.maximalIdeal P'.ring).comap ((AffineChart.ofAffineOpen U₂).pointHom P'.a h₂))
    have e : (IsLocalRing.maximalIdeal P'.ring).comap
        ((AffineChart.ofAffineOpen U).pointHom (P'.map g).a hUmem) =
        ((IsLocalRing.maximalIdeal P'.ring).comap
          ((AffineChart.ofAffineOpen U₂).pointHom P'.a h₂)).comap
            (algebraMap Γ(X, U) Γ(X₂, g ⁻¹ᵁ X.basicOpen s)) :=
      (congrArg (fun φ => (IsLocalRing.maximalIdeal P'.ring).comap φ) hpc).trans rfl
    exact (congrArg (Ideal.map (algebraMap Γ(X, U) Γ(X₂, g ⁻¹ᵁ X.basicOpen s))) e).trans hK
  · rintro ⟨_, ⟨⟨P, hE, hns, h₁, rfl⟩, hs⟩, rfl⟩
    have hPV : P.special ∈ X.basicOpen s := (key P h₁).mp hs
    obtain ⟨a₂, ha₂, hr₂⟩ :=
      exists_lift_of_isIso g (X.basicOpen s) P.a (range_subset_of_closedPoint_mem P.a _ hPV)
    have hP'V : (P.lift g a₂ ha₂).special ∈ g ⁻¹ᵁ X.basicOpen s := hr₂ ⟨_, rfl⟩
    have h₂ : (P.lift g a₂ ha₂).special ∈ (AffineChart.ofAffineOpen U₂).ι.opensRange := by
      rw [AffineChart.ofAffineOpen_opensRange]; exact hP'V
    have hgP : g (P.lift g a₂ ha₂).special = P.special := by
      change (a₂ ≫ g) _ = _
      rw [ha₂]
      rfl
    refine ⟨P.lift g a₂ ha₂, ⟨by rw [TestPoint.map_lift]; exact hE, hP'V⟩, ?_, h₂, ?_⟩
    · intro hsm
      apply hns
      have := (mem_smoothLocus_comp_iff f g _ _ hP'V).mp hsm
      rwa [hgP] at this
    · have hpc := AffineChart.pointHom_comp g U U₂ h a₂ P.a ha₂ h₂ h₁
      have hK := IsLocalization.map_under (Submonoid.powers s) Γ(X₂, g ⁻¹ᵁ X.basicOpen s)
        ((IsLocalRing.maximalIdeal P.ring).comap ((AffineChart.ofAffineOpen U₂).pointHom a₂ h₂))
      have e : (IsLocalRing.maximalIdeal P.ring).comap
          ((AffineChart.ofAffineOpen U).pointHom P.a h₁) =
          ((IsLocalRing.maximalIdeal P.ring).comap
            ((AffineChart.ofAffineOpen U₂).pointHom a₂ h₂)).comap
              (algebraMap Γ(X, U) Γ(X₂, g ⁻¹ᵁ X.basicOpen s)) :=
        (congrArg (fun φ => (IsLocalRing.maximalIdeal P.ring).comap φ) hpc).trans rfl
      exact (congrArg (Ideal.map (algebraMap Γ(X, U) Γ(X₂, g ⁻¹ᵁ X.basicOpen s))) e).trans hK

/-- If a morphism maps the non-smooth closed points of a family into a closed set, it maps the
centre of the family into it. -/
theorem centre_map_le {X X₁ : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    (g : X₁ ⟶ X) [LocallyOfFinitePresentation (g ≫ f)] (E₁ : TestPoint X₁ (g ≫ f) → Prop)
    (T : Set X) (hT : IsClosed T)
    (h : ∀ P, E₁ P → P.special ∉ (g ≫ f).smoothLocus → g P.special ∈ T) :
    ∀ x ∈ centre (g ≫ f) E₁, g x ∈ T := by
  intro x hx
  have hcl : IsClosed (g ⁻¹' T) := hT.preimage g.continuous
  have hsub : badSet (g ≫ f) E₁ ⊆ g ⁻¹' T := by
    rintro _ ⟨P, hP, hs, rfl⟩
    exact h P hP hs
  exact closure_minimal hsub hcl hx

theorem resolved_id {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
    [LocallyOfFinitePresentation f] (P : TestPoint X f) (h : P.special ∈ f.smoothLocus) :
    Resolved (𝟙 X) P :=
  ⟨P.a, Category.comp_id _, (smoothLocus_congr (Category.id_comp f) _).mpr h⟩

variable (R) in
/-- The inductive claim: for every `X` locally of finite type and quasi-compact over `Spec R` with
smooth generic fibre, every family of test points of defect less than `n` can be resolved by a
proper morphism which is an isomorphism away from its centre. -/
def Claim (n : ℕ) : Prop :=
  ∀ (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] [QuasiCompact f],
    GenericallySmooth f → ∀ E : TestPoint X f → Prop, (∀ P, E P → P.defect < n) →
    ∃ (X' : Scheme.{u}) (g : X' ⟶ X) (_ : IsProper g), IsIso (g ∣_ (centre f E).compl) ∧
      ∀ P, E P → Resolved g P

theorem resolve_of_centre_eq_bot {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [LocallyOfFiniteType f] (E : TestPoint X f → Prop) (h : centre f E = ⊥) :
    ∃ (X' : Scheme.{u}) (g : X' ⟶ X) (_ : IsProper g), IsIso (g ∣_ (centre f E).compl) ∧
      ∀ P, E P → Resolved g P := by
  refine ⟨X, 𝟙 X, inferInstance, inferInstance, fun P hP => resolved_id P ?_⟩
  by_contra hs
  have := mem_badSet f hP hs
  rw [h] at this
  exact this

theorem claim_zero : Claim R 0 := by
  intro X f _ _ _ E hE
  apply resolve_of_centre_eq_bot
  have hb : badSet f E = ∅ := by
    ext x
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨P, hP, -, -⟩
    have := hE P hP
    simp at this
  apply Closeds.ext
  change closure (badSet f E) = ∅
  rw [hb, closure_empty]

theorem claim_succ (hDZ : DefectZeroSmoothAtStatement.{u}) (hDD : DilatationDefectStatement.{u})
    (hGC : GoodChartStatement.{u}) (hBC : BlowupChartStatement.{u}) {ϖ : R} (hϖ : Irreducible ϖ)
    (n : ℕ) (ih : Claim R n) : Claim R (n + 1) := by
  intro X f _ _ hgen
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := ⟨⟩
  suffices H : ∀ (Z : Closeds X) (E : TestPoint X f → Prop), centre f E = Z →
      (∀ P, E P → P.defect < ((n + 1 : ℕ) : ℕ∞)) →
      ∃ (X' : Scheme.{u}) (g : X' ⟶ X) (_ : IsProper g), IsIso (g ∣_ (centre f E).compl) ∧
        ∀ P, E P → Resolved g P from fun E hE => H _ E rfl hE
  intro Z
  induction Z using WellFoundedLT.induction with
  | ind Z IH => ?_
  intro E hZ hE
  subst hZ
  by_cases hbot : centre f E = ⊥
  · exact resolve_of_centre_eq_bot f E hbot
  -- a point of the centre and an affine open around it
  obtain ⟨z, hz⟩ : ∃ z, z ∈ centre f E := by
    by_contra hne
    push Not at hne
    exact hbot (Closeds.ext (Set.eq_empty_iff_forall_notMem.mpr hne))
  obtain ⟨_, ⟨U, hU, rfl⟩, hzU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
  let U' : X.affineOpens := ⟨U, hU⟩
  letI : Algebra R Γ(X, U) := ((AffineChart.ofAffineOpen U').base f).toAlgebra
  have hft : Algebra.FiniteType R Γ(X, U) := (AffineChart.ofAffineOpen U').finiteType_base f
  have hS : (chartPrimes f (AffineChart.ofAffineOpen U') E).Nonempty := by
    obtain ⟨x, hxU, P, hP, hs, rfl⟩ := mem_closure_iff.mp hz U U.2 hzU
    refine ⟨_, P, hP, hs, ?_, rfl⟩
    rw [AffineChart.ofAffineOpen_opensRange]
    exact hxU
  obtain ⟨s, hsJ, hgoodS⟩ := hGC R Γ(X, U)
    (PrimeSpectrum.vanishingIdeal (U'.2.fromSpec ⁻¹' centre f E))
    (chartPrimes f (AffineChart.ofAffineOpen U') E)
    (by exact vanishingIdeal_centre_eq f E (AffineChart.ofAffineOpen U')) hS
    (by exact chartPrimes_spec f (AffineChart.ofAffineOpen U') E)
  -- a point of the centre in `D(s)`
  obtain ⟨y, hyZ, hys⟩ : ∃ y, U'.2.fromSpec y ∈ centre f E ∧ s ∉ y.asIdeal := by
    by_contra hne
    push Not at hne
    exact hsJ ((PrimeSpectrum.mem_vanishingIdeal _ _).mpr fun y hy => hne y hy)
  have hyV : U'.2.fromSpec y ∈ X.basicOpen s := by
    have : y ∈ U'.2.fromSpec ⁻¹ᵁ X.basicOpen s := by
      rw [U'.2.fromSpec_preimage_basicOpen]
      exact (PrimeSpectrum.mem_basicOpen _ _).mpr hys
    exact this
  -- the points outside `D(s)` are resolved by the inner induction hypothesis
  let E₂ : TestPoint X f → Prop := fun P => E P ∧ P.special ∉ X.basicOpen s
  have hsub : (centre f E₂ : Set X) ⊆ ((X.basicOpen s : Set X))ᶜ := by
    apply closure_minimal _ (X.basicOpen s).2.isClosed_compl
    rintro _ ⟨P, hP, -, rfl⟩
    exact hP.2
  have hlt : centre f E₂ < centre f E := by
    refine lt_of_le_of_ne (centre_mono f fun P hP => hP.1) ?_
    intro heq
    have : U'.2.fromSpec y ∈ centre f E₂ := by rw [heq]; exact hyZ
    exact hsub this hyV
  obtain ⟨X₂, g₂, hg₂p, hg₂i, hres₂⟩ := IH _ hlt E₂ rfl (fun P hP => hE P hP.1)
  have hV₂ : X.basicOpen s ≤ (centre f E₂).compl := fun x hx hxc => hsub hxc hx
  have : IsIso (g₂ ∣_ X.basicOpen s) := isIso_morphismRestrict_of_le g₂ hV₂
  have hgen₂ : GenericallySmooth (g₂ ≫ f) :=
    hgen.comp g₂ (centre f E₂).compl (fun x hx => not_mem_centre_of_generic f E₂ hx)
  have hU₂a : IsAffineOpen (g₂ ⁻¹ᵁ X.basicOpen s) := by
    have : IsAffine (X.basicOpen s) := U'.2.basicOpen s
    exact IsAffine.of_isIso (g₂ ∣_ X.basicOpen s)
  let U₂ : X₂.affineOpens := ⟨g₂ ⁻¹ᵁ X.basicOpen s, hU₂a⟩
  have hU₂U : g₂ ⁻¹ᵁ X.basicOpen s ≤ g₂ ⁻¹ᵁ U := fun x hx => X.basicOpen_le s hx
  let E₁ : TestPoint X₂ (g₂ ≫ f) → Prop :=
    fun P' => E (P'.map g₂) ∧ P'.special ∈ g₂ ⁻¹ᵁ X.basicOpen s
  -- the good chart over `D(s)`, transported to `X₂`
  letI alg₂ : Algebra Γ(X, U) Γ(X₂, g₂ ⁻¹ᵁ X.basicOpen s) :=
    (g₂.appLE U (g₂ ⁻¹ᵁ X.basicOpen s) hU₂U).hom.toAlgebra
  have hloc : IsLocalization.Away s Γ(X₂, g₂ ⁻¹ᵁ X.basicOpen s) :=
    isLocalization_appLE g₂ U' s hU₂U
  letI : Algebra R Γ(X₂, g₂ ⁻¹ᵁ X.basicOpen s) :=
    ((AffineChart.ofAffineOpen U₂).base (g₂ ≫ f)).toAlgebra
  have htower : IsScalarTower R Γ(X, U) Γ(X₂, g₂ ⁻¹ᵁ X.basicOpen s) :=
    IsScalarTower.of_algebraMap_eq fun r => by
      change (AffineChart.ofAffineOpen U₂).base (g₂ ≫ f) r =
        (g₂.appLE U (g₂ ⁻¹ᵁ X.basicOpen s) hU₂U).hom ((AffineChart.ofAffineOpen U').base f r)
      rw [AffineChart.base_comp f g₂ U' U₂ hU₂U]
      rfl
  obtain ⟨hsm₂, hfree₂⟩ := hgoodS Γ(X₂, g₂ ⁻¹ᵁ X.basicOpen s)
  have hJ₂ : (PrimeSpectrum.vanishingIdeal (U₂.2.fromSpec ⁻¹' centre (g₂ ≫ f) E₁) :
      Ideal Γ(X₂, g₂ ⁻¹ᵁ X.basicOpen s)) =
      (PrimeSpectrum.vanishingIdeal (U'.2.fromSpec ⁻¹' centre f E)).map
        (algebraMap Γ(X, U) Γ(X₂, g₂ ⁻¹ᵁ X.basicOpen s)) := by
    calc (PrimeSpectrum.vanishingIdeal (U₂.2.fromSpec ⁻¹' centre (g₂ ≫ f) E₁) :
          Ideal Γ(X₂, g₂ ⁻¹ᵁ X.basicOpen s))
        = (sInf (chartPrimes (g₂ ≫ f) (AffineChart.ofAffineOpen U₂) E₁) :
            Ideal Γ(X₂, g₂ ⁻¹ᵁ X.basicOpen s)) := by
          exact vanishingIdeal_centre_eq _ E₁ (AffineChart.ofAffineOpen U₂)
      _ = sInf (Ideal.map (algebraMap Γ(X, U) Γ(X₂, g₂ ⁻¹ᵁ X.basicOpen s)) ''
            {q : Ideal Γ(X, U) | q ∈ chartPrimes f (AffineChart.ofAffineOpen U') E ∧ s ∉ q}) := by
          exact congrArg sInf (chartPrimes_comp f g₂ U' s hU₂a hU₂U E)
      _ = (sInf (chartPrimes f (AffineChart.ofAffineOpen U') E : Set (Ideal Γ(X, U)))).map
            (algebraMap Γ(X, U) Γ(X₂, g₂ ⁻¹ᵁ X.basicOpen s)) :=
          by
            have hp : ∀ q ∈ (chartPrimes f (AffineChart.ofAffineOpen U') E : Set (Ideal Γ(X, U))),
                q.IsPrime := chartPrimes_isPrime f (AffineChart.ofAffineOpen U') E
            exact (@map_sInf_eq Γ(X, U) Γ(X₂, g₂ ⁻¹ᵁ X.basicOpen s) _ _ alg₂ s hloc _ hp).symm
      _ = _ := by
          exact congrArg (Ideal.map (algebraMap Γ(X, U) Γ(X₂, g₂ ⁻¹ᵁ X.basicOpen s)))
            (vanishingIdeal_centre_eq f E (AffineChart.ofAffineOpen U')).symm
  -- one dilatation lowers the defects of the points of `E₁` through the centre
  obtain ⟨X₃, g₃, hg₃p, hg₃i, hdrop⟩ := dilatation_step hDZ hDD hBC hϖ (g₂ ≫ f) hgen₂ U₂ E₁ n
    (fun P' hP' => by
      rw [← TestPoint.defect_map g₂ (X.basicOpen s) P' hP'.2]
      exact hE _ hP'.1)
    (fun P' hP' => hP'.2) _ hJ₂ (by exact ⟨hsm₂, hfree₂⟩)
  have hgen₃ : GenericallySmooth (g₃ ≫ g₂ ≫ f) :=
    hgen₂.comp g₃ (centre (g₂ ≫ f) E₁).compl
      (fun x hx => not_mem_centre_of_generic (g₂ ≫ f) E₁ hx)
  let E₃ : TestPoint X₃ (g₃ ≫ g₂ ≫ f) → Prop :=
    fun P₃ => E₁ (P₃.map g₃) ∧ (P₃.map g₃).special ∈ centre (g₂ ≫ f) E₁
  obtain ⟨X₄, g₄, hg₄p, hg₄i, hres₄⟩ := ih X₃ (g₃ ≫ g₂ ≫ f) hgen₃ E₃ (fun P₃ hP₃ => by
    have := hdrop (P₃.map g₃) hP₃.1 hP₃.2 P₃.a rfl
    rwa [TestPoint.lift_map] at this)
  -- the composite resolves every point of `E`
  have hY₁ : ∀ x ∈ centre (g₂ ≫ f) E₁, g₂ x ∈ centre f E :=
    centre_map_le f g₂ E₁ _ (centre f E).2 (fun P' hP' hns =>
      mem_badSet f hP'.1 (fun hs => hns ((mem_smoothLocus_comp_iff f g₂ _ _ hP'.2).mpr hs)))
  have hY₃ : ∀ x ∈ centre (g₃ ≫ g₂ ≫ f) E₃, g₃ x ∈ centre (g₂ ≫ f) E₁ :=
    centre_map_le (g₂ ≫ f) g₃ E₃ _ (centre (g₂ ≫ f) E₁).2 (fun P₃ hP₃ _ => hP₃.2)
  refine ⟨X₄, g₄ ≫ g₃ ≫ g₂, inferInstance, ?_, ?_⟩
  · have hZ₂ : (centre f E).compl ≤ (centre f E₂).compl :=
      fun x hx hx' => hx (centre_mono f (fun P hP => hP.1) hx')
    have : IsIso (g₂ ∣_ (centre f E).compl) := isIso_morphismRestrict_of_le g₂ hZ₂
    have : IsIso (g₃ ∣_ g₂ ⁻¹ᵁ (centre f E).compl) :=
      isIso_morphismRestrict_of_le g₃ (U := (centre (g₂ ≫ f) E₁).compl)
        (fun x hx hx' => hx (hY₁ x hx'))
    have : IsIso (g₄ ∣_ (g₃ ≫ g₂) ⁻¹ᵁ (centre f E).compl) :=
      isIso_morphismRestrict_of_le g₄ (U := (centre (g₃ ≫ g₂ ≫ f) E₃).compl)
        (fun x hx hx' => hx (hY₁ _ (hY₃ x hx')))
    have : IsIso ((g₃ ≫ g₂) ∣_ (centre f E).compl) := isIso_morphismRestrict_comp g₃ g₂ _
    exact isIso_morphismRestrict_comp g₄ (g₃ ≫ g₂) _
  · intro P hP
    have hW₃ : (g₂ ≫ f).smoothLocus ≤ (centre (g₂ ≫ f) E₁).compl :=
      fun x hx hx' => centre_nonsmooth _ E₁ hx' hx
    have hW₄ : ((g₃ ≫ g₂) ≫ f).smoothLocus ≤ (centre (g₃ ≫ g₂ ≫ f) E₃).compl :=
      fun x hx hx' => centre_nonsmooth _ E₃ hx' ((smoothLocus_congr (Category.assoc g₃ g₂ f) x).mp hx)
    by_cases hPV : P.special ∈ X.basicOpen s
    · obtain ⟨a₂, ha₂, hr₂⟩ :=
        exists_lift_of_isIso g₂ (X.basicOpen s) P.a (range_subset_of_closedPoint_mem P.a _ hPV)
      have hP' : E₁ (P.lift g₂ a₂ ha₂) := ⟨by rw [TestPoint.map_lift]; exact hP, hr₂ ⟨_, rfl⟩⟩
      by_cases hPY : (P.lift g₂ a₂ ha₂).special ∈ centre (g₂ ≫ f) E₁
      · obtain ⟨a₃, ha₃⟩ := TestPoint.exists_lift g₃ (centre (g₂ ≫ f) E₁).compl
          (fun x hx => not_mem_centre_of_generic (g₂ ≫ f) E₁ hx) (P.lift g₂ a₂ ha₂)
        have hP₃ : E₃ ((P.lift g₂ a₂ ha₂).lift g₃ a₃ ha₃) :=
          ⟨by rw [TestPoint.map_lift]; exact hP', by rw [TestPoint.map_lift]; exact hPY⟩
        obtain ⟨a₄, ha₄, hs₄⟩ := hres₄ _ hP₃
        refine ⟨a₄, ?_, ?_⟩
        · change a₄ ≫ g₄ = a₃ at ha₄
          change a₃ ≫ g₃ = a₂ at ha₃
          exact ((reassoc_of% ha₄) (g₃ ≫ g₂)).trans (((reassoc_of% ha₃) g₂).trans ha₂)
        · exact (smoothLocus_congr (by simp only [Category.assoc]) _).mp hs₄
      · have hsm : (P.lift g₂ a₂ ha₂).special ∈ (g₂ ≫ f).smoothLocus := by
          by_contra hns
          exact hPY (mem_badSet _ hP' hns)
        have hr : Resolved g₂ P := ⟨a₂, ha₂, hsm⟩
        exact (hr.comp g₃ _ hW₃).comp g₄ _ hW₄
    · have hr : Resolved g₂ P := hres₂ P ⟨hP, hPV⟩
      exact (hr.comp g₃ _ hW₃).comp g₄ _ hW₄

/-- Given the four input statements and a uniformizer, `Claim R n` holds for every `n`: test points
of bounded defect can be resolved. -/
theorem claim (hDZ : DefectZeroSmoothAtStatement.{u}) (hDD : DilatationDefectStatement.{u})
    (hGC : GoodChartStatement.{u}) (hBC : BlowupChartStatement.{u}) {ϖ : R} (hϖ : Irreducible ϖ)
    (n : ℕ) : Claim R n := by
  induction n with
  | zero => exact claim_zero
  | succ n ih => exact claim_succ hDZ hDD hGC hBC hϖ n ih

end Langlands.AlgebraicGeometry.DvrSmoothening
