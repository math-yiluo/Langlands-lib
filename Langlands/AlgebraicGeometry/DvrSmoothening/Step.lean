import Langlands.AlgebraicGeometry.BlowupChartStatement
import Langlands.AlgebraicGeometry.DvrSmoothening.Centres
import Langlands.AlgebraicGeometry.DvrSmoothening.ChartLocalization
import Langlands.AlgebraicGeometry.DvrSmoothening.DefectZeroStatement
import Langlands.AlgebraicGeometry.DvrSmoothening.DilatationDefectStatement
import Langlands.AlgebraicGeometry.DvrSmoothening.Modification

/-! # One dilatation lowers the defect of the points through its centre -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open scoped TensorProduct

universe u

namespace Langlands.AlgebraicGeometry.DvrSmoothening

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

section Chart

variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))

/-- A test point read in a chart, as a homomorphism of `R`-algebras. -/
noncomputable def AffineChart.pointAlgHom (C : AffineChart X) (P : TestPoint X f)
    (h : P.special ∈ C.ι.opensRange) :
    letI := (C.base f).toAlgebra
    C.ring →ₐ[R] P.ring :=
  letI := (C.base f).toAlgebra
  { C.pointHom P.a h with
    commutes' := fun r => RingHom.congr_fun (C.pointHom_comp_base f P.a P.ha h) r }

theorem TestPoint.defect_eq_pointDefect (P : TestPoint X f) (C : AffineChart X)
    (h : P.special ∈ C.ι.opensRange) :
    letI := (C.base f).toAlgebra
    P.defect = pointDefect (C.pointAlgHom f P h) := by
  let := (C.base f).toAlgebra
  rw [P.defect_eq C h, ← chartDefect_algebraMap]
  rfl

variable [LocallyOfFinitePresentation f]

/-- The primes of the closed points of the non-smooth points of `E` through a chart. -/
def chartPrimes (C : AffineChart X) (E : TestPoint X f → Prop) : Set (Ideal C.ring) :=
  {q | ∃ P, E P ∧ P.special ∉ f.smoothLocus ∧ ∃ h : P.special ∈ C.ι.opensRange,
    q = (IsLocalRing.maximalIdeal P.ring).comap (C.pointHom P.a h)}

theorem vanishingIdeal_centre_eq (E : TestPoint X f → Prop) (C : AffineChart X) :
    PrimeSpectrum.vanishingIdeal (C.ι ⁻¹' (centre f E)) = sInf (chartPrimes f C E) :=
  vanishingIdeal_centre f E C

theorem chartPrimes_spec (C : AffineChart X) (E : TestPoint X f → Prop) :
    letI := (C.base f).toAlgebra
    ∀ p ∈ chartPrimes f C E, ∃ (R'' : Type u) (_ : CommRing R'') (_ : IsDomain R'')
      (_ : IsDiscreteValuationRing R'') (_ : Algebra R R'') (_ : IsLocalHom (algebraMap R R''))
      (ψ : C.ring →ₐ[R] R''), IsRamificationIndexOne R R'' ∧
        (IsLocalRing.maximalIdeal R'').comap ψ = p := by
  letI := (C.base f).toAlgebra
  rintro _ ⟨P, -, -, h, rfl⟩
  exact ⟨P.ring, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    C.pointAlgHom f P h, P.ram, rfl⟩

theorem chartPrimes_isPrime (C : AffineChart X) (E : TestPoint X f → Prop) :
    ∀ q ∈ chartPrimes f C E, q.IsPrime := by
  rintro _ ⟨P, -, -, h, rfl⟩
  exact Ideal.comap_isPrime _ _

/-- Given `DefectZeroSmoothAtStatement`, for `f` locally of finite type with smooth generic fibre,
a test point whose closed point is not in the smooth locus has non-zero defect. -/
theorem TestPoint.defect_ne_zero (hDZ : DefectZeroSmoothAtStatement.{u}) {ϖ : R}
    (hϖ : Irreducible ϖ) [LocallyOfFiniteType f] (hgen : GenericallySmooth f)
    (P : TestPoint X f) (hs : P.special ∉ f.smoothLocus) : P.defect ≠ 0 := by
  obtain ⟨C, h⟩ := P.mem_chart
  letI := (C.base f).toAlgebra
  have := C.finiteType_base f
  have hsm := C.smooth_away f hϖ hgen
  intro h0
  rw [P.defect_eq_pointDefect f C h] at h0
  have hmem := hDZ R C.ring P.ring ϖ hϖ P.ram hsm (C.pointAlgHom f P h) h0
  apply hs
  have hy : (C.liftPoint P.a h (IsLocalRing.closedPoint P.ring) : PrimeSpectrum C.ring) =
      ⟨(IsLocalRing.maximalIdeal P.ring).comap (C.pointAlgHom f P h), Ideal.comap_isPrime _ _⟩ :=
    PrimeSpectrum.ext (C.liftPoint_closedPoint P.a h)
  have := (C.ι_mem_smoothLocus_iff f (C.liftPoint P.a h (IsLocalRing.closedPoint P.ring))).mpr
    (by rw [hy]; exact hmem)
  rwa [C.ι_liftPoint_closedPoint] at this

end Chart

theorem lt_of_lt_of_lt_succ {a b : ℕ∞} {n : ℕ} (h₁ : a < b) (h₂ : b < ((n + 1 : ℕ) : ℕ∞)) :
    a < n := by
  have hb : b ≤ n := by
    induction b using ENat.recTopCoe with
    | top => exact absurd h₂ (not_lt.mpr le_top)
    | coe m =>
      have : m < n + 1 := by exact_mod_cast h₂
      exact_mod_cast Nat.lt_succ_iff.mp this
  exact lt_of_lt_of_le h₁ hb

/-- **One dilatation.** Let `f` be locally of finite type with smooth generic fibre, `U` an affine
open, and `E` a family of test points of defect `< n + 1` whose closed points lie in `U`. Let `J₀`
be the ideal of the centre of `E` on `U`, and assume the good chart condition of
`GoodChartStatement`: `k ⊗_R (Γ(U) ⧸ J₀)` is smooth over the residue field `k` of `R` and
`(Γ(U) ⧸ J₀) ⊗ Ω_{Γ(U)/R}` is free. Then there is a proper `g : X' ⟶ X` (the blow-up of the
centre), an isomorphism away from the centre, such that every lift along `g` of a member of `E`
whose closed point lies in the centre has defect `< n`. -/
theorem dilatation_step (hDZ : DefectZeroSmoothAtStatement.{u})
    (hDD : DilatationDefectStatement.{u}) (hBC : BlowupChartStatement.{u}) {ϖ : R}
    (hϖ : Irreducible ϖ) {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [LocallyOfFiniteType f] (hgen : GenericallySmooth f) (U : X.affineOpens)
    (E : TestPoint X f → Prop) (n : ℕ) (hn : ∀ P, E P → P.defect < ((n + 1 : ℕ) : ℕ∞))
    (hU : ∀ P, E P → P.special ∈ (U : X.Opens)) (J₀ : Ideal Γ(X, U))
    (hJ₀ : PrimeSpectrum.vanishingIdeal (U.2.fromSpec ⁻¹' centre f E) = J₀)
    (hgood : letI : Algebra R Γ(X, U) := ((AffineChart.ofAffineOpen U).base f).toAlgebra
      Algebra.Smooth (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R ⊗[R]
        (Γ(X, U) ⧸ J₀)) ∧
      Module.Free (Γ(X, U) ⧸ J₀) ((Γ(X, U) ⧸ J₀) ⊗[Γ(X, U)] Ω[Γ(X, U)⁄R])) :
    ∃ (X' : Scheme.{u}) (g : X' ⟶ X) (_ : IsProper g), IsIso (g ∣_ (centre f E).compl) ∧
      ∀ P, E P → P.special ∈ centre f E →
        ∀ (a : Spec (CommRingCat.of P.ring) ⟶ X') (ha : a ≫ g = P.a),
          (P.lift g a ha).defect < n := by
  classical
  subst hJ₀
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have ht : ∀ V : X.affineOpens, X.presheaf.map (homOfLE le_top).op
      (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ϖ)) ∈
        (Scheme.IdealSheafData.vanishingIdeal (centre f E)).ideal V := by
    intro V
    rw [AffineChart.restrict_appTop_eq_base f V ϖ, Scheme.IdealSheafData.vanishingIdeal_ideal]
    refine (PrimeSpectrum.mem_vanishingIdeal _ _).mpr ?_
    intro y hy
    have hcomap : f ((AffineChart.ofAffineOpen V).ι y) =
        PrimeSpectrum.comap ((AffineChart.ofAffineOpen V).base f) y := by
      change ((AffineChart.ofAffineOpen V).ι ≫ f) y = _
      rw [← AffineChart.Spec_base]
      rfl
    have h1 : (PrimeSpectrum.comap ((AffineChart.ofAffineOpen V).base f) y).asIdeal =
        IsLocalRing.maximalIdeal R := by
      rw [← hcomap]
      exact congrArg PrimeSpectrum.asIdeal (centre_special f E hy)
    have h2 : ϖ ∈ IsLocalRing.maximalIdeal R :=
      (IsLocalRing.mem_maximalIdeal _).mpr hϖ.not_isUnit
    rw [← h1] at h2
    exact h2
  obtain ⟨X', g, hgp, hgi, hch⟩ := hBC X _ (Scheme.IdealSheafData.vanishingIdeal (centre f E)) ht
  have hsupp : (Scheme.IdealSheafData.vanishingIdeal (centre f E)).support = centre f E :=
    Closeds.ext (Scheme.IdealSheafData.coe_support_vanishingIdeal _)
  rw [hsupp] at hgi
  refine ⟨X', g, hgp, hgi, ?_⟩
  intro P hE hPY a ha
  have hPU : P.special ∈ (AffineChart.ofAffineOpen U).ι.opensRange := by
    rw [AffineChart.ofAffineOpen_opensRange]; exact hU P hE
  letI : Algebra R Γ(X, U) := ((AffineChart.ofAffineOpen U).base f).toAlgebra
  have hft : Algebra.FiniteType R Γ(X, U) := (AffineChart.ofAffineOpen U).finiteType_base f
  let φ : Γ(X, U) →ₐ[R] P.ring := (AffineChart.ofAffineOpen U).pointAlgHom f P hPU
  let J : Ideal Γ(X, U) := PrimeSpectrum.vanishingIdeal (U.2.fromSpec ⁻¹' centre f E)
  have hJφ : J ≤ (IsLocalRing.maximalIdeal P.ring).comap φ := by
    intro x hx
    have hy : (AffineChart.ofAffineOpen U).liftPoint P.a hPU (IsLocalRing.closedPoint P.ring) ∈
        U.2.fromSpec ⁻¹' centre f E := by
      change (AffineChart.ofAffineOpen U).ι _ ∈ centre f E
      rw [AffineChart.ι_liftPoint_closedPoint]
      exact hPY
    have := (PrimeSpectrum.mem_vanishingIdeal _ _).mp hx _ hy
    rw [AffineChart.liftPoint_closedPoint] at this
    exact this
  have hdiv : ∀ x ∈ J, φ x ∈ Ideal.span {algebraMap R P.ring ϖ} := by
    intro x hx
    have := hJφ hx
    rw [Ideal.mem_comap, ← P.ram.1, hϖ.maximalIdeal_eq, Ideal.map_span,
      Set.image_singleton] at this
    exact this
  have : Module.IsTorsionFree R P.ring :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (algebraMap_injective_of_ram P.ram)
  let φ' := GroupScheme.Dilatation.liftBlowup hϖ0 J φ hdiv
  have hφ' : φ'.comp (GroupScheme.Dilatation.blowupMap ϖ J) = φ :=
    GroupScheme.Dilatation.liftBlowup_comp hϖ0 J φ hdiv
  obtain ⟨j, hj, hjg⟩ : ∃ j : Spec (CommRingCat.of (GroupScheme.Dilatation.blowupAlgebra ϖ J)) ⟶ X',
      IsOpenImmersion j ∧
        j ≫ g = Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) _)) ≫ U.2.fromSpec := by
    have := hch U
    rw [AffineChart.restrict_appTop_eq_base, Scheme.IdealSheafData.vanishingIdeal_ideal] at this
    exact this
  let C₃ : AffineChart X' := ⟨CommRingCat.of (GroupScheme.Dilatation.blowupAlgebra ϖ J), j⟩
  have hφa : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ U.2.fromSpec = P.a := by
    have e := AffineChart.Spec_pointHom (AffineChart.ofAffineOpen U) P.a hPU
    change Spec.map (CommRingCat.ofHom ((AffineChart.ofAffineOpen U).pointHom P.a hPU)) ≫
      (AffineChart.ofAffineOpen U).ι = P.a
    rw [e, AffineChart.liftPoint_ι]
  have hgen' : ∀ x : X, (f x).asIdeal = ⊥ → x ∈ (centre f E).compl :=
    fun x hx => not_mem_centre_of_generic f E hx
  have ha' : a = Spec.map (CommRingCat.ofHom φ'.toRingHom) ≫ j := by
    apply TestPoint.lift_unique g (centre f E).compl hgen' P a _ ha
    rw [Category.assoc, hjg, ← Category.assoc, ← Spec.map_comp, ← hφa]
    congr 2
    rw [← hφ']
    rfl
  have h₃ : (P.lift g a ha).special ∈ C₃.ι.opensRange := by
    refine ⟨(Spec.map (CommRingCat.ofHom φ'.toRingHom)) (IsLocalRing.closedPoint P.ring), ?_⟩
    change _ = a (IsLocalRing.closedPoint P.ring)
    rw [ha']
    rfl
  have hbase₃ : C₃.base (g ≫ f) =
      algebraMap R (GroupScheme.Dilatation.blowupAlgebra ϖ J) := by
    have e : Spec.map (CommRingCat.ofHom (C₃.base (g ≫ f))) =
        Spec.map (CommRingCat.ofHom (algebraMap R (GroupScheme.Dilatation.blowupAlgebra ϖ J))) := by
      rw [AffineChart.Spec_base, IsScalarTower.algebraMap_eq R Γ(X, U)
        (GroupScheme.Dilatation.blowupAlgebra ϖ J), CommRingCat.ofHom_comp, Spec.map_comp]
      change j ≫ g ≫ f = _
      rw [← Category.assoc, hjg, Category.assoc]
      congr 1
      exact (AffineChart.Spec_base (AffineChart.ofAffineOpen U) f).symm
    exact congrArg CommRingCat.Hom.hom (AffineChart.Spec_map_injective e)
  have hpt₃ : C₃.pointHom a h₃ = φ'.toRingHom :=
    AffineChart.pointHom_eq_of_Spec C₃ h₃ _ ha'.symm
  have hdef₃ : (P.lift g a ha).defect = pointDefect φ' := by
    rw [TestPoint.defect_eq _ C₃ h₃]
    change chartDefect (C₃.base (g ≫ f)) (C₃.pointHom a h₃) = _
    rw [hbase₃, hpt₃]
    exact chartDefect_algebraMap φ'
  have hdef : P.defect = pointDefect φ := P.defect_eq_pointDefect f _ hPU
  have hne : pointDefect φ ≠ 0 := by
    rw [← hdef]
    exact P.defect_ne_zero f hDZ hϖ hgen (centre_nonsmooth f E hPY)
  have hlt := hDD R Γ(X, U) ϖ hϖ
    (by exact (AffineChart.ofAffineOpen U).smooth_away f hϖ hgen) J
    (chartPrimes f (AffineChart.ofAffineOpen U) E)
    (by exact vanishingIdeal_centre_eq f E (AffineChart.ofAffineOpen U))
    (by exact chartPrimes_spec f (AffineChart.ofAffineOpen U) E) hgood.1 hgood.2 P.ring P.ram φ hJφ
    φ' hφ' hne
  rw [hdef₃]
  rw [← hdef] at hlt
  exact lt_of_lt_of_lt_succ hlt (hn P hE)

end Langlands.AlgebraicGeometry.DvrSmoothening
