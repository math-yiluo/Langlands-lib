import Langlands.Algebra.GenericDensity
import Langlands.AlgebraicGeometry.GeometricallyConnectedFiberGenericConstancy
import Langlands.AlgebraicGeometry.ClosedSubschemeFiberIncidence
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.Spectrum.Prime.Chevalley

/-! # Actual fibre-zero loci for finite type algebras -/

noncomputable section

universe u v w

open TensorProduct Set Topology

namespace Langlands.Algebra.FiberZeroConstructibility

variable {R : Type u} [CommRing R] {B : Type v} [CommRing B] [Algebra R B]

/-- The ideal annihilating one specified element, retaining all nilpotents. -/
def elementAnnihilator (b : B) : Ideal B :=
  (Submodule.span B ({b} : Set B)).annihilator

@[simp]
theorem mem_elementAnnihilator (b x : B) :
    x ∈ elementAnnihilator b ↔ x * b = 0 :=
  Submodule.mem_annihilator_span_singleton b x

/-- Multiplication by the specified element, with its actual kernel removed. -/
def annihilatorMul (b : B) : (B ⧸ elementAnnihilator b) →ₗ[R] B :=
  ((elementAnnihilator b).liftQ (LinearMap.toSpanSingleton B B b)
    (by rw [elementAnnihilator, Submodule.annihilator_span_singleton])).restrictScalars R

@[simp]
theorem annihilatorMul_mk (b x : B) :
    annihilatorMul (R := R) b (Ideal.Quotient.mk _ x) = x * b := rfl

theorem annihilatorMul_injective (b : B) :
    Function.Injective (annihilatorMul (R := R) b) := by
  change Function.Injective
    ((elementAnnihilator b).liftQ (LinearMap.toSpanSingleton B B b)
      (by rw [elementAnnihilator, Submodule.annihilator_span_singleton]))
  apply LinearMap.ker_eq_bot.mp
  apply Submodule.ker_liftQ_eq_bot'
  exact Submodule.annihilator_span_singleton b

theorem annihilatorMul_exact (b : B) :
    Function.Exact (annihilatorMul (R := R) b)
      (Ideal.Quotient.mkₐ R (Ideal.span ({b} : Set B))).toLinearMap := by
  intro x
  change Ideal.Quotient.mk _ x = 0 ↔ ∃ y, annihilatorMul (R := R) b y = x
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨Ideal.Quotient.mk _ y, by simpa [mul_comm] using hy⟩
  · rintro ⟨y, hy⟩
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨z, by simpa [mul_comm] using hy⟩

/-- Passing from a field to a field extension detects equations in the full
tensor algebra. -/
theorem tensor_eq_zero_iff_of_field_extension
    {K : Type w} [Field K] {L : Type*} [Field L]
    [Algebra R K] [Algebra R L] [Algebra K L] [IsScalarTower R K L] (b : B) :
    (1 : L) ⊗ₜ[R] b = 0 ↔ (1 : K) ⊗ₜ[R] b = 0 := by
  let e := Algebra.TensorProduct.cancelBaseChange R K L L B
  have hinj := Algebra.TensorProduct.includeRight_injective
    (R := K) (A := L) (B := K ⊗[R] B) (RingHom.injective (algebraMap K L))
  have he : e ((1 : L) ⊗ₜ[K] ((1 : K) ⊗ₜ[R] b)) = (1 : L) ⊗ₜ[R] b := by
    simp [e]
  constructor
  · intro h
    apply hinj
    apply e.injective
    simpa only [Algebra.TensorProduct.includeRight_apply, map_zero, he] using h
  · intro h
    rw [← he, h, TensorProduct.tmul_zero, map_zero]

set_option backward.isDefEq.respectTransparency false in
/-- Scalar extension carries the actual fibre-zero locus to its full inverse
image on prime spectra. -/
theorem mem_fiberZeroLocus_baseChange_iff
    {S : Type*} [CommRing S] [Algebra R S] (b : B) (q : PrimeSpectrum S) :
    (1 : q.asIdeal.ResidueField) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] b) = 0 ↔
      (1 : (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField) ⊗ₜ[R] b = 0 := by
  let p := PrimeSpectrum.comap (algebraMap R S) q
  let ψ := Ideal.ResidueField.mapₐ p.asIdeal q.asIdeal (Algebra.ofId R S) rfl
  let : Algebra p.asIdeal.ResidueField q.asIdeal.ResidueField := ψ.toRingHom.toAlgebra
  let : IsScalarTower R p.asIdeal.ResidueField q.asIdeal.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun r => (ψ.commutes r).symm
  let e := Algebra.TensorProduct.cancelBaseChange R S q.asIdeal.ResidueField
    q.asIdeal.ResidueField B
  rw [← e.map_eq_zero_iff]
  simpa [e] using
    (tensor_eq_zero_iff_of_field_extension
      (R := R) (K := p.asIdeal.ResidueField) (L := q.asIdeal.ResidueField) b)

/-- Generic exactness compares zero in the full base-changed algebra with
emptiness of the base change of the annihilator quotient. -/
theorem exists_ne_zero_tensor_eq_zero_iff_subsingleton
    [IsDomain R] [Algebra.FiniteType R B] (b : B) :
    ∃ a : R, a ≠ 0 ∧ ∀ (K : Type w) [CommRing K] [Algebra R K],
      IsUnit (algebraMap R K a) →
        ((1 : K) ⊗ₜ[R] b = 0 ↔ Subsingleton (K ⊗[R] (B ⧸ elementAnnihilator b))) := by
  let Q := B ⧸ Ideal.span ({b} : Set B)
  obtain ⟨a, ha, hflat⟩ :=
    GenericDensity.genFlat_of_finiteType (R := R) Q
  have : Module.Flat R (LocalizedModule (Submonoid.powers a) Q) := hflat a dvd_rfl
  refine ⟨a, ha, fun K _ _ hK => ?_⟩
  have hi := GenericDensity.lTensor_injective_of_localized_cokernel_flat
    (annihilatorMul (R := R) b) (Ideal.Quotient.mkₐ R _).toLinearMap
    (annihilatorMul_injective b) (Ideal.Quotient.mk_surjective)
    (annihilatorMul_exact b) a K hK
  have hmap : (annihilatorMul (R := R) b).lTensor K
      (1 : K ⊗[R] (B ⧸ elementAnnihilator b)) = (1 : K) ⊗ₜ[R] b := by
    change (1 : K) ⊗ₜ[R] annihilatorMul (R := R) b 1 = _
    rw [show (1 : B ⧸ elementAnnihilator b) = Ideal.Quotient.mk _ 1 from rfl,
      annihilatorMul_mk, one_mul]
  constructor
  · intro hb
    apply subsingleton_of_zero_eq_one
    exact (hi (by rw [hmap, hb, map_zero])).symm
  · intro h
    let _ := h
    rw [← hmap, Subsingleton.elim (1 : K ⊗[R] (B ⧸ elementAnnihilator b)) 0, map_zero]

/-- The actual zero locus on residue-field algebras. -/
def fiberZeroLocus (b : B) : Set (PrimeSpectrum R) :=
  {p | (1 : p.asIdeal.ResidueField) ⊗ₜ[R] b = 0}

theorem fiberZeroLocus_baseChange
    {S : Type*} [CommRing S] [Algebra R S] (b : B) :
    fiberZeroLocus (R := S) ((1 : S) ⊗ₜ[R] b) =
      PrimeSpectrum.comap (algebraMap R S) ⁻¹' fiberZeroLocus (R := R) b := by
  ext q
  exact mem_fiberZeroLocus_baseChange_iff b q

/-- A fibre algebra is zero precisely when no prime of the algebra lies over the base prime. -/
theorem subsingleton_fiber_iff_not_mem_range (C : Type v) [CommRing C] [Algebra R C]
    (p : PrimeSpectrum R) :
    Subsingleton (p.asIdeal.Fiber C) ↔
      p ∉ Set.range (PrimeSpectrum.comap (algebraMap R C)) := by
  rw [← PrimeSpectrum.isEmpty_iff_subsingleton]
  constructor
  · intro h ⟨q, hq⟩
    let _ := h
    exact isEmptyElim (PrimeSpectrum.preimageEquivFiber R C p ⟨q, hq⟩)
  · intro h
    exact ⟨fun q => h ⟨(PrimeSpectrum.preimageEquivFiber R C p).symm q |>.1,
      (PrimeSpectrum.preimageEquivFiber R C p).symm q |>.2⟩⟩

/-- Generic flatness and Chevalley give constructibility on a nonempty basic open
of a noetherian domain, without any reducedness assumption on the algebra. -/
theorem exists_ne_zero_isConstructible_inter_basicOpen
    [IsDomain R] [IsNoetherianRing R] [Algebra.FiniteType R B] (b : B) :
    ∃ a : R, a ≠ 0 ∧
      IsConstructible (fiberZeroLocus (R := R) b ∩ (PrimeSpectrum.basicOpen a : Set _)) := by
  obtain ⟨a, ha, h⟩ :=
    exists_ne_zero_tensor_eq_zero_iff_subsingleton.{u,v,u} (R := R) b
  refine ⟨a, ha, ?_⟩
  let C := B ⧸ elementAnnihilator b
  have hC : Algebra.FinitePresentation R C := Algebra.FinitePresentation.of_finiteType.mp
    inferInstance
  have hchev := PrimeSpectrum.isConstructible_range_comap
    (RingHom.finitePresentation_algebraMap.mpr hC)
  have heq : fiberZeroLocus (R := R) b ∩ (PrimeSpectrum.basicOpen a : Set _) =
      (Set.range (PrimeSpectrum.comap (algebraMap R C)))ᶜ ∩
        (PrimeSpectrum.basicOpen a : Set _) := by
    ext p
    by_cases hp : p ∈ (PrimeSpectrum.basicOpen a : Set _)
    · have hunit : IsUnit (algebraMap R p.asIdeal.ResidueField a) :=
        isUnit_iff_ne_zero.mpr fun hz =>
          hp (Ideal.algebraMap_residueField_eq_zero.mp hz)
      simpa only [Set.mem_inter_iff, hp, and_true, Set.mem_compl_iff, fiberZeroLocus,
        Set.mem_ofPred] using
        (h p.asIdeal.ResidueField hunit).trans (subsingleton_fiber_iff_not_mem_range C p)
    · simp only [Set.mem_inter_iff, hp, and_false]
  rw [heq]
  exact hchev.compl.inter PrimeSpectrum.isConstructible_basicOpen

/-- Membership in the actual fibre-zero locus is constant near the generic point
of a noetherian domain. -/
theorem exists_open_generic_constancy
    [IsDomain R] [IsNoetherianRing R] [Algebra.FiniteType R B] (b : B) :
    ∃ U : Set (PrimeSpectrum R), IsOpen U ∧
      (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) ∈ U ∧
        ∀ p ∈ U, (p ∈ fiberZeroLocus (R := R) b ↔
          (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) ∈ fiberZeroLocus (R := R) b) := by
  obtain ⟨a, ha, hc⟩ := exists_ne_zero_isConstructible_inter_basicOpen (R := R) b
  let η : PrimeSpectrum R := ⟨⊥, Ideal.isPrime_bot⟩
  have hη : IsGenericPoint η Set.univ := by
    change closure ({η} : Set (PrimeSpectrum R)) = Set.univ
    rw [PrimeSpectrum.closure_singleton]
    exact PrimeSpectrum.zeroLocus_bot
  obtain ⟨V, hV, hηV, hconst⟩ :=
    Langlands.AlgebraicGeometry.GenericImagePattern.exists_open_constructible_membership hη hc
  have hηa : η ∈ (PrimeSpectrum.basicOpen a : Set _) := by
    change a ∉ (⊥ : Ideal R)
    simpa using ha
  refine ⟨V ∩ (PrimeSpectrum.basicOpen a : Set _),
    hV.inter (PrimeSpectrum.basicOpen a).isOpen, ⟨hηV, hηa⟩, ?_⟩
  intro p hp
  have hc' : (p ∈ fiberZeroLocus (R := R) b ∩ (PrimeSpectrum.basicOpen a : Set _)) ↔
      η ∈ fiberZeroLocus (R := R) b ∩ (PrimeSpectrum.basicOpen a : Set _) :=
    hconst p hp.1
  simpa only [Set.mem_inter_iff, hp.2, hηa, and_true] using hc'

set_option backward.isDefEq.respectTransparency false in
/-- An equation in actual residue-field algebras cuts out a constructible locus
over a noetherian base. -/
theorem isConstructible_fiberZeroLocus
    [IsNoetherianRing R] [Algebra.FiniteType R B] (b : B) :
    IsConstructible (fiberZeroLocus (R := R) b) := by
  classical
  apply Langlands.AlgebraicGeometry.SchemeFiberGeometry.isConstructible_of_irreducibleClosed_genericConstancy
  intro Z hZ hZi
  let I := PrimeSpectrum.vanishingIdeal Z
  let _ : I.IsPrime := PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime.mp hZi
  let A := R ⧸ I
  let C := A ⊗[R] B
  let c : C := (1 : A) ⊗ₜ[R] b
  let f : PrimeSpectrum A → PrimeSpectrum R :=
    PrimeSpectrum.comap (Ideal.Quotient.mk I)
  have hf := PrimeSpectrum.isClosedEmbedding_comap_of_surjective
    A (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hrange : Set.range f = Z := by
    change Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) = Z
    rw [range_comap_of_surjective A _ Ideal.Quotient.mk_surjective,
      Ideal.mk_ker]
    exact (PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure Z).trans hZ.closure_eq
  obtain ⟨U, hU, hηU, hconst⟩ := exists_open_generic_constancy (R := A) c
  obtain ⟨V, hV, hpre⟩ := hf.isEmbedding.isInducing.isOpen_iff.mp hU
  let η : PrimeSpectrum A := ⟨⊥, Ideal.isPrime_bot⟩
  have hmem (q : PrimeSpectrum A) :
      q ∈ fiberZeroLocus (R := A) c ↔ f q ∈ fiberZeroLocus (R := R) b :=
    mem_fiberZeroLocus_baseChange_iff b q
  refine ⟨V, hV, ⟨f η, hrange ▸ Set.mem_range_self η, ?_⟩, ?_⟩
  · change η ∈ f ⁻¹' V
    rwa [hpre]
  · by_cases hηc : η ∈ fiberZeroLocus (R := A) c
    · left
      intro p hp
      obtain ⟨q, rfl⟩ := hrange.symm ▸ hp.1
      have hqU : q ∈ U := by
        rw [← hpre]
        exact hp.2
      exact (hmem q).mp ((hconst q hqU).mpr hηc)
    · right
      apply Set.disjoint_left.mpr
      intro p hp hpb
      obtain ⟨q, rfl⟩ := hrange.symm ▸ hp.1
      have hqU : q ∈ U := by
        rw [← hpre]
        exact hp.2
      exact hηc ((hconst q hqU).mp ((hmem q).mpr hpb))

end Langlands.Algebra.FiberZeroConstructibility
