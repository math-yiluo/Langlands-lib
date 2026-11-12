import Langlands.Representation.Compact.CompactGroupSmoothStatements
import Langlands.Representation.Compact.Definitions
import Langlands.Representation.CompactCoefficient.SemisimplicityProof
import Langlands.Representation.OrbitSpan
import Mathlib.Analysis.InnerProductSpace.l2Space

/-! # Smooth representations of a compact totally disconnected group -/

noncomputable section
universe u v

namespace Langlands.Renard.CompactRepresentation

open MeasureTheory TopologicalSpace

section Finite

variable {K : Type u} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
  [CompactSpace K] {V : Type v} [AddCommGroup V] [Module ℂ V]

/-- A nonzero orbit spans an irreducible representation, and a smooth compact orbit is finite. -/
theorem finiteDimensional_of_compact_irreducible
    (ρ : Representation ℂ K V) (hs : IsSmooth ρ) (hi : ρ.IsIrreducible) :
    FiniteDimensional ℂ V := by
  let : Nontrivial V := IsSimpleModule.nontrivial (MonoidAlgebra ℂ K) ρ.asModule
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  have horbit := Compact.finite_orbit_of_smooth ρ hs ⊤ isCompact_univ x
  have hf : (Set.range fun g : K => ρ g x).Finite := by
    have hfin : (Set.range fun g : (⊤ : OpenSubgroup K) => ρ g.val x).Finite :=
      Set.finite_coe_iff.mp horbit
    exact hfin.subset (by rintro _ ⟨g, rfl⟩; exact ⟨⟨g, Subgroup.mem_top g⟩, rfl⟩)
  have hfd := FiniteDimensional.span_of_finite ℂ hf
  rw [span_range_orbit_eq_top hi hx] at hfd
  let := hfd
  exact Module.Finite.equiv (Submodule.topEquiv : (⊤ : Submodule ℂ V) ≃ₗ[ℂ] V)

omit [CompactSpace K] in
/-- A finite basis has a common open fixing subgroup contained in the action kernel. -/
theorem exists_openNormal_trivial_of_finiteDimensional
    (ρ : Representation ℂ K V) (hs : IsSmooth ρ) [FiniteDimensional ℂ V] :
    ∃ N : OpenSubgroup K, (N : Subgroup K).Normal ∧
      ∀ n ∈ N, ∀ x : V, ρ n x = x := by
  classical
  let b := Module.finBasis ℂ V
  choose U hU using fun i => hs (b i)
  let L : OpenSubgroup K := OpenSubgroup.iInfOfFinite U
  let N := ρ.asGroupHom.ker
  have hLN : L.toSubgroup ≤ N := by
    intro g hg
    apply Units.ext
    change ρ g = 1
    apply b.ext
    intro i
    have hgi : g ∈ U i := (show L ≤ U i from OpenSubgroup.iInfOfFinite_le U i) hg
    exact hU i ⟨g, hgi⟩
  refine ⟨⟨N, N.isOpen_of_openSubgroup hLN⟩, inferInstance, ?_⟩
  intro n hn x
  have hn' : ρ n = 1 := congrArg Units.val hn
  rw [hn']
  rfl

end Finite

section Form

variable {V : Type v} [AddCommGroup V] [Module ℂ V]

/-- An arbitrary complex vector space has a positive definite Hermitian core. -/
@[instance_reducible]
private def positiveCore : InnerProductSpace.Core ℂ V := by
  classical
  let b := Module.Free.chooseBasis ℂ V
  let f : V →ₗ[ℂ] lp (fun _ : Module.Free.ChooseBasisIndex ℂ V => ℂ) 2 :=
    { toFun := fun x => ⟨(fun i => b.repr x i),
        (memℓp_zero (b.repr x).hasFiniteSupport).of_exponent_ge (by positivity)⟩
      map_add' := fun x y => by apply lp.ext; funext i; exact DFunLike.congr_fun (map_add b.repr x y) i
      map_smul' := fun a x => by apply lp.ext; funext i; exact DFunLike.congr_fun (map_smul b.repr a x) i }
  have hf : Function.Injective f := by
    intro x y h
    apply b.repr.injective
    exact Finsupp.ext fun i => congrArg (fun z => z i) h
  let c : InnerProductSpace.Core ℂ (lp (fun _ : Module.Free.ChooseBasisIndex ℂ V => ℂ) 2) :=
    InnerProductSpace.toCore
  exact
    { inner := fun x y => c.inner (f x) (f y)
      conj_inner_symm := fun x y => c.conj_inner_symm (f x) (f y)
      re_inner_nonneg := fun x => c.re_inner_nonneg (f x)
      add_left := fun x y z => by rw [map_add, c.add_left]
      smul_left := fun x y a => by rw [map_smul, c.smul_left]
      definite := fun x hx => hf (by rw [map_zero]; exact c.definite (f x) hx) }

variable {K : Type u} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
  [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (μ : Measure K) [μ.IsHaarMeasure]
  (ρ : Representation ℂ K V) (hs : IsSmooth ρ) (b : InnerProductSpace.Core ℂ V)

omit [CompactSpace K] [MeasurableSpace K] [BorelSpace K] in
include hs in
private theorem pairing_locallyConstant (x y : V) :
    IsLocallyConstant (fun g : K => b.inner (ρ g⁻¹ x) (ρ g⁻¹ y)) :=
  ((Hecke.orbitMap_locallyConstant ρ (hs x)).comp_continuous continuous_inv).comp₂
    ((Hecke.orbitMap_locallyConstant ρ (hs y)).comp_continuous continuous_inv) b.inner

include hs in
private theorem pairing_integrable (x y : V) :
    Integrable (fun g : K => b.inner (ρ g⁻¹ x) (ρ g⁻¹ y)) μ :=
  (pairing_locallyConstant ρ hs b x y).continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Average a positive definite core on inverse orbits, using only left Haar invariance. -/
private def averagedPositiveForm : InvariantPositiveForm ρ where
  inner x y := ∫ g : K, b.inner (ρ g⁻¹ x) (ρ g⁻¹ y) ∂μ
  conj_inner_symm x y := by
    rw [← integral_conj]
    exact integral_congr_ae (Filter.Eventually.of_forall fun g => b.conj_inner_symm _ _)
  re_inner_nonneg x := by
    rw [← integral_re (pairing_integrable μ ρ hs b x x)]
    exact integral_nonneg fun g => b.re_inner_nonneg _
  add_left x y z := by
    simp_rw [map_add, b.add_left]
    exact integral_add (pairing_integrable μ ρ hs b x z) (pairing_integrable μ ρ hs b y z)
  smul_left x y a := by
    simp_rw [map_smul, b.smul_left]
    exact integral_const_mul _ _
  definite x hx := by
    let : InnerProductSpace.Core ℂ V := b
    have hz : (∫ g : K, RCLike.re (b.inner (ρ g⁻¹ x) (ρ g⁻¹ x)) ∂μ) = 0 := by
      rw [integral_re (pairing_integrable μ ρ hs b x x), hx]
      rfl
    have hae : (fun g : K => RCLike.re (b.inner (ρ g⁻¹ x) (ρ g⁻¹ x))) =ᵐ[μ] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun g => b.re_inner_nonneg _)
        (pairing_integrable μ ρ hs b x x).re).mp hz
    have heq := Measure.eq_of_ae_eq hae
      ((pairing_locallyConstant ρ hs b x x).comp RCLike.re).continuous continuous_const
    have h1 := congrFun heq 1
    have hnorm : InnerProductSpace.Core.normSq (𝕜 := ℂ) x = 0 := by
      simpa [InnerProductSpace.Core.normSq] using h1
    exact (InnerProductSpace.Core.normSq_eq_zero (𝕜 := ℂ)).mp hnorm
  invariant h x y := by
    simpa only [mul_inv_rev, inv_inv, map_mul, Module.End.mul_apply] using
      (integral_mul_left_eq_self (μ := μ)
        (fun g : K => b.inner (ρ g⁻¹ x) (ρ g⁻¹ y)) h⁻¹)

end Form

/-- Renard IV.1.1, Theorem, with all four assertions and the published hypotheses. -/
theorem compactGroupSmoothRepresentation : CompactGroupSmoothRepresentationStatement.{u, v} := by
  intro K _ _ _ _ _ _ π
  let : MeasurableSpace K := borel K
  let : BorelSpace K := ⟨rfl⟩
  let μ : Measure K := Measure.haarMeasure (⊤ : PositiveCompacts K)
  refine ⟨finiteDimensional_of_compact_irreducible π.representation π.isSmooth, ?_, ?_, ?_⟩
  · intro hfin
    let := hfin
    exact exists_openNormal_trivial_of_finiteDimensional π.representation π.isSmooth
  · apply (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule _).mp
    exact CompactCoefficientSemisimplicity.isSemisimpleRepresentation_of_compactCoefficients
      μ π.representation π.isSmooth (fun x ℓ hℓ => HasCompactSupport.of_compactSpace _)
  · exact ⟨averagedPositiveForm μ π.representation π.isSmooth positiveCore⟩

end Langlands.Renard.CompactRepresentation
