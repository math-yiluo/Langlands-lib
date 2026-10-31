import Langlands.Representation.OrbitSpan
import Langlands.Representation.Smooth.SmallRealizationStatement
import Langlands.Representation.Smooth.Transfer.SubquotientProof
import Langlands.Representation.Classification.SupercuspidalContragredientAux
import Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof

/-! Proof that irreducible smooth complex representations of an actual p-adic
general linear group have equivalent realizations in every carrier universe.
The orbit of a nonzero vector is countable and spans, so a basis chosen inside
it is countable and can be reindexed by a type in the prescribed universe. -/

open TopologicalSpace

namespace Langlands

universe uF uG uW uV

section Transport

variable {k : Type*} {G : Type*} {V : Type*} {W : Type*}
variable [CommRing k] [Monoid G] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]

/-- Transport a representation along a linear equivalence of carriers. -/
noncomputable def transportRepresentation (ρ : Representation k G V) (e : V ≃ₗ[k] W) :
    Representation k G W where
  toFun g := e.toLinearMap ∘ₗ ρ g ∘ₗ e.symm.toLinearMap
  map_one' := by
    ext w
    simp
  map_mul' g h := by
    ext w
    simp

/-- The carrier equivalence intertwines a representation with its transport. -/
noncomputable def transportRepresentationEquiv (ρ : Representation k G V) (e : V ≃ₗ[k] W) :
    ρ.Equiv (transportRepresentation ρ e) :=
  Representation.Equiv.mk e fun g => by
    ext v
    simp [transportRepresentation]

end Transport

section Orbit

variable {k : Type*} [Field k] {G : Type uG} [Group G]
  {V : Type uW} [AddCommGroup V] [Module k V]

variable [TopologicalSpace G] [IsTopologicalGroup G] [SeparableSpace G]

/-- Over a separable topological group, the orbit of a smooth vector is countable:
every coset of its open fixing subgroup meets a countable dense set. -/
theorem countable_range_orbit {ρ : Representation k G V} {v : V}
    (hv : IsSmoothVector ρ v) :
    (Set.range fun g : G => ρ g v).Countable := by
  obtain ⟨K, hK⟩ := hv
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense G
  refine (hDc.image fun g : G => ρ g v).mono ?_
  rintro _ ⟨g, rfl⟩
  have hU : IsOpen ((fun h : G => g⁻¹ * h) ⁻¹' (K : Set G)) :=
    K.isOpen.preimage (continuous_const.mul continuous_id)
  obtain ⟨d, hdD, hdU⟩ := hDd.exists_mem_open hU ⟨g, by simp⟩
  refine ⟨d, hdD, ?_⟩
  have hfix : ρ (g⁻¹ * d) v = v :=
    (mem_fixedVectors_iff (ρ := ρ) K.toSubgroup v).mp hK ⟨g⁻¹ * d, hdU⟩
  calc ρ d v = ρ g (ρ (g⁻¹ * d) v) := by
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
    _ = ρ g v := by rw [hfix]

end Orbit

section Realization

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SeparableSpace G]

/-- Over a separable topological group, an irreducible smooth complex
representation has an equivalent irreducible smooth realization with carrier
in any prescribed universe. -/
theorem exists_irreducible_smoothRep_equiv_of_separable
    (π : SmoothRep.{0, uG, uW} ℂ G) (hπ : π.IsIrreducible) :
    ∃ σ : SmoothRep.{0, uG, uV} ℂ G,
      σ.IsIrreducible ∧ Nonempty (π.representation.Equiv σ.representation) := by
  classical
  have hirr : π.representation.IsIrreducible := hπ
  obtain ⟨v, hv⟩ : ∃ v : π, v ≠ 0 := by
    by_contra! h
    apply (bot_ne_top : (⊥ : Subrepresentation π.representation) ≠ ⊤)
    apply Subrepresentation.toSubmodule_injective
    ext w
    change w ∈ (⊥ : Submodule ℂ π) ↔ w ∈ (⊤ : Submodule ℂ π)
    simp [h w]
  let S : Set π := Set.range fun g : G => π.representation g v
  have hSc : S.Countable := countable_range_orbit (π.isSmooth v)
  have hSspan : Submodule.span ℂ S = ⊤ := span_range_orbit_eq_top hirr hv
  obtain ⟨b, hbS, hbspan, hbli⟩ := exists_linearIndependent ℂ S
  have : Countable b := (hSc.mono hbS).to_subtype
  let basis : Module.Basis b ℂ π :=
    Module.Basis.mk hbli (le_of_eq (by rw [Subtype.range_coe, hbspan, hSspan]))
  let e : π ≃ₗ[ℂ] (Shrink.{uV} b →₀ ℂ) :=
    basis.repr.trans (Finsupp.domLCongr (equivShrink.{uV} b))
  let φ := transportRepresentationEquiv π.representation e
  have hsmooth : IsSmooth (transportRepresentation π.representation e) :=
    isSmooth_of_surjective φ.toIntertwiningMap e.surjective π.isSmooth
  refine ⟨SmoothRep.of (transportRepresentation π.representation e) hsmooth, ?_, ⟨φ⟩⟩
  exact (isIrreducible_iff_of_equiv φ).mp hirr

end Realization

/-- The general linear group of an actual p-adic field, with the topology of a
supplied realization, is second countable. -/
theorem PadicField.TopologicalData.generalLinearSecondCountableTopology
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData) (n : ℕ) :
    letI := T.generalLinearTopology n
    SecondCountableTopology (GeneralLinear n F.Carrier) := by
  let := T.topology
  have := T.secondCountableTopology
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) F.Carrier) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → F.Carrier))
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) F.Carrier)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isInducing_embedProduct.secondCountableTopology

/-- Irreducible smooth complex representations of an actual p-adic general
linear group have equivalent irreducible smooth realizations in every carrier
universe. -/
theorem padicIrreducibleSmoothSmallRealization :
    PadicIrreducibleSmoothSmallRealizationStatement.{uF, uW, uV} := by
  intro p _ F T n
  let := T.topology
  intro π hπ
  have : IsTopologicalGroup (GeneralLinear n F.Carrier) :=
    T.generalLinearTopologicalGroup n
  have : SecondCountableTopology (GeneralLinear n F.Carrier) :=
    T.generalLinearSecondCountableTopology n
  exact exists_irreducible_smoothRep_equiv_of_separable.{uF, uW, uV} π hπ

end Langlands
