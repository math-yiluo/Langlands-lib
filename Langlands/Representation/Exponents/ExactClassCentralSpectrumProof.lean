import Langlands.Representation.Exponents.ExactClassCentralSpectrumStatement
import Langlands.Representation.Exponents.AdmissibleCentralSubquotientProof
import Langlands.Representation.Exponents.AdmissibleCentralDualToPrimalProof
import Langlands.Representation.Filtration.CentralEigenspaceSplitting
import Langlands.Representation.Filtration.GeneralizedEigencharacterProof
import Langlands.Representation.Smooth.IrreducibleCompositionFactors

/-!
# Central generalized spectrum of equal exact finite-length classes

A generalized eigencharacter of a central action on a finite-length smooth
representation is a scalar character of one actual simple composition factor.
Equal exact classes have the same composition factors with multiplicity, and an
admissible representation detects the generalized eigencharacters of the
central scalars of its actual simple subquotients.
-/

open CategoryTheory

namespace Langlands

universe uG uA uV

namespace ExactClassCentralSpectrumProof

open SmoothRep.IrreducibleGrothendieckProof

/-- On an irreducible representation, a generalized eigencharacter of an action
through central elements is a scalar character: every `ι a` acts by `χ a`. -/
theorem apply_eq_smul_of_isGeneralizedEigencharacter
    {G : Type uG} [Monoid G] {A : Type uA} [Monoid A]
    {V : Type uV} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    (hρ : ρ.IsIrreducible) (ι : A →* G) (hι : ∀ a g, ι a * g = g * ι a)
    (χ : A →* ℂˣ) (h : IsGeneralizedEigencharacter (ρ.comp ι) χ) (a : A) (v : V) :
    ρ (ι a) v = (χ a : ℂ) • v := by
  obtain ⟨k, hk⟩ := h
  obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).mp hk
  have hgen : Module.End.HasGenEigenvalue (ρ (ι a)) (χ a : ℂ) k := by
    rw [Module.End.hasGenEigenvalue_iff, Submodule.ne_bot_iff]
    exact ⟨w, (Submodule.mem_iInf _).mp hw a, hw0⟩
  have heig :
      CentralEigenspaceSplitting.eigenSubrep ρ (ι a) (hι a) (χ a : ℂ) ≠ ⊥ := by
    intro hbot
    apply Module.End.hasEigenvalue_iff.mp
      (Module.End.hasEigenvalue_of_hasGenEigenvalue hgen)
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hx' : x ∈ CentralEigenspaceSplitting.eigenSubrep ρ (ι a) (hι a) (χ a : ℂ) := hx
    rw [hbot] at hx'
    exact CentralEigenspaceSplitting.mem_bot_iff.mp hx'
  have htop := (hρ.eq_bot_or_eq_top _).resolve_left heig
  have hv : v ∈ CentralEigenspaceSplitting.eigenSubrep ρ (ι a) (hι a) (χ a : ℂ) :=
    htop ▸ CentralEigenspaceSplitting.mem_top v
  exact CentralEigenspaceSplitting.mem_eigenSubrep.mp hv

/-- One direction: a central generalized eigencharacter of `R` is one of the
admissible representation `S` with the same exact finite-length class. -/
theorem isGeneralizedEigencharacter_of_ofRepresentation_eq
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (hG : ∀ H : OpenSubgroup G, ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ K ≤ H)
    {A : Type uA} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
    (c : A →* Subgroup.center G) (hc : Continuous c)
    {R S : SmoothRep.{0, uG, uV} ℂ G} (hR : R.HasFiniteLength) (hS : S.HasFiniteLength)
    (hSadm : IsAdmissible S.representation)
    (hRS : SmoothRep.FiniteLengthGrothendieckGroup.ofRepresentation R hR =
      SmoothRep.FiniteLengthGrothendieckGroup.ofRepresentation S hS)
    (χ : A →* ℂˣ)
    (h : IsGeneralizedEigencharacter
      (R.representation.comp ((Subgroup.center G).subtype.comp c)) χ) :
    IsGeneralizedEigencharacter
      (S.representation.comp ((Subgroup.center G).subtype.comp c)) χ := by
  classical
  let ι : A →* G := (Subgroup.center G).subtype.comp c
  have hcentral : ∀ a g, ι a * g = g * ι a := fun a g =>
    (Subgroup.mem_center_iff.mp (c a).2 g).symm
  obtain ⟨n, s, hs⟩ := MultiplicityAdditivityProof.exists_series hR
  obtain ⟨m, t, ht⟩ := MultiplicityAdditivityProof.exists_series hS
  -- The character occurs in one actual simple graded piece of `R`, where it is scalar.
  obtain ⟨i, hi⟩ :=
    RepFunctorFiltration.exists_graded_isGeneralizedEigencharacter s
      (Discrete.mk PUnit.unit) ι χ h
  have hscalar : ∀ a v, (s.gradedRepresentation i).ρ (ι a) v = (χ a : ℂ) • v :=
    apply_eq_smul_of_isGeneralizedEigencharacter (hs i) ι hcentral χ hi
  -- Equal exact classes have equal actual factor counts.
  have hclass := congrArg factorMap hRS
  rw [factorMap_ofRepresentation, factorMap_ofRepresentation,
    compositionFactors_eq_series ⟨R, hR⟩ s hs,
    compositionFactors_eq_series ⟨S, hS⟩ t ht] at hclass
  have hcount : (s.factorMultiplicity (gradedSmooth s i).obj : ℤ) =
      (t.factorMultiplicity (gradedSmooth s i).obj : ℤ) := by
    rw [← seriesClass_apply s hs _ (hs i), ← seriesClass_apply t ht _ (hs i), hclass]
  have hcount' : s.factorMultiplicity (s.gradedRepresentation i) =
      t.factorMultiplicity (s.gradedRepresentation i) :=
    Nat.cast_injective hcount
  have hpos : 0 < t.factorMultiplicity (s.gradedRepresentation i) := by
    rw [← hcount', ObjectRepFiltration.factorMultiplicity]
    have : Nonempty {j : Fin n // Nonempty
        ((s.gradedRepresentation j).ρ.Equiv (s.gradedRepresentation i).ρ)} :=
      ⟨⟨i, ⟨Representation.Equiv.refl _⟩⟩⟩
    exact Nat.card_pos
  rw [ObjectRepFiltration.factorMultiplicity, Nat.card_pos_iff] at hpos
  obtain ⟨⟨j, ⟨e⟩⟩⟩ := hpos.1
  -- The matching simple graded piece of `S` carries the same central scalars.
  have hscalar' : ∀ a v, (t.gradedRepresentation j).ρ (ι a) v = (χ a : ℂ) • v :=
    fun a v => CentralEigenspaceSplitting.apply_eq_smul_of_equiv e (ι a) (χ a : ℂ)
      (hscalar a) v
  obtain ⟨w, hw⟩ := CentralEigenspaceSplitting.exists_ne_zero_of_isIrreducible (ht j)
  have : Nontrivial (t.gradedRepresentation j) := ⟨⟨w, 0, hw⟩⟩
  have hdual := (admissibleCentralSubquotient.{uG, uA, uV, uV} G hG A _ S.representation
    c hc hSadm χ (t.subrepresentation j.succ) (t.gradedRepresentation j)
    (t.gradedProjection j).hom.toLinearMap (t.gradedProjection_surjective j)
    (fun a u => by
      have h1 := LinearMap.congr_fun
        ((t.gradedProjection j).hom.isIntertwining' (c a : G)) u
      rw [LinearMap.comp_apply, LinearMap.comp_apply] at h1
      exact h1.trans (hscalar' a _))).2
  exact admissibleCentralDualToPrimal.{uG, uA, uV} G hG A _ S.representation c hSadm χ hdual

end ExactClassCentralSpectrumProof

/-- Equal actual exact finite-length classes of admissible smooth
representations have the same central generalized eigencharacters. -/
theorem exactClassCentralSpectrum : ExactClassCentralSpectrumStatement.{uG, uA, uV} := by
  intro G _ _ _ hG A _ _ _ c hc R S hR hS hRadm hSadm hRS χ
  exact ⟨ExactClassCentralSpectrumProof.isGeneralizedEigencharacter_of_ofRepresentation_eq
      hG c hc hR hS hSadm hRS χ,
    ExactClassCentralSpectrumProof.isGeneralizedEigencharacter_of_ofRepresentation_eq
      hG c hc hS hR hRadm hRS.symm χ⟩

end Langlands
