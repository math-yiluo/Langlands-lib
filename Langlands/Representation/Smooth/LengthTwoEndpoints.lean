import Langlands.Representation.Smooth.IrreducibleCompositionFactors
import Langlands.Representation.Filtration.RepresentationLength
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

/-! # Object-level deductions for a rank-one Jacquet pattern -/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open Langlands.VirtualRepresentation

namespace Langlands.SmoothRep

universe uR uG uV

variable {k : Type uR} [Field k] {G : Type uG} [Group G] [TopologicalSpace G]

private theorem enat_add_eq_two_of_pos {a b : ℕ∞}
    (h : a + b = 2) (ha : 0 < a) (hb : 0 < b) : a = 1 ∧ b = 1 := by
  have hat : a ≠ ⊤ := by
    intro ht
    simp [ht] at h
  have hbt : b ≠ ⊤ := by
    intro ht
    simp [ht] at h
  lift a to ℕ using hat with a
  lift b to ℕ using hbt with b
  norm_cast at h ha hb ⊢
  omega

/-- Two nonzero endpoints of an actual length-two short exact sequence are
irreducible, without any assumed global preservation of finite length. -/
theorem isIrreducible_endpoints_of_shortExact_length_two
    {A E B : SmoothRep.{uR, uG, uV} k G}
    {f : A.representation.IntertwiningMap E.representation}
    {g : E.representation.IntertwiningMap B.representation}
    (hex : IsShortExact f g) (hE : repLength E.representation = 2)
    (hA : Nontrivial A) (hB : Nontrivial B) : A.IsIrreducible ∧ B.IsIrreducible := by
  have hlen := repLength_eq_add_of_exact f g hex.1 hex.2.1 hex.2.2
  rw [hE] at hlen
  obtain ⟨ha, hb⟩ := enat_add_eq_two_of_pos hlen.symm
    (repLength_pos_iff.mpr hA) (repLength_pos_iff.mpr hB)
  exact ⟨repLength_eq_one_iff.mp ha, repLength_eq_one_iff.mp hb⟩

private theorem generator_pair_eq_iff {α : Type*} (a b c d : α)
    (h : generator a + generator b = generator c + generator d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  classical
  have ha : a = c ∨ a = d := by
    by_contra hn
    have hac : a ≠ c := fun hc => hn (Or.inl hc)
    have had : a ≠ d := fun hd => hn (Or.inr hd)
    have hv := congrArg (fun v : IntegralLattice α => v a) h
    by_cases hba : b = a <;>
      simp [generator, hba, hac, had] at hv
  rcases ha with hac | had
  · left
    refine ⟨hac, ?_⟩
    rw [hac] at h
    exact Finsupp.single_left_injective (one_ne_zero : (1 : ℤ) ≠ 0)
      (add_left_cancel h)
  · right
    refine ⟨had, ?_⟩
    have hbc : generator b = generator c := by
      apply add_left_cancel (a := generator d)
      simpa only [had, add_comm (generator c) (generator d)] using h
    exact Finsupp.single_left_injective (one_ne_zero : (1 : ℤ) ≠ 0) hbc

/-- Two nonzero endpoints of a short exact sequence with the same middle as
a supplied two-simple-factor sequence are those actual simple objects, up to
order. The two supplied simple objects may be isomorphic. -/
theorem endpoints_iso_of_shortExact_two_irreducibles
    {A E B σ τ : SmoothRep.{uR, uG, uV} k G}
    {f : A.representation.IntertwiningMap E.representation}
    {g : E.representation.IntertwiningMap B.representation}
    {i : σ.representation.IntertwiningMap E.representation}
    {p : E.representation.IntertwiningMap τ.representation}
    (hex : IsShortExact f g) (hστ : IsShortExact i p)
    (hσ : σ.IsIrreducible) (hτ : τ.IsIrreducible)
    (hA : Nontrivial A) (hB : Nontrivial B) :
    (Nonempty (A ≅ σ) ∧ Nonempty (B ≅ τ)) ∨
      (Nonempty (A ≅ τ) ∧ Nonempty (B ≅ σ)) := by
  have hE : repLength E.representation = 2 := by
    rw [repLength_eq_add_of_exact i p hστ.1 hστ.2.1 hστ.2.2,
      repLength_eq_one_iff.mpr hσ, repLength_eq_one_iff.mpr hτ]
    norm_num
  obtain ⟨hAi, hBi⟩ :=
    isIrreducible_endpoints_of_shortExact_length_two hex hE hA hB
  have hAf := hasFiniteLength_of_isIrreducible hAi
  have hBf := hasFiniteLength_of_isIrreducible hBi
  have hσf := hasFiniteLength_of_isIrreducible hσ
  have hτf := hasFiniteLength_of_isIrreducible hτ
  have hEf : E.HasFiniteLength := Module.length_ne_top_iff.mp (by
    change repLength E.representation ≠ ⊤
    rw [hE]
    norm_num)
  have hfactors :
      generator (irreducibleIsoClass A hAi) + generator (irreducibleIsoClass B hBi) =
        generator (irreducibleIsoClass σ hσ) + generator (irreducibleIsoClass τ hτ) := by
    open IrreducibleGrothendieckProof in
      calc
        _ = compositionFactors ⟨E, hEf⟩ := by
          rw [compositionFactors_shortExact ⟨A, hAf⟩ ⟨E, hEf⟩ ⟨B, hBf⟩ f g hex,
            compositionFactors_irreducible A hAi hAf,
            compositionFactors_irreducible B hBi hBf]
        _ = _ := by
          rw [compositionFactors_shortExact ⟨σ, hσf⟩ ⟨E, hEf⟩ ⟨τ, hτf⟩ i p hστ,
            compositionFactors_irreducible σ hσ hσf,
            compositionFactors_irreducible τ hτ hτf]
  rcases generator_pair_eq_iff _ _ _ _ hfactors with ⟨hAs, hBt⟩ | ⟨hAt, hBs⟩
  · exact Or.inl ⟨(irreducibleIsoClass_eq_iff hAi hσ).mp hAs,
      (irreducibleIsoClass_eq_iff hBi hτ).mp hBt⟩
  · exact Or.inr ⟨(irreducibleIsoClass_eq_iff hAi hτ).mp hAt,
      (irreducibleIsoClass_eq_iff hBi hσ).mp hBs⟩

/-- Choose actual endpoint isomorphisms and their order from the two actual
short exact sequences. -/
def endpointIsomorphismsOfShortExactTwoIrreducibles
    {A E B σ τ : SmoothRep.{uR, uG, uV} k G}
    {f : A.representation.IntertwiningMap E.representation}
    {g : E.representation.IntertwiningMap B.representation}
    {i : σ.representation.IntertwiningMap E.representation}
    {p : E.representation.IntertwiningMap τ.representation}
    (hex : IsShortExact f g) (hστ : IsShortExact i p)
    (hσ : σ.IsIrreducible) (hτ : τ.IsIrreducible)
    (hA : Nontrivial A) (hB : Nontrivial B) :
    ((A ≅ σ) × (B ≅ τ)) ⊕ ((A ≅ τ) × (B ≅ σ)) :=
  Classical.choice (by
    rcases endpoints_iso_of_shortExact_two_irreducibles hex hστ hσ hτ hA hB with
      ⟨⟨eA⟩, ⟨eB⟩⟩ | ⟨⟨eA⟩, ⟨eB⟩⟩
    · exact ⟨Sum.inl (eA, eB)⟩
    · exact ⟨Sum.inr (eA, eB)⟩)

/-- A smooth object is zero precisely when its actual carrier is a singleton. -/
theorem isZero_iff_subsingleton_carrier (A : SmoothRep.{uR, uG, uV} k G) :
    IsZero A ↔ Subsingleton A := by
  constructor
  · intro h
    refine ⟨fun x y => ?_⟩
    have hx : x = 0 := congrArg (fun f : A ⟶ A => hom f x)
      (h.eq_of_src (𝟙 A) 0)
    have hy : y = 0 := congrArg (fun f : A ⟶ A => hom f y)
      (h.eq_of_src (𝟙 A) 0)
    exact hx.trans hy.symm
  · intro h
    apply (IsZero.iff_id_eq_zero A).mpr
    apply (toRep (R := k) (G := G)).map_injective
    apply Rep.hom_ext
    ext x
    exact h.elim _ _

/-- Actual exactness propagates a zero middle object to both endpoint objects. -/
theorem isZero_endpoints_of_shortExact
    {A E B : SmoothRep.{uR, uG, uV} k G}
    {f : A.representation.IntertwiningMap E.representation}
    {g : E.representation.IntertwiningMap B.representation}
    (hex : IsShortExact f g) (hE : IsZero E) : IsZero A ∧ IsZero B := by
  have hE' := (isZero_iff_subsingleton_carrier E).mp hE
  constructor
  · apply (isZero_iff_subsingleton_carrier A).mpr
    exact ⟨fun a b => hex.1 (hE'.elim _ _)⟩
  · apply (isZero_iff_subsingleton_carrier B).mpr
    refine ⟨fun a b => ?_⟩
    obtain ⟨a', rfl⟩ := hex.2.1 a
    obtain ⟨b', rfl⟩ := hex.2.1 b
    exact congrArg g (hE'.elim a' b')

end Langlands.SmoothRep
