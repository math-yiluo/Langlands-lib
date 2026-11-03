import Langlands.Representation.Classification.LinkedSegmentSocleGluingStatement
import Langlands.Representation.Classification.SegmentSocleCriterionHalvesStatement
import Langlands.Representation.Classification.TwoFactorProductConstituentCommutativityProof
import Langlands.Representation.Classification.LinkedSegmentSocleReverseProductStructureProof
import Langlands.Representation.Filtration.JordanHolderComparisonProof
import Langlands.Representation.Filtration.LengthTwoMatching

/-!
# Proof of the gluing of the forward product of two linked segment socles

The reverse product `⟨Δ⟩ × ⟨Δ'⟩` has the length-two composition series of
Zelevinsky's Proposition 4.6. The forward product `⟨Δ'⟩ × ⟨Δ⟩` has the same
composition factors (Ze80 1.9), so by the Jordan–Hölder comparison its own
composition series has length two with the same two factors.
-/

namespace Langlands

namespace LinkedSegmentSocleGluingProof

open LengthCriterionProof (quotientRep lower)

section Transfer

variable {k : Type*} [Field k] {G : Type*} [Monoid G]
  {V W : Type*} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  {ρ : Representation k G V} {σ : Representation k G W}

/-- A successive quotient whose lower step is zero embeds into the
representation by the inclusion of its upper step. -/
theorem exists_injective_quotientRep_of_eq_bot {S T : Subrepresentation σ} (hS : S = ⊥) :
    ∃ f : (quotientRep S T).IntertwiningMap σ, Function.Injective f := by
  subst hS
  have hle : lower ⊥ T ≤ LinearMap.ker T.toSubmodule.subtype := by
    intro x hx
    rw [LinearMap.mem_ker]
    exact (Submodule.mem_bot k).mp hx
  have hker : LinearMap.ker T.toSubmodule.subtype ≤ lower ⊥ T := by
    intro x hx
    exact (Submodule.mem_bot k).mpr (LinearMap.mem_ker.mp hx)
  let L := (lower ⊥ T).liftQ T.toSubmodule.subtype hle
  refine ⟨{ toLinearMap := L
            isIntertwining' := fun g =>
              Submodule.linearMap_qext _ (LinearMap.ext fun x => rfl) }, ?_⟩
  exact LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot _ _ hle hker)

/-- The bottom graded piece of a filtration embeds into the representation. -/
theorem exists_injective_gradedRepresentation_zero {n : ℕ}
    (u : ObjectRepFiltration (Rep.of σ) (n + 1)) :
    ∃ f : (u.gradedRepresentation 0).ρ.IntertwiningMap σ, Function.Injective f :=
  exists_injective_quotientRep_of_eq_bot (u.subrepresentation_zero)

/-- If `ρ` and `σ` have the same composition factors and `σ` has a composition
series of length two, then `ρ` has a composition series of length two whose
two graded pieces, at distinct positions, are equivalent to the two graded
pieces of the given series of `σ`. -/
theorem exists_lengthTwo_transfer
    (h : HaveSameJordanHolderFactors (Rep.of ρ) (Rep.of σ))
    (u : ObjectRepFiltration (Rep.of σ) 2) (hu : u.HasSimpleFactors) :
    ∃ (s : ObjectRepFiltration (Rep.of ρ) 2) (i j : Fin 2), i ≠ j ∧
      Nonempty ((s.gradedRepresentation i).ρ.Equiv (u.gradedRepresentation 1).ρ) ∧
      Nonempty ((s.gradedRepresentation j).ρ.Equiv (u.gradedRepresentation 0).ρ) := by
  obtain ⟨n, s, t, -, ht, e, he⟩ := h
  obtain ⟨g, hg⟩ := jordanHolderSeriesComparison k G (Rep.of σ) n 2 t u ht hu
  have hn : n = 2 := by simpa using Fintype.card_congr g
  subst hn
  let φ := e.trans g
  have hmatch (a : Fin 2) :
      Nonempty ((s.gradedRepresentation (φ.symm a)).ρ.Equiv (u.gradedRepresentation a).ρ) := by
    obtain ⟨x⟩ := he (φ.symm a)
    obtain ⟨y⟩ := hg (e (φ.symm a))
    have hφ : g (e (φ.symm a)) = a := φ.apply_symm_apply a
    rw [hφ] at y
    exact ⟨x.trans y⟩
  refine ⟨s, φ.symm 1, φ.symm 0, fun hij => ?_, hmatch 1, hmatch 0⟩
  exact absurd (φ.symm.injective hij) (by decide)

end Transfer

end LinkedSegmentSocleGluingProof

namespace PadicField.TopologicalData.Segment

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

/-- Union/intersection replacement does not depend on the order of the pair. -/
theorem IsUnionIntersectionReplacement.comm {Δ Γ U : Segment.{uV, uF} T}
    {I : Option (Segment.{uV, uF} T)} (h : Δ.IsUnionIntersectionReplacement Γ U I) :
    Γ.IsUnionIntersectionReplacement Δ U I := by
  obtain ⟨hU, hI⟩ := h
  refine ⟨hU.trans (Set.union_comm _ _), ?_⟩
  cases I with
  | none => exact (Set.inter_comm _ _).trans hI
  | some J => exact hI.trans (Set.inter_comm _ _)

end PadicField.TopologicalData.Segment

namespace Classification

open CategoryTheory LinkedSegmentSocleGluingProof

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Assembly of the gluing from Ze80 Proposition 4.6 for the reverse product and
the two-factor case of Ze80 1.9. -/
theorem linkedSegmentSocleGluing_of
    (h46 : LinkedSegmentSocleReverseProductStructure.{uF, max uF uV} F T)
    (h19 : TwoFactorProductConstituentCommutativity.{uF, max uF uV} F T) :
    LinkedSegmentSocleGluing.{uF, uV} F T := by
  let := T.topology
  intro n d h₂ hsoc hprec σ
  have hσ0 : σ ⟨0, by change 0 < d.length; omega⟩ = ⟨1, by change 1 < d.length; omega⟩ :=
    Equiv.swap_apply_left _ _
  have hσ1 : σ ⟨1, by change 1 < d.length; omega⟩ = ⟨0, by change 0 < d.length; omega⟩ :=
    Equiv.swap_apply_right _ _
  have hsocσ : (d.permute σ).HasSegmentSocles := fun i => hsoc (σ i)
  have hprecσ : ((d.permute σ).segments ⟨1, by change 1 < d.length; omega⟩).Precedes
      ((d.permute σ).segments ⟨0, by change 0 < d.length; omega⟩) := by
    change (d.segments (σ ⟨1, _⟩)).Precedes (d.segments (σ ⟨0, _⟩))
    rw [hσ0, hσ1]
    exact hprec
  obtain ⟨U, I, e, hrep, hseg, hesoc, -, s', hs', ⟨h1⟩, -, -⟩ :=
    h46 n (d.permute σ) h₂ hsocσ hprecσ
  have hrep' : (d.segments (σ ⟨0, by change 0 < d.length; omega⟩)).IsUnionIntersectionReplacement
      (d.segments (σ ⟨1, by change 1 < d.length; omega⟩)) U I := hrep
  rw [hσ0, hσ1] at hrep'
  have hirr : ∀ i, (d.blocks i).IsIrreducible := fun i => by
    obtain ⟨A, -, hA, -⟩ := hsoc i
    exact hA
  have hJH : HaveSameJordanHolderFactors (Rep.of d.induced.representation)
      (Rep.of (d.permute σ).induced.representation) :=
    h19 n d.shape h₂ d.blocks hirr
  obtain ⟨s, i, j, hij, ⟨a⟩, ⟨b⟩⟩ := exists_lengthTwo_transfer hJH s' hs'
  obtain ⟨f, hf⟩ := exists_injective_gradedRepresentation_zero s'
  refine ⟨U, I, e, hrep'.comm, hseg, hesoc, s, i, j, hij, ⟨a.trans h1⟩,
    f.comp b.toIntertwiningMap, fun x y hxy => b.toLinearEquiv.injective (hf hxy)⟩

/-- The gluing from Ze80 Proposition 4.6 for the reverse product, using the
published proof of the two-factor case of Ze80 1.9. -/
theorem linkedSegmentSocleGluing_of_reverseProductStructure
    (h46 : LinkedSegmentSocleReverseProductStructure.{uF, max uF uV} F T) :
    LinkedSegmentSocleGluing.{uF, uV} F T :=
  linkedSegmentSocleGluing_of F T h46 (twoFactorProductConstituentCommutativity.{uF, max uF uV} F T)

/-- Ze80 4.6 gluing: the forward product `⟨Δ'⟩ × ⟨Δ⟩` of two linked segment
socles has a length-two composition series with the same two factors as the
reverse product. -/
theorem linkedSegmentSocleGluing : LinkedSegmentSocleGluing.{uF, uV} F T :=
  linkedSegmentSocleGluing_of_reverseProductStructure F T
    (linkedSegmentSocleReverseProductStructure.{uF, max uF uV} F T)

end Classification

end Langlands
