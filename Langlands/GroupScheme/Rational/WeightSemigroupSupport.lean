import Langlands.GroupScheme.Rational.SemigroupClosure
import Langlands.GroupScheme.Rational.WeightSemigroupStatement

/-! # Actual weight support and order of semigroup subgroup functors -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (b : AutomorphicAction S.toGrp G)

/-- Containment of semigroups after restriction to actual ambient action weights.
Characters that do not occur impose no condition. -/
def SemigroupWeightSupportLE
    (A A' : AddSubsemigroup (characterLattice S)) : Prop :=
  ∀ χ ∈ actionWeightSupport b ⊤, χ ∈ A → χ ∈ A'

/-- Ambient action weights are exactly the characters with a nonzero weight space. -/
theorem mem_actionWeightSupport_top {χ : characterLattice S} :
    χ ∈ actionWeightSupport b ⊤ ↔ actionWeightSpace b χ ≠ ⊥ := by
  constructor
  · rintro ⟨X, hX0, hXχ, _⟩ hbot
    exact hX0 (by simpa only [hbot, Submodule.mem_bot] using hXχ)
  · intro hχ
    obtain ⟨X, hXχ, hX0⟩ := (actionWeightSpace b χ).ne_bot_iff.mp hχ
    exact ⟨X, hX0, hXχ, Subgroup.mem_top _⟩

/-- Only ambient weights can obstruct monotonicity of the generated subgroup.
The semigroups may differ arbitrarily away from those actual weights. -/
theorem semigroupSubgroup_mono_on_weightSupport
    {A A' : AddSubsemigroup (characterLattice S)}
    (h : SemigroupWeightSupportLE b A A') :
    semigroupSubgroup b A ≤ semigroupSubgroup b A' := by
  intro T g hg
  apply (Subgroup.closure_le _).mpr ?_ hg
  rintro x ⟨F, hF, hx⟩
  apply generator_le_semigroupSubgroup b A' F ?_ T hx
  refine ⟨hF.1, hF.2.1, ?_⟩
  intro χ hχ
  exact h χ (actionWeightSupport_mono b (fun _ _ _ => Subgroup.mem_top _) hχ)
    (hF.2.2 hχ)

/-- A nonzero ambient A-weight belongs to the subgroup tangent support whenever
its Lie image is the full A-weight span. -/
theorem weightSupport_inter_subset_of_hasLieImage
    {A : AddSubsemigroup (characterLattice S)} {F : SubgroupFunctor G}
    (hF : HasLieImage F (semigroupWeightSpan b A))
    {χ : characterLattice S} (hχ : χ ∈ actionWeightSupport b ⊤) (hχA : χ ∈ A) :
    χ ∈ actionWeightSupport b F := by
  obtain ⟨X, hX0, hXχ, _⟩ := hχ
  refine ⟨X, hX0, hXχ, (hF X).mpr ?_⟩
  exact (le_iSup (fun ψ : A => actionWeightSpace b ψ.val) ⟨χ, hχA⟩) hXχ

/-- Exact Lie image and the target support bound turn all-test subgroup order
into order of the semigroups restricted to actual ambient weights. -/
theorem semigroupSubgroup_le_iff_on_weightSupport
    {A A' : AddSubsemigroup (characterLattice S)}
    (hA : HasLieImage (semigroupSubgroup b A) (semigroupWeightSpan b A))
    (hA' : actionWeightSupport b (semigroupSubgroup b A') ⊆ A') :
    semigroupSubgroup b A ≤ semigroupSubgroup b A' ↔
      SemigroupWeightSupportLE b A A' := by
  constructor
  · intro h χ hχ hχA
    exact hA' (actionWeightSupport_mono b h
      (weightSupport_inter_subset_of_hasLieImage b hA hχ hχA))
  · exact semigroupSubgroup_mono_on_weightSupport b

end Langlands.GroupScheme.RelativeRoot
