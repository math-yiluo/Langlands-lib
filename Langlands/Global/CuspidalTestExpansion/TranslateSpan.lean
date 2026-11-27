import Langlands.Global.CuspidalTestExpansion.GeneralizedEigenComponents
import Langlands.Global.AdelicLeadingExponentDirectness
import Langlands.Global.AdelicEisensteinPositiveParametersProof

/-! # Exponent components as combinations of positive split translates -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme Langlands.Global.AdelicGroupPoints Langlands.HarishChandraSchwartz

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G) (J : StandardIndex F G fam.i fam.ν)

local instance translateSpanSplitCommGroup : CommGroup (fam.positiveSplitComponent J) where
  toGroup := inferInstance
  mul_comm x y :=
    Subtype.ext (fam.positiveSplitComponent_mul_comm J x.property y.property)

/-- The complex span of the left translates `g ↦ f(a g)` of `f` by the positive split
component of `P_J`. -/
def translateSpan (f : AdelicGroupPoints F G → ℂ) : Submodule ℂ (AdelicGroupPoints F G → ℂ) :=
  Submodule.span ℂ (Set.range fun b : fam.positiveSplitComponent J =>
    fam.splitComponentRepresentation J b f)

theorem self_mem_translateSpan (f : AdelicGroupPoints F G → ℂ) : f ∈ fam.translateSpan J f := by
  refine Submodule.subset_span ⟨1, ?_⟩
  simp

/-- The span of the translates is stable under positive split translation. -/
theorem splitComponentRepresentation_mem_translateSpan (f : AdelicGroupPoints F G → ℂ)
    (b : fam.positiveSplitComponent J) {x : AdelicGroupPoints F G → ℂ}
    (hx : x ∈ fam.translateSpan J f) :
    fam.splitComponentRepresentation J b x ∈ fam.translateSpan J f := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b', rfl⟩ := hy
    refine Submodule.subset_span ⟨b * b', ?_⟩
    change fam.splitComponentRepresentation J (b * b') f =
      fam.splitComponentRepresentation J b (fam.splitComponentRepresentation J b' f)
    rw [map_mul, Module.End.mul_apply]
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul a y _ hy => rw [map_smul]; exact Submodule.smul_mem _ a hy

set_option maxHeartbeats 1000000 in
/-- In a finite sum of functions with distinct unnormalized exponents along `J`, every summand is
a finite combination of positive split translates of the sum. -/
theorem mem_translateSpan_of_sum (s : Finset (ComplexCharacterParameter F (fam.P J)))
    (c : ComplexCharacterParameter F (fam.P J) → AdelicGroupPoints F G → ℂ)
    (hc : ∀ lam ∈ s, fam.HasUnnormalizedExponent J lam (c lam)) :
    ∀ lam ∈ s, c lam ∈ fam.translateSpan J (∑ lam ∈ s, c lam) := by
  classical
  let r : ParabolicRootPresentation (fam.p J) (fam.l J) (fam.a J) :=
    ⟨⟨fam.T, fam.i, fam.ν, J.val, fam.f J⟩, fam.isCompatible J⟩
  have hinj : Function.Injective (fun lam : ComplexCharacterParameter F (fam.P J) =>
      fun x : fam.positiveSplitComponent J => parameterPower F (fam.P J) lam x.val) :=
    (eisensteinPositiveParameters F G (fam.P J) (fam.M J) (fam.A J) (fam.p J)
      (fam.l J) (fam.a J) r).2
  let χ : ComplexCharacterParameter F (fam.P J) → fam.positiveSplitComponent J → ℂ :=
    fun lam b => parameterPower F (fam.P J) lam b.val
  have hχ : ∀ i ∈ s, ∀ j ∈ s, χ i = χ j → i = j := fun i _ j _ h => hinj h
  have hgen : ∀ lam ∈ s, ∀ b : fam.positiveSplitComponent J, ∃ k : ℕ,
      ((fam.splitComponentRepresentation J b -
        χ lam b • (1 : Module.End ℂ (AdelicGroupPoints F G → ℂ))) ^ k) (c lam) = 0 := by
    intro lam hlam b
    have hmem := fam.mem_jointGenEigenspace_of_hasUnnormalizedExponent J (hc lam hlam)
    rw [mem_jointGenEigenspace] at hmem
    exact hmem b
  have hW : ∀ b : fam.positiveSplitComponent J, ∀ x ∈ fam.translateSpan J (∑ lam ∈ s, c lam),
      fam.splitComponentRepresentation J b x ∈ fam.translateSpan J (∑ lam ∈ s, c lam) :=
    fun b x hx => fam.splitComponentRepresentation_mem_translateSpan J _ b hx
  exact GeneralizedEigenComponents.mem_of_sum_mem
    (fun b => fam.splitComponentRepresentation J b)
    (commute_jointFamily (fam.splitComponentRepresentation J)) χ _ hW s hχ c hgen
    (fam.self_mem_translateSpan J _)

end Langlands.Global.StandardParabolicFamily
