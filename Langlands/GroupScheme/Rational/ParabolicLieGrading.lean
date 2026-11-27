import Langlands.GroupScheme.Lie.CocharacterGrading
import Langlands.GroupScheme.Rational.OriginalLeviCocharacter
import Langlands.GroupScheme.Rational.LeviSubgroup
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Dynamic.RingLieProof
import Langlands.GroupScheme.Rational.RootAnnihilatorCentralityReduction
import Langlands.GroupScheme.ClosedSubgroupMonomorphism
import Langlands.GroupScheme.Dynamic.RingWeightLift

/-! # The tangent grading of a rational parabolic subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Lie

open scoped FieldLie

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
/-- **The tangent grading of a rational parabolic.** For a connected reductive group over a
field of characteristic zero with a parabolic subgroup `q`, its geometric unipotent radical `iV`
and a rational Levi subgroup `l`, there is a tangent vector `H₀` whose integral eigenvectors span
the Lie algebra, such that the tangent map of the Levi is injective with image the centralizer
of `H₀`, and the tangent image of the radical is spanned by the eigenvectors with positive
integral eigenvalues. -/
theorem exists_parabolicLieGrading [CharZero k]
    {G Q M V : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom M.X.hom] [IsAffineHom V.X.hom]
    (q : Q ⟶ G) (iV : V ⟶ Q) (l : M ⟶ Q) (hG : IsConnectedReductive G)
    (hq : IsParabolicSubgroup q) (hV : LeviSubgroup.IsGeometricUnipotentRadical iV)
    (hl : IsRationalLeviSubgroup l) :
    letI : IsAffineHom G.X.hom := hG.isAffineHom
    ∃ H₀ : Additive (lieKernel G k),
      Submodule.span k {Y : Additive (lieKernel G k) | ∃ n : ℤ, ⁅H₀, Y⁆ = (n : k) • Y} = ⊤ ∧
      Function.Injective (targetMapLinear (l ≫ q) k) ∧
      (∀ Y, Y ∈ LinearMap.range (targetMapLinear (l ≫ q) k) ↔ ⁅H₀, Y⁆ = 0) ∧
      LinearMap.range (targetMapLinear (iV ≫ q) k) =
        Submodule.span k {Y : Additive (lieKernel G k) | ∃ n : ℕ, ⁅H₀, Y⁆ = ((n + 1 : ℕ) : k) • Y} := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  have : Smooth G.X.hom := hG.smooth
  obtain ⟨χ, hχ⟩ := (parabolicDynamic k G hG Q q hq.isClosedSubgroup).mp hq
  have hP : (Dynamic.parabolic χ).IsRepresentedBy q := ⟨hq.isClosedSubgroup.mono_overHom, hχ⟩
  obtain ⟨ψ, -, hψ⟩ := hl.exists_centralCocharacter_of_dynamicParabolic hG χ hP
  have hZ : Dynamic.centralizer (ψ ≫ l ≫ q) = SubgroupFunctor.range (l ≫ q) :=
    hl.centralizer_eq_of_dynamicParabolic hG ψ hψ
  have hU : SubgroupFunctor.range (iV ≫ q) = Dynamic.unipotent (ψ ≫ l ≫ q) :=
    Dynamic.range_comp_radical_eq_unipotent_of_reductive hG (ψ ≫ l ≫ q) q hψ iV hV.1
  have : Mono l.hom.hom := hl.isClosedSubgroup.mono_overHom
  have : Mono q.hom.hom := hq.isClosedSubgroup.mono_overHom
  have : Mono iV.hom.hom := hV.1.isClosedSubgroup.mono_overHom
  have hlq : Mono (l ≫ q).hom.hom := by
    rw [Grp.comp_hom_hom]
    infer_instance
  have hvq : Mono (iV ≫ q).hom.hom := by
    rw [Grp.comp_hom_hom]
    infer_instance
  have hRL := dynamicRingLie k G (ψ ≫ l ≫ q)
  set H₀ := cocharacterLieVector (ψ ≫ l ≫ q) with hH₀
  have hW (n : ℤ) (Y : Additive (lieKernel G k)) :=
    mem_weightSpace_powerHom_iff (ψ ≫ l ≫ q) n Y
  refine ⟨H₀, ?_, targetMapLinear_injective (l ≫ q) k, ?_, ?_⟩
  · rw [eq_top_iff]
    intro Y _
    have hY : Y ∈ ⨆ m : ℤ,
        weightSpace (ψ ≫ l ≫ q) (Gm.powerHom (Spec (CommRingCat.of k)) m) := by
      rw [iSup_weightSpace_powerHom_eq_top]
      exact Submodule.mem_top
    refine Submodule.iSup_induction _
      (motive := fun x => x ∈ Submodule.span k {Y : Additive (lieKernel G k) | ∃ n : ℤ, ⁅H₀, Y⁆ = (n : k) • Y}) hY ?_ ?_ ?_
    · exact fun m x hx => Submodule.subset_span ⟨m, (hW m x).mp hx⟩
    · exact Submodule.zero_mem _
    · exact fun x y hx hy => Submodule.add_mem _ hx hy
  · intro Y
    rw [mem_range_targetMapLinear_iff ⟨hlq, rfl⟩, ← hZ, (hRL Y.toMul).1]
    have := hW 0 Y
    rw [Int.cast_zero, zero_smul] at this
    exact this
  · ext Y
    rw [mem_range_targetMapLinear_iff ⟨hvq, rfl⟩, hU, (hRL Y.toMul).2.2]
    constructor
    · intro hY
      refine Submodule.iSup_induction _
        (motive := fun x => x ∈ Submodule.span k
          {Y : Additive (lieKernel G k) | ∃ n : ℕ, ⁅H₀, Y⁆ = ((n + 1 : ℕ) : k) • Y}) hY ?_ ?_ ?_
      · intro m x hx
        refine Submodule.subset_span ⟨m, ?_⟩
        have := (hW ((m : ℤ) + 1) x).mp hx
        rw [this]
        push_cast
        rfl
      · exact Submodule.zero_mem _
      · exact fun x y hx hy => Submodule.add_mem _ hx hy
    · intro hY
      induction hY using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨m, hm⟩ := hx
        refine Submodule.mem_iSup_of_mem m ?_
        refine (hW ((m : ℤ) + 1) x).mpr ?_
        rw [hm]
        push_cast
        rfl
      | zero => exact Submodule.zero_mem _
      | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
      | smul c x _ hx => exact Submodule.smul_mem _ c hx

end Langlands.GroupScheme.Lie
