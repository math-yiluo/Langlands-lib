import Langlands.GroupScheme.Rational.LanglandsInvariantForm
import Langlands.GroupScheme.Rational.RelativeSimpleRootBasis
import Langlands.GroupScheme.Rational.ReflectionStandardCocharacter
import Langlands.GroupScheme.Rational.RelativeCharacterRootComplementBaseChange
import Mathlib.RingTheory.Flat.Basic

/-! # A real obtuse basis of the actual relative root span -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open Langlands.LinearAlgebra.RationalSpan Langlands.LinearAlgebra

namespace Langlands.GroupScheme

open RealTorusSpace

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) [IsAffineHom G.X.hom] [Mono i.hom.hom.left]
  (ν : cocharacterLattice T) (D : RelativeRootReflectionData i)

/-- An actual simple relative root in the real root span. -/
def realSimpleRootVector (α : simpleRelativeRoots i ν) : relativeRootSpanReal i :=
  ⟨(1 : ℝ) ⊗ₜ[ℤ] α.val, Submodule.subset_span ⟨α.val, α.property.1.1, rfl⟩⟩

include D in
/-- Simple-root spanning survives real scalar extension. -/
theorem real_span_simpleRelativeRoots (hν : IsGenericCocharacter i ν) :
    Submodule.span ℝ ((fun α : characterLattice T => (1 : ℝ) ⊗ₜ[ℤ] α) ''
      simpleRelativeRoots i ν) = relativeRootSpanReal i := by
  rw [← map_ratSpan_baseChange, ratSpan_simpleRelativeRoots_eq_relativeRootSpan i ν hν
    (fun _ hα => D.neg_mem_relativeRoots i hα), map_relativeRootSpan_baseChange]

include D in
/-- Rational independence survives extension to the actual real character space. -/
theorem RelativeRootReflectionData.linearIndependent_realSimpleRoots
    (hT : IsSplitTorus T.toGrp) (hfinite : (relativeRoots i).Finite)
    (hν : IsGenericCocharacter i ν) :
    LinearIndependent ℝ (fun α : simpleRelativeRoots i ν =>
      (1 : ℝ) ⊗ₜ[ℤ] (α : characterLattice T)) := by
  have h := Module.Flat.linearIndependent_one_tmul (S := ℝ)
    (D.linearIndependent_simpleRelativeRoots i ν hT hfinite hν)
  have h' := h.map' (rationalRealTensorEquiv (characterLattice T)).toLinearMap
    (by simp)
  simpa only [Function.comp_def, LinearEquiv.coe_coe, toRat_apply,
    rationalRealTensorEquiv_tmul, one_smul] using h'

/-- The real basis consisting of the actual simple roots, including the empty case. -/
def realSimpleRootBasis (hT : IsSplitTorus T.toGrp) (hfinite : (relativeRoots i).Finite)
    (hν : IsGenericCocharacter i ν) :
    Module.Basis (simpleRelativeRoots i ν) ℝ (relativeRootSpanReal i) :=
  Module.Basis.mk
    (LinearIndependent.of_comp (v := realSimpleRootVector i ν)
      (relativeRootSpanReal i).subtype
      (D.linearIndependent_realSimpleRoots i ν hT hfinite hν))
    (by
      apply le_of_eq
      symm
      apply (Submodule.span_range_subtype_eq_top_iff _ _).mpr
      have he : Set.range (fun α : simpleRelativeRoots i ν =>
          (1 : ℝ) ⊗ₜ[ℤ] (α : characterLattice T)) =
          (fun α : characterLattice T => (1 : ℝ) ⊗ₜ[ℤ] α) '' simpleRelativeRoots i ν := by
        ext x
        exact ⟨fun ⟨a, ha⟩ => ⟨a.val, a.property, ha⟩,
          fun ⟨a, ha, hx⟩ => ⟨⟨a, ha⟩, hx⟩⟩
      rw [he]
      exact real_span_simpleRelativeRoots i ν D hν)

@[simp] theorem realSimpleRootBasis_apply
    (hT : IsSplitTorus T.toGrp) (hfinite : (relativeRoots i).Finite)
    (hν : IsGenericCocharacter i ν) (α : simpleRelativeRoots i ν) :
    realSimpleRootBasis i ν D hT hfinite hν α = realSimpleRootVector i ν α :=
  Module.Basis.mk_apply _ _ _

/-- Distinct actual simple roots have nonpositive integral Cartan pairings. -/
theorem RelativeRootReflectionData.simple_pairing_nonpos
    (hT : IsSplitTorus T.toGrp) (hfinite : (relativeRoots i).Finite)
    (hν : IsGenericCocharacter i ν) (α β : simpleRelativeRoots i ν) (hne : α ≠ β) :
    latticePairing T α.val (D.coroot ⟨β.val, β.property.1.1⟩) ≤ 0 := by
  classical
  let := hfinite.fintype
  let P := D.rootPairing hT hfinite
  have : P.IsRootSystem := D.rootPairing_isRootSystem hT hfinite
  have : P.IsCrystallographic := D.rootPairing_isCrystallographic hT hfinite
  let f := RelativeRootSystem.corootFunctional i ν
  have hfr (γ : relativeRoots i) :
      f (P.root γ) = (latticePairing T γ.val ν : ℚ) :=
    RelativeRootSystem.corootFunctional_rootVector i ν γ
  have hf (γ : relativeRoots i) : f (P.root γ) ≠ 0 := by
    rw [hfr]
    exact_mod_cast hν γ.val γ.property
  let a : simpleRelativeRoots i ν → relativeRoots i := fun γ => ⟨γ.val, γ.property.1.1⟩
  have hbase (γ : simpleRelativeRoots i ν) :
      a γ ∈ IsAddIndecomposable.baseOf P.root f.toAddMonoidHom := by
    refine ⟨?_, fun δ hδ ε hε heq => ?_⟩
    · change 0 < f (P.root (a γ))
      rw [hfr]
      exact_mod_cast γ.property.1.2
    · exfalso
      apply γ.property.2
      have hδpos : 0 < latticePairing T δ.val ν := by
        change 0 < f (P.root δ) at hδ
        rw [hfr] at hδ
        exact_mod_cast hδ
      have hεpos : 0 < latticePairing T ε.val ν := by
        change 0 < f (P.root ε) at hε
        rw [hfr] at hε
        exact_mod_cast hε
      refine ⟨δ.val, ⟨δ.property, hδpos⟩, ε.val, ⟨ε.property, hεpos⟩, ?_⟩
      apply hT.character_toRat_injective
      rw [map_add]
      exact congrArg Subtype.val heq
  have hab : a α ≠ a β := by
    intro he
    apply hne
    apply Subtype.ext
    exact congrArg (fun x : relativeRoots i => x.val) he
  have h := P.baseOf_pairwise_pairing_le_zero f.toAddMonoidHom hf
    (hbase α) (hbase β) hab
  have he : (P.pairingIn ℤ (a α) (a β) : ℚ) =
      (latticePairing T α.val (D.coroot ⟨β.val, β.property.1.1⟩) : ℚ) := by
    exact (P.algebraMap_pairingIn ℤ (a α) (a β)).trans
      (RelativeRootSystem.corootFunctional_rootVector i _ _)
  exact_mod_cast (show (latticePairing T α.val
    (D.coroot ⟨β.val, β.property.1.1⟩) : ℚ) ≤ 0 by rw [← he]; exact_mod_cast h)

include D in
/-- Every supplied invariant positive form makes distinct simple roots obtuse. -/
theorem RelativeRootReflectionData.simple_form_nonpos
    (hT : IsSplitTorus T.toGrp) (hfinite : (relativeRoots i).Finite)
    (hν : IsGenericCocharacter i ν)
    (B : LinearMap.BilinForm ℝ (Vstar T)) (hB : IsWeylInvariantInnerProduct i B)
    (α β : simpleRelativeRoots i ν) (hne : α ≠ β) :
    B ((1 : ℝ) ⊗ₜ[ℤ] α.val) ((1 : ℝ) ⊗ₜ[ℤ] β.val) ≤ 0 := by
  have h := D.coroot_mul_form i B hB ⟨β.val, β.property.1.1⟩
    ((1 : ℝ) ⊗ₜ[ℤ] α.val)
  have hc : pair T ((1 : ℝ) ⊗ₜ[ℤ] α.val)
      ((1 : ℝ) ⊗ₜ[ℤ] D.coroot ⟨β.val, β.property.1.1⟩) ≤ 0 := by
    rw [pair_tmul_tmul]
    simpa using (Int.cast_nonpos.mpr (D.simple_pairing_nonpos i ν hT hfinite hν α β hne) :
      (latticePairing T α.val (D.coroot ⟨β.val, β.property.1.1⟩) : ℝ) ≤ 0)
  have hn := hB.2.1 ((1 : ℝ) ⊗ₜ[ℤ] β.val)
    (D.one_tmul_ne_zero i ⟨β.val, β.property.1.1⟩)
  have hm := mul_nonpos_of_nonpos_of_nonneg hc hn.le
  linarith

end Langlands.GroupScheme
