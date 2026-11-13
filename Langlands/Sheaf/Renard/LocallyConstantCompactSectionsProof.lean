import Langlands.Sheaf.Renard.CompactOpenSheafCharacterizationStatements
import Langlands.Sheaf.Renard.RegularProjectorSheaf

/-! # The compact-section characterization for locally constant functions -/

set_option autoImplicit false

noncomputable section

open TopologicalSpace

namespace Langlands.Sheaf.Renard

universe u

namespace LocallyConstantCompactSections

open HarmonicAnalysis.PointwiseTestAlgebra ProjectorBasisSheaf

variable {X : Type u} [TopologicalSpace X]
variable (hX : Langlands.Topology.IsLocallyProfinite X)

/-- The additive subgroup of test functions supported in the specified compact open. -/
def supported (U : CompactOpen hX) : AddSubgroup (Carrier X) where
  carrier := {f | Function.support f ⊆ (U.obj : Set X)}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg x hx
    by_contra h
    exact hx (by
      change f x + g x = 0
      rw [Function.notMem_support.mp (fun hx => h (hf hx)),
        Function.notMem_support.mp (fun hx => h (hg hx)), add_zero])
  neg_mem' := by
    intro f hf x hx
    apply hf
    simpa only [Function.mem_support,
      HarmonicAnalysis.PointwiseTestAlgebra.neg_apply, neg_ne_zero] using hx

/-- Extension by zero, using the published compact-open extension of functions. -/
def extend (U : CompactOpen hX) (f : LocallyConstant U.obj ℂ) : supported hX U :=
  ⟨RegularProjectorSheaf.extendTest U f, by
    intro x hx
    by_contra h
    exact hx (RegularProjectorSheaf.extendTest_apply_of_not_mem U f h)⟩

theorem extend_mem (U : CompactOpen hX) (f : LocallyConstant U.obj ℂ)
    (x : X) (hx : x ∈ U.obj) : (extend hX U f).val x = f ⟨x, hx⟩ :=
  RegularProjectorSheaf.extendTest_apply_of_mem U f hx

theorem extend_not_mem (U : CompactOpen hX) (f : LocallyConstant U.obj ℂ)
    (x : X) (hx : x ∉ U.obj) : (extend hX U f).val x = 0 :=
  RegularProjectorSheaf.extendTest_apply_of_not_mem U f hx

/-- Restriction and extension by zero are inverse additive maps. -/
def equiv (U : CompactOpen hX) : LocallyConstant U.obj ℂ ≃+ supported hX U where
  toFun := extend hX U
  invFun f := f.val.val.comap ⟨Subtype.val, continuous_subtype_val⟩
  left_inv f := by
    apply LocallyConstant.ext
    intro x
    exact extend_mem hX U f x.val x.property
  right_inv f := by
    apply Subtype.ext
    apply HarmonicAnalysis.PointwiseTestAlgebra.ext
    intro x
    by_cases hx : x ∈ U.obj
    · exact extend_mem hX U _ x hx
    · rw [extend_not_mem hX U _ x hx]
      exact (Function.notMem_support.mp (fun h => hx (f.property h))).symm
  map_add' f g := by
    apply Subtype.ext
    apply HarmonicAnalysis.PointwiseTestAlgebra.ext
    intro x
    change (extend hX U (f + g)).val x =
      (extend hX U f).val x + (extend hX U g).val x
    by_cases hx : x ∈ U.obj
    · rw [extend_mem hX U _ x hx, extend_mem hX U _ x hx,
        extend_mem hX U _ x hx]
      rfl
    · rw [extend_not_mem hX U _ x hx, extend_not_mem hX U _ x hx,
        extend_not_mem hX U _ x hx, add_zero]

theorem equiv_apply (U : CompactOpen hX) (f : LocallyConstant U.obj ℂ)
    (x : X) (hx : x ∈ U.obj) : (equiv hX U f).val x = f ⟨x, hx⟩ :=
  extend_mem hX U f x hx

theorem equiv_symm_apply (U : CompactOpen hX) (f : supported hX U) (x : U.obj) :
    (equiv hX U).symm f x = f.val x.val := rfl

end LocallyConstantCompactSections

/-- Renard II.2.4, Example: test functions with support in `U` give the required model. -/
theorem locallyConstantCompactSections : LocallyConstantCompactSectionsStatement.{u} := by
  intro X _ hX
  dsimp only
  let S := LocallyConstantCompactSections.supported hX
  let φ := LocallyConstantCompactSections.equiv hX
  refine ⟨S, φ, (fun _ _ => Iff.rfl), ?_, ?_, ?_, ?_, ?_⟩
  · intro U s x hx
    exact LocallyConstantCompactSections.equiv_apply hX U s x hx
  · intro U V h f hf
    change Function.support f ⊆ (U.obj : Set X) at hf
    exact fun x hx => h (hf hx)
  · intro f
    refine ⟨⟨⟨Function.support f, (HarmonicAnalysis.PointwiseTestAlgebra.isClopen_support f).isOpen⟩,
      HarmonicAnalysis.PointwiseTestAlgebra.isCompact_support f⟩, Set.Subset.refl _⟩
  · intro U V hUV y hyU hyV
    apply HarmonicAnalysis.PointwiseTestAlgebra.ext
    intro x
    change (LocallyConstantCompactSections.extend hX U
      (LocallyConstantScalar.restrict ℂ hUV
        ((LocallyConstantCompactSections.equiv hX V).symm ⟨y, hyV⟩))).val x = y x
    by_cases hx : x ∈ U.obj
    · rw [LocallyConstantCompactSections.extend_mem hX U _ x hx]
      rfl
    · rw [LocallyConstantCompactSections.extend_not_mem hX U _ x hx]
      change Function.support y ⊆ (U.obj : Set X) at hyU
      exact (Function.notMem_support.mp (fun h => hx (hyU h))).symm
  · intro U V W hWV _ hW y hyU hyV
    apply LocallyConstant.ext
    intro x
    change y x.val = 0
    have hxW : x.val ∈ (W.obj : Set X) := x.property
    rw [hW] at hxW
    have hxU : x.val ∉ U.obj := hxW.2
    change Function.support y ⊆ (U.obj : Set X) at hyU
    exact Function.notMem_support.mp (fun h => hxU (hyU h))

end Langlands.Sheaf.Renard
