import Langlands.Representation.LanglandsClassification.SimpleCorootFaces
import Langlands.GroupScheme.Rational.ReflectionStandardCocharacter
import Mathlib.LinearAlgebra.RootSystem.Finite.Nondegenerate

/-! # Every open simple-coroot face is nonempty -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.LinearAlgebra

/-- A functional takes arbitrary prescribed values on a linearly independent family. -/
theorem exists_dual_apply_eq_of_linearIndepOn {ι K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] {s : Set ι} {v : ι → V} (hli : LinearIndepOn K v s) (c : ι → K) :
    ∃ f : Module.Dual K V, ∀ i ∈ s, f (v i) = c i := by
  classical
  have hinj := hli.injOn
  have hli' : LinearIndepOn K id (v '' s) := LinearIndepOn.id_image hli
  let b : Module.Basis _ K V := .mk (hli'.linearIndepOn_extend (Set.subset_univ _)) <| by
    simpa using hli'.span_extend_eq_span <| Set.subset_univ _
  let g : hli'.extend (Set.subset_univ _) → K := fun w =>
    if h : ∃ i ∈ s, v i = w.1 then c h.choose else 0
  refine ⟨b.constr K g, fun i hi => ?_⟩
  have hi' : v i ∈ hli'.extend (Set.subset_univ _) :=
    hli'.subset_extend _ <| Set.mem_image_of_mem v hi
  let ri : hli'.extend (Set.subset_univ _) := ⟨v i, hi'⟩
  have hb : b ri = v i := by simp [b, ri]
  rw [← hb, Module.Basis.constr_basis]
  have h : ∃ j ∈ s, v j = ri.1 := ⟨i, hi, rfl⟩
  simp only [g, h, ↓reduceDIte]
  have hspec := h.choose_spec
  rw [hinj hspec.1 hi hspec.2]

end Langlands.LinearAlgebra

namespace Langlands.GroupScheme

open RealTorusSpace

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
  (ν : cocharacterLattice T)

/-- The real character attached to a rational character vector. -/
def rationalToRealCharacter :
    ℚ ⊗[ℤ] characterLattice T →ₗ[ℤ] Vstar T :=
  LinearMap.rTensor (characterLattice T) (algebraMap ℚ ℝ).toAddMonoidHom.toIntLinearMap

@[simp] theorem rationalToRealCharacter_tmul (q : ℚ) (χ : characterLattice T) :
    rationalToRealCharacter (T := T) (q ⊗ₜ[ℤ] χ) = ((q : ℝ) ⊗ₜ[ℤ] χ) := rfl

/-- The real pairing of a rationally defined character with an integral
cocharacter is the rational lattice pairing. -/
theorem pair_rationalToRealCharacter (x : ℚ ⊗[ℤ] characterLattice T)
    (μ : cocharacterLattice T) :
    pair T (rationalToRealCharacter x) ((1 : ℝ) ⊗ₜ[ℤ] μ) =
      (((TensorProduct.AlgebraTensorModule.rid ℤ ℚ ℚ).toLinearMap.comp
        (((latticePairing T).flip μ).baseChange ℚ)) x : ℝ) := by
  induction x using TensorProduct.inductionOn with
  | tmul q χ =>
    rw [rationalToRealCharacter_tmul, pair_tmul_tmul]
    simp [mul_comm]
  | add x y hx hy =>
    rw [map_add, map_add, LinearMap.add_apply, hx, hy, map_add, Rat.cast_add]

/-- The coroot functionals of the actual simple roots are linearly independent on
the rational root span. -/
theorem RelativeRootReflectionData.linearIndepOn_simple_corootFunctional
    (D : RelativeRootReflectionData i)
    (hT : IsSplitTorus T.toGrp) (hfinite : (relativeRoots i).Finite)
    (hν : IsGenericCocharacter i ν) :
    LinearIndepOn ℚ
      (fun α : relativeRoots i => RelativeRootSystem.corootFunctional i (D.coroot α))
      {α | α.val ∈ simpleRelativeRoots i ν} := by
  classical
  let := hfinite.fintype
  let P := D.rootPairing hT hfinite
  have : P.IsRootSystem := D.rootPairing_isRootSystem hT hfinite
  have : P.IsCrystallographic := D.rootPairing_isCrystallographic hT hfinite
  let f : relativeRootSpan i →ₗ[ℚ] ℚ := RelativeRootSystem.corootFunctional i ν
  have hfr (α : relativeRoots i) :
      f (P.root α) = (latticePairing T α.val ν : ℚ) :=
    RelativeRootSystem.corootFunctional_rootVector i ν α
  have hf (α : relativeRoots i) : f (P.root α) ≠ 0 := by
    rw [hfr]
    exact_mod_cast hν α.val α.property
  have hbase : {α : relativeRoots i | α.val ∈ simpleRelativeRoots i ν} ⊆
      IsAddIndecomposable.baseOf P.root f.toAddMonoidHom := by
    intro α hα
    refine ⟨?_, fun β hβ γ hγ heq => ?_⟩
    · change 0 < f (P.root α)
      rw [hfr]
      exact_mod_cast hα.1.2
    · exfalso
      apply hα.2
      have hβpos : 0 < latticePairing T β.val ν := by
        change 0 < f (P.root β) at hβ
        rw [hfr] at hβ
        exact_mod_cast hβ
      have hγpos : 0 < latticePairing T γ.val ν := by
        change 0 < f (P.root γ) at hγ
        rw [hfr] at hγ
        exact_mod_cast hγ
      refine ⟨β.val, ⟨β.property, hβpos⟩, γ.val, ⟨γ.property, hγpos⟩, ?_⟩
      apply hT.character_toRat_injective
      rw [map_add]
      exact congrArg Subtype.val heq
  have hli : LinearIndepOn ℚ P.root {α : relativeRoots i | α.val ∈ simpleRelativeRoots i ν} :=
    (P.linearIndepOn_root_baseOf f.toAddMonoidHom hf).mono hbase
  exact P.linearIndepOn_coroot_iff.mpr hli

/-- Every open simple-coroot face of a selected set of simple roots contains a
real character: the simple coroots can be prescribed to vanish on the selected
roots and to equal one on the remaining simple roots. -/
theorem RelativeRootReflectionData.exists_mem_openSimpleCorootFace
    (D : RelativeRootReflectionData i)
    (hT : IsSplitTorus T.toGrp) (hfinite : (relativeRoots i).Finite)
    (hν : IsGenericCocharacter i ν)
    (J : Set (characterLattice T)) (hJ : J ⊆ simpleRelativeRoots i ν) :
    ∃ y : Vstar T, y ∈ openSimpleCorootFace i ν D J := by
  classical
  have : FiniteDimensional ℚ (relativeRootSpan i) :=
    FiniteDimensional.span_of_finite ℚ (hfinite.image toRat)
  obtain ⟨g, hg⟩ := Langlands.LinearAlgebra.exists_dual_apply_eq_of_linearIndepOn
    (D.linearIndepOn_simple_corootFunctional i ν hT hfinite hν)
    (fun α => if α.val ∈ J then 0 else 1)
  let w : relativeRootSpan i := (Module.evalEquiv ℚ (relativeRootSpan i)).symm g
  have hw (α : relativeRoots i) (hα : α.val ∈ simpleRelativeRoots i ν) :
      RelativeRootSystem.corootFunctional i (D.coroot α) w =
        if α.val ∈ J then 0 else 1 := by
    rw [← hg α hα]
    exact Module.apply_evalEquiv_symm_apply ℚ (relativeRootSpan i) _ g
  have hy (α : relativeRoots i) (hα : α.val ∈ simpleRelativeRoots i ν) :
      pair T (rationalToRealCharacter (w : ℚ ⊗[ℤ] characterLattice T))
          ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α) =
        ((if α.val ∈ J then 0 else 1 : ℚ) : ℝ) := by
    rw [pair_rationalToRealCharacter, ← hw α hα]
    rfl
  refine ⟨rationalToRealCharacter (w : ℚ ⊗[ℤ] characterLattice T), fun α hα => ?_,
    fun α hα hαJ => ?_⟩
  · rw [hy α (hJ hα)]
    simp [hα]
  · rw [hy α hα]
    simp [hαJ]

end Langlands.GroupScheme
