import Langlands.GroupScheme.Lie.TranslationJordan
import Langlands.GroupScheme.Lie.PrimePowerCentralizer

/-! # Semisimple replacement and centralizer spanning over arbitrary fields -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry Module
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.LinearAlgebra

variable {k : Type u} [Field k] [PerfectField k]
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

@[simp]
theorem jordanSemisimplePart_zero : jordanSemisimplePart (0 : End k V) = 0 := by
  exact jordanSemisimplePart_eq_of_decomposition 0 0 0
    (by exact ⟨1, by simp⟩) Module.End.isSemisimple_zero (Commute.refl 0) (by simp)

/-- The canonical semisimple part kills every vector killed by the original map. -/
theorem jordanSemisimplePart_apply_eq_zero_of_apply_eq_zero
    (f : End k V) {v : V} (hv : f v = 0) : jordanSemisimplePart f v = 0 := by
  let T : k →ₗ[k] V := LinearMap.toSpanSingleton k V v
  have hT : f.comp T = T.comp (0 : End k k) := by
    apply LinearMap.ext
    intro a
    simp [T, hv]
  have h := LinearMap.congr_fun (jordanSemisimplePart_intertwines T hT) 1
  simpa [T] using h

end Langlands.LinearAlgebra

namespace Langlands.GroupScheme.Lie

open Langlands.LinearAlgebra

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    {d : ℕ} (c : FiniteCoordinates G d)

local instance semisimpleJordanCentralizerKernelCommGroup : CommGroup (lieKernel G k) :=
  lieKernelCommGroup G

local instance semisimpleJordanCentralizerKernelModule : Module k (Additive (lieKernel G k)) :=
  lieKernelModule G

section Perfect

variable [PerfectField k]

omit [LocallyOfFiniteType G.X.hom] in
/-- The actual adjoint differential preserves the constructed Jordan component. -/
theorem adjointDifferentialFamily_semisimpleKernel (X : lieKernel G k) :
    adjointDifferentialFamily c (Additive.ofMul (semisimpleKernel G X)) =
      jordanSemisimplePart (adjointDifferentialFamily c (Additive.ofMul X)) := by
  exact MatrixRepresentation.tangentMatrix_semisimpleKernel (adjointRepresentation c) X

include c in
/-- Passing to the actual semisimple component enlarges the tangent centralizer. -/
theorem elementCentralizerLie_le_semisimpleKernel (X : lieKernel G k) :
    elementCentralizerLie G X ≤ elementCentralizerLie G (semisimpleKernel G X) := by
  intro Y hY
  have hzero := (mem_elementCentralizerLie_iff_adjointDifferential_self c X Y.toMul).mp hY
  apply (mem_elementCentralizerLie_iff_adjointDifferential_self c
    (semisimpleKernel G X) Y.toMul).mpr
  rw [adjointDifferentialFamily_semisimpleKernel]
  exact jordanSemisimplePart_apply_eq_zero_of_apply_eq_zero _ hzero

include c in
/-- Every actual Lie element belongs to its semisimple component's centralizer. -/
theorem mem_elementCentralizerLie_semisimpleKernel (X : lieKernel G k) :
    Additive.ofMul X ∈ elementCentralizerLie G (semisimpleKernel G X) :=
  elementCentralizerLie_le_semisimpleKernel c X (mem_elementCentralizerLie_self X)

/-- A nonnilpotent adjoint differential gives a noncentral semisimple component. -/
theorem elementCentralizerLie_semisimpleKernel_ne_top (X : lieKernel G k)
    (hX : ¬ IsNilpotent (adjointDifferentialFamily c (Additive.ofMul X))) :
    elementCentralizerLie G (semisimpleKernel G X) ≠ ⊤ := by
  intro h
  apply hX
  have hz := (elementCentralizerLie_eq_top_iff_adjointDifferential_eq_zero c _).mp h
  rw [adjointDifferentialFamily_semisimpleKernel] at hz
  have hn := (jordanSemisimplePart_properties
    (adjointDifferentialFamily c (Additive.ofMul X))).2.1
  simpa only [jordanNilpotentPart, hz, sub_zero] using hn

/-- Over a perfect field, the actual semisimple component has the centralizer
inclusion and noncentrality needed for spanning. -/
theorem semisimpleKernel_centralizer_properties (X : lieKernel G k)
    (hX : ¬ IsNilpotent (adjointDifferentialFamily c (Additive.ofMul X))) :
    IsSemisimpleElement G (semisimpleKernel G X) ∧
      elementCentralizerLie G (semisimpleKernel G X) ≠ ⊤ ∧
      elementCentralizerLie G X ≤ elementCentralizerLie G (semisimpleKernel G X) :=
  ⟨isSemisimpleElement_semisimpleKernel G X,
    elementCentralizerLie_semisimpleKernel_ne_top c X hX,
    elementCentralizerLie_le_semisimpleKernel c X⟩

/-- Every nonnilpotent adjoint vector lies in a noncentral semisimple tangent
centralizer over the original perfect field. -/
theorem exists_noncentral_semisimple_centralizing_of_not_isNilpotent_perfect
    (X : lieKernel G k)
    (hX : ¬ IsNilpotent (adjointDifferentialFamily c (Additive.ofMul X))) :
    ∃ Y : lieKernel G k, IsSemisimpleElement G Y ∧
      elementCentralizerLie G Y ≠ ⊤ ∧
      Additive.ofMul X ∈ elementCentralizerLie G Y := by
  obtain ⟨hss, hproper, hle⟩ := semisimpleKernel_centralizer_properties c X hX
  exact ⟨semisimpleKernel G X, hss, hproper, hle (mem_elementCentralizerLie_self X)⟩

end Perfect

/-- Over any field, nonnilpotent adjoint vectors are covered by noncentral
semisimple tangent centralizers. -/
theorem exists_noncentral_semisimple_centralizing_of_not_isNilpotent_anyChar
    (X : lieKernel G k)
    (hX : ¬ IsNilpotent (adjointDifferentialFamily c (Additive.ofMul X))) :
    ∃ Y : lieKernel G k, IsSemisimpleElement G Y ∧
      elementCentralizerLie G Y ≠ ⊤ ∧
      Additive.ofMul X ∈ elementCentralizerLie G Y := by
  rcases CharP.exists' k with hzero | ⟨p, hp, hchar⟩
  · let _ : CharZero k := hzero
    exact exists_noncentral_semisimple_centralizing_of_not_isNilpotent_perfect c X hX
  · let _ : Fact p.Prime := hp
    let _ : CharP k p := hchar
    exact exists_noncentral_semisimple_centralizing_of_not_isNilpotent c X p hX

/-- Choose a noncentral semisimple replacement whose tangent centralizer contains
the specified vector on the nonnilpotent adjoint locus, over any field. -/
def noncentralSemisimpleReplacement (X : lieKernel G k)
    (hX : ¬ IsNilpotent (adjointDifferentialFamily c (Additive.ofMul X))) :
    lieKernel G k :=
  (exists_noncentral_semisimple_centralizing_of_not_isNilpotent_anyChar c X hX).choose

theorem noncentralSemisimpleReplacement_properties (X : lieKernel G k)
    (hX : ¬ IsNilpotent (adjointDifferentialFamily c (Additive.ofMul X))) :
    IsSemisimpleElement G (noncentralSemisimpleReplacement c X hX) ∧
      elementCentralizerLie G (noncentralSemisimpleReplacement c X hX) ≠ ⊤ ∧
      Additive.ofMul X ∈ elementCentralizerLie G (noncentralSemisimpleReplacement c X hX) :=
  (exists_noncentral_semisimple_centralizing_of_not_isNilpotent_anyChar c X hX).choose_spec

variable {K : Type u} [Field K] [Algebra k K]

local notation "G_K" => Functor.obj (GroupScheme.baseChange (algebraBaseMap k K)) G

local instance semisimpleJordanCentralizerBaseChangeAffine : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (Limits.pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

include c in
/-- A geometric noncentral semisimple Lie element gives ground-field existence
and full tangent-centralizer spanning over every infinite field. -/
theorem semisimpleCentralizer_spanning_of_geometric_semisimple
    [Infinite k]
    (hgeo : ∃ X : lieKernel G_K K, IsSemisimpleElement G_K X ∧
      elementCentralizerLie G_K X ≠ ⊤) :
    (∃ X : lieKernel G k, IsSemisimpleElement G X ∧
      elementCentralizerLie G X ≠ ⊤) ∧
      noncentralSemisimpleCentralizerSpan G = ⊤ := by
  obtain ⟨⟨X, hX⟩, hspan⟩ :=
    nonnilpotent_adjoint_locus_spans_of_geometric_semisimple c hgeo
  constructor
  · obtain ⟨Y, hY, hproper, _⟩ :=
      exists_noncentral_semisimple_centralizing_of_not_isNilpotent_anyChar c X hX
    exact ⟨Y, hY, hproper⟩
  · apply top_unique
    rw [← hspan]
    apply Submodule.span_le.mpr
    intro x hx
    obtain ⟨Y, hY, hproper, hmem⟩ :=
      exists_noncentral_semisimple_centralizing_of_not_isNilpotent_anyChar c x.toMul hx
    exact elementCentralizerLie_le_noncentralSemisimpleCentralizerSpan G hY hproper hmem

end Langlands.GroupScheme.Lie
