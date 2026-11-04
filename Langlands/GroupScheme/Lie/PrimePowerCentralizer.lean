import Langlands.GroupScheme.Lie.SemisimplePrimePowerReplacement
import Langlands.GroupScheme.Lie.AdjointDifferentialBaseChange
import Langlands.GroupScheme.Lie.SemisimpleCentralizerPolynomialSpanning

/-! # Centralizers of actual Lie prime powers in positive characteristic -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.Lie

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

local instance primePowerCentralizerKernelCommGroup : CommGroup (lieKernel G k) :=
  lieKernelCommGroup G

local instance primePowerCentralizerKernelModule : Module k (Additive (lieKernel G k)) :=
  lieKernelModule G

/-- Choose one exponent that makes the actual Lie prime power semisimple
simultaneously in every finite algebraic representation. -/
def semisimplePrimePowerExponent (X : lieKernel G k) (p : ℕ)
    [Fact p.Prime] [CharP k p] : ℕ :=
  (exists_isSemisimpleElement_primePowerKernel G X p).choose

/-- The actual ground-field semisimple replacement at the chosen exponent. -/
def semisimplePrimePowerReplacement (X : lieKernel G k) (p : ℕ)
    [Fact p.Prime] [CharP k p] : lieKernel G k :=
  primePowerKernel G X p (semisimplePrimePowerExponent G X p)

theorem isSemisimpleElement_semisimplePrimePowerReplacement
    (X : lieKernel G k) (p : ℕ) [Fact p.Prime] [CharP k p] :
    IsSemisimpleElement G (semisimplePrimePowerReplacement G X p) :=
  (exists_isSemisimpleElement_primePowerKernel G X p).choose_spec

variable {G} {d : ℕ} (c : FiniteCoordinates G d)

omit [LocallyOfFiniteType G.X.hom] in
/-- The actual adjoint differential respects the constructed prime powers. -/
theorem adjointDifferentialFamily_primePowerKernel
    (X : lieKernel G k) (p r : ℕ) [Fact p.Prime] [CharP k p] :
    adjointDifferentialFamily c (Additive.ofMul (primePowerKernel G X p r)) =
      adjointDifferentialFamily c (Additive.ofMul X) ^ (p ^ r) := by
  change Matrix.toLin' ((adjointRepresentation c).tangentMatrix k
    (primePowerKernel G X p r)) =
      Matrix.toLin' ((adjointRepresentation c).tangentMatrix k X) ^ (p ^ r)
  rw [MatrixRepresentation.tangentMatrix_primePowerKernel, Matrix.toLin'_pow]

include c in
/-- Taking a positive prime power can only enlarge the actual tangent
centralizer. -/
theorem elementCentralizerLie_le_primePowerKernel
    (X : lieKernel G k) (p r : ℕ) [Fact p.Prime] [CharP k p] :
    elementCentralizerLie G X ≤ elementCentralizerLie G (primePowerKernel G X p r) := by
  intro Y hY
  have hzero := (mem_elementCentralizerLie_iff_adjointDifferential_self c X Y.toMul).mp hY
  apply (mem_elementCentralizerLie_iff_adjointDifferential_self c
    (primePowerKernel G X p r) Y.toMul).mpr
  rw [adjointDifferentialFamily_primePowerKernel]
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  obtain ⟨a, ha⟩ := Nat.exists_eq_succ_of_ne_zero (pow_ne_zero r hp)
  rw [ha, pow_succ, Module.End.mul_apply, hzero, map_zero]

include c in
/-- Every actual Lie element centralizes its prime powers. -/
theorem mem_elementCentralizerLie_primePowerKernel
    (X : lieKernel G k) (p r : ℕ) [Fact p.Prime] [CharP k p] :
    Additive.ofMul X ∈ elementCentralizerLie G (primePowerKernel G X p r) :=
  elementCentralizerLie_le_primePowerKernel c X p r (mem_elementCentralizerLie_self X)

/-- A nonnilpotent actual adjoint differential prevents any prime power
from having the full tangent centralizer. -/
theorem elementCentralizerLie_primePowerKernel_ne_top
    (X : lieKernel G k) (p r : ℕ) [Fact p.Prime] [CharP k p]
    (hX : ¬ IsNilpotent (adjointDifferentialFamily c (Additive.ofMul X))) :
    elementCentralizerLie G (primePowerKernel G X p r) ≠ ⊤ := by
  intro h
  apply hX
  refine ⟨p ^ r, ?_⟩
  rw [← adjointDifferentialFamily_primePowerKernel c X p r]
  exact (elementCentralizerLie_eq_top_iff_adjointDifferential_eq_zero c _).mp h

/-- The chosen semisimple replacement remains noncentral and its tangent
centralizer contains the original one on the nonnilpotent adjoint locus. -/
theorem semisimplePrimePowerReplacement_properties
    (X : lieKernel G k) (p : ℕ) [Fact p.Prime] [CharP k p]
    (hX : ¬ IsNilpotent (adjointDifferentialFamily c (Additive.ofMul X))) :
    IsSemisimpleElement G (semisimplePrimePowerReplacement G X p) ∧
      elementCentralizerLie G (semisimplePrimePowerReplacement G X p) ≠ ⊤ ∧
      elementCentralizerLie G X ≤
        elementCentralizerLie G (semisimplePrimePowerReplacement G X p) :=
  ⟨isSemisimpleElement_semisimplePrimePowerReplacement G X p,
    elementCentralizerLie_primePowerKernel_ne_top c X p _ hX,
    elementCentralizerLie_le_primePowerKernel c X p _⟩

/-- Every element in the nonnilpotent adjoint locus belongs to a noncentral
semisimple actual tangent centralizer over the original field. -/
theorem exists_noncentral_semisimple_centralizing_of_not_isNilpotent
    (X : lieKernel G k) (p : ℕ) [Fact p.Prime] [CharP k p]
    (hX : ¬ IsNilpotent (adjointDifferentialFamily c (Additive.ofMul X))) :
    ∃ Y : lieKernel G k, IsSemisimpleElement G Y ∧
      elementCentralizerLie G Y ≠ ⊤ ∧
      Additive.ofMul X ∈ elementCentralizerLie G Y := by
  obtain ⟨hss, hproper, hle⟩ := semisimplePrimePowerReplacement_properties c X p hX
  exact ⟨semisimplePrimePowerReplacement G X p, hss, hproper,
    hle (mem_elementCentralizerLie_self X)⟩

variable {K : Type u} [Field K] [Algebra k K]

local notation "G_K" => Functor.obj (GroupScheme.baseChange (algebraBaseMap k K)) G

local instance primePowerCentralizerBaseChangeAffine : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (Limits.pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

include c in
/-- In positive characteristic, a geometric noncentral semisimple Lie
element supplies one over the infinite ground field, and the actual tangent
centralizers of all such elements span the full actual Lie module. -/
theorem semisimpleCentralizer_spanning_of_geometric_semisimple_primeChar
    [Infinite k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (hgeo : ∃ X : lieKernel G_K K, IsSemisimpleElement G_K X ∧
      elementCentralizerLie G_K X ≠ ⊤) :
    (∃ X : lieKernel G k, IsSemisimpleElement G X ∧
      elementCentralizerLie G X ≠ ⊤) ∧
      noncentralSemisimpleCentralizerSpan G = ⊤ := by
  obtain ⟨⟨X, hX⟩, hspan⟩ :=
    nonnilpotent_adjoint_locus_spans_of_geometric_semisimple c hgeo
  constructor
  · obtain ⟨Y, hY, hproper, _⟩ :=
      exists_noncentral_semisimple_centralizing_of_not_isNilpotent c X p hX
    exact ⟨Y, hY, hproper⟩
  · apply top_unique
    rw [← hspan]
    apply Submodule.span_le.mpr
    intro x hx
    obtain ⟨Y, hY, hproper, hmem⟩ :=
      exists_noncentral_semisimple_centralizing_of_not_isNilpotent c x.toMul p hx
    exact elementCentralizerLie_le_noncentralSemisimpleCentralizerSpan G hY hproper hmem

end Langlands.GroupScheme.Lie
