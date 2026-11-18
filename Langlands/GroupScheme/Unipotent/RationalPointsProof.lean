import Langlands.GroupScheme.Unipotent.RationalPointsStatement
import Langlands.GroupScheme.Unipotent.RationalFixedVector
import Langlands.GroupScheme.Chevalley.ReindexRepresentation
import Langlands.GroupScheme.Rational.UnipotentProductBound
import Langlands.LinearAlgebra.IrreducibleRepresentationSpan
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Trace
import Mathlib.RingTheory.Artinian.Module

/-! # Unipotence from schematically dense rational points -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme

private theorem irreducible_of_atom {K : Type u} [Field K] {H : Type v} [Monoid H]
    {V : Type w} [AddCommGroup V] [Module K V] {r : Representation K H V}
    {W : Subrepresentation r} (hW : IsAtom W) :
    Representation.IsIrreducible W.toRepresentation := by
  have : Nontrivial W.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr
    (fun h => hW.ne_bot (Subrepresentation.toSubmodule_injective h))
  have : Nontrivial (Subrepresentation W.toRepresentation) :=
    ⟨⟨⊥, ⊤, fun h => bot_ne_top (congrArg Subrepresentation.toSubmodule h)⟩⟩
  apply IsSimpleOrder.of_forall_eq_top
  intro U hU
  let I : Subrepresentation r :=
    ⟨U.toSubmodule.map W.toSubmodule.subtype, by
      intro g _ hv
      obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hv
      exact Submodule.mem_map.mpr ⟨W.toRepresentation g x, U.apply_mem_toSubmodule g hx, rfl⟩⟩
  have hinj := Submodule.map_injective_of_injective W.toSubmodule.subtype_injective
  have hI : I ≠ ⊥ := by
    intro h
    apply hU
    apply Subrepresentation.toSubmodule_injective
    apply hinj
    change I.toSubmodule = Submodule.map W.toSubmodule.subtype ⊥
    rw [Submodule.map_bot]
    exact congrArg Subrepresentation.toSubmodule h
  have hle : I ≤ W := by
    intro _ hx
    obtain ⟨x, _, rfl⟩ := Submodule.mem_map.mp hx
    exact x.property
  have heq : I = W := (hW.le_iff_eq hI).mp hle
  apply Subrepresentation.toSubmodule_injective
  apply hinj
  change I.toSubmodule = Submodule.map W.toSubmodule.subtype ⊤
  rw [Submodule.map_top, Submodule.range_subtype]
  exact congrArg Subrepresentation.toSubmodule heq

private theorem eq_one_of_irreducible_unipotent {K : Type u} [Field K] [IsAlgClosed K]
    {H : Type v} [Monoid H] {V : Type w} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (r : Representation K H V) [Representation.IsIrreducible r]
    (hnil : ∀ h, IsNilpotent (r h - 1)) (g : H) : r g = 1 := by
  classical
  have htrace (h : H) : LinearMap.trace K V (r h) = LinearMap.trace K V 1 := by
    have hzero := (LinearMap.isNilpotent_trace_of_isNilpotent (hnil h)).eq_zero
    rwa [map_sub, sub_eq_zero] at hzero
  let t := (LinearMap.trace K V).comp (LinearMap.mulLeft K (r g - 1))
  have hker : Submodule.span K (Set.range r) ≤ LinearMap.ker t := by
    apply Submodule.span_le.mpr
    rintro _ ⟨h, rfl⟩
    change LinearMap.trace K V ((r g - 1) * r h) = 0
    rw [sub_mul, one_mul, ← map_mul, map_sub, htrace, htrace, sub_self]
  have hzero (f : Module.End K V) : LinearMap.trace K V ((r g - 1) * f) = 0 :=
    hker (by rw [Langlands.LinearAlgebra.irreducibleRepresentationSpan_proof
      K H V r inferInstance]; exact Submodule.mem_top)
  let b := Module.Free.chooseBasis K V
  let e := LinearMap.toMatrixAlgEquiv b
  apply e.injective
  rw [map_one]
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro B
  have h := hzero (e.symm B)
  rw [LinearMap.trace_eq_matrix_trace K b] at h
  change (e ((r g - 1) * e.symm B)).trace = 0 at h
  rw [map_mul, map_sub, map_one, e.apply_symm_apply, sub_mul, one_mul,
    Matrix.trace_sub, sub_eq_zero] at h
  simpa only [one_mul] using h

private theorem exists_fixed_of_unipotent_representation
    {K : Type u} [Field K] [IsAlgClosed K] {H : Type v} [Monoid H]
    {V : Type w} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Nontrivial V]
    (r : Representation K H V) (hnil : ∀ h, IsNilpotent (r h - 1)) :
    ∃ x : V, x ≠ 0 ∧ ∀ h, r h x = x := by
  let emb : Subrepresentation r ↪o Submodule K V :=
    ⟨⟨Subrepresentation.toSubmodule, Subrepresentation.toSubmodule_injective⟩, Iff.rfl⟩
  have : WellFoundedLT (Subrepresentation r) := emb.wellFoundedLT
  have htop : (⊤ : Subrepresentation r) ≠ ⊥ :=
    fun h => top_ne_bot (congrArg Subrepresentation.toSubmodule h)
  obtain ⟨W, hW, _⟩ := (eq_bot_or_exists_atom_le (⊤ : Subrepresentation r)).resolve_left htop
  have : Representation.IsIrreducible W.toRepresentation := irreducible_of_atom hW
  have hnilW (h : H) : IsNilpotent (W.toRepresentation h - 1) := by
    obtain ⟨m, hm⟩ := hnil h
    refine ⟨m, Module.End.submodule_pow_eq_zero_of_pow_eq_zero ?_ hm⟩
    ext x
    rfl
  have hW' : W.toSubmodule ≠ ⊥ := fun h =>
    hW.ne_bot (Subrepresentation.toSubmodule_injective h)
  obtain ⟨x, hx, hx0⟩ := W.toSubmodule.ne_bot_iff.mp hW'
  refine ⟨x, hx0, fun h => ?_⟩
  have heq := eq_one_of_irreducible_unipotent W.toRepresentation hnilW h
  exact congrArg (fun f : Module.End K W.toSubmodule => (f ⟨x, hx⟩ : V)) heq

private theorem exists_fixed_of_unipotent_matrices {k : Type u} [Field k]
    {H : Type v} [Monoid H] {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
    (r : H →* GL n k) (hnil : ∀ h, IsNilpotent ((r h : Matrix n n k) - 1)) :
    ∃ x : n → k, x ≠ 0 ∧ ∀ h, (r h : Matrix n n k) *ᵥ x = x := by
  classical
  let K := AlgebraicClosure k
  let rK := (Matrix.GeneralLinearGroup.map (algebraMap k K)).comp r
  let a := Langlands.LinearAlgebra.matrixAction rK
  have hnilK (h : H) : IsNilpotent (a h - 1) := by
    let f : Matrix n n k →+* Module.End K (n → K) :=
      Matrix.toLinAlgEquiv'.toAlgHom.toRingHom.comp (algebraMap k K).mapMatrix
    have hn := (hnil h).map f
    rw [map_sub, map_one] at hn
    exact hn
  obtain ⟨y, hy, hfix⟩ := exists_fixed_of_unipotent_representation a hnilK
  obtain ⟨i, hi⟩ : ∃ i, y i ≠ 0 := by
    by_contra! hz
    exact hy (funext hz)
  obtain ⟨ell, hell⟩ := Module.Projective.exists_dual_ne_zero k hi
  refine ⟨fun j => ell (y j), ?_, fun h => ?_⟩
  · intro heq
    exact hell (congrFun heq i)
  · funext j
    have heq := congrArg (fun z : n → K => ell (z j)) (hfix h)
    simp only [a, Langlands.LinearAlgebra.matrixAction_apply, Matrix.mulVec,
      dotProduct, map_sum] at heq
    simpa only [rK, MonoidHom.comp_apply, Matrix.GeneralLinearGroup.map_apply,
      ← Algebra.smul_def, map_smul, smul_eq_mul, Matrix.mulVec, dotProduct] using heq

private theorem rationalMatrix_sub_one_nilpotent {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsUnipotent G)
    {n : Type} [Fintype n] [DecidableEq n] (ρ : MatrixRepresentation G n)
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :
    IsNilpotent ((ρ.rationalMatrix g : Matrix n n k) - 1) := by
  let R := CommRingCat.of k
  let T := Over.mk (𝟙 (Spec R))
  let e := Fintype.equivFin n
  let E := Matrix.reindexRingEquiv Γ(T.left, ⊤) e
  have hp := MatrixRepresentation.pointMatrix_sub_one_pow_eq_zero_of_isUnipotent
    hG (Chevalley.reindexRepresentation e R ρ) T g
  rw [Chevalley.reindexRepresentation_pointMatrix] at hp
  change (E (ρ.pointMatrix T g).val - 1) ^ Fintype.card n = 0 at hp
  have hz : IsNilpotent ((ρ.pointMatrix T g).val - 1) := by
    refine ⟨Fintype.card n, E.injective ?_⟩
    rwa [map_pow, map_sub, map_one, map_zero]
  have h := hz.map (Scheme.ΓSpecIso R).hom.hom.mapMatrix
  rw [map_sub, map_one] at h
  exact h

/-- Milne, Corollary 14.10, with elementwise unipotence tested in every
matrix representation and the converse using schematic density. -/
theorem perfectFieldUnipotentRationalPoints : PerfectFieldUnipotentRationalPointsStatement.{u} := by
  intro k _ _ G _ _
  constructor
  · intro hG n _ _ ρ g
    exact rationalMatrix_sub_one_nilpotent hG ρ g
  · intro hdense hpoints n _ _ _ ρ
    obtain ⟨v, hv, hfix⟩ :=
      exists_fixed_of_unipotent_matrices ρ.rationalMatrix (hpoints n ρ)
    exact ⟨v, hv, isFixedVector_of_schematicallyDense hdense ρ v hfix⟩

end Langlands.GroupScheme
