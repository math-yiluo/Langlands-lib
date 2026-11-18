import Langlands.GroupScheme.Reductive.CharZeroSemisimplicity.TangentStability
import Langlands.GroupScheme.MatrixRepresentation.StableComplements
import Langlands.GroupScheme.Reductive.InvariantLinearForm
import Langlands.GroupScheme.MatrixRepresentation.StableSubrepresentation
import Mathlib.RingTheory.SimpleModule.Basic

/-! # Semisimple matrix representations and their rational-point representations -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj MonoidAlgebra

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {n : Type} [Fintype n] [DecidableEq n]

/-- The coordinate space `n → k` of `ρ` is the sum of its simple stable subspaces: the
semisimplicity predicate of Milne's Definition 4.15 for matrix representations. -/
abbrev IsSemisimpleStable (ρ : MatrixRepresentation G n) : Prop :=
  ρ.IsSemisimple

/-- The stability equation of split coordinates, read on a rational point. -/
theorem IsStableCoordinates.rationalMatrix_mul {m : Type} [Fintype m]
    {ρ : MatrixRepresentation G n} {B : Matrix n m k} {C : Matrix m n k}
    (h : ρ.IsStableCoordinates B C)
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :
    (ρ.rationalMatrix g : Matrix n n k) * B =
      B * (C * (ρ.rationalMatrix g : Matrix n n k) * B) := by
  let e := (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv
  have hB : (B.map (scalarMap (Over.mk (𝟙 (Spec (CommRingCat.of k)))))).map
      e.toRingHom = B := by
    ext r s
    exact e.apply_symm_apply _
  have hC : (C.map (scalarMap (Over.mk (𝟙 (Spec (CommRingCat.of k)))))).map
      e.toRingHom = C := by
    ext r s
    exact e.apply_symm_apply _
  have hM : ((ρ.pointMatrix (Over.mk (𝟙 (Spec (CommRingCat.of k))))) g).val.map
      e.toRingHom = (ρ.rationalMatrix g : Matrix n n k) := rfl
  have hx := congrArg (fun M => M.map e.toRingHom) (h _ g)
  simpa only [Matrix.map_mul (f := e.toRingHom), hB, hC, hM] using hx

/-- A stable subspace is invariant under the actual rational points. -/
theorem IsStableSubspace.rationalRepresentation_mem [IsAffineHom G.X.hom]
    {ρ : MatrixRepresentation G n} {W : Submodule k (n → k)}
    (hW : ρ.IsStableSubspace W)
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) {v : n → k} (hv : v ∈ W) :
    ρ.rationalRepresentation g v ∈ W :=
  by
    simpa only [rationalRepresentation_apply] using hW.rationalMatrix_mulVec_mem g hv

section AlgebraicallyClosed

variable [IsAlgClosed k] [IsReduced G.X.left] [LocallyOfFiniteType G.X.hom]

/-- Over an algebraically closed field, invariance under the rational points of a reduced
group locally of finite type implies stability on every affine test. -/
theorem isStableSubspace_of_rationalRepresentation (ρ : MatrixRepresentation G n)
    (W : Submodule k (n → k))
    (h : ∀ g v, v ∈ W → ρ.rationalRepresentation g v ∈ W) :
    ρ.IsStableSubspace W :=
  isStableSubspace_of_rationalMatrix ρ W (by
    simpa only [rationalRepresentation_apply] using h)

end AlgebraicallyClosed

section Lattice

variable (ρ : MatrixRepresentation G n)

/-- The coordinate subspace underlying a submodule of the group-algebra module of the
rational-point representation. -/
def submoduleOfModule
    (m : Submodule k[Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X]
      ρ.rationalRepresentation.asModule) : Submodule k (n → k) :=
  (Subrepresentation.ofSubmodule' m).toSubmodule

theorem mem_submoduleOfModule
    (m : Submodule k[Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X]
      ρ.rationalRepresentation.asModule) (v : n → k) :
    v ∈ ρ.submoduleOfModule m ↔ v ∈ m :=
  Iff.rfl

theorem isStableSubspace_submoduleOfModule [IsAlgClosed k] [IsReduced G.X.left]
    [LocallyOfFiniteType G.X.hom] (m : Submodule k[Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X]
      ρ.rationalRepresentation.asModule) :
    ρ.IsStableSubspace (ρ.submoduleOfModule m) :=
  isStableSubspace_of_rationalRepresentation ρ _
    (fun g _ hv => (Subrepresentation.ofSubmodule' m).apply_mem_toSubmodule g hv)

/-- The group-algebra submodule carried by a stable subspace. -/
def moduleOfStable [IsAffineHom G.X.hom] (W : Submodule k (n → k)) (hW : ρ.IsStableSubspace W) :
    Submodule k[Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X]
      ρ.rationalRepresentation.asModule :=
  Subrepresentation.asSubmodule
    ⟨W, fun g _ hv => hW.rationalRepresentation_mem g hv⟩

theorem submoduleOfModule_moduleOfStable [IsAffineHom G.X.hom] (W : Submodule k (n → k))
    (hW : ρ.IsStableSubspace W) :
    ρ.submoduleOfModule (ρ.moduleOfStable W hW) = W :=
  rfl

theorem submoduleOfModule_le_iff
    {m m' : Submodule k[Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X]
      ρ.rationalRepresentation.asModule} :
    ρ.submoduleOfModule m ≤ ρ.submoduleOfModule m' ↔ m ≤ m' :=
  Iff.rfl

theorem submoduleOfModule_injective :
    Function.Injective ρ.submoduleOfModule := fun _ _ h =>
  le_antisymm ((ρ.submoduleOfModule_le_iff).1 h.le) ((ρ.submoduleOfModule_le_iff).1 h.ge)

theorem submoduleOfModule_bot : ρ.submoduleOfModule ⊥ = ⊥ := by
  ext v
  change (v : ρ.rationalRepresentation.asModule) ∈ (⊥ : Submodule _ _) ↔
    v ∈ (⊥ : Submodule k (n → k))
  simp only [Submodule.mem_bot]

theorem submoduleOfModule_top : ρ.submoduleOfModule ⊤ = ⊤ := by
  ext v
  change (v : ρ.rationalRepresentation.asModule) ∈ (⊤ : Submodule _ _) ↔
    v ∈ (⊤ : Submodule k (n → k))
  simp only [Submodule.mem_top]

/-- Every supremum of rational-point invariant subspaces is invariant. -/
theorem sSup_rationalRepresentation_mem (S : Set (Submodule k (n → k)))
    (hS : ∀ W ∈ S, ∀ g v, v ∈ W → ρ.rationalRepresentation g v ∈ W)
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) {v : n → k} (hv : v ∈ sSup S) :
    ρ.rationalRepresentation g v ∈ sSup S := by
  have hle : sSup S ≤ (sSup S).comap (ρ.rationalRepresentation g) :=
    sSup_le fun W hW _ hw => le_sSup hW (hS W hW g _ hw)
  exact hle hv

theorem submoduleOfModule_sSup [IsAffineHom G.X.hom] [IsAlgClosed k] [IsReduced G.X.left]
    [LocallyOfFiniteType G.X.hom] (s : Set (Submodule k[Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X]
      ρ.rationalRepresentation.asModule)) :
    ρ.submoduleOfModule (sSup s) = sSup (ρ.submoduleOfModule '' s) := by
  apply le_antisymm
  · have hT : ρ.IsStableSubspace (sSup (ρ.submoduleOfModule '' s)) := by
      apply isStableSubspace_of_rationalRepresentation
      apply sSup_rationalRepresentation_mem
      rintro W ⟨m, -, rfl⟩ g v hv
      exact (Subrepresentation.ofSubmodule' m).apply_mem_toSubmodule g hv
    rw [← ρ.submoduleOfModule_moduleOfStable _ hT, submoduleOfModule_le_iff]
    apply sSup_le
    intro m hm
    rw [← submoduleOfModule_le_iff, submoduleOfModule_moduleOfStable]
    exact le_sSup ⟨m, hm, rfl⟩
  · apply sSup_le
    rintro W ⟨m, hm, rfl⟩
    rw [submoduleOfModule_le_iff]
    exact le_sSup hm

/-- The set of simple stable subspaces of a matrix representation. -/
def simpleStableSet : Set (Submodule k (n → k)) :=
  {W : Submodule k (n → k) | ρ.IsStableSubspace W ∧ W ≠ ⊥ ∧
    ∀ U : Submodule k (n → k), ρ.IsStableSubspace U → U ≤ W → U = ⊥ ∨ U = W}

theorem isAtom_iff_submoduleOfModule_mem [IsAffineHom G.X.hom] [IsAlgClosed k]
    [IsReduced G.X.left] [LocallyOfFiniteType G.X.hom] (m : Submodule k[Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X]
      ρ.rationalRepresentation.asModule) :
    IsAtom m ↔ ρ.submoduleOfModule m ∈ ρ.simpleStableSet := by
  constructor
  · intro hm
    refine ⟨ρ.isStableSubspace_submoduleOfModule m, ?_, ?_⟩
    · intro h
      apply hm.1
      apply ρ.submoduleOfModule_injective
      rw [h, submoduleOfModule_bot]
    · intro U hU hUW
      rw [← ρ.submoduleOfModule_moduleOfStable U hU, submoduleOfModule_le_iff] at hUW
      rcases hUW.lt_or_eq with hlt | heq
      · left
        rw [← ρ.submoduleOfModule_moduleOfStable U hU, hm.2 _ hlt, submoduleOfModule_bot]
      · right
        rw [← ρ.submoduleOfModule_moduleOfStable U hU, heq]
  · rintro ⟨-, hne, hmin⟩
    refine ⟨fun h => hne (by rw [h, submoduleOfModule_bot]), ?_⟩
    intro b hb
    rcases hmin _ (ρ.isStableSubspace_submoduleOfModule b)
        ((submoduleOfModule_le_iff ρ).2 hb.le) with h | h
    · apply ρ.submoduleOfModule_injective
      rw [h, submoduleOfModule_bot]
    · exact absurd (ρ.submoduleOfModule_injective h) hb.ne

theorem simpleStableSet_eq_image [IsAffineHom G.X.hom] [IsAlgClosed k]
    [IsReduced G.X.left] [LocallyOfFiniteType G.X.hom] :
    ρ.simpleStableSet = ρ.submoduleOfModule '' {m | IsAtom m} := by
  ext W
  constructor
  · intro hW
    refine ⟨ρ.moduleOfStable W hW.1, ?_, ρ.submoduleOfModule_moduleOfStable W hW.1⟩
    change IsAtom _
    rw [isAtom_iff_submoduleOfModule_mem, submoduleOfModule_moduleOfStable]
    exact hW
  · rintro ⟨m, hm, rfl⟩
    exact (ρ.isAtom_iff_submoduleOfModule_mem m).1 hm

/-- Over an algebraically closed field, for a reduced affine group locally of finite type,
semisimplicity of a matrix representation in the all-test sense is semisimplicity of its
rational-point representation. -/
theorem isSemisimpleStable_iff_rationalRepresentation [IsAffineHom G.X.hom] [IsAlgClosed k]
    [IsReduced G.X.left] [LocallyOfFiniteType G.X.hom] :
    ρ.IsSemisimpleStable ↔ ρ.rationalRepresentation.IsSemisimpleRepresentation := by
  rw [Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]
  have hsimple : {m : Submodule k[Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X]
      ρ.rationalRepresentation.asModule |
        IsSimpleModule k[Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X] m} =
      {m | IsAtom m} := by
    ext m
    exact isSimpleModule_iff_isAtom
  have hss : ρ.IsSemisimpleStable ↔ sSup ρ.simpleStableSet = ⊤ := Iff.rfl
  rw [hss, simpleStableSet_eq_image, ← submoduleOfModule_sSup, ← submoduleOfModule_top]
  rw [ρ.submoduleOfModule_injective.eq_iff]
  constructor
  · intro h
    apply IsSemisimpleModule.of_sSup_simples_eq_top
    rw [hsimple]
    exact h
  · intro h
    rw [← hsimple]
    exact IsSemisimpleModule.sSup_simples_eq_top _ _

end Lattice

end Langlands.GroupScheme.MatrixRepresentation
