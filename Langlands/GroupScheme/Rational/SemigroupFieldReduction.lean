import Langlands.GroupScheme.Rational.SemigroupBaseChange
import Langlands.GroupScheme.Rational.OrderedProductBaseChange
import Langlands.GroupScheme.Rational.CentralProductKernel
import Langlands.GroupScheme.Rational.SemigroupProductRestriction
import Langlands.GroupScheme.Rational.SolvableSchemeComparison

/-! # Field-extension detection of exact ordered semigroup products -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

section Blocks

variable {B C : Scheme.{u}} (b : C ⟶ B) (S : CommGroupScheme B)
    {I : Type v}

/-- Transport each block by actual character pullback, retaining its index. -/
def weightBlocksBaseChange (Ψ : I → Set (characterLattice S)) :
    I → Set (characterLattice ((CommGroupScheme.baseChange b).obj S)) :=
  fun r => characterLattice.baseChange b S '' Ψ r

@[simp] theorem mem_weightBlocksBaseChange (Ψ : I → Set (characterLattice S))
    (r : I) (ψ : characterLattice ((CommGroupScheme.baseChange b).obj S)) :
    ψ ∈ weightBlocksBaseChange b S Ψ r ↔
      ∃ χ ∈ Ψ r, characterLattice.baseChange b S χ = ψ := Iff.rfl

/-- Taking a union of blocks commutes with character pullback. -/
theorem iUnion_weightBlocksBaseChange (Ψ : I → Set (characterLattice S)) :
    (⋃ r, weightBlocksBaseChange b S Ψ r) =
      characterLattice.baseChange b S '' (⋃ r, Ψ r) :=
  Set.image_iUnion.symm

/-- The positive closure of a transported block is the transported original
positive closure; no zero is inserted. -/
theorem closure_weightBlocksBaseChange (Ψ : I → Set (characterLattice S)) (r : I) :
    (AddSubsemigroup.closure (weightBlocksBaseChange b S Ψ r) :
      Set (characterLattice ((CommGroupScheme.baseChange b).obj S))) =
      characterLattice.baseChange b S ''
        (AddSubsemigroup.closure (Ψ r) : Set (characterLattice S)) := by
  exact congrArg
    (fun A : AddSubsemigroup (characterLattice ((CommGroupScheme.baseChange b).obj S)) =>
      (A : Set (characterLattice ((CommGroupScheme.baseChange b).obj S))))
    (characterSemigroupBaseChange_closure b S (Ψ r)).symm

end Blocks

section Field

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

local notation "b" => algebraBaseMap k K
local notation "G_K" => Functor.obj (GroupScheme.baseChange b) G
local notation "S_K" => Functor.obj (CommGroupScheme.baseChange b) S

local instance fieldReductionAffine : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom b)
  infer_instance

local instance fieldReductionFiniteType : LocallyOfFiniteType (G_K).X.hom := by
  change LocallyOfFiniteType (pullback.snd G.X.hom b)
  infer_instance

variable (a : AutomorphicAction S.toGrp G) (hS : IsSplitTorus S.toGrp)

include hS

/-- Character pullback identifies the full occurring support, including zero. -/
theorem actionWeightSupport_top_baseChange :
    actionWeightSupport (k := K) (G := G_K) (S := S_K) (a.baseChange b) ⊤ =
      characterLattice.baseChange b S '' actionWeightSupport a ⊤ := by
  ext ψ
  obtain ⟨χ, rfl⟩ := (hS.characterLattice_baseChange_bijective b S).surjective ψ
  rw [mem_actionWeightSupport_top_baseChange_iff (K := K) a hS]
  constructor
  · exact fun hχ => ⟨χ, hχ, rfl⟩
  · rintro ⟨χ', hχ', he⟩
    have hχ : χ' = χ := (hS.characterLattice_baseChange_bijective b S).injective he
    exact hχ ▸ hχ'

/-- A partition of the entire original support remains a covering after
field extension. -/
theorem weightBlocksBaseChange_cover {I : Type v}
    (Ψ : I → Set (characterLattice S))
    (hcover : (⋃ r, Ψ r) = actionWeightSupport a ⊤) :
    (⋃ r, weightBlocksBaseChange b S Ψ r) =
      actionWeightSupport (k := K) (G := G_K) (S := S_K) (a.baseChange b) ⊤ := by
  rw [iUnion_weightBlocksBaseChange, hcover, actionWeightSupport_top_baseChange (K := K) a hS]

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
/-- Distinct disjoint blocks remain disjoint under split character pullback. -/
theorem weightBlocksBaseChange_disjoint {I : Type v}
    (Ψ : I → Set (characterLattice S))
    (hdis : ∀ r s : I, r ≠ s → Disjoint (Ψ r) (Ψ s)) :
    ∀ r s : I, r ≠ s →
      Disjoint (weightBlocksBaseChange b S Ψ r) (weightBlocksBaseChange b S Ψ s) := by
  intro r s hrs
  exact Set.disjoint_image_of_injective
    (hS.characterLattice_baseChange_bijective b S).injective (hdis r s hrs)

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
/-- The exact block-versus-positive-closure exclusion persists. -/
theorem weightBlocksBaseChange_cross_exclusion {I : Type v}
    (Ψ : I → Set (characterLattice S))
    (hcross : ∀ r s : I, r ≠ s →
      Disjoint (Ψ r) (AddSubsemigroup.closure (Ψ s) : Set (characterLattice S))) :
    ∀ r s : I, r ≠ s →
      Disjoint (weightBlocksBaseChange b S Ψ r)
        (AddSubsemigroup.closure (weightBlocksBaseChange b S Ψ s) :
          Set (characterLattice S_K)) := by
  intro r s hrs
  rw [closure_weightBlocksBaseChange]
  exact Set.disjoint_image_of_injective
    (hS.characterLattice_baseChange_bijective b S).injective (hcross r s hrs)

variable [Smooth G.X.hom]

local instance fieldReductionSmooth : Smooth (G_K).X.hom := by
  change Smooth (pullback.snd G.X.hom b)
  infer_instance

/-- Ordered semigroup products descend from every field extension. Original
geometric representatives supply the factors, so no representative descent
datum is assumed. -/
theorem HasOrderedSemigroupProducts.of_fieldExtension
    (h : HasOrderedSemigroupProducts (k := K) (G := G_K) (S := S_K)
      (a.baseChange b)) : HasOrderedSemigroupProducts a := by
  classical
  intro n Ψ hcover hdis hcross
  obtain ⟨R, l, hl, hprod⟩ := h n (weightBlocksBaseChange b S Ψ)
    (weightBlocksBaseChange_cover (K := K) a hS Ψ hcover)
    (weightBlocksBaseChange_disjoint (K := K) hS Ψ hdis)
    (weightBlocksBaseChange_cross_exclusion (K := K) hS Ψ hcross)
  choose H j hj hc hs hconn using
    (fun r => isSmoothConnectedClosed_semigroupSubgroup a hS
      (AddSubsemigroup.closure (Ψ r)))
  have hrep (r : Fin n) :
      (semigroupSubgroup (k := K) (G := G_K) (S := S_K) (a.baseChange b)
        (AddSubsemigroup.closure (weightBlocksBaseChange b S Ψ r))).IsRepresentedBy
          ((GroupScheme.baseChange b).map (j r)) := by
    have hr := isRepresentedBy_semigroupSubgroup_baseChange (K := K) a hS
      (AddSubsemigroup.closure (Ψ r)) (hj r)
    rw [characterSemigroupBaseChange_closure] at hr
    exact hr
  have hpull : IsIso (orderedMultiplication
      (fun r => (GroupScheme.baseChange b).map (j r))) :=
    isIso_orderedMultiplication_of_same_representatives
      (fun r => semigroupSubgroup (k := K) (G := G_K) (S := S_K) (a.baseChange b)
        (AddSubsemigroup.closure (weightBlocksBaseChange b S Ψ r)))
      l (fun r => (GroupScheme.baseChange b).map (j r))
      (fun r => (hl r).1) hrep hprod
  exact ⟨H, j, fun r => ⟨hj r, hc r, hs r, hconn r⟩,
    (isIso_orderedMultiplication_fieldExtension_iff (K := K) j).mp hpull⟩

end Field

/-- To prove the exact arbitrary-field target, it suffices to prove it for
solvable groups over algebraically closed fields in the same universe. -/
theorem semigroupOrderedProduct_of_algebraicallyClosed
    (h : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (G : GroupScheme (Spec (CommRingCat.of k)))
      (_hG : Smooth G.X.hom) (hAff : IsAffineHom G.X.hom)
      (_hConn : ConnectedSpace G.X.left) (_hSolv : IsSolvableScheme G)
      (S : CommGroupScheme (Spec (CommRingCat.of k)))
      (_hS : IsSplitTorus S.toGrp) (a : AutomorphicAction S.toGrp G),
      letI := hAff
      HasOrderedSemigroupProducts a) :
    SemigroupOrderedProductStatement.{u} := by
  intro k _ G hG hAff hConn hSolv S hS a
  let := hAff
  let := hG
  let := hConn
  change HasOrderedSemigroupProducts a
  apply HasOrderedSemigroupProducts.of_fieldExtension (K := AlgebraicClosure k) a hS
  let b := algebraBaseMap k (AlgebraicClosure k)
  let G' := (GroupScheme.baseChange b).obj G
  let S' := (CommGroupScheme.baseChange b).obj S
  have haff : IsAffineHom G'.X.hom := by
    change IsAffineHom (pullback.snd G.X.hom b)
    infer_instance
  have hsmooth : Smooth G'.X.hom := by
    change Smooth (pullback.snd G.X.hom b)
    infer_instance
  have hconn : ConnectedSpace G'.X.left :=
    G.connectedSpace_baseChange_of_smooth_affine b
  exact h (AlgebraicClosure k) G' hsmooth haff hconn (hSolv.baseChange b)
    S' (hS.baseChange b) (a.baseChange b)

end Langlands.GroupScheme.RelativeRoot
