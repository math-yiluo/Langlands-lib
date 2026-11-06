import Langlands.Automorphic.GroupSchemeFiniteLevel
import Langlands.Representation.FiniteVectors
import Mathlib.RepresentationTheory.Stabilizer
import Mathlib.RingTheory.Artinian.Module

/-! # Finite-level subgroups from actual finite locally constant orbits -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped Classical CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]

local instance finiteLevelContinuousAddCommGroup :
    AddCommGroup (ContinuousRationalFunctions F G) :=
  Module.addCommMonoidToAddCommGroup ℂ

/-- Actual finite point evaluations separate every finite-dimensional subspace
of the original continuous rational-invariant functions. -/
theorem exists_finset_evaluate_eq_zero (S : Submodule ℂ (ContinuousRationalFunctions F G))
    [Module.Finite ℂ S] :
    ∃ t : Finset (AdelicGroupPoints F G),
      ∀ f ∈ S, (∀ x ∈ t, evaluate F G f x = 0) → f = 0 := by
  let ev (x : AdelicGroupPoints F G) : ContinuousRationalFunctions F G →ₗ[ℂ] ℂ :=
    { toFun := fun f => evaluate F G f x
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  let K (t : Finset (AdelicGroupPoints F G)) : Submodule ℂ S :=
    ⨅ x ∈ t, LinearMap.ker ((ev x).comp S.subtype)
  have hK (t : Finset (AdelicGroupPoints F G)) (f : S) :
      f ∈ K t ↔ ∀ x ∈ t, evaluate F G f.val x = 0 := by
    simp only [K, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.comp_apply]
    rfl
  obtain ⟨M, ⟨t, rfl⟩, hmin⟩ :=
    IsArtinian.set_has_minimal (Set.range K) ⟨K ∅, ∅, rfl⟩
  refine ⟨t, fun f hf ht => ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  funext x
  have hle : K (insert x t) ≤ K t := fun w hw =>
    (hK t w).mpr fun y hy => (hK _ w).mp hw y (Finset.mem_insert_of_mem hy)
  have heq : K (insert x t) = K t :=
    eq_of_le_of_not_lt hle (hmin _ ⟨insert x t, rfl⟩)
  have hf' : (⟨f, hf⟩ : S) ∈ K (insert x t) := by
    rw [heq]
    exact (hK t _).mpr ht
  exact (hK _ _).mp hf' x (Finset.mem_insert_self x t)

variable (C : OpenSubgroup (FiniteAdelicGroupPoints F G))

/-- The specified actual finite subgroup acting on the original continuous functions. -/
def continuousFiniteSubgroupAction :
    Representation ℂ C (ContinuousRationalFunctions F G) :=
  (finiteRightAction F G).comp C.toSubgroup.subtype

/-- Finite-slice local constancy gives locally constant point evaluations of the orbit. -/
theorem isLocallyConstant_continuousFiniteSubgroupAction_evaluate
    (f : ContinuousRationalFunctions F G)
    (hf : f ∈ finiteLocallyConstantSubrepresentation F G) (x : AdelicGroupPoints F G) :
    IsLocallyConstant (fun c : C =>
      evaluate F G (continuousFiniteSubgroupAction F G C c f) x) := by
  have heq : (fun c : C => evaluate F G (continuousFiniteSubgroupAction F G C c f) x) =
      fun c : C => evaluate F G f (AdelicGroupPoints.pair F G
        (AdelicGroupPoints.infinite F G x) (AdelicGroupPoints.finite F G x * c.val)) := by
    funext c
    change evaluate F G f (x * AdelicGroupPoints.ofFinite F G c.val) = _
    rw [AdelicGroupPoints.ofFinite_eq_pair, ← AdelicGroupPoints.pair_projections F G x,
      AdelicGroupPoints.pair_mul, mul_one]
    simp only [AdelicGroupPoints.infinite_pair, AdelicGroupPoints.finite_pair]
  rw [heq]
  exact (hf (AdelicGroupPoints.infinite F G x)).comp_continuous
    (continuous_const.mul continuous_subtype_val)

/-- A finite-dimensional actual orbit and locally constant point evaluations
make the entire function-valued orbit locally constant. -/
theorem isLocallyConstant_continuousFiniteSubgroupOrbit
    (f : ContinuousRationalFunctions F G)
    (hf : f ∈ finiteLocallyConstantSubrepresentation F G)
    (hfin : Langlands.FiniteVectors.IsFiniteVector (continuousFiniteSubgroupAction F G C) f) :
    IsLocallyConstant (fun c : C => continuousFiniteSubgroupAction F G C c f) := by
  let ρ := continuousFiniteSubgroupAction F G C
  let S := Langlands.FiniteVectors.orbitSpan ρ f
  let : Module.Finite ℂ S := hfin
  obtain ⟨t, ht⟩ := exists_finset_evaluate_eq_zero F G S
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro a
  refine ⟨{b : C | ∀ x ∈ t, evaluate F G (ρ b f) x = evaluate F G (ρ a f) x}, ?_, ?_, ?_⟩
  · have hopen : IsOpen (⋂ x ∈ t,
        {b : C | evaluate F G (ρ b f) x = evaluate F G (ρ a f) x}) :=
      isOpen_biInter_finset fun x _ =>
        (isLocallyConstant_continuousFiniteSubgroupAction_evaluate F G C f hf x).isOpen_fiber _
    convert hopen using 1
    ext b
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
  · intro x _
    rfl
  · intro b hb
    have hzero : ρ b f + (-1 : ℂ) • ρ a f = 0 := by
      apply ht (ρ b f + (-1 : ℂ) • ρ a f)
        (S.add_mem (Langlands.FiniteVectors.action_mem_orbitSpan ρ b f)
          (S.smul_mem (-1) (Langlands.FiniteVectors.action_mem_orbitSpan ρ a f)))
      intro x hx
      change evaluate F G (ρ b f) x + (-1 : ℂ) * evaluate F G (ρ a f) x = 0
      rw [hb x hx]
      ring
    apply Subtype.ext
    apply Subtype.ext
    funext x
    have hx := congrArg (fun w : ContinuousRationalFunctions F G => evaluate F G w x) hzero
    change evaluate F G (ρ b f) x + (-1 : ℂ) * evaluate F G (ρ a f) x = 0 at hx
    change evaluate F G (ρ b f) x = evaluate F G (ρ a f) x
    exact sub_eq_zero.mp (by simpa only [neg_one_mul, sub_eq_add_neg] using hx)

/-- The actual stabilizer, now proved open inside the specified finite subgroup. -/
def finiteOrbitOpenStabilizer (f : ContinuousRationalFunctions F G)
    (hf : f ∈ finiteLocallyConstantSubrepresentation F G)
    (hfin : Langlands.FiniteVectors.IsFiniteVector (continuousFiniteSubgroupAction F G C) f) :
    OpenSubgroup C where
  toSubgroup := Representation.stabilizer (continuousFiniteSubgroupAction F G C) f
  isOpen' :=
    (isLocallyConstant_continuousFiniteSubgroupOrbit F G C f hf hfin).isOpen_fiber f

/-- Map the actual stabilizer into the original finite adelic group.
Openness of C makes this an open subgroup of that whole group. -/
def finiteOrbitLevelSubgroup (f : ContinuousRationalFunctions F G)
    (hf : f ∈ finiteLocallyConstantSubrepresentation F G)
    (hfin : Langlands.FiniteVectors.IsFiniteVector (continuousFiniteSubgroupAction F G C) f) :
    OpenSubgroup (FiniteAdelicGroupPoints F G) where
  toSubgroup := (finiteOrbitOpenStabilizer F G C f hf hfin).toSubgroup.map C.toSubgroup.subtype
  isOpen' := by
    change IsOpen (Subtype.val '' (finiteOrbitOpenStabilizer F G C f hf hfin : Set C))
    exact C.isOpen.isOpenMap_subtype_val _
      (finiteOrbitOpenStabilizer F G C f hf hfin).isOpen

theorem finiteOrbitLevelSubgroup_le (f : ContinuousRationalFunctions F G)
    (hf : f ∈ finiteLocallyConstantSubrepresentation F G)
    (hfin : Langlands.FiniteVectors.IsFiniteVector (continuousFiniteSubgroupAction F G C) f) :
    (finiteOrbitLevelSubgroup F G C f hf hfin).toSubgroup ≤ C.toSubgroup := by
  rintro _ ⟨c, _, rfl⟩
  exact c.property

/-- The constructed subgroup fixes the entire original function. -/
theorem mem_levelSubmodule_finiteOrbitLevelSubgroup (f : ContinuousRationalFunctions F G)
    (hf : f ∈ finiteLocallyConstantSubrepresentation F G)
    (hfin : Langlands.FiniteVectors.IsFiniteVector (continuousFiniteSubgroupAction F G C) f) :
    f ∈ levelSubmodule F G (finiteOrbitLevelSubgroup F G C f hf hfin).toSubgroup := by
  intro l
  obtain ⟨c, hc, hcl⟩ := l.property
  change continuousFiniteSubgroupAction F G C c f = f at hc
  rw [← hcl]
  exact hc

/-- Compactness of C supplies actual compact finite level, without any tensor-rank assertion. -/
theorem hasFiniteLevel_of_finiteLocallyConstant_finiteVector
    (hC : IsCompact (C : Set (FiniteAdelicGroupPoints F G)))
    (f : ContinuousRationalFunctions F G)
    (hf : f ∈ finiteLocallyConstantSubrepresentation F G)
    (hfin : Langlands.FiniteVectors.IsFiniteVector (continuousFiniteSubgroupAction F G C) f) :
    HasFiniteLevel F G f := by
  let L := finiteOrbitLevelSubgroup F G C f hf hfin
  refine ⟨L.toSubgroup, L.isOpen, ?_,
    mem_levelSubmodule_finiteOrbitLevelSubgroup F G C f hf hfin⟩
  exact hC.of_isClosed_subset L.isClosed (finiteOrbitLevelSubgroup_le F G C f hf hfin)

end Langlands.Automorphic.GroupSchemeFunctions
