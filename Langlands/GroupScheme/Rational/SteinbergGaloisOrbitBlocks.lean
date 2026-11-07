import Langlands.GroupScheme.Rational.SteinbergFactorGaloisTransport
import Mathlib.Data.List.NodupEquivFin
import Mathlib.GroupTheory.GroupAction.Quotient

/-! # Actual Galois orbit blocks for the canonical Steinberg product -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands

namespace Algebra.FiniteActionOrbitBlocks

variable (Γ : Type v) [Group Γ] (I : Type u) [Finite I] [MulAction Γ I]

local instance : Fintype I := Fintype.ofFinite I
local instance : Fintype (MulAction.orbitRel.Quotient Γ I) := Fintype.ofFinite _

/-- List all elements of the specified actual orbit, without repetition. -/
def orbitList (o : MulAction.orbitRel.Quotient Γ I) : List I := by
  classical
  exact (Finset.univ.filter (fun i => (⟦i⟧ : MulAction.orbitRel.Quotient Γ I) = o)).toList

@[simp]
theorem mem_orbitList (o : MulAction.orbitRel.Quotient Γ I) (i : I) :
    i ∈ orbitList Γ I o ↔ (⟦i⟧ : MulAction.orbitRel.Quotient Γ I) = o := by
  classical
  simp [orbitList]

theorem orbitList_nodup (o : MulAction.orbitRel.Quotient Γ I) :
    (orbitList Γ I o).Nodup := by
  classical
  exact Finset.nodup_toList _

/-- Enumerate the actual orbits once, keeping each orbit contiguous. -/
def blocks : List (List I) :=
  (Finset.univ : Finset (MulAction.orbitRel.Quotient Γ I)).toList.map (orbitList Γ I)

theorem mem_blocks (l : List I) :
    l ∈ blocks Γ I ↔ ∃ o, orbitList Γ I o = l := by
  classical
  simp [blocks]

theorem flatten_nodup : (blocks Γ I).flatten.Nodup := by
  classical
  apply List.nodup_flatten.mpr
  constructor
  · intro l hl
    obtain ⟨o, rfl⟩ := (mem_blocks Γ I l).mp hl
    exact orbitList_nodup Γ I o
  · rw [blocks, List.pairwise_map]
    apply (Finset.nodup_toList (Finset.univ :
      Finset (MulAction.orbitRel.Quotient Γ I))).pairwise_of_forall_ne
    intro o ho p hp hop
    apply List.disjoint_left.mpr
    intro i hi hip
    exact hop (((mem_orbitList Γ I o i).mp hi).symm.trans
      ((mem_orbitList Γ I p i).mp hip))

theorem mem_flatten (i : I) : i ∈ (blocks Γ I).flatten := by
  apply List.mem_flatten.mpr
  refine ⟨orbitList Γ I ⟦i⟧, (mem_blocks Γ I _).mpr ⟨_, rfl⟩, ?_⟩
  exact (mem_orbitList Γ I _ i).mpr rfl

/-- The induced ordering lists the entire finite set once. -/
def ordering : Fin (blocks Γ I).flatten.length ≃ I := by
  classical
  exact List.Nodup.getEquivOfForallMemList _ (flatten_nodup Γ I) (mem_flatten Γ I)

theorem flatten_eq_ofFn_ordering :
    (blocks Γ I).flatten = List.ofFn (ordering Γ I) :=
  (List.ofFn_get _).symm

/-- Every orbit block is invariant up to permutation under every group element. -/
theorem blocks_invariant (σ : Γ) (l : List I) (hl : l ∈ blocks Γ I) :
    (l.map (fun i => σ • i)).Perm l := by
  classical
  obtain ⟨o, rfl⟩ := (mem_blocks Γ I l).mp hl
  apply (List.perm_ext_iff_of_nodup
    ((orbitList_nodup Γ I o).map (MulAction.injective σ))
    (orbitList_nodup Γ I o)).mpr
  intro i
  constructor
  · intro hi
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    rw [mem_orbitList] at hj ⊢
    exact MulAction.orbitRel.Quotient.quotient_smul_eq.trans hj
  · intro hi
    apply List.mem_map.mpr
    refine ⟨σ⁻¹ • i, ?_, by simp⟩
    rw [mem_orbitList] at hi ⊢
    exact MulAction.orbitRel.Quotient.quotient_smul_eq.trans hi

/-- Two entries of one block belong to the same actual orbit. -/
theorem same_orbit_of_mem_block
    (l : List I) (hl : l ∈ blocks Γ I) (i j : I) (hi : i ∈ l) (hj : j ∈ l) :
    ∃ σ : Γ, σ • i = j := by
  obtain ⟨o, rfl⟩ := (mem_blocks Γ I l).mp hl
  have h : (⟦j⟧ : MulAction.orbitRel.Quotient Γ I) = ⟦i⟧ :=
    ((mem_orbitList Γ I o j).mp hj).trans ((mem_orbitList Γ I o i).mp hi).symm
  exact MulAction.mem_orbit_iff.mp (Quotient.exact h)

end Algebra.FiniteActionOrbitBlocks

namespace GroupScheme.SplitPinning

variable {K : Type u} [Field K]
    {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom G.X.hom]
    (p : SplitPinning G) {Γ : Type v} [Group Γ]
    (ρ : Γ →* Equiv.Perm p.base.support)

/-- Every two distinct simple roots in the same supplied action orbit are
orthogonal. This is a premise, not a property of all simple-root actions. -/
def OrthogonalSimpleOrbits : Prop :=
  ∀ (σ : Γ) (a : p.base.support),
    a ≠ ρ σ a → p.rootDatum.IsOrthogonal a (ρ σ a)

/-- Enumerate the actual action orbits on the supplied simple-root support. -/
def simpleOrbitBlocks : List (List p.base.support) := by
  letI : MulAction Γ p.base.support := MulAction.compHom _ ρ
  exact Algebra.FiniteActionOrbitBlocks.blocks Γ p.base.support

/-- Order all simple roots, with each actual orbit in one contiguous block. -/
def simpleOrbitOrdering :
    Fin (p.simpleOrbitBlocks ρ).flatten.length ≃ p.base.support := by
  letI : MulAction Γ p.base.support := MulAction.compHom _ ρ
  exact Algebra.FiniteActionOrbitBlocks.ordering Γ p.base.support

theorem simpleOrbitBlocks_flatten_nodup :
    (p.simpleOrbitBlocks ρ).flatten.Nodup := by
  let _ : MulAction Γ p.base.support := MulAction.compHom _ ρ
  exact Algebra.FiniteActionOrbitBlocks.flatten_nodup Γ p.base.support

theorem simpleOrbitBlocks_flatten_eq :
    (p.simpleOrbitBlocks ρ).flatten = List.ofFn (p.simpleOrbitOrdering ρ) := by
  let _ : MulAction Γ p.base.support := MulAction.compHom _ ρ
  exact Algebra.FiniteActionOrbitBlocks.flatten_eq_ofFn_ordering Γ p.base.support

theorem simpleOrbitBlocks_invariant (σ : Γ) (l : List p.base.support)
    (hl : l ∈ p.simpleOrbitBlocks ρ) :
    (l.map (ρ σ)).Perm l := by
  let _ : MulAction Γ p.base.support := MulAction.compHom _ ρ
  exact Algebra.FiniteActionOrbitBlocks.blocks_invariant Γ p.base.support σ l hl

theorem simpleOrbitBlocks_same_orbit (l : List p.base.support)
    (hl : l ∈ p.simpleOrbitBlocks ρ) (a b : p.base.support) (ha : a ∈ l) (hb : b ∈ l) :
    ∃ σ : Γ, ρ σ a = b := by
  let _ : MulAction Γ p.base.support := MulAction.compHom _ ρ
  exact Algebra.FiniteActionOrbitBlocks.same_orbit_of_mem_block
    Γ p.base.support l hl a b ha hb

/-- Orbit orthogonality and duplicate-free enumeration supply precisely the
distinct orthogonal blocks needed by the actual Steinberg factor theorem. -/
theorem simpleOrbitBlocks_pairwise
    (horth : p.OrthogonalSimpleOrbits ρ)
    (l : List p.base.support) (hl : l ∈ p.simpleOrbitBlocks ρ) :
    l.Pairwise (fun (a b : p.base.support) => a ≠ b ∧ p.rootDatum.IsOrthogonal a b) := by
  apply ((List.nodup_flatten.mp (p.simpleOrbitBlocks_flatten_nodup ρ)).1 l hl
    ).pairwise_of_forall_ne
  intro a ha b hb hab
  obtain ⟨σ, hσ⟩ := p.simpleOrbitBlocks_same_orbit ρ l hl a b ha hb
  refine ⟨hab, ?_⟩
  simpa only [hσ] using horth σ a (by rwa [hσ])

end GroupScheme.SplitPinning

namespace GroupScheme.SteinbergOrbitImageDescent

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option autoImplicit false

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]

local instance :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

variable (p : SplitPinning ((GroupScheme.baseChange (algebraBaseMap k K)).obj G))

/-- Using the simple roots themselves as coordinates leaves the supplied
permutation representation unchanged. -/
theorem rootCoordinateAction_self
    {r : ℕ} (e : Fin r ≃ p.base.support)
    (ρ : (K ≃ₐ[k] K) →* Equiv.Perm p.base.support) :
    rootCoordinateAction k K G p p.base.support e e ρ = ρ := by
  ext σ a
  simp [rootCoordinateAction]

/-- Choose the actual simple-root orbit order and descend the full image ideal
of its canonical Steinberg product. Only orbit orthogonality, whole-root-map
compatibility and the actual descended torus/character data remain premises. -/
def definingIdealDescent_of_orthogonalSimpleOrbits [IsGalois k K]
    {T : CommGroupScheme (Spec (CommRingCat.of k))} (j : T.toGrp ⟶ G)
    (eT : p.torus ≅ ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))
    (hT : p.inclusion = CommGroupScheme.groupHom eT.hom ≫
      (GroupScheme.baseChange (algebraBaseMap k K)).map j)
    (x : p.NormalizedSimpleRootParametrizations)
    (ρ : (K ≃ₐ[k] K) →* Equiv.Perm p.base.support)
    (hroot : ∀ (σ : K ≃ₐ[k] K) (a : p.base.support),
      characterLattice.congr eT (p.rootDatum.root (ρ σ a)) =
        characterLattice.galoisRepresentation k K T σ
          (characterLattice.congr eT (p.rootDatum.root a)))
    (hx : SplitPinning.RootMapsGaloisCompatible k K p x ρ)
    (horth : p.OrthogonalSimpleOrbits ρ) :
    DefiningIdealDescent (pullback.fst G.X.hom (algebraBaseMap k K))
      (SplitPinning.steinbergProduct (p.simpleOrbitOrdering ρ) x
        (SplitPinning.canonicalSimpleReflectionRepresentatives x)).left.ker := by
  apply definingIdealDescent_of_compatibleRootMaps k K G p p.base.support
    (p.simpleOrbitOrdering ρ) (p.simpleOrbitOrdering ρ) x
    j eT hT ρ hroot hx (p.simpleOrbitBlocks ρ)
  · exact p.simpleOrbitBlocks_flatten_eq ρ
  · intro σ l hl
    rw [rootCoordinateAction_self]
    exact p.simpleOrbitBlocks_invariant ρ σ l hl
  · intro l hl
    simpa only [Equiv.apply_symm_apply] using p.simpleOrbitBlocks_pairwise ρ horth l hl

end GroupScheme.SteinbergOrbitImageDescent

end Langlands
