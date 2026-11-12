import Langlands.Representation.Intertwining.PQRegularity

/-! # Inclusions between the four PQ support subspaces -/

noncomputable section

open CategoryTheory

namespace Langlands.RepSubfunctor

/-- The natural same-vector inclusion associated to pointwise containment. -/
def inclusionOfLE {R H : Type*} [CommRing R] [Monoid H]
    {C : Type*} [Category C] {F : C ⥤ Rep R H}
    (S T : RepSubfunctor F) (h : ∀ X, S.obj X ≤ T.obj X) :
    S.toFunctor ⟶ T.toFunctor where
  app X := Rep.ofHom
    { toLinearMap :=
        { toFun := fun x => ⟨x.val, h X x.property⟩
          map_add' _ _ := rfl
          map_smul' _ _ := rfl }
      isIntertwining' _ := rfl }
  naturality _ _ _ := rfl

end Langlands.RepSubfunctor

namespace Langlands.Geometric

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Double-coset closures are also invariant under left multiplication by P. -/
theorem mul_mem_closure_doubleCoset (P Q : Subgroup G)
    (w : DoubleCoset.Quotient (P : Set G) Q) (p : P) (g : G)
    (hg : g ∈ closure (DoubleCoset.quotToDoubleCoset P Q w)) :
    (p : G) * g ∈ closure (DoubleCoset.quotToDoubleCoset P Q w) := by
  refine map_mem_closure (f := fun x => (p : G) * x) (continuous_const_mul (p : G)) hg ?_
  intro x hx
  rw [DoubleCoset.mem_quotToDoubleCoset_iff] at hx ⊢
  rwa [DoubleCoset.mk_mem_mul]

/-- Point membership in an orbit closure is the Bruhat relation for its orbit. -/
theorem mem_closure_doubleCoset_iff_bruhatLE (P Q : Subgroup G)
    (w : DoubleCoset.Quotient (P : Set G) Q) (g : G) :
    g ∈ closure (DoubleCoset.quotToDoubleCoset P Q w) ↔
      BruhatLE P Q (DoubleCoset.mk P Q g) w := by
  constructor
  · intro hg x hx
    rw [DoubleCoset.mem_quotToDoubleCoset_iff] at hx
    obtain ⟨p, hp, q, hq, rfl⟩ := DoubleCoset.eq.mp hx.symm
    exact closure_doubleCoset_mul_mem P Q w ⟨q, hq⟩ _
      (mul_mem_closure_doubleCoset P Q w ⟨p, hp⟩ g hg)
  · intro hg
    exact hg ((DoubleCoset.mem_quotToDoubleCoset_iff _ _).mpr rfl)

/-- A linear refinement places every boundary orbit strictly before the orbit. -/
theorem boundary_doubleCoset_subset_strictInitial (P Q : Subgroup G)
    (o : LinearOrder (DoubleCoset.Quotient (P : Set G) Q))
    (ho : IsBruhatRefinement P Q o) (w : DoubleCoset.Quotient (P : Set G) Q) :
    closure (DoubleCoset.quotToDoubleCoset P Q w) \
        DoubleCoset.quotToDoubleCoset P Q w ⊆
      DoubleCoset.mk P Q ⁻¹' {w' | o.lt w' w} := by
  intro g hg
  exact (o.lt_iff_le_not_ge _ _).mpr
    ⟨ho _ _ ((mem_closure_doubleCoset_iff_bruhatLE P Q w g).mp hg.1),
      fun hge => hg.2 ((DoubleCoset.mem_quotToDoubleCoset_iff _ _).mpr
        (o.le_antisymm _ _
          (ho _ _ ((mem_closure_doubleCoset_iff_bruhatLE P Q w g).mp hg.1)) hge))⟩

end Langlands.Geometric

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance supportInclusionAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {P M N Q : GroupScheme (Spec (CommRingCat.of k))}
  (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P)
  (hp : IsParabolicSubgroup p) (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hl : IsRationalLeviSubgroup l) (hmul : IsIso (subgroupMultiplication l r)) (q : Q ⟶ G)

/-- Enlarging the vanishing set shrinks the support subfunctor. -/
theorem leviVanishingSubfunctor_antitone
    {Z Z' : Set (rationalPoints G)}
    (hZ : ∀ (x : pointImage q) g, g ∈ Z → g * (x : rationalPoints G) ∈ Z)
    (hZ' : ∀ (x : pointImage q) g, g ∈ Z' → g * (x : rationalPoints G) ∈ Z')
    (h : Z ⊆ Z') :
    letI := leviPointTopology l hl
    ∀ W : SmoothRep.{0, u, v} ℂ (rationalPoints M),
      (leviVanishingSubfunctor p l r hp hr hl hmul q Z' hZ').obj W ≤
        (leviVanishingSubfunctor p l r hp hr hl hmul q Z hZ).obj W := by
  let := leviPointTopology l hl
  intro W f hf
  apply (Geometric.mem_rawSmoothVanishingSubfunctor_iff _ _ Z hZ _ f).mpr
  intro g hg
  exact (Geometric.mem_rawSmoothVanishingSubfunctor_iff _ _ Z' hZ' _ f).mp hf g (h hg)

/-- The three support-space inclusions in Renard VII.3.2. -/
theorem pqSupportInclusions
    (o : LinearOrder (parabolicDoubleCosets p q))
    (ho : Geometric.IsBruhatRefinement (pointImage p) (pointImage q) o)
    (w : parabolicDoubleCosets p q) :
    letI := leviPointTopology l hl
    ∀ W : SmoothRep.{0, u, v} ℂ (rationalPoints M),
      (initialVanishingSubfunctor p l r hp hr hl hmul q o w).obj W ≤
          (strictInitialVanishingSubfunctor p l r hp hr hl hmul q o w).obj W ∧
        (strictInitialVanishingSubfunctor p l r hp hr hl hmul q o w).obj W ≤
          (boundaryVanishingSubfunctor p l r hp hr hl hmul q w).obj W ∧
        (closureVanishingSubfunctor p l r hp hr hl hmul q w).obj W ≤
          (boundaryVanishingSubfunctor p l r hp hr hl hmul q w).obj W := by
  let := leviPointTopology l hl
  intro W
  refine ⟨?_, ?_, ?_⟩
  · exact leviVanishingSubfunctor_antitone p l r hp hr hl hmul q _ _
      (fun _ h => ((o.lt_iff_le_not_ge _ _).mp h).1) W
  · exact leviVanishingSubfunctor_antitone p l r hp hr hl hmul q _ _
      (Geometric.boundary_doubleCoset_subset_strictInitial _ _ o ho w) W
  · exact leviVanishingSubfunctor_antitone p l r hp hr hl hmul q _ _ Set.sdiff_subset W

/-- The three natural same-function support inclusions of Renard VII.3.2. -/
def pqSupportInclusionMaps
    (o : LinearOrder (parabolicDoubleCosets p q))
    (ho : Geometric.IsBruhatRefinement (pointImage p) (pointImage q) o)
    (w : parabolicDoubleCosets p q) :
    letI := leviPointTopology l hl
    ((initialVanishingSubfunctor.{u, v} p l r hp hr hl hmul q o w).toFunctor ⟶
      (strictInitialVanishingSubfunctor p l r hp hr hl hmul q o w).toFunctor) ×
    ((strictInitialVanishingSubfunctor.{u, v} p l r hp hr hl hmul q o w).toFunctor ⟶
      (boundaryVanishingSubfunctor p l r hp hr hl hmul q w).toFunctor) ×
    ((closureVanishingSubfunctor.{u, v} p l r hp hr hl hmul q w).toFunctor ⟶
      (boundaryVanishingSubfunctor p l r hp hr hl hmul q w).toFunctor) := by
  letI := leviPointTopology l hl
  exact ⟨RepSubfunctor.inclusionOfLE _ _
      (fun W => (pqSupportInclusions p l r hp hr hl hmul q o ho w W).1),
    RepSubfunctor.inclusionOfLE _ _
      (fun W => (pqSupportInclusions p l r hp hr hl hmul q o ho w W).2.1),
    RepSubfunctor.inclusionOfLE _ _
      (fun W => (pqSupportInclusions p l r hp hr hl hmul q o ho w W).2.2)⟩

end Langlands.Aubert.General.RepresentedParabolic
