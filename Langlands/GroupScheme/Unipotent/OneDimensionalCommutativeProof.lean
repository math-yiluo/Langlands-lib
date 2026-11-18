import Langlands.GroupScheme.Unipotent.OneDimensionalCommutativeStatement
import Langlands.GroupScheme.Absolute.LowDimensionSolvableProof
import Langlands.GroupScheme.Absolute.RationalPointClosureSolvable
import Langlands.GroupScheme.Reductive.SplitLeviGluingGeneratedDensity
import Langlands.GroupScheme.ReducedBaseSmooth.DimensionBridge
import Langlands.GroupScheme.RelativeIdentityComponent.OpenGeometry
import Langlands.GroupScheme.SchemeActionRationalPoints
import Langlands.GroupScheme.Torus.MaximalAmbient

/-! # One-dimensional connected group varieties are commutative -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Order TopologicalSpace
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj commutatorElement

namespace Langlands.GroupScheme

/-- Two distinct closed points in a closed irreducible subset exclude a proper inclusion
in an irreducible space of Krull dimension at most one. -/
private theorem eq_univ_of_two_closed_points {X : Type u} [TopologicalSpace X]
    [IrreducibleSpace X] (hdim : topologicalKrullDim X ≤ 1) {Z : Set X}
    (hZ : IsClosed Z) (hirr : IsIrreducible Z) {x y : X} (hx : IsClosed ({x} : Set X))
    (hxZ : x ∈ Z) (hyZ : y ∈ Z) (hxy : x ≠ y) : Z = Set.univ := by
  by_contra hproper
  let A : IrreducibleCloseds X := ⟨{x}, isIrreducible_singleton, hx⟩
  let B : IrreducibleCloseds X := ⟨Z, hirr, hZ⟩
  let C : IrreducibleCloseds X := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  have hAB : A < B := by
    refine lt_of_le_not_ge (Set.singleton_subset_iff.mpr hxZ) ?_
    intro h
    exact hxy (Set.mem_singleton_iff.mp (h hyZ)).symm
  have hBC : B < C := lt_of_le_of_ne (Set.subset_univ _) fun h =>
    hproper (congrArg (fun W : IrreducibleCloseds X => (W : Set X)) h)
  let p : LTSeries (IrreducibleCloseds X) :=
    ((RelSeries.singleton _ A).snoc B (by simpa using hAB)).snoc C (by simpa using hBC)
  have htwo : (2 : WithBot ℕ∞) ≤ topologicalKrullDim X := by
    simpa [p, topologicalKrullDim] using p.length_le_krullDim
  have hle : (2 : WithBot ℕ∞) ≤ 1 := htwo.trans hdim
  norm_num at hle

section AlgebraicallyClosed

variable {k : Type u} [Field k] [IsAlgClosed k]
  (G : GroupScheme (Spec (CommRingCat.of k)))

local notation "KPoints" => (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)

omit [IsAlgClosed k] in
/-- The closure of the rational points in a subgroup's closure is contained in the same
closed set. -/
private theorem pointClosureSubgroup_idem_le (Γ : Subgroup KPoints) :
    pointClosureSubgroup G (pointClosureSubgroup G Γ) ≤ pointClosureSubgroup G Γ := by
  intro z hz
  apply mem_pointClosureSubgroup.mpr
  apply closure_minimal _ isClosed_closure (mem_pointClosureSubgroup.mp hz)
  rintro _ ⟨p, hp, rfl⟩
  exact mem_pointClosureSubgroup.mp hp

/-- A nontrivial commutator on a curve forces the first derived subgroup of rational
points to be Zariski dense. Such density propagates through the derived series. -/
private theorem isMulCommutative_points_of_solvable
    [IrreducibleSpace G.X.left] [LocallyOfFiniteType G.X.hom]
    (hdim : topologicalKrullDim G.X.left ≤ 1) (hsolv : Group.IsSolvable KPoints) :
    IsMulCommutative KPoints := by
  obtain ⟨n, hn⟩ := hsolv.solvable
  refine ⟨⟨fun a b => ?_⟩⟩
  by_contra h
  have hcomm : ⁅a, b⁆ ≠ 1 := fun e => h (commutatorElement_eq_one_iff_mul_comm.mp e)
  obtain ⟨f, hf⟩ := exists_comp_eq_commutator_left a
  have hpoint (z : KPoints) :
      (z ≫ f).left (IsLocalRing.closedPoint k) ∈ closure (Set.range f.left) :=
    subset_closure ⟨z.left (IsLocalRing.closedPoint k), rfl⟩
  have hone : (1 : KPoints).left (IsLocalRing.closedPoint k) ∈ closure (Set.range f.left) := by
    simpa only [hf, commutatorElement_one_right] using hpoint 1
  have hab : (⁅a, b⁆ : KPoints).left (IsLocalRing.closedPoint k) ∈
      closure (Set.range f.left) := by
    simpa only [hf] using hpoint b
  have hirr : IsIrreducible (Set.range f.left) := by
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image f.left f.left.continuous.continuousOn
  have hdense : closure (Set.range f.left) = Set.univ :=
    eq_univ_of_two_closed_points hdim isClosed_closure hirr.closure
      (isClosed_singleton_rationalPoint 1) hone hab (fun he => hcomm (rationalPoint_ext he.symm))
  have hfirst : ⊤ ≤ pointClosureSubgroup G ⁅(⊤ : Subgroup KPoints), ⊤⁆ := by
    intro z _
    apply mem_pointClosureSubgroup.mpr
    have hle := closure_minimal
      (LeviGluing.range_subset_closure_rationalPointImage f
        (⁅(⊤ : Subgroup KPoints), ⊤⁆ : Subgroup KPoints) fun p => by
          rw [hf]
          exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top p))
      isClosed_closure
    rw [hdense] at hle
    exact hle (Set.mem_univ _)
  have hall : ∀ m, ⊤ ≤ pointClosureSubgroup G (derivedSeries KPoints m) := by
    intro m
    induction m with
    | zero =>
      rw [derivedSeries_zero]
      exact le_pointClosureSubgroup ⊤
    | succ m ih =>
      rw [derivedSeries_succ]
      have hle := (Subgroup.commutator_mono ih ih).trans (commutator_pointClosureSubgroup_le _ _)
      exact hfirst.trans ((pointClosureSubgroup_mono hle).trans (pointClosureSubgroup_idem_le G _))
  have hbot := hall n
  rw [hn, pointClosureSubgroup_bot] at hbot
  exact hcomm (Subgroup.mem_bot.mp (hbot (Subgroup.mem_top ⁅a, b⁆)))

/-- Over an algebraically closed field the multiplication of a smooth affine group
is determined by products of rational points. -/
private theorem isCommMonObj_of_rationalPoints [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (h : IsMulCommutative KPoints) : IsCommMonObj G.X := by
  let := h
  have : Smooth (G.X ⊗ G.X).hom := smooth_tensor G.X G.X inferInstance inferInstance
  have : IsReduced (G.X ⊗ G.X).left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      k _ (G.X ⊗ G.X).hom
  refine ⟨hom_ext_rationalPoints fun z => ?_⟩
  let x := z ≫ fst G.X G.X
  let y := z ≫ snd G.X G.X
  have hz : lift x y = z := by simp [x, y]
  rw [← hz, ← Category.assoc, lift_braiding_hom, ← Hom.mul_def, ← Hom.mul_def]
  exact mul_comm' y x

private theorem isCommMonObj_of_relativeDimension_one
    [SmoothOfRelativeDimension 1 G.X.hom] [IsAffineHom G.X.hom]
    [ConnectedSpace G.X.left] : IsCommMonObj G.X := by
  have : Smooth G.X.hom := SmoothOfRelativeDimension.smooth 1 _
  have : IrreducibleSpace G.X.left :=
    Langlands.AlgebraicGeometry.irreducibleSpace_of_smooth_connected G.X.hom
  have hdim : topologicalKrullDim G.X.left ≤ 1 := by
    rw [ReducedBaseSmooth.topologicalKrullDim_eq_of_smoothOfRelativeDimension k _ G.X.hom 1]
    simp
  have hLie : Lie.dimension G = 1 :=
    Lie.dimension_eq_of_smoothOfRelativeDimension G inferInstance
  have hsolv : Group.IsSolvable KPoints :=
    (isSolvableGroupScheme_iff_isSolvable_points G).mp
      (lowDimensionSolvable k G (hLie.symm ▸ (by decide : 1 ≤ 2)))
  exact isCommMonObj_of_rationalPoints G (isMulCommutative_points_of_solvable G hdim hsolv)

end AlgebraicallyClosed

/-- Milne 2017, Proposition 14.25. -/
theorem oneDimensionalCommutative : OneDimensionalCommutativeStatement.{u} := by
  intro k _ G hdim _ hconn
  let := hconn
  have : Smooth G.X.hom := SmoothOfRelativeDimension.smooth 1 _
  let b := toAlgebraicClosure k
  let H := (GroupScheme.baseChange b).obj G
  have : SmoothOfRelativeDimension 1 H.X.hom := by
    change SmoothOfRelativeDimension 1 (pullback.snd G.X.hom b)
    let : MorphismProperty.IsStableUnderBaseChange
        (@SmoothOfRelativeDimension 1 : MorphismProperty Scheme.{u}) :=
      smoothOfRelativeDimension_isStableUnderBaseChange 1
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := (@SmoothOfRelativeDimension 1 : MorphismProperty Scheme.{u}))
      (IsPullback.of_hasPullback G.X.hom b) hdim
  have : IsAffineHom H.X.hom := by
    change IsAffineHom (pullback.snd G.X.hom b)
    infer_instance
  have : ConnectedSpace H.X.left := G.connectedSpace_baseChange_of_smooth_affine b
  obtain ⟨hs, hf, hq⟩ := fieldExtension_fpqc k (AlgebraicClosure k)
  let : Surjective b := hs
  let : Flat b := hf
  let : QuasiCompact b := hq
  exact isCommMonObj_of_baseChange b G (isCommMonObj_of_relativeDimension_one H)

end Langlands.GroupScheme
