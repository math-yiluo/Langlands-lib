import Langlands.GroupScheme.SchemeActionAffineOrbitClosure
import Langlands.GroupScheme.SchemeActionReducedClosed
import Langlands.GroupScheme.SchemeActionFiniteTarget
import Langlands.AlgebraicGeometry.FiniteEtale.GeometricFiberFiniteProof
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Proper unipotent actions with invariant affine neighborhoods -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open TopologicalSpace Topology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SchemeAction

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : GroupScheme (Spec (CommRingCat.of k))}
  {X : Over (Spec (CommRingCat.of k))} (a : SchemeAction G X)

/-- Every actual orbit of a rational section has closed underlying image. -/
def HasClosedOrbits : Prop :=
  ∀ x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X, IsClosed (a.orbit x)

variable [Smooth G.X.hom] [IsAffineHom G.X.hom] [LocallyOfFiniteType X.hom]

/-- KR in a neighborhood of the given rational point removes the closure. -/
theorem mem_orbit_of_rational_mem_closure_of_invariantAffineNeighborhoods
    (hKR : UnipotentAffineOrbitClosedStatement.{u}) (hG : IsUnipotent G)
    (hcover : a.HasInvariantAffineNeighborhoods)
    (x y : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X)
    (hxy : y.left (IsLocalRing.closedPoint k) ∈ closure (a.orbit x)) :
    y.left (IsLocalRing.closedPoint k) ∈ a.orbit x := by
  obtain ⟨V, hyV, hVa, hV⟩ := hcover y
  have : IsAffine V := hVa
  have : LocallyOfFiniteType (openSubscheme V).hom := by
    dsimp [openSubscheme]
    infer_instance
  have hxV := a.range_subset_of_closure_orbitImage hV x y hyV hxy
  have hc := hKR k G hG (openSubscheme V) (a.onInvariantOpen hV) (liftToOpen V x hxV)
  change IsClosed (Set.range
    ((a.onInvariantOpen hV).orbitMap (liftToOpen V x hxV)).left) at hc
  have hxyV := a.mem_closure_orbitImage_onInvariantOpen hV x y hxV hyV hxy
  rw [hc.closure_eq] at hxyV
  obtain ⟨g, hg⟩ := hxyV
  refine ⟨g, ?_⟩
  calc
    (a.orbitMap x).left g =
        V.ι (((a.onInvariantOpen hV).orbitMap (liftToOpen V x hxV)).left g) := by
      have ho : ((a.onInvariantOpen hV).orbitMap (liftToOpen V x hxV)).left ≫ V.ι =
          (a.orbitMap x).left :=
        congrArg Over.Hom.left (a.onInvariantOpen_orbitMap_comp hV x hxV)
      rw [← ho, Scheme.Hom.comp_apply]
      rfl
    _ = V.ι ((liftToOpen V y hyV).left (IsLocalRing.closedPoint k)) :=
      congrArg V.ι hg
    _ = y.left (IsLocalRing.closedPoint k) := by
      have hy : (liftToOpen V y hyV).left ≫ V.ι = y.left :=
        congrArg Over.Hom.left (liftToOpen_comp V y hyV)
      exact (Scheme.Hom.comp_apply (liftToOpen V y hyV).left V.ι
        (IsLocalRing.closedPoint k)).symm.trans
          (congrArg (fun f : (Spec (CommRingCat.of k)) ⟶ X.left =>
            f (IsLocalRing.closedPoint k)) hy)

/-- An orbit closure lies in each invariant open containing the original section. -/
theorem closure_orbit_subset_invariantOpen_of_invariantAffineNeighborhoods
    (hKR : UnipotentAffineOrbitClosedStatement.{u}) (hG : IsUnipotent G)
    (hcover : a.HasInvariantAffineNeighborhoods)
    (x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X)
    {V : X.left.Opens} (hV : a.IsInvariantOpen V) (hxV : Set.range x.left ⊆ V) :
    closure (a.orbit x) ⊆ V := by
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  have horbitV : a.orbit x ⊆ V := by
    apply (hV.range_act_subset_iff _ _).mpr
    rintro _ ⟨g, rfl⟩
    rw [Over.comp_left, Scheme.Hom.comp_apply]
    exact hxV ⟨_, rfl⟩
  by_contra h
  obtain ⟨z, hz, hzV⟩ := Set.not_subset.mp h
  have hC : IsClosed (closure (a.orbit x) ∩ (V : Set X.left)ᶜ) :=
    isClosed_closure.inter V.isOpen.isClosed_compl
  obtain ⟨y, hy, hyclosed⟩ := nonempty_inter_closedPoints
    (show (closure (a.orbit x) ∩ (V : Set X.left)ᶜ).Nonempty from
      ⟨z, hz, hzV⟩) hC.isLocallyClosed
  let y' : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X :=
    Over.homMk (pointOfClosedPoint X.hom y hyclosed) (by simp)
  have hy' : y'.left (IsLocalRing.closedPoint k) = y :=
    pointOfClosedPoint_apply _ _ _ _
  have hyorbit := a.mem_orbit_of_rational_mem_closure_of_invariantAffineNeighborhoods
    hKR hG hcover x y' (by rw [hy']; exact hy.1)
  rw [hy'] at hyorbit
  exact hy.2 (horbitV hyorbit)

/-- KR and invariant affine neighborhoods force every rational orbit to be closed. -/
theorem hasClosedOrbits_of_invariantAffineNeighborhoods
    (hKR : UnipotentAffineOrbitClosedStatement.{u}) (hG : IsUnipotent G)
    (hcover : a.HasInvariantAffineNeighborhoods) : a.HasClosedOrbits := by
  intro x
  obtain ⟨V, hxV, hVa, hV⟩ := hcover x
  have : IsAffine V := hVa
  have : LocallyOfFiniteType (openSubscheme V).hom := by
    dsimp [openSubscheme]
    infer_instance
  have hc := hKR k G hG (openSubscheme V) (a.onInvariantOpen hV) (liftToOpen V x hxV)
  change IsClosed (Set.range
    ((a.onInvariantOpen hV).orbitMap (liftToOpen V x hxV)).left) at hc
  have hsubset := a.closure_orbit_subset_invariantOpen_of_invariantAffineNeighborhoods
    hKR hG hcover x hV hxV
  apply isClosed_of_closure_subset
  intro z hz
  let zV : (openSubscheme V).left := ⟨z, hsubset hz⟩
  have hpre : zV ∈ closure (Set.range
      ((a.onInvariantOpen hV).orbitMap (liftToOpen V x hxV)).left) := by
    have hclosure := V.ι.isOpenEmbedding.isEmbedding.closure_eq_preimage_closure_image
      (Set.range ((a.onInvariantOpen hV).orbitMap (liftToOpen V x hxV)).left)
    rw [hclosure]
    have hr : V.ι '' Set.range
        ((a.onInvariantOpen hV).orbitMap (liftToOpen V x hxV)).left = a.orbit x := by
      let o := (a.onInvariantOpen hV).orbitMap (liftToOpen V x hxV)
      have ho : o.left ≫ V.ι = (a.orbitMap x).left :=
        congrArg Over.Hom.left (a.onInvariantOpen_orbitMap_comp hV x hxV)
      have he : V.ι ∘ o.left = (a.orbitMap x).left := by
        funext w
        exact (Scheme.Hom.comp_apply o.left V.ι w).symm.trans (congrFun
          (congrArg (fun f : G.X.left ⟶ X.left => (f : G.X.left → X.left)) ho) w)
      exact (Set.range_comp (f := (o.left : G.X.left → V.toScheme))
        (g := (V.ι : V.toScheme → X.left))).symm.trans (congrArg Set.range he)
    rw [hr]
    exact hz
  rw [hc.closure_eq] at hpre
  obtain ⟨g, hg⟩ := hpre
  refine ⟨g, ?_⟩
  have ho : ((a.onInvariantOpen hV).orbitMap (liftToOpen V x hxV)).left ≫ V.ι =
      (a.orbitMap x).left :=
    congrArg Over.Hom.left (a.onInvariantOpen_orbitMap_comp hV x hxV)
  have he := congrArg (fun f : G.X.left ⟶ X.left => f g) ho
  rw [Scheme.Hom.comp_apply, hg] at he
  exact he.symm

omit [LocallyOfFiniteType X.hom] in
/-- For proper actions, KR and invariant affine neighborhoods imply all-test
fixedness, without a proper solvable fixed-point input. -/
theorem isFixed_of_invariantAffineNeighborhoods_of_kostantRosenlicht
    (hKR : UnipotentAffineOrbitClosedStatement.{u})
    [ConnectedSpace G.X.left] (hG : IsUnipotent G) [IsProper X.hom]
    (hcover : a.HasInvariantAffineNeighborhoods)
    (x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X) : a.IsFixed x := by
  obtain ⟨V, hxV, hVa, hV⟩ := hcover x
  have : IsAffine V := hVa
  obtain ⟨O, j, b, _, hj, hjrange, hb⟩ := a.exists_reduced_orbitClosure x
  have : IsClosedImmersion j.left := hj
  have : IsProper O.hom := by
    rw [← Over.w j]
    infer_instance
  have hjV : Set.range j.left ⊆ V := by
    rw [hjrange]
    exact a.closure_orbit_subset_invariantOpen_of_invariantAffineNeighborhoods
      hKR hG hcover x hV hxV
  let jV := liftToOpen V j hjV
  have : IsClosedImmersion (jV.left ≫ V.ι) := by
    change IsClosedImmersion (jV ≫ openSubschemeι V).left
    rw [liftToOpen_comp]
    infer_instance
  have : IsSeparated V.ι := isSeparated_of_injective V.ι V.ι.injective
  have : IsClosedImmersion jV.left := IsClosedImmersion.of_comp jV.left V.ι
  have : IsAffine O.left := isAffine_of_isAffineHom jV.left
  have : IsFinite O.hom :=
    IsFinite.iff_isProper_and_isAffineHom.mpr ⟨inferInstance, inferInstance⟩
  have := Langlands.AlgebraicGeometry.FiniteEtale.finite_sections_of_isFinite O.hom
  have : Finite (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ O) := by
    apply Finite.of_injective (fun r =>
      (⟨r.left, Over.w r⟩ :
        {r : Spec (CommRingCat.of k) ⟶ O.left // r ≫ O.hom = 𝟙 _}))
    intro r s h
    exact Over.OverMorphism.ext (congrArg Subtype.val h)
  have hxmem : x.left (IsLocalRing.closedPoint k) ∈ a.orbit x := by
    apply (a.mem_rationalOrbit_iff x x).mp
    exact ⟨1, a.act_one x⟩
  have hxO : Set.range x.left ⊆ Set.range j.left := by
    rw [hjrange]
    rintro _ ⟨s, rfl⟩
    rw [@Subsingleton.elim (Spec (CommRingCat.of k)) inferInstance s
      (IsLocalRing.closedPoint k)]
    exact subset_closure hxmem
  have : IsReduced (𝟙_ (Over (Spec (CommRingCat.of k)))).left :=
    inferInstanceAs (IsReduced (Spec (CommRingCat.of k)))
  obtain ⟨r, hr⟩ := FiniteIndexTransfer.exists_lift_of_range_subset j.left x.left hxO
  let xO : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ O := Over.homMk r (by
    rw [← Over.w j, ← Category.assoc, hr]
    exact Over.w x)
  have hxOj : xO ≫ j = x := Over.OverMorphism.ext hr
  have hfix := b.isFixed_of_finite_rationalPoints xO
  intro T t g
  have h := (hb T g (t ≫ xO)).symm.trans
    (congrArg (fun f => f ≫ j) (hfix T t g))
  simpa only [Category.assoc, hxOj] using h

end Langlands.GroupScheme.SchemeAction
