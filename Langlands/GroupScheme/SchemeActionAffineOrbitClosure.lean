import Langlands.GroupScheme.SchemeActionInvariantOpen
import Langlands.GroupScheme.SchemeActionRationalOrbit
import Langlands.GroupScheme.UnipotentAffineOrbitClosedStatement

/-! # Invariant affine neighborhoods and orbit closures -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SchemeAction

section AnyBase

variable {S : Scheme.{u}} {H : GroupScheme S} {X : Over S}
variable (a : SchemeAction H X) {V : X.left.Opens}

/-- Every base section has an invariant affine open neighborhood. -/
def HasInvariantAffineNeighborhoods : Prop :=
  ∀ y : 𝟙_ (Over S) ⟶ X,
    ∃ V : X.left.Opens, Set.range y.left ⊆ V ∧ IsAffine V ∧ a.IsInvariantOpen V

/-- The restricted orbit morphism followed by inclusion is the ambient orbit morphism. -/
theorem onInvariantOpen_orbitMap_comp (hV : a.IsInvariantOpen V)
    (x : 𝟙_ (Over S) ⟶ X) (hxV : Set.range x.left ⊆ V) :
    (a.onInvariantOpen hV).orbitMap (liftToOpen V x hxV) ≫ openSubschemeι V =
      a.orbitMap x := by
  rw [orbitMap, onInvariantOpen_act_comp, Category.assoc, liftToOpen_comp]
  rfl

end AnyBase

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {H : GroupScheme (Spec (CommRingCat.of k))}
  {X : Over (Spec (CommRingCat.of k))} (a : SchemeAction H X) {V : X.left.Opens}

omit [IsAlgClosed k] in
/-- An invariant open meeting the closure of an orbit contains the original section. -/
theorem range_subset_of_closure_orbitImage (hV : a.IsInvariantOpen V)
    (x y : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X)
    (hyV : Set.range y.left ⊆ V)
    (hxy : y.left (IsLocalRing.closedPoint k) ∈
      closure (Set.range (a.orbitMap x).left)) : Set.range x.left ⊆ V := by
  obtain ⟨z, hzV, hz⟩ := mem_closure_iff.mp hxy V V.isOpen (hyV ⟨_, rfl⟩)
  obtain ⟨h, rfl⟩ := hz
  have hx := (hV.mem_act_iff (𝟙 H.X) (toUnit H.X ≫ x) h).mp hzV
  rw [Over.comp_left, Scheme.Hom.comp_apply] at hx
  rintro _ ⟨s, rfl⟩
  have hs : (toUnit H.X).left h = s :=
    @Subsingleton.elim (Spec (CommRingCat.of k)) inferInstance _ _
  exact hs ▸ hx

omit [IsAlgClosed k] in
/-- Passing into an invariant open preserves membership in an orbit closure. -/
theorem mem_closure_orbitImage_onInvariantOpen (hV : a.IsInvariantOpen V)
    (x y : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X)
    (hxV : Set.range x.left ⊆ V) (hyV : Set.range y.left ⊆ V)
    (hxy : y.left (IsLocalRing.closedPoint k) ∈
      closure (Set.range (a.orbitMap x).left)) :
    (liftToOpen V y hyV).left (IsLocalRing.closedPoint k) ∈
      closure (Set.range
        ((a.onInvariantOpen hV).orbitMap (liftToOpen V x hxV)).left) := by
  let cp : (𝟙_ (Over (Spec (CommRingCat.of k)))).left := IsLocalRing.closedPoint k
  change y.left cp ∈ closure (Set.range (a.orbitMap x).left) at hxy
  let o := (a.onInvariantOpen hV).orbitMap (liftToOpen V x hxV)
  change (liftToOpen V y hyV).left cp ∈ closure (Set.range o.left)
  have ho : o.left ≫ V.ι = (a.orbitMap x).left :=
    congrArg Over.Hom.left (a.onInvariantOpen_orbitMap_comp hV x hxV)
  have hy : V.ι ((liftToOpen V y hyV).left cp) = y.left cp := by
    have e := congrArg (fun f => f.left cp) (liftToOpen_comp V y hyV)
    change ((liftToOpen V y hyV).left ≫ V.ι) cp = y.left cp at e
    exact (Scheme.Hom.comp_apply (liftToOpen V y hyV).left V.ι cp).symm.trans e
  have hc : closure (Set.range o.left) =
      V.ι ⁻¹' closure (V.ι '' Set.range o.left) :=
    V.ι.isOpenEmbedding.isEmbedding.closure_eq_preimage_closure_image _
  rw [hc]
  change V.ι ((liftToOpen V y hyV).left cp) ∈
    closure (V.ι '' Set.range o.left)
  have he : V.ι ∘ o.left = (a.orbitMap x).left := by
    funext z
    exact (Scheme.Hom.comp_apply o.left V.ι z).symm.trans (congrFun
      (congrArg (fun f : H.X.left ⟶ X.left => (f : H.X.left → X.left)) ho) z)
  have hr : V.ι '' Set.range o.left = Set.range (a.orbitMap x).left := by
    exact (Set.range_comp (f := (o.left : H.X.left → V.toScheme))
      (g := (V.ι : V.toScheme → X.left))).symm.trans (congrArg Set.range he)
  rw [hy, hr]
  exact hxy

/-- KR in an invariant affine neighborhood turns a fixed point in an orbit closure
into fixedness of the original section. -/
theorem isFixed_of_fixed_mem_closure_of_invariantAffineOpen
    (hKR : UnipotentAffineOrbitClosedStatement.{u})
    [Smooth H.X.hom] [IsAffineHom H.X.hom] (hH : IsUnipotent H)
    [LocallyOfFiniteType X.hom] [IsAffine V]
    (hV : a.IsInvariantOpen V)
    {x y : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X}
    (hy : a.IsFixed y) (hyV : Set.range y.left ⊆ V)
    (hxy : y.left (IsLocalRing.closedPoint k) ∈
      closure (Set.range (a.orbitMap x).left)) : a.IsFixed x := by
  have hxV := a.range_subset_of_closure_orbitImage hV x y hyV hxy
  have : LocallyOfFiniteType (openSubscheme V).hom := by
    dsimp [openSubscheme]
    infer_instance
  have hy' := a.isFixed_liftToOpen hV y hy hyV
  have hc := hKR k H hH (openSubscheme V) (a.onInvariantOpen hV) (liftToOpen V x hxV)
  have hxy' := a.mem_closure_orbitImage_onInvariantOpen hV x y hxV hyV hxy
  have hx' := (a.onInvariantOpen hV).isFixed_of_closed_orbitImage hy' hc hxy'
  have hx := (a.isFixed_onInvariantOpen_iff hV _).mp hx'
  simpa only [liftToOpen_comp] using hx

/-- Conditional assembly: invariant affine neighborhoods, KR, and fixed points
in every orbit closure imply all rational sections are all-test fixed. -/
theorem isFixed_of_invariantAffineCover_of_closure_fixedPoint
    (hKR : UnipotentAffineOrbitClosedStatement.{u})
    [Smooth H.X.hom] [IsAffineHom H.X.hom] (hH : IsUnipotent H)
    [LocallyOfFiniteType X.hom]
    (hcover : a.HasInvariantAffineNeighborhoods)
    (hclosure : ∀ x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X,
      ∃ y : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X, a.IsFixed y ∧
        y.left (IsLocalRing.closedPoint k) ∈ closure (Set.range (a.orbitMap x).left))
    (x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X) : a.IsFixed x := by
  obtain ⟨y, hy, hxy⟩ := hclosure x
  obtain ⟨V, hyV, hVAff, hV⟩ := hcover y
  have := hVAff
  exact a.isFixed_of_fixed_mem_closure_of_invariantAffineOpen hKR hH hV hy hyV hxy

end Langlands.GroupScheme.SchemeAction
