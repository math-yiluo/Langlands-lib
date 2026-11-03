import Langlands.GroupScheme.IdentityComponent
import Langlands.GroupScheme.Absolute.ParabolicTransport
import Langlands.AlgebraicGeometry.ClosedPointHomogeneousSmoothProof
import Langlands.AlgebraicGeometry.SmoothReducedProof
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_isReduced_subscheme_vanishingIdeal_and_le_ker

/-! # The reduced subgroup and its identity component

For a group scheme `S` locally of finite type over an algebraically closed field `k`, the
reduced closed subscheme `S_red` is a smooth closed subgroup of `S`, and its identity component
`(S_red)⁰` is a smooth connected closed subgroup, open in `S`, through which every smooth
connected closed subgroup contained in `S` factors.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.ReducedSubgroup

/-! ### The reduced closed subscheme of a scheme -/

section Scheme

variable (X : Scheme.{u})

/-- The reduced closed subscheme of `X`: the closed subscheme cut out by the vanishing ideal of
the whole space (the nilradical). -/
abbrev red : Scheme.{u} :=
  (Scheme.IdealSheafData.vanishingIdeal (⊤ : TopologicalSpace.Closeds X)).subscheme

/-- The inclusion of the reduced closed subscheme. -/
def redι : red X ⟶ X :=
  (Scheme.IdealSheafData.vanishingIdeal (⊤ : TopologicalSpace.Closeds X)).subschemeι

instance : IsClosedImmersion (redι X) := by
  unfold redι
  infer_instance

instance : IsReduced (red X) :=
  (Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal_and_le_ker
    (⊤ : TopologicalSpace.Closeds X)).1

theorem range_redι : Set.range (redι X) = Set.univ := by
  rw [redι, Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.vanishingIdeal_top,
    Scheme.support_nilradical]
  rfl

theorem redι_surjective : Function.Surjective (redι X) :=
  Set.range_eq_univ.mp (range_redι X)

theorem redι_injective : Function.Injective (redι X) :=
  (redι X).isClosedEmbedding.injective

/-- The inclusion of the reduced closed subscheme maps open sets to open sets. -/
theorem isOpen_image_redι {U : Set (red X)} (hU : IsOpen U) : IsOpen ((redι X) '' U) := by
  obtain ⟨V, hV, rfl⟩ := (redι X).isClosedEmbedding.isInducing.isOpen_iff.mp hU
  rwa [Set.image_preimage_eq V (redι_surjective X)]

variable {X} {T : Scheme.{u}} [IsReduced T] (f : T ⟶ X)

theorem ker_redι_le : (redι X).ker ≤ f.ker := by
  rw [redι, Scheme.IdealSheafData.ker_subschemeι]
  exact (Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal_and_le_ker
    (⊤ : TopologicalSpace.Closeds X)).2 f (by simp)

/-- A morphism from a reduced scheme factors through the reduced closed subscheme. -/
def redLift : T ⟶ red X :=
  IsClosedImmersion.lift (redι X) f (ker_redι_le f)

@[reassoc (attr := simp)]
theorem redLift_fac : redLift f ≫ redι X = f :=
  IsClosedImmersion.lift_fac _ _ _

/-- An isomorphism of schemes restricts to an isomorphism of their reduced closed
subschemes. -/
def redIso {X Y : Scheme.{u}} (e : X ≅ Y) : red X ≅ red Y where
  hom := redLift (redι X ≫ e.hom)
  inv := redLift (redι Y ≫ e.inv)
  hom_inv_id := by
    rw [← cancel_mono (redι X)]
    simp
  inv_hom_id := by
    rw [← cancel_mono (redι Y)]
    simp

@[reassoc (attr := simp)]
theorem redIso_hom_redι {X Y : Scheme.{u}} (e : X ≅ Y) :
    (redIso e).hom ≫ redι Y = redι X ≫ e.hom :=
  redLift_fac _

end Scheme

/-! ### The reduced subgroup of a group scheme over a field -/

section Over

variable {k : Type u} [Field k] (S : GroupScheme (Spec (CommRingCat.of k)))

/-- The reduced closed subscheme of `S`, as a scheme over `k`. -/
abbrev redOver : Over (Spec (CommRingCat.of k)) :=
  Over.mk (redι S.X.left ≫ S.X.hom)

/-- The inclusion of `S_red` into `S`, over `k`. -/
abbrev redOverι : redOver S ⟶ S.X :=
  Over.homMk (redι S.X.left)

instance : IsClosedImmersion (redOverι S).left :=
  inferInstanceAs (IsClosedImmersion (redι S.X.left))

instance : Mono (redOverι S) := Over.mono_of_mono_left _

variable {S} in
/-- A morphism over `k` from a scheme with reduced underlying scheme into `S` factors through
`S_red`. -/
def liftOver {P : Over (Spec (CommRingCat.of k))} [IsReduced P.left] (g : P ⟶ S.X) :
    P ⟶ redOver S :=
  Over.homMk (redLift g.left) (by
    change redLift g.left ≫ redι S.X.left ≫ S.X.hom = P.hom
    rw [redLift_fac_assoc, Over.w g])

variable {S} in
@[reassoc (attr := simp)]
theorem liftOver_fac {P : Over (Spec (CommRingCat.of k))} [IsReduced P.left] (g : P ⟶ S.X) :
    liftOver g ≫ redOverι S = g := by
  ext1
  exact redLift_fac g.left

/-- In a group object, right translation by `x⁻¹ * y` sends the point `x` to the point `y`. -/
theorem point_comp_mulRight
    {C : Type*} [Category C] [CartesianMonoidalCategory C] {A : C} [GrpObj A]
    (x y : 𝟙_ C ⟶ A) :
    x ≫ ((GrpObj.mulRight x).symm ≪≫ GrpObj.mulRight y).hom = y := by
  dsimp only [Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, ← Iso.eq_comp_inv]
  simp [GrpObj.mulRight, comp_lift_assoc]

section AlgClosed

variable [IsAlgClosed k] [LocallyOfFiniteType S.X.hom]

/-- Automorphisms of `S` over `k` act transitively on the closed points of `S`: right
translation by `x⁻¹ y` sends `x` to `y`. -/
theorem exists_translation (x y : S.X.left) (hx : IsClosed ({x} : Set S.X.left))
    (hy : IsClosed ({y} : Set S.X.left)) :
    ∃ β : S.X.left ≅ S.X.left, β.hom ≫ S.X.hom = S.X.hom ∧ β.hom x = y := by
  let x' : 𝟙_ _ ⟶ S.X := Over.homMk _ ((pointEquivClosedPoint S.X.hom).symm ⟨x, hx⟩).2
  let y' : 𝟙_ _ ⟶ S.X := Over.homMk _ ((pointEquivClosedPoint S.X.hom).symm ⟨y, hy⟩).2
  let α := (GrpObj.mulRight x').symm ≪≫ GrpObj.mulRight y'
  have hα : x' ≫ α.hom = y' := point_comp_mulRight x' y'
  have hx' : x'.left (IsLocalRing.closedPoint k) = x :=
    congrArg Subtype.val ((pointEquivClosedPoint S.X.hom).apply_symm_apply ⟨x, hx⟩)
  have hy' : y'.left (IsLocalRing.closedPoint k) = y :=
    congrArg Subtype.val ((pointEquivClosedPoint S.X.hom).apply_symm_apply ⟨y, hy⟩)
  have h := congrArg
    (fun f : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ S.X => f.left (IsLocalRing.closedPoint k)) hα
  refine ⟨(Over.forget _).mapIso α, Over.w α.hom, ?_⟩
  change α.hom.left x = y
  rw [← hx', ← hy']
  exact h

instance : LocallyOfFiniteType (redOver S).hom :=
  inferInstanceAs (LocallyOfFiniteType (redι S.X.left ≫ S.X.hom))

instance : IsReduced (redOver S).left :=
  inferInstanceAs (IsReduced (red S.X.left))

/-- `S_red` is smooth over `k`: right translations by `k`-points of `S` restrict to
automorphisms of `S_red` acting transitively on closed points. -/
instance smooth_redOver : Smooth (redOver S).hom := by
  refine Langlands.AlgebraicGeometry.closedPointHomogeneousSmooth k (red S.X.left)
    (redOver S).hom ?_
  intro x y hx hy
  have hx' : IsClosed ({redι S.X.left x} : Set S.X.left) := by
    rw [← Set.image_singleton]
    exact (redι S.X.left).isClosedEmbedding.isClosedMap _ hx
  have hy' : IsClosed ({redι S.X.left y} : Set S.X.left) := by
    rw [← Set.image_singleton]
    exact (redι S.X.left).isClosedEmbedding.isClosedMap _ hy
  obtain ⟨β, hβ, hβxy⟩ := exists_translation S _ _ hx' hy'
  refine ⟨redIso β, ?_, ?_⟩
  · change (redIso β).hom ≫ redι S.X.left ≫ S.X.hom = redι S.X.left ≫ S.X.hom
    rw [redIso_hom_redι_assoc, hβ]
  · apply redι_injective
    rw [← Scheme.Hom.comp_apply, redIso_hom_redι, Scheme.Hom.comp_apply]
    exact hβxy

instance : IsReduced (redOver S ⊗ redOver S).left := by
  have : Smooth (redOver S ⊗ redOver S).hom := by
    change Smooth (pullback.fst (redOver S).hom (redOver S).hom ≫ (redOver S).hom)
    infer_instance
  exact Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field k _
    (redOver S ⊗ redOver S).hom

instance : IsReduced (𝟙_ (Over (Spec (CommRingCat.of k)))).left :=
  inferInstanceAs (IsReduced (Spec (CommRingCat.of k)))

/-- The unit of `S_red`. -/
def redOne : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ redOver S :=
  liftOver η[S.X]

omit [IsAlgClosed k] [LocallyOfFiniteType S.X.hom] in
@[reassoc (attr := simp)]
theorem redOne_fac : redOne S ≫ redOverι S = η[S.X] :=
  liftOver_fac _

/-- The multiplication of `S_red`: the restriction of the multiplication of `S`. -/
def redMul : redOver S ⊗ redOver S ⟶ redOver S :=
  liftOver ((redOverι S ⊗ₘ redOverι S) ≫ μ[S.X])

@[reassoc (attr := simp)]
theorem redMul_fac : redMul S ≫ redOverι S = (redOverι S ⊗ₘ redOverι S) ≫ μ[S.X] :=
  liftOver_fac _

/-- The inverse of `S_red`: the restriction of the inverse of `S`. -/
def redInv : redOver S ⟶ redOver S :=
  liftOver (redOverι S ≫ ι[S.X])

omit [IsAlgClosed k] [LocallyOfFiniteType S.X.hom] in
@[reassoc (attr := simp)]
theorem redInv_fac : redInv S ≫ redOverι S = redOverι S ≫ ι[S.X] :=
  liftOver_fac _

instance grpObj_redOver : GrpObj (redOver S) :=
  Langlands.CategoryTheory.GroupObjectDescent.grpObjOfMono
    (redOverι S) (redOne S) (redMul S) (redInv S) (redOne_fac S) (redMul_fac S) (redInv_fac S)

instance : IsMonHom (redOverι S) :=
  Langlands.CategoryTheory.GroupObjectDescent.isMonHom_grpObjOfMono
    (redOverι S) (redOne S) (redMul S) (redInv S) (redOne_fac S) (redMul_fac S) (redInv_fac S)

/-- The reduced subgroup `S_red` of `S`. -/
abbrev _root_.Langlands.GroupScheme.reducedSubgroup : GroupScheme (Spec (CommRingCat.of k)) :=
  { X := redOver S }

/-- The inclusion `S_red ⟶ S`. -/
def _root_.Langlands.GroupScheme.reducedSubgroupι : reducedSubgroup S ⟶ S :=
  Grp.homMk (redOverι S)

@[simp]
theorem reducedSubgroupι_hom_hom : (reducedSubgroupι S).hom.hom = redOverι S :=
  rfl

instance isClosedImmersion_reducedSubgroupι :
    IsClosedImmersion (reducedSubgroupι S).hom.hom.left :=
  inferInstanceAs (IsClosedImmersion (redι S.X.left))

instance smooth_reducedSubgroup : Smooth (reducedSubgroup S).X.hom :=
  smooth_redOver S

instance isAffineHom_reducedSubgroup [IsAffineHom S.X.hom] :
    IsAffineHom (reducedSubgroup S).X.hom :=
  inferInstanceAs (IsAffineHom (redι S.X.left ≫ S.X.hom))

section Lift

variable {S} {K : GroupScheme (Spec (CommRingCat.of k))} [IsReduced K.X.left] (g : K ⟶ S)

/-- The factorization over `k` through `S_red` of a homomorphism from a group scheme with
reduced underlying scheme. -/
def liftHomOver : K.X ⟶ redOver S :=
  liftOver g.hom.hom

omit [IsAlgClosed k] [LocallyOfFiniteType S.X.hom] in
@[reassoc (attr := simp)]
theorem liftHomOver_fac : liftHomOver g ≫ redOverι S = g.hom.hom :=
  liftOver_fac _

instance : IsMonHom (liftHomOver g) where
  one_hom := by
    apply (cancel_mono (redOverι S)).mp
    rw [Category.assoc, liftHomOver_fac, IsMonHom.one_hom, IsMonHom.one_hom]
  mul_hom := by
    apply (cancel_mono (redOverι S)).mp
    rw [Category.assoc, liftHomOver_fac, IsMonHom.mul_hom, Category.assoc, IsMonHom.mul_hom,
      tensorHom_comp_tensorHom_assoc, liftHomOver_fac]

/-- The factorization through `S_red` of a homomorphism from a group scheme with reduced
underlying scheme. -/
def liftHom : K ⟶ reducedSubgroup S :=
  Grp.homMk (liftHomOver g)

@[reassoc (attr := simp)]
theorem liftHom_fac : liftHom g ≫ reducedSubgroupι S = g :=
  Grp.hom_ext _ _ (liftHomOver_fac g)

end Lift

end AlgClosed

end Over

/-! ### The identity component of the reduced subgroup -/

section IdentityComponent

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Every closed subgroup `S` of an affine group scheme `G` locally of finite type over an
algebraically closed field contains a smooth connected closed subgroup `H = (S_red)⁰`, open in
`S`, through which every smooth connected closed subgroup of `G` contained in `S` factors. -/
theorem exists_reducedIdentityComponent {G S : GroupScheme (Spec (CommRingCat.of k))}
    [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom] (iS : S ⟶ G)
    (hS : IsClosedSubgroup iS) :
    ∃ (H : GroupScheme (Spec (CommRingCat.of k))) (f : H ⟶ S),
      IsClosedSubgroup (f ≫ iS) ∧ Smooth H.X.hom ∧ ConnectedSpace H.X.left ∧
        IsOpen (Set.range f.hom.hom.left) ∧
        ∀ (K : GroupScheme (Spec (CommRingCat.of k))) (iK : K ⟶ G),
          IsClosedSubgroup iK → Smooth K.X.hom → ConnectedSpace K.X.left →
            SubgroupFunctor.range iK ≤ SubgroupFunctor.range iS →
              ∃ e : K ⟶ H, e ≫ f ≫ iS = iK := by
  have : IsClosedImmersion iS.hom.hom.left := hS
  have : LocallyOfFiniteType S.X.hom := by
    rw [← Over.w iS.hom.hom]
    infer_instance
  have : IsAffineHom S.X.hom := by
    rw [← Over.w iS.hom.hom]
    infer_instance
  have : Mono iS.hom.hom := Over.mono_of_mono_left _
  have : Smooth (reducedSubgroup S).X.hom := smooth_reducedSubgroup S
  have : IsAffineHom (reducedSubgroup S).X.hom := isAffineHom_reducedSubgroup S
  refine ⟨identityComponent (reducedSubgroup S),
    identityComponentι (reducedSubgroup S) ≫ reducedSubgroupι S, ?_,
    IdentityComponent.smooth_identityComponent _,
    IdentityComponent.connectedSpace_identityComponent _, ?_, ?_⟩
  · change IsClosedImmersion ((identityComponentι (reducedSubgroup S)).hom.hom.left ≫
      (redι S.X.left ≫ iS.hom.hom.left))
    infer_instance
  · change IsOpen (Set.range
      ((identityComponentι (reducedSubgroup S)).hom.hom.left ≫ redι S.X.left))
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    exact isOpen_image_redι _
      (IsOpenImmersion.isOpen_range (identityComponentι (reducedSubgroup S)).hom.hom.left)
  · intro K iK hK hKs hKc hle
    have : IsClosedImmersion iK.hom.hom.left := hK
    have : Mono iK.hom.hom := Over.mono_of_mono_left _
    have : IsReduced K.X.left :=
      Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field k _ K.X.hom
    obtain ⟨g, hg⟩ := SubgroupFunctor.exists_factor_of_range_le hle
    refine ⟨IdentityComponent.factor (reducedSubgroup S) (liftHom g), ?_⟩
    rw [Category.assoc, IdentityComponent.factor_identityComponentι_assoc, liftHom_fac_assoc, hg]

end IdentityComponent

end Langlands.GroupScheme.ReducedSubgroup
