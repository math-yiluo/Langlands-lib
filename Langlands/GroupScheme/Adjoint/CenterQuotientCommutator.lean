import Langlands.GroupScheme.CentralIsogeny.SemisimpleTransfer
import Langlands.GroupScheme.Rational.UnipotentSmoothCenter
import Langlands.GroupScheme.Reductive.UnipotentRadicalQuotientReduction
import Langlands.GroupScheme.HomDescent
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement

/-! # Commutators in the preimage of a unipotent subgroup

Let `q : G ⟶ Q` be an fppf quotient of a smooth affine group `G` with trivial unipotent
radical by its full centre, and let `j : C ⟶ Q` be a homomorphism from a smooth connected
affine unipotent group. For a rational point `h` of the preimage `H = q⁻¹(C)` whose image
in `C` is central, the commutator with `h` is a homomorphism from `H` into the centre of `G`
that kills the kernel of `H ⟶ C`; it descends to a central homomorphism from `C`, which is
trivial. Hence such an `h` commutes with all points of `H`. -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry commutatorElement
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.CenterQuotient

section Central

variable {k : Type u} [Field k] {G U : GroupScheme (Spec (CommRingCat.of k))}

/-- **Central unipotent images are trivial.** A central homomorphism from a smooth connected
affine unipotent group to a smooth affine group with trivial unipotent radical is trivial.
Its generated image is smooth, connected and unipotent, and central, hence normal. -/
theorem hom_eq_one_of_isCentral [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (hG : HasTrivialUnipotentRadical G) (f : U ⟶ G) [Smooth U.X.hom] [IsAffineHom U.X.hom]
    [ConnectedSpace U.X.left] (hu : IsUnipotent U) (hf : IsCentral f) : f.hom.hom = 1 := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsAffine U.X.left := isAffine_of_isAffineHom U.X.hom
  have hUint : GeometricallyIntegral U.X.hom :=
    smoothConnectedAffineGeometry.1 k U inferInstance inferInstance inferInstance
  have horigin : (1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ U.X) ≫ f.hom.hom = 1 :=
    MonObj.one_comp _
  obtain ⟨E, hE⟩ := ImageGeneration.pointedImageGeneration k G inferInstance inferInstance
    U.X inferInstance inferInstance hUint 1 f.hom.hom horigin
  have : Smooth E.group.X.hom := hE.1
  have : IsAffineHom E.group.X.hom := hE.2.1
  have : GeometricallyConnected E.group.X.hom := hE.2.2.1
  have hEc : ConnectedSpace E.group.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := E.group.X.hom)
  -- The generated image is unipotent: the factor map is dominant onto a reduced group.
  let p := E.factorGroupHom f
  obtain ⟨n, _hn, hDom⟩ := hE.2.2.2
  have : IsDominant p.hom.hom.left := E.factorGroupHom_isDominant f n hDom
  have : IsReduced E.group.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field k
      E.group.X.left E.group.X.hom
  have : IsSchemeTheoreticallyDominant p.hom.hom.left :=
    IsSchemeTheoreticallyDominant.of_isDominant _
  have : IsAffine E.group.X.left := isAffine_of_isAffineHom E.group.X.hom
  have : QuasiCompact p.hom.hom.left := inferInstance
  have hEu : IsUnipotent E.group :=
    hu.of_appTop_injective p (p.hom.hom.left.app_injective ⊤)
  -- The generated image is central, hence normal.
  have hcent : closedImageEnvelope f.hom.hom ≤ center G :=
    closedImageEnvelope_le_center f.hom.hom hf
  have hEn : (SubgroupFunctor.range E.inclusion).IsNormal := by
    intro T g x _ hx
    rw [E.represents.2] at hx ⊢
    have hc := commute_of_mem_center (hcent T hx) g
    rw [← hc.eq, mul_inv_cancel_right]
    exact hx
  have hEbot := hG E.group E.inclusion E.closed hE.1 hEc hEu hEn
  have hincl : E.inclusion.hom.hom = 1 := by
    have h1 : 𝟙 E.group.X ≫ E.inclusion.hom.hom ∈
        (SubgroupFunctor.range E.inclusion).carrier E.group.X :=
      SubgroupFunctor.mem_range.mpr ⟨𝟙 _, rfl⟩
    rw [hEbot, SubgroupFunctor.bot_carrier, Subgroup.mem_bot, Category.id_comp] at h1
    exact h1
  have h := congrArg (fun g => g.hom.hom) (E.factorGroupHom_comp f)
  change p.hom.hom ≫ E.inclusion.hom.hom = f.hom.hom at h
  rw [← h, hincl, MonObj.comp_one]

end Central

section Commutators

variable {S : Scheme.{u}} {A B : GroupScheme S}

/-- Homomorphisms of group schemes preserve commutators of points. -/
theorem commutatorElement_comp (f : A ⟶ B) {T : Over S} (x y : T ⟶ A.X) :
    ⁅x, y⁆ ≫ f.hom.hom = ⁅x ≫ f.hom.hom, y ≫ f.hom.hom⁆ := by
  simp only [commutatorElement_def, MonObj.mul_comp, GrpObj.inv_comp]

/-- Pulling back along a test-scheme morphism preserves commutators of points. -/
theorem comp_commutatorElement {T T' : Over S} (a : T' ⟶ T) (x y : T ⟶ A.X) :
    a ≫ ⁅x, y⁆ = ⁅a ≫ x, a ≫ y⁆ := by
  simp only [commutatorElement_def, MonObj.comp_mul, GrpObj.comp_inv]

/-- In a group, the commutator with `a` is multiplicative in the second argument as soon as
`⁅a, y⁆` commutes with `x`. -/
theorem commutatorElement_mul_right_of_commute {M : Type*} [Group M] (a x y : M)
    (hc : Commute ⁅a, y⁆ x) : ⁅a, x * y⁆ = ⁅a, x⁆ * ⁅a, y⁆ := by
  have h1 : ⁅a, x * y⁆ = a * x * a⁻¹ * (⁅a, y⁆ * x⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [h1, hc.inv_right.eq, commutatorElement_def a x]
  simp only [mul_assoc]

end Commutators

section Preimage

variable {k : Type u} [Field k] {G Q C : GroupScheme (Spec (CommRingCat.of k))}
  (q : G ⟶ Q) (j : C ⟶ Q)

/-- Points of the preimage whose images in `C` commute have central commutator in `G`. -/
theorem commutator_mem_center (hq : RelativeRoot.IsFppfQuotient (center G) q)
    {T : Over (Spec (CommRingCat.of k))} (a b : T ⟶ (SubgroupPreimage.groupScheme q j).X) (hab : Commute (a ≫ (SubgroupPreimage.projection q j).hom.hom) (b ≫ (SubgroupPreimage.projection q j).hom.hom)) :
    ⁅a ≫ (SubgroupPreimage.inclusion q j).hom.hom, b ≫ (SubgroupPreimage.inclusion q j).hom.hom⁆ ∈ (center G).carrier T := by
  rw [← hq.2.2.2, mem_range_kernelι_iff, commutatorElement_comp, Category.assoc,
    Category.assoc, (SubgroupPreimage.isPullback q j).w, ← Category.assoc a,
    ← Category.assoc b, ← commutatorElement_comp, commutatorElement_eq_one_iff_commute.mpr hab,
    MonObj.one_comp]

/-- Points of the kernel of the projection of the preimage are central in `G`. -/
theorem mem_center_of_comp_projection_eq_one (hq : RelativeRoot.IsFppfQuotient (center G) q)
    {T : Over (Spec (CommRingCat.of k))} (a : T ⟶ (SubgroupPreimage.groupScheme q j).X) (ha : a ≫ (SubgroupPreimage.projection q j).hom.hom = 1) :
    a ≫ (SubgroupPreimage.inclusion q j).hom.hom ∈ (center G).carrier T := by
  rw [← hq.2.2.2, mem_range_kernelι_iff, Category.assoc, (SubgroupPreimage.isPullback q j).w,
    ← Category.assoc, ha, MonObj.one_comp]

variable (hq : RelativeRoot.IsFppfQuotient (center G) q)
  (h : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ (SubgroupPreimage.groupScheme q j).X)
  (hcen : h ≫ (SubgroupPreimage.projection q j).hom.hom ∈ (center C).carrier _)

include hq hcen in
/-- The commutator of `h` with a point of the preimage is central in `G`, because the image
of `h` in `C` is central. -/
theorem commutator_rational_mem_center {T : Over (Spec (CommRingCat.of k))}
    (y : T ⟶ (SubgroupPreimage.groupScheme q j).X) :
    ⁅toUnit T ≫ h ≫ (SubgroupPreimage.inclusion q j).hom.hom, y ≫ (SubgroupPreimage.inclusion q j).hom.hom⁆ ∈ (center G).carrier T := by
  have hab : Commute ((toUnit T ≫ h) ≫ (SubgroupPreimage.projection q j).hom.hom)
      (y ≫ (SubgroupPreimage.projection q j).hom.hom) := by
    rw [Category.assoc]
    exact hcen T (toUnit T) _
  have := commutator_mem_center q j hq (toUnit T ≫ h) y hab
  rwa [Category.assoc] at this

/-- The commutator with the fixed rational point `h` of the preimage, on the points of the
preimage. It is multiplicative because its values are central. -/
def commutatorPoints (T : Over (Spec (CommRingCat.of k))) : (T ⟶ (SubgroupPreimage.groupScheme q j).X) →* (T ⟶ G.X) where
  toFun x := ⁅toUnit T ≫ h ≫ (SubgroupPreimage.inclusion q j).hom.hom, x ≫ (SubgroupPreimage.inclusion q j).hom.hom⁆
  map_one' := by
    rw [MonObj.one_comp, commutatorElement_one_right]
  map_mul' x y := by
    rw [MonObj.mul_comp]
    exact commutatorElement_mul_right_of_commute _ _ _ (commute_of_mem_center
      (commutator_rational_mem_center q j hq h hcen y) (x ≫ (SubgroupPreimage.inclusion q j).hom.hom))

theorem commutatorPoints_apply (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ (SubgroupPreimage.groupScheme q j).X) :
    commutatorPoints q j hq h hcen T x = ⁅toUnit T ≫ h ≫ (SubgroupPreimage.inclusion q j).hom.hom, x ≫ (SubgroupPreimage.inclusion q j).hom.hom⁆ :=
  rfl

theorem commutatorPoints_naturality {T T' : Over (Spec (CommRingCat.of k))} (a : T' ⟶ T)
    (x : T ⟶ (SubgroupPreimage.groupScheme q j).X) :
    commutatorPoints q j hq h hcen T' (a ≫ x) = a ≫ commutatorPoints q j hq h hcen T x := by
  rw [commutatorPoints_apply, commutatorPoints_apply, comp_commutatorElement,
    ← Category.assoc a (toUnit T), comp_toUnit, Category.assoc]

/-- The commutator homomorphism `x ↦ ⁅h, x⁆` from the preimage to `G`. -/
def commutatorHom : SubgroupPreimage.groupScheme q j ⟶ G :=
  homOfPoints (commutatorPoints q j hq h hcen) (commutatorPoints_naturality q j hq h hcen)

theorem comp_commutatorHom {T : Over (Spec (CommRingCat.of k))} (x : T ⟶ (SubgroupPreimage.groupScheme q j).X) :
    x ≫ (commutatorHom q j hq h hcen).hom.hom = ⁅toUnit T ≫ h ≫ (SubgroupPreimage.inclusion q j).hom.hom, x ≫ (SubgroupPreimage.inclusion q j).hom.hom⁆ :=
  comp_homOfPoints _ _ T x

theorem range_commutatorHom_le_center :
    SubgroupFunctor.range (commutatorHom q j hq h hcen) ≤ center G := by
  intro T x hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  rw [comp_commutatorHom]
  exact commutator_rational_mem_center q j hq h hcen y

include hq hcen

/-- **Rational points over central points are central in the preimage.** For a smooth affine
`G` with trivial unipotent radical, an fppf quotient `q` of `G` by its centre with affine
target, and a smooth connected affine unipotent `C ⟶ Q`, a rational point of the preimage `H`
with central image in `C` commutes in `G` with every point of `H`. -/
theorem commute_preimage [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (hG : HasTrivialUnipotentRadical G) [IsAffineHom Q.X.hom] [Smooth C.X.hom]
    [IsAffineHom C.X.hom] [ConnectedSpace C.X.left] (hu : IsUnipotent C)
    {T : Over (Spec (CommRingCat.of k))} (x : T ⟶ (SubgroupPreimage.groupScheme q j).X) :
    Commute (toUnit T ≫ h ≫ (SubgroupPreimage.inclusion q j).hom.hom) (x ≫ (SubgroupPreimage.inclusion q j).hom.hom) := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsAffine Q.X.left := isAffine_of_isAffineHom Q.X.hom
  have : Flat q.hom.hom.left := hq.1
  have : Surjective q.hom.hom.left := hq.2.1
  have : QuasiCompact q.hom.hom.left := inferInstance
  have : Flat (SubgroupPreimage.projection q j).hom.hom.left := SubgroupPreimage.flat_projection q j
  have : Surjective (SubgroupPreimage.projection q j).hom.hom.left := SubgroupPreimage.surjective_projection q j
  have : QuasiCompact (SubgroupPreimage.projection q j).hom.hom.left :=
    MorphismProperty.of_isPullback (SubgroupPreimage.isPullback_scheme q j) inferInstance
  obtain ⟨Z, z, hzc, hz⟩ := center_hasClosedRepresentative (G := G)
  have : Mono z.hom.hom := hz.1
  set ψ := commutatorHom q j hq h hcen with hψ
  have hψc : SubgroupFunctor.range ψ ≤ SubgroupFunctor.range z := by
    rw [hz.2]
    exact range_commutatorHom_le_center q j hq h hcen
  let ψ' : SubgroupPreimage.groupScheme q j ⟶ Z := SubgroupFunctor.IsRepresentedBy.factorHom hz ψ (hz.2 ▸ hψc)
  have hψ' : ψ' ≫ z = ψ := SubgroupFunctor.IsRepresentedBy.factorHom_comp hz ψ _
  have hk : kernelι (SubgroupPreimage.projection q j) ≫ ψ' = 0 := by
    apply Grp.hom_ext
    change (kernelι (SubgroupPreimage.projection q j)).hom.hom ≫ ψ'.hom.hom = 1
    apply (cancel_mono z.hom.hom).mp
    have hψψ : ψ'.hom.hom ≫ z.hom.hom = ψ.hom.hom :=
      congrArg (fun g => g.hom.hom) hψ'
    rw [Category.assoc, hψψ, MonObj.one_comp, hψ, comp_commutatorHom,
      commutatorElement_eq_one_iff_commute]
    refine (commute_of_mem_center
      (mem_center_of_comp_projection_eq_one q j hq _ ?_) _).symm
    exact (mem_range_kernelι_iff (SubgroupPreimage.projection q j) _).mp
      (SubgroupFunctor.mem_range.mpr ⟨𝟙 _, Category.id_comp _⟩)
  let d : C ⟶ Z := FpqcHomDescent.hom (SubgroupPreimage.projection q j) ψ' hk
  have hd : SubgroupPreimage.projection q j ≫ d = ψ' := FpqcHomDescent.fac _ _ _
  have hcent : IsCentral (d ≫ z) := by
    intro T' v
    rw [← hz.2, Grp.comp_hom_hom, ← Category.assoc]
    exact SubgroupFunctor.mem_range.mpr ⟨_, rfl⟩
  have h1 := hom_eq_one_of_isCentral hG (d ≫ z) hu hcent
  have hψ1 : ψ.hom.hom = 1 := by
    have : ψ = SubgroupPreimage.projection q j ≫ (d ≫ z) := by
      rw [← Category.assoc, hd, hψ']
    rw [this, Grp.comp_hom_hom, h1, MonObj.comp_one]
  have hx := comp_commutatorHom q j hq h hcen x
  rw [← hψ, hψ1, MonObj.comp_one] at hx
  exact commutatorElement_eq_one_iff_commute.mp hx.symm

/-- In particular such a rational point commutes in `G` with the rational points of `H`. -/
theorem commute_rational_preimage [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (hG : HasTrivialUnipotentRadical G) [IsAffineHom Q.X.hom] [Smooth C.X.hom]
    [IsAffineHom C.X.hom] [ConnectedSpace C.X.left] (hu : IsUnipotent C)
    (h' : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ (SubgroupPreimage.groupScheme q j).X) :
    Commute (h ≫ (SubgroupPreimage.inclusion q j).hom.hom) (h' ≫ (SubgroupPreimage.inclusion q j).hom.hom) := by
  have := commute_preimage q j hq h hcen hG hu h'
  have e : toUnit (Over.mk (𝟙 (Spec (CommRingCat.of k)))) ≫ h = h := by
    have e0 : toUnit (Over.mk (𝟙 (Spec (CommRingCat.of k)))) =
        (𝟙 (Over.mk (𝟙 (Spec (CommRingCat.of k)))) : _ ⟶ 𝟙_ _) :=
      toUnit_unique _ _
    rw [e0, Category.id_comp]
  rwa [← Category.assoc, e] at this

omit hcen in
/-- **Rational points over central points commute.** Two rational points of `G` whose images
in `Q` are images of rational points of `C`, the first of which is central in `C`, commute. -/
theorem commute_of_lift [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (hG : HasTrivialUnipotentRadical G) [IsAffineHom Q.X.hom] [Smooth C.X.hom]
    [IsAffineHom C.X.hom] [ConnectedSpace C.X.left] (hu : IsUnipotent C)
    {x x' : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X}
    {c c' : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ C.X}
    (hx : x ≫ q.hom.hom = c ≫ j.hom.hom) (hx' : x' ≫ q.hom.hom = c' ≫ j.hom.hom)
    (hc : c ∈ (center C).carrier _) : Commute x x' := by
  have hl := (SubgroupPreimage.isPullback q j).lift_fst x c hx
  have hl' := (SubgroupPreimage.isPullback q j).lift_fst x' c' hx'
  have hcen' : (SubgroupPreimage.isPullback q j).lift x c hx ≫
      (SubgroupPreimage.projection q j).hom.hom ∈ (center C).carrier _ := by
    rwa [(SubgroupPreimage.isPullback q j).lift_snd]
  have := commute_rational_preimage q j hq _ hcen' hG hu
    ((SubgroupPreimage.isPullback q j).lift x' c' hx')
  rwa [hl, hl'] at this

end Preimage

end Langlands.GroupScheme.CenterQuotient
