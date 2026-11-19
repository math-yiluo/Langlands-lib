import Langlands.AlgebraicGeometry.AdicClosedImmersionNeighborhood
import Langlands.GroupScheme.HomScheme.CentralAdmissiblePresheaf
import Langlands.GroupScheme.ConnectedFieldOpenProduct
import Langlands.GroupScheme.RelativeIdentityComponent.UnitNeighbourhood
import Langlands.GroupScheme.Torus.RelativeCommutativity
import Langlands.GroupScheme.Torus.SeparatedCentralizerModel

/-! # Reflection of central torus subgroups from adic restrictions -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite IsLocalRing
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.TorusSubgroupModuli

open Langlands.AlgebraicGeometry.UnramifiedFunctor
open SubgroupFunctor
open RelativeIdentityComponent (overPullback_isPullback)

private theorem unitOpen_mul_surjective {S : Scheme.{u}} (G : GroupScheme S)
    [LocallyOfFiniteType G.X.hom] [GeometricallyConnected G.X.hom]
    {U : Over S} (i : U ⟶ G.X) [IsOpenImmersion i.left]
    (hunit : Set.range η[G.X].left ⊆ Set.range i.left) :
    Surjective ((i ⊗ₘ i) ≫ μ[G.X]).left := by
  constructor
  intro x
  let k := G.X.left.residueField x
  let b : Spec (CommRingCat.of k) ⟶ S := G.X.left.fromSpecResidueField x ≫ G.X.hom
  let P := Over.pullback b
  let G' := (baseChange b).obj G
  let i' := P.map i
  have : LocallyOfFiniteType G'.X.hom :=
    MorphismProperty.pullback_snd (P := @LocallyOfFiniteType) _ _ inferInstance
  have : ConnectedSpace G'.X.left :=
    (geometrically_iff_of_isClosedUnderIsomorphisms.mp
      (GeometricallyConnected.geometrically_connectedSpace (f := G.X.hom))) k b
  have : IsOpenImmersion i'.left :=
    MorphismProperty.of_isPullback (overPullback_isPullback b i).flip
      (inferInstanceAs (IsOpenImmersion i.left))
  let e := FiniteEtaleImage.liftOver i η[G.X] hunit
  have hei : e ≫ i = η[G.X] := FiniteEtaleImage.liftOver_fac _ _ _
  let e' : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ P.obj U :=
    Functor.LaxMonoidal.ε P ≫ P.map e
  have hei' : e' ≫ i' = η[G'.X] := by
    change (Functor.LaxMonoidal.ε P ≫ P.map e) ≫ P.map i = _
    rw [Category.assoc, ← P.map_comp, hei]
    rfl
  have hunit' : IdentityComponent.identityPoint G' ∈ Set.range i'.left :=
    ⟨e'.left (closedPoint k), congrArg (fun f => f.left (closedPoint k)) hei'⟩
  let g : Over.mk b ⟶ G.X := Over.homMk (G.X.left.fromSpecResidueField x) rfl
  let x' := (baseChangeBasePointsEquiv b G).symm g
  let y := x'.left (closedPoint k)
  have hy : pullback.fst G.X.hom b y = x := by
    have h := congrArg (fun f : Over.mk b ⟶ G.X => f.left (closedPoint k))
      ((baseChangeBasePointsEquiv b G).apply_symm_apply g)
    rw [baseChangeBasePointsEquiv_left] at h
    exact h.trans (Scheme.fromSpecResidueField_apply _ _)
  obtain ⟨z, hz⟩ := ConnectedFieldOpenProduct.surjective G' i' hunit' y
  let q := (i ⊗ₘ i) ≫ μ[G.X]
  have hmul : RelativeIdentityComponent.fieldOpenProduct G' i' =
      Functor.LaxMonoidal.μ P U U ≫ P.map q := by
    change ((_ ⊗ₘ _) ≫
      (Functor.LaxMonoidal.μ P G.X G.X ≫ P.map μ[G.X])) = _
    rw [← Category.assoc, Functor.LaxMonoidal.μ_natural, Category.assoc, ← P.map_comp]
  let z' := (Functor.LaxMonoidal.μ P U U).left z
  have hz' : (P.map q).left z' = y := by
    change ((Functor.LaxMonoidal.μ P U U ≫ P.map q).left) z = y
    rw [← hmul]
    exact hz
  have hq : (P.map q).left ≫ pullback.fst G.X.hom b =
      pullback.fst (U ⊗ U).hom b ≫ q.left := pullback.lift_fst _ _ _
  refine ⟨pullback.fst (U ⊗ U).hom b z', ?_⟩
  exact (congrArg (fun f : (P.obj (U ⊗ U)).left ⟶ G.X.left => f z') hq).symm.trans
    ((congrArg (pullback.fst G.X.hom b).base hz').trans hy)

set_option maxHeartbeats 1200000 in
/-- For a smooth separated group with geometrically connected fibres over a
noetherian local ring, centrality of a relative torus map is detected on all
maximal-ideal power thickenings. -/
theorem isCentral_of_adicRestrictions {R : CommRingCat.{u}} [IsLocalRing R] [IsNoetherianRing R]
    {G : GroupScheme (Spec R)} [Smooth G.X.hom] [IsSeparated G.X.hom]
    [GeometricallyConnected G.X.hom] {T : CommGroupScheme (Spec R)}
    (j : T.toGrp ⟶ G) (hT : RelativeTorus.IsTorus T.toGrp)
    (h : ∀ n : ℕ, IsCentral ((baseChange (Spec.algebraMap R (R ⧸ maximalIdeal R ^ n))).map j)) :
    IsCentral j := by
  let C := separatedRelativeTorusCentralizerModel j hT
  let c := C.hom.hom.hom.left
  have : IsClosedImmersion c := C.closed
  let x := η[G.X].left (closedPoint R)
  have hx : G.X.hom x = closedPoint R :=
    congrArg (fun f : Spec R ⟶ Spec R => f (closedPoint R)) (Over.w η[G.X])
  have hfac (n : ℕ) :
      ∃ v : pullback G.X.hom (Spec.algebraMap R (R ⧸ maximalIdeal R ^ n)) ⟶ C.group.X.left,
        v ≫ c = pullback.fst G.X.hom (Spec.algebraMap R (R ⧸ maximalIdeal R ^ n)) := by
    let b := Spec.algebraMap R (R ⧸ maximalIdeal R ^ n)
    let G' := (baseChange b).obj G
    let T' := (CommGroupScheme.baseChange b).obj T
    let j' : T'.toGrp ⟶ G' := (baseChange b).map j
    have hrep : (torusCentralizer j').IsRepresentedBy ((baseChange b).map C.hom) := by
      rw [torusCentralizer_baseChange]
      exact C.represents.baseChange b
    have hmem : 𝟙 G'.X ∈ (torusCentralizer j').carrier G'.X :=
      (mem_torusCentralizer j').mpr fun V a y => (commute_of_mem_center (h n V y) (a ≫ 𝟙 _)).symm
    rw [← hrep.2] at hmem
    obtain ⟨v, hv⟩ := mem_range.mp hmem
    refine ⟨v.left ≫ pullback.fst C.group.X.hom b, ?_⟩
    have he := congrArg (fun f : G'.X ⟶ G'.X => f.left ≫ pullback.fst G.X.hom b) hv
    have hm : ((baseChange b).map C.hom).hom.hom.left ≫ pullback.fst G.X.hom b =
        pullback.fst C.group.X.hom b ≫ c := pullback.lift_fst _ _ _
    simpa only [Over.comp_left, Category.assoc, Over.id_left, Category.id_comp, hm] using he
  obtain ⟨W, hxW, v, hv⟩ :=
    Langlands.AlgebraicGeometry.exists_open_factor_of_adicThickenings _ c x hx hfac
  let U : Over (Spec R) := Over.mk (W.ι ≫ G.X.hom)
  let i : U ⟶ G.X := Over.homMk W.ι rfl
  have : IsOpenImmersion i.left := inferInstanceAs (IsOpenImmersion W.ι)
  let d : U ⟶ C.group.X := Over.homMk v (by
    rw [← Over.w C.hom.hom.hom, ← Category.assoc, hv]
    rfl)
  have hd : d ≫ C.hom.hom.hom = i := Over.OverMorphism.ext hv
  have hunit : Set.range η[G.X].left ⊆ Set.range i.left := by
    rintro _ ⟨s, rfl⟩
    refine ⟨⟨η[G.X].left s, ?_⟩, rfl⟩
    exact (specializes_closedPoint s).mem_open
      (W.isOpen.preimage η[G.X].left.continuous) hxW
  let q := (i ⊗ₘ i) ≫ μ[G.X]
  have : Surjective q.left := unitOpen_mul_surjective G i hunit
  have : Smooth q.left := by
    have : IsOpenImmersion (i ⊗ₘ i).left := by
      rw [Over.tensorHom_left]
      exact MorphismProperty.pullbackMap (P := @IsOpenImmersion) inferInstance inferInstance
        i.w.symm i.w.symm
    have : Smooth μ[G.X].left := RelativeIdentityComponent.smooth_multiplication G
    change Smooth ((i ⊗ₘ i).left ≫ μ[G.X].left)
    infer_instance
  let r : U ⊗ U ⟶ C.group.X := (d ⊗ₘ d) ≫ μ[C.group.X]
  have hr : r ≫ C.hom.hom.hom = q := by
    change ((d ⊗ₘ d) ≫ μ[C.group.X]) ≫ C.hom.hom.hom = (i ⊗ₘ i) ≫ μ[G.X]
    rw [Category.assoc, IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc, hd]
  intro V t V' a y
  let Q : Over (Spec R) := Over.mk (pullback.fst y.left q.left ≫ V'.hom)
  let u : Q ⟶ V' := Over.homMk (pullback.fst y.left q.left) rfl
  let w : Q ⟶ U ⊗ U := Over.homMk (pullback.snd y.left q.left) (by
    rw [← Over.w q, ← Category.assoc, ← pullback.condition, Category.assoc, Over.w y]
    rfl)
  have hw : u ≫ y = w ≫ q := Over.OverMorphism.ext pullback.condition
  have hy : u ≫ y ∈ (torusCentralizer j).carrier Q := by
    rw [hw, ← hr]
    have hmem : w ≫ r ≫ C.hom.hom.hom ∈ (range C.hom).carrier Q :=
      mem_range.mpr ⟨w ≫ r, Category.assoc _ _ _⟩
    exact Eq.mp (congrArg (fun F : SubgroupFunctor G =>
      w ≫ r ≫ C.hom.hom.hom ∈ F.carrier Q) C.represents.2) hmem
  have he := ((mem_torusCentralizer j).mp hy Q (𝟙 _) (u ≫ a ≫ t)).symm.eq
  have hcomm : u ≫ ((a ≫ t ≫ j.hom.hom) * y) = u ≫ (y * (a ≫ t ≫ j.hom.hom)) := by
    simpa only [Category.id_comp, Category.assoc, MonObj.comp_mul] using he
  have : Epi u.left := by
    change Epi (pullback.fst y.left q.left)
    exact Flat.epi_of_flat_of_surjective _
  change (a ≫ (t ≫ j.hom.hom)) * y = y * (a ≫ (t ≫ j.hom.hom))
  apply Over.OverMorphism.ext
  apply (cancel_epi u.left).mp
  exact congrArg (fun f => f.left) hcomm

/-- Adic bijectivity of the torus-subgroup presheaf restricts to
its central subpresheaf for a smooth separated group with geometrically
connected fibres. -/
def CentralAdmissibleAdicLimitsTransferStatement : Prop :=
  ∀ {S : Scheme.{u}} (G : GroupScheme S)
    [Smooth G.X.hom] [IsSeparated G.X.hom] [GeometricallyConnected G.X.hom],
    AdicLimits (smallAdmissiblePresheaf G) → AdicLimits (smallCentralAdmissiblePresheaf G)

/-- Apply detection of centrality on the adic restrictions to a lift in the
full admissible presheaf. -/
theorem centralAdmissible_adicLimits_of_admissible :
    CentralAdmissibleAdicLimitsTransferStatement.{u} := by
  intro S G _ _ _ h A _ _ _ _ f
  constructor
  · intro x y hxy
    apply Subtype.ext
    exact (h A f).1 x.val y.val fun n => congrArg Subtype.val (hxy n)
  · intro s hs
    obtain ⟨x, hx⟩ := (h A f).2 (fun n => (s n).val) (fun n => congrArg Subtype.val (hs n))
    let H := (baseChange f).obj G
    let r := admissibleRepresentative (smallAdmissibleEquiv G (Over.mk f) x)
    have hr (n : ℕ) : IsCentral ((baseChange (Spec.algebraMap A (A ⧸ maximalIdeal A ^ n))).map r.hom) :=
      (mem_centralAdmissible_map_iff (algebraOverBase f (A ⧸ maximalIdeal A ^ n)) x).mp
        ((hx n).symm ▸ (s n).property)
    have : Smooth H.X.hom := MorphismProperty.pullback_snd (P := @Smooth) _ _ inferInstance
    have : IsSeparated H.X.hom := MorphismProperty.pullback_snd (P := @IsSeparated) _ _ inferInstance
    have : GeometricallyConnected H.X.hom :=
      MorphismProperty.pullback_snd (P := @GeometricallyConnected) _ _ inferInstance
    let T : CommGroupScheme (Spec (CommRingCat.of A)) :=
      r.torus.commGroupScheme
    have hc : IsCentral r.hom :=
      isCentral_of_adicRestrictions (G := H) (T := T) r.hom r.torus hr
    exact ⟨⟨x, (mem_centralAdmissible_iff x).mpr hc⟩, fun n => Subtype.ext (hx n)⟩

end Langlands.GroupScheme.TorusSubgroupModuli
