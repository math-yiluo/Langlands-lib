import Langlands.GroupScheme.Absolute.StronglyRegularTorusPointProof
import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerProof
import Langlands.GroupScheme.Cartan.ConjugacyDensityProof
import Langlands.GroupScheme.ClosedOrbitProof
import Langlands.GroupScheme.PointCentralizer
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-! # A nonempty open of strongly regular points -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry Topology TopologicalSpace
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Over an algebraically closed field there is a nonempty open subset of a
connected reductive group whose rational points have maximal torus centralizers. -/
def StronglyRegularGroupOpenStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
    ∃ V : Set G.X.left, IsOpen V ∧ V.Nonempty ∧
      ∀ x : rationalPoints G, Set.range x.left ⊆ V →
        ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (j : T.toGrp ⟶ G),
          IsMaximalTorus j ∧ SubgroupFunctor.range j = G.pointCentralizer x

namespace StronglyRegularGroupOpen

variable {k : Type u} [Field k] [IsAlgClosed k]

private theorem exists_point_lift_in_open {X Y : Scheme.{u}}
    (f : X ⟶ Y) [LocallyOfFiniteType f] (U : Set X) (hU : IsOpen U)
    (x : Spec (CommRingCat.of k) ⟶ Y) (hx : x (IsLocalRing.closedPoint k) ∈ f '' U) :
    ∃ z : Spec (CommRingCat.of k) ⟶ X, z ≫ f = x ∧ Set.range z ⊆ U := by
  let p := pullback.snd f x
  let q := pullback.fst f x
  have : JacobsonSpace ↥(pullback f x : Scheme.{u}) := LocallyOfFiniteType.jacobsonSpace p
  obtain ⟨a, ha, hax⟩ := hx
  obtain ⟨b, hb, -⟩ :=
    Scheme.Pullback.exists_preimage_pullback (f := f) (g := x) a (IsLocalRing.closedPoint k) hax
  have hne : (q ⁻¹' U).Nonempty := ⟨b, by change q b ∈ U; rw [show q b = a from hb]; exact ha⟩
  obtain ⟨c, hc, hcl⟩ := nonempty_inter_closedPoints (Z := q ⁻¹' U) hne
    (hU.preimage q.continuous).isLocallyClosed
  have hcClosed : IsClosed ({c} : Set ↥(pullback f x : Scheme.{u})) := hcl
  refine ⟨pointOfClosedPoint p c hcClosed ≫ q, ?_, ?_⟩
  · rw [Category.assoc, show q ≫ f = p ≫ x from pullback.condition, ← Category.assoc,
      pointOfClosedPoint_comp, Category.id_comp]
  · rintro _ ⟨z, rfl⟩
    rw [Scheme.Hom.comp_apply, pointOfClosedPoint_apply]
    exact hc

variable {G : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))} (j : T.toGrp ⟶ G)

omit [IsAlgClosed k] in
private theorem pointCentralizer_conj_eq
    (g : rationalPoints G) (t : rationalPoints T.toGrp)
    (ht : ∀ {Z : Over (Spec (CommRingCat.of k))} (c : Z ⟶ G.X),
      c * (toUnit Z ≫ t ≫ j.hom.hom) = (toUnit Z ≫ t ≫ j.hom.hom) * c →
        ∃ s : Z ⟶ T.X, s ≫ j.hom.hom = c) :
    SubgroupFunctor.range (j ≫ (G.innerIso g).hom) =
      G.pointCentralizer (g * (t ≫ j.hom.hom) * g⁻¹) := by
  apply range_eq_pointCentralizer
  intro Z c hc
  rw [MaximalTorusParameterExistence.mem_range_comp_innerIso_iff, SubgroupFunctor.mem_range]
  apply ht
  let a := G.constantPoint g Z
  let d := toUnit Z ≫ t ≫ j.hom.hom
  rw [mem_pointCentralizer, MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv] at hc
  change c * (a * d * a⁻¹) = (a * d * a⁻¹) * c at hc
  change (a⁻¹ * c * a) * d = d * (a⁻¹ * c * a)
  calc
    _ = a⁻¹ * (c * (a * d * a⁻¹)) * a := by group
    _ = a⁻¹ * ((a * d * a⁻¹) * c) * a := by rw [hc]
    _ = _ := by group

end StronglyRegularGroupOpen

open StronglyRegularGroupOpen in
set_option backward.isDefEq.respectTransparency false in
/-- Conjugating the strongly regular open of a maximal torus gives a
constructible dense image, containing a nonempty open of the group. -/
theorem stronglyRegularGroupOpen : StronglyRegularGroupOpenStatement.{u} := by
  intro k _ _ G hG
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : ConnectedSpace G.X.left := hG.connectedSpace
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsLocallyNoetherian G.X.left := LocallyOfFiniteType.isLocallyNoetherian G.X.hom
  let : IsNoetherian G.X.left := AlgebraicGeometry.IsNoetherian.mk
  obtain ⟨T, j, hj⟩ := TorusExistence.exists_isMaximalTorus G
  obtain ⟨U, hU, hUne, htU⟩ := algClosedStronglyRegularTorusPoint k G hG T j hj
  let : Smooth T.X.hom := hj.1.smooth
  let : IsIntegral T.X.left := hj.1.isIntegral
  let : IsAffineHom T.X.hom := hj.2.1.isAffineHom
  let : IsAffine T.X.left := isAffine_of_isAffineHom T.X.hom
  let Z := G.X ⊗ T.X
  let s := snd G.X T.X
  let D := s.left ⁻¹' U
  let con := BorelPointContainment.conjugation j
  have : Smooth s.left := inferInstanceAs (Smooth (pullback.snd G.X.hom T.X.hom))
  have : Smooth Z.hom := smooth_tensor G.X T.X inferInstance inferInstance
  let : IsAffine Z.left := inferInstanceAs (IsAffine (pullback G.X.hom T.X.hom))
  let : IsLocallyNoetherian Z.left := LocallyOfFiniteType.isLocallyNoetherian Z.hom
  let : IsNoetherian Z.left := AlgebraicGeometry.IsNoetherian.mk
  have : LocallyOfFinitePresentation con.left :=
    Langlands.AlgebraicGeometry.TangentSmoothness.locallyOfFinitePresentation_of_comp_eq
      con.left (Over.w con)
  have hD : IsOpen D := hU.preimage s.left.continuous
  have dD : Dense D := (hU.dense hUne).preimage s.left.isOpenMap
  obtain ⟨A, -, hAd, hAcon⟩ := CartanConjugacyDensity.exists_isOpen_dense_subset_range_conjugation
    (hj.isCartanSubgroup_of_centralizerStatement maximalTorusCentralizer hG)
  have dcon : DenseRange con.left := hAd.mono hAcon
  have hconstruct : IsConstructible (con.left '' D) :=
    con.left.isConstructible_image ((NoetherianSpace.isCompact D).isConstructible hD)
  obtain ⟨V, hV, hVne, hVcon⟩ := ClosedOrbit.exists_isOpen_subset_of_dense hconstruct
    (dcon.dense_image con.left.continuous dD)
  refine ⟨V, hV, hVne, fun x hx => ?_⟩
  obtain ⟨z, hz, hzD⟩ := exists_point_lift_in_open con.left D hD x.left
    (hVcon (hx ⟨IsLocalRing.closedPoint k, rfl⟩))
  have hzbase : z ≫ Z.hom = 𝟙 _ := by
    rw [← Over.w con, ← Category.assoc, hz, Over.w x]
    rfl
  let p : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Z := Over.homMk z hzbase
  let g : rationalPoints G := p ≫ fst G.X T.X
  let t : rationalPoints T.toGrp := p ≫ s
  have hxt : x = g * (t ≫ j.hom.hom) * g⁻¹ := by
    have hp : p ≫ con = x := Over.OverMorphism.ext hz
    rw [← hp]
    simp only [con, BorelPointContainment.conjugation, MonObj.comp_mul, GrpObj.comp_inv,
      ← Category.assoc]
    rfl
  have ht : Set.range t.left ⊆ U := by
    rintro _ ⟨a, rfl⟩
    change s.left (z a) ∈ U
    exact hzD ⟨a, rfl⟩
  exact ⟨T, j ≫ (G.innerIso g).hom, hj.comp_iso _, hxt ▸ pointCentralizer_conj_eq j g t (htU t ht)⟩

end Langlands.GroupScheme
