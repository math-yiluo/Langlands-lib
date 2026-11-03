import Langlands.GroupScheme.Absolute.ChevalleyUnipotentEnvelopeSteps
import Langlands.GroupScheme.Absolute.SolvableUnipotentPartStatement
import Langlands.GroupScheme.UnipotentClosedSubgroupStatement
import Langlands.GroupScheme.ImageGenerationStatement
import Langlands.GroupScheme.Absolute.RationalSubgroupContainment
import Langlands.GroupScheme.Absolute.BorelTransport
import Langlands.GroupScheme.Absolute.BorelExistence
import Langlands.GroupScheme.InnerAutomorphism
import Langlands.GroupScheme.NormalizedSubgroup
import Langlands.GroupScheme.SmoothProducts
import Langlands.GroupScheme.Rational.SplitRankTransport
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.Rational.LeviSplitComponentFactorization
import Langlands.GroupScheme.Rational.ParabolicAmbientTransport
import Langlands.GroupScheme.ImageEnvelopeStabilityProof
import Langlands.GroupScheme.SmoothConnectedGeometryProof
import Langlands.AlgebraicGeometry.SmoothReducedProof

/-! # The envelope step of Chevalley's Borel-intersection theorem -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.UnipotentAllBorelsEnvelope

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A morphism from a reduced scheme locally of finite type over an algebraically closed
field factors through a closed subgroup as soon as all its rational points do. -/
theorem exists_factor_of_algClosed_points {G K : GroupScheme (Spec (CommRingCat.of k))}
    {X : Over (Spec (CommRingCat.of k))} [IsReduced X.left] [LocallyOfFiniteType X.hom]
    (φ : X ⟶ G.X) {j : K ⟶ G} (hj : IsClosedSubgroup j)
    (h : ∀ x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X,
      x ≫ φ ∈ (SubgroupFunctor.range j).carrier _) :
    ∃ a : X ⟶ K.X, a ≫ j.hom.hom = φ := by
  let f := φ.left
  let g := j.hom.hom.left
  let p := pullback.fst f g
  have : IsClosedImmersion g := hj
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  have hpclosed : IsClosed (Set.range p) := p.isClosedEmbedding.isClosed_range
  have hppts : closedPoints X.left ⊆ Set.range p := by
    intro x hx
    let a : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X :=
      Over.homMk (pointOfClosedPoint X.hom x hx)
        (pointOfClosedPoint_comp X.hom x hx)
    obtain ⟨b, hb⟩ := h a
    change b ≫ j.hom.hom = a ≫ φ at hb
    rw [Scheme.Pullback.range_fst]
    change ∃ y, g y = f x
    refine ⟨b.left (IsLocalRing.closedPoint k), ?_⟩
    have he := congrArg
      (fun q : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X =>
        q.left (IsLocalRing.closedPoint k)) hb
    change g (b.left (IsLocalRing.closedPoint k)) =
      f (pointOfClosedPoint X.hom x hx (IsLocalRing.closedPoint k)) at he
    exact he.trans (congrArg f
      (pointOfClosedPoint_apply X.hom x hx (IsLocalRing.closedPoint k)))
  have hprange : Set.range p = Set.univ := by
    apply Set.Subset.antisymm (Set.subset_univ _)
    rw [← closure_closedPoints (X := X.left)]
    exact closure_minimal hppts hpclosed
  have : Surjective p := ⟨Set.range_eq_univ.mp hprange⟩
  have : IsIso p := isIso_of_isClosedImmersion_of_surjective p
  let a := inv p ≫ pullback.snd f g
  have ha : a ≫ g = f := by
    dsimp [a]
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, IsIso.inv_hom_id,
      Category.id_comp]
  refine ⟨Over.homMk a (by
    rw [← Over.w j.hom.hom, ← Category.assoc, ha]
    exact Over.w φ), ?_⟩
  apply Over.OverMorphism.ext
  exact ha

section Translation

variable {S : Scheme.{u}} (G : GroupScheme S) (X : Over S)

private def leftTranslationHom : G.X ⊗ (G.X ⊗ X) ⟶ G.X ⊗ X :=
  lift (fst G.X (G.X ⊗ X) * (snd G.X (G.X ⊗ X) ≫ fst G.X X)) (snd G.X (G.X ⊗ X) ≫ snd G.X X)

private theorem lift_leftTranslationHom {T : Over S} (h : T ⟶ G.X) (x : T ⟶ G.X ⊗ X) :
    lift h x ≫ leftTranslationHom G X = lift (h * (x ≫ fst G.X X)) (x ≫ snd G.X X) := by
  rw [leftTranslationHom, comp_lift, MonObj.comp_mul, lift_fst, lift_snd_assoc, lift_snd_assoc]

/-- Left translation of `G` on the first factor of `G.X ⊗ X`. -/
def leftTranslation : PointwiseSchemeAction G (G.X ⊗ X) where
  hom := leftTranslationHom G X
  one_left x := by
    rw [lift_leftTranslationHom, one_mul, lift_comp_fst_snd]
  mul_left h h' x := by
    rw [lift_leftTranslationHom, lift_leftTranslationHom, lift_leftTranslationHom, lift_fst,
      lift_snd, mul_assoc]

theorem leftTranslation_act {T : Over S} (h : T ⟶ G.X) (x : T ⟶ G.X ⊗ X) :
    (leftTranslation G X).act h x = lift (h * (x ≫ fst G.X X)) (x ≫ snd G.X X) :=
  lift_leftTranslationHom G X h x

end Translation

section Conjugation

variable {S : Scheme.{u}} {G U : GroupScheme S} (i : U ⟶ G)

/-- The conjugation morphism `(g, u) ↦ g i(u) g⁻¹` intertwines left translation on the
first factor with conjugation on `G`. -/
theorem conjugationMap_isEquivariant :
    (leftTranslation G U.X).IsEquivariant
      (AutomorphicAction.conjugation (𝟙 G)).toPointwiseSchemeAction
      (SubgroupFunctor.conjugationMap i (𝟙 G)) := by
  intro T h v
  rw [leftTranslation_act, AutomorphicAction.toPointwiseSchemeAction_act,
    AutomorphicAction.conjugation_act]
  conv_rhs => rw [← lift_comp_fst_snd v]
  rw [SubgroupFunctor.lift_comp_conjugationMap, SubgroupFunctor.lift_comp_conjugationMap]
  simp only [Grp.id_hom_hom, Category.comp_id]
  group

end Conjugation

section Envelope

variable {G U : GroupScheme (Spec (CommRingCat.of k))} {i : U ⟶ G}

omit [IsAlgClosed k] in
/-- If `U` lies in every Borel subgroup, then the conjugate of `U` by every rational point
of `G` lies in the unipotent part `Bu` of a fixed Borel subgroup `B₀`. -/
theorem conjugationMap_points_mem {B₀ Bu : GroupScheme (Spec (CommRingCat.of k))}
    {b₀ : B₀ ⟶ G} (hb₀ : IsBorelSubgroup b₀) {h : Bu ⟶ B₀}
    (hmax : ∀ (W : GroupScheme (Spec (CommRingCat.of k))) (w : W ⟶ B₀),
      IsClosedSubgroup w → IsUnipotent W → SubgroupFunctor.range w ≤ SubgroupFunctor.range h)
    (hi : IsClosedSubgroup i) (hU : IsUnipotent U)
    (hB : ∀ (B : GroupScheme (Spec (CommRingCat.of k))) (b : B ⟶ G),
        IsBorelSubgroup b → SubgroupFunctor.range i ≤ SubgroupFunctor.range b)
    (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X ⊗ U.X) :
    x ≫ SubgroupFunctor.conjugationMap i (𝟙 G) ∈
      (SubgroupFunctor.range (h ≫ b₀)).carrier _ := by
  let a := x ≫ fst G.X U.X
  let e := G.innerIso a
  have hle : SubgroupFunctor.range (i ≫ e.hom) ≤ SubgroupFunctor.range b₀ := by
    have := SubgroupFunctor.range_comp_mono (hB _ _ (hb₀.comp_iso e.symm)) e.hom
    simpa only [Category.assoc, Iso.symm_hom, Iso.inv_hom_id, Category.comp_id] using this
  have : IsClosedImmersion b₀.hom.hom.left := hb₀.isClosedSubgroup
  have hrep : (SubgroupFunctor.range b₀).IsRepresentedBy b₀ :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  let w := hrep.factorHom (i ≫ e.hom) hle
  have hw : w ≫ b₀ = i ≫ e.hom := hrep.factorHom_comp _ hle
  have hwc : IsClosedSubgroup w :=
    IsClosedSubgroup.of_comp hb₀.isClosedSubgroup (by rw [hw]; exact hi.comp_iso e)
  obtain ⟨z, hz⟩ := SubgroupFunctor.mem_range.1 (hmax U w hwc hU _
    (SubgroupFunctor.mem_range.2 ⟨x ≫ snd G.X U.X, rfl⟩))
  refine SubgroupFunctor.mem_range.2 ⟨z, ?_⟩
  have hc : G.constantPoint a (Over.mk (𝟙 _)) = a := by
    unfold GroupScheme.constantPoint
    convert Category.id_comp a
    ext
    simp
  calc z ≫ (h ≫ b₀).hom.hom = (z ≫ h.hom.hom) ≫ b₀.hom.hom := by
        rw [Grp.comp_hom_hom, Category.assoc]
    _ = (x ≫ snd G.X U.X) ≫ (w ≫ b₀).hom.hom := by
        rw [hz, Grp.comp_hom_hom, Category.assoc]
    _ = ((x ≫ snd G.X U.X) ≫ i.hom.hom) ≫ e.hom.hom.hom := by
        rw [hw, Grp.comp_hom_hom]
        simp only [Category.assoc]
    _ = a * ((x ≫ snd G.X U.X) ≫ i.hom.hom) * a⁻¹ := by
        rw [GroupScheme.comp_innerIso_hom, hc]
    _ = x ≫ SubgroupFunctor.conjugationMap i (𝟙 G) := by
        conv_rhs => rw [← lift_comp_fst_snd x]
        rw [SubgroupFunctor.lift_comp_conjugationMap]
        simp only [Grp.id_hom_hom, Category.comp_id, a]

end Envelope

/-- The envelope step, conditional on pointed-image generation, the unipotent part of a
solvable group and unipotence of closed subgroups of unipotent groups. -/
theorem unipotentAllBorelsEnvelope_of_statements
    (hGen : PointedImageGenerationStatement.{u})
    (hSolv : SolvableUnipotentPartStatement.{u})
    (hSub : UnipotentClosedSubgroupStatement.{u}) :
    UnipotentAllBorelsEnvelopeStatement.{u} := by
  intro k _ _ G _ _ _ U i hi hUsm hUconn hUunip hB
  have hUaff : IsAffineHom U.X.hom := hi.isAffineHom_source
  obtain ⟨hVAff, hVFin, -, hVInt⟩ := smoothConnectedAffineGeometry.2 k G U
    inferInstance inferInstance inferInstance hUsm hUaff hUconn
  let f := SubgroupFunctor.conjugationMap i (𝟙 G)
  have hv₀ : (lift 1 1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X ⊗ U.X) ≫ f = 1 := by
    simp only [f, SubgroupFunctor.lift_comp_conjugationMap, MonObj.one_comp,
      mul_one, inv_one]
  obtain ⟨D, hD⟩ :=
    hGen k G inferInstance inferInstance (G.X ⊗ U.X) hVAff hVFin hVInt _ f hv₀
  obtain ⟨B₀, b₀, hb₀⟩ := BorelExistence.exists_isBorelSubgroup G
  have : Smooth B₀.X.hom := hb₀.smooth
  have : ConnectedSpace B₀.X.left := hb₀.connectedSpace
  have : IsAffineHom B₀.X.hom := hb₀.isClosedSubgroup.isAffineHom_source
  obtain ⟨Bu, h, hhc, hBusm, -, hBuunip, -, hmax⟩ := hSolv k B₀ hb₀.isSolvableGroupScheme
  have hc : IsClosedSubgroup (h ≫ b₀) := hhc.comp hb₀.isClosedSubgroup
  have : Smooth (G.X ⊗ U.X).hom := smooth_tensor _ _ inferInstance hUsm
  have : IsReduced (G.X ⊗ U.X).left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field k _
      (G.X ⊗ U.X).hom
  have : LocallyOfFiniteType (G.X ⊗ U.X).hom := hVFin
  have hfac : FactorsThrough f (h ≫ b₀) :=
    exists_factor_of_algClosed_points f hc (conjugationMap_points_mem hb₀ hmax hi hUunip hB)
  have hmc : IsClosedSubgroup (D.minimalHom (h ≫ b₀) hc hfac) :=
    IsClosedSubgroup.of_comp hc (by rw [D.minimalHom_comp]; exact D.closed)
  have : IsAffineHom Bu.X.hom := hhc.isAffineHom_source
  have : Smooth Bu.X.hom := hBusm
  have hNunip : IsUnipotent D.group := hSub k Bu D.group _ hmc hBuunip
  have : GeometricallyConnected D.group.X.hom := hD.2.2.1
  refine ⟨D.group, D.inclusion, D.closed, hD.1, ?_, hNunip, ?_, ?_⟩
  · exact GeometricallyConnected.connectedSpace_of_subsingleton (f := D.group.X.hom)
  · intro T g x _ hx
    rw [D.represents.2] at hx ⊢
    have hst := AutomorphicAction.closedImageEnvelope_isStable
      (AutomorphicAction.conjugation (𝟙 G)) inferInstance (leftTranslation G U.X) f
      (conjugationMap_isEquivariant i) T g x hx
    simpa only [AutomorphicAction.conjugation_act, Grp.id_hom_hom, Category.comp_id]
      using hst
  · intro T x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.1 hx
    rw [D.represents.2]
    have hy := closedImageEnvelope_containsImage f T (lift 1 y)
    simpa only [f, SubgroupFunctor.lift_comp_conjugationMap, Grp.id_hom_hom,
      Category.comp_id, one_mul, inv_one, mul_one] using hy

end Langlands.GroupScheme.UnipotentAllBorelsEnvelope
