import Langlands.GroupScheme.Rational.NoProperPseudoParabolicSplitTorusCentralReduction
import Langlands.GroupScheme.SubgroupFunctor.SmoothConnectedNormalFactorProductExistenceStatement
import Langlands.GroupScheme.Dynamic.ConnectedProof

/-! # Split tori are central modulo the radical: the smooth connected product route

This variant of `NoProperPseudoParabolicSplitTorusCentralReduction` uses the
represented product of two smooth connected closed subgroups, the second one
normal, in place of the product of an arbitrary closed subgroup with a normal
one. Both factors used in Conrad–Gabber–Prasad, Lemma 2.2.3, namely `P_G(χ)`
and the radical, are smooth and connected.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The smooth connected normal-factor product existence and dynamic unipotence
propositions imply that split subtori become central modulo the radical when
there is no proper pseudo-parabolic subgroup. -/
def NoProperPseudoParabolicSplitTorusCentralSmoothReductionStatement : Prop :=
  SmoothConnectedNormalFactorFppfProductExistenceStatement.{u} →
    DynamicUnipotentUnipotenceStatement.{u} →
      NoProperPseudoParabolicSplitTorusCentralStatement.{u}

namespace NoProperPseudoParabolicSplitTorusCentralSmooth

open NoProperPseudoParabolicSplitTorusCentral

variable {k : Type u} [Field k]

/-- Without a proper pseudo-parabolic subgroup, every point of `G` lies in the
fppf-local product of `P_G(χ)` and the radical; both factors are smooth and
connected. -/
theorem fppfLocallyInProduct_of_noProper
    (hprod : SmoothConnectedNormalFactorFppfProductExistenceStatement.{u})
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [ConnectedSpace G.X.left] [IsAffineHom G.X.hom]
    (hG : ∀ (P : GroupScheme (Spec (CommRingCat.of k))) (i : P ⟶ G),
      IsPseudoParabolicSubgroup i → IsIso i)
    {U : GroupScheme (Spec (CommRingCat.of k))} {r : U ⟶ G} (hr : IsUnipotentRadical r)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    {T : Over (Spec (CommRingCat.of k))} (x : T ⟶ G.X) :
    SubgroupFunctor.FppfLocallyInProduct (Dynamic.parabolic χ)
      (SubgroupFunctor.range r) x := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hrep := Dynamic.Affine.isRepresentedBy_parabolicHom χ
  obtain ⟨P, p, hp, -, -⟩ := hprod k G inferInstance inferInstance _ _
    (Dynamic.Affine.parabolicHom χ) r (Dynamic.Affine.isClosedSubgroup_parabolicHom χ)
    ((dynamicSmooth k G χ _ _).1 hrep)
    (DynamicConnected.connectedSpace_of_isRepresentedBy_parabolic G χ hrep)
    hr.isClosedSubgroup hr.smooth hr.connectedSpace hr.isNormal
  rw [hrep.2] at hp
  have hpp : IsPseudoParabolicSubgroup p :=
    ⟨inferInstance, inferInstance, inferInstance, ⟨U, r, χ, hr, hp⟩⟩
  have := hG P p hpp
  refine (hp.mem_range_iff T x).mp ⟨x ≫ (inv p).hom.hom, ?_⟩
  change (x ≫ (inv p).hom.hom) ≫ p.hom.hom = x
  rw [Category.assoc, ← Grp.comp_hom_hom, IsIso.inv_hom_id, Grp.id_hom_hom,
    Category.comp_id]

/-- If every point of `G` lies fppf-locally in the product of `P_G(χ)` and the
kernel of an fppf quotient `q : G ⟶ Q`, then the dynamic parabolic subgroup of
the image cocharacter contains every point of `Q`. -/
theorem mem_parabolic_comp_of_fppfLocallyInProduct
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {U : GroupScheme (Spec (CommRingCat.of k))} {r : U ⟶ G}
    {Q : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom Q.X.hom] {q : G ⟶ Q}
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range r) q)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hloc : ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X),
      SubgroupFunctor.FppfLocallyInProduct (Dynamic.parabolic χ)
        (SubgroupFunctor.range r) x)
    (T : Over (Spec (CommRingCat.of k))) (y : T ⟶ Q.X) :
    y ∈ (Dynamic.parabolic (χ ≫ q)).carrier T := by
  have : IsAffine Q.X.left := isAffine_of_isAffineHom Q.X.hom
  have : Flat q.hom.hom.left := hq.1
  have : Surjective q.hom.hom.left := hq.2.1
  have : LocallyOfFinitePresentation q.hom.hom.left := hq.2.2.1
  -- Lift `y` along `q` after the base change of `q` along `y`.
  let W : Over (Spec (CommRingCat.of k)) :=
    Over.mk (pullback.fst y.left q.hom.hom.left ≫ T.hom)
  let a : W ⟶ T := Over.homMk (pullback.fst y.left q.hom.hom.left) rfl
  let x : W ⟶ G.X := Over.homMk (pullback.snd y.left q.hom.hom.left) (by
    rw [← Over.w q.hom.hom, ← Category.assoc, ← pullback.condition,
      Category.assoc, Over.w y]
    rfl)
  have ha : a ≫ y = x ≫ q.hom.hom := Over.OverMorphism.ext pullback.condition
  have : Flat a.left := by change Flat (pullback.fst _ _); infer_instance
  have : Surjective a.left := by change Surjective (pullback.fst _ _); infer_instance
  have : LocallyOfFinitePresentation a.left := by
    change LocallyOfFinitePresentation (pullback.fst _ _)
    infer_instance
  obtain ⟨V, v, hvf, hvs, hvl, p, n, hp, hn, hv⟩ := hloc W x
  have : Flat v.left := hvf
  have : Surjective v.left := hvs
  have : LocallyOfFinitePresentation v.left := hvl
  rw [← hq.2.2.2, mem_range_kernelι_iff] at hn
  have hvy : (v ≫ a) ≫ y = p ≫ q.hom.hom := by
    rw [Category.assoc, ha, ← Category.assoc, hv, MonObj.mul_comp, hn, mul_one]
  have hpq : (v ≫ a) ≫ y ∈ (Dynamic.parabolic (χ ≫ q)).carrier V := by
    rw [hvy]
    exact Dynamic.parabolic_le_comap χ q V hp
  have hrep := Dynamic.Affine.isRepresentedBy_parabolicHom (χ ≫ q)
  have : Mono (Dynamic.Affine.parabolicHom (χ ≫ q)).hom.hom := hrep.1
  rw [← hrep.2] at hpq ⊢
  exact SubgroupFunctor.isFppfLocal_range _ T V (v ≫ a)
    (by change Flat (v.left ≫ a.left); infer_instance)
    (by change Surjective (v.left ≫ a.left); infer_instance)
    (by change LocallyOfFinitePresentation (v.left ≫ a.left); infer_instance) y hpq

/-- A homomorphism `q : G ⟶ Q` such that the image of every cocharacter of `G`
commutes with every point of `Q` is central on every split subtorus of `G`. -/
theorem isCentral_comp_of_forall_commute
    {G Q : GroupScheme (Spec (CommRingCat.of k))} (q : G ⟶ Q)
    (hcent : ∀ (ν : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
      (T : Over (Spec (CommRingCat.of k))) (t : T ⟶ (Gm (Spec (CommRingCat.of k))).X)
      (h : T ⟶ Q.X), Commute (t ≫ (ν ≫ q).hom.hom) h)
    {S : CommGroupScheme (Spec (CommRingCat.of k))} (i : S.toGrp ⟶ G)
    (hi : IsSplitSubtorus i) : IsCentral (i ≫ q) := by
  classical
  obtain ⟨⟨I, hI, ⟨e⟩⟩, -⟩ := hi
  have : Fintype I := Fintype.ofFinite I
  -- The coordinate decomposition of points of the split torus.
  let f : splitTorus (Spec (CommRingCat.of k)) I ⟶ Q := e.inv ≫ i ≫ q
  have hsplit : ∀ (T : Over (Spec (CommRingCat.of k)))
      (z : T ⟶ (splitTorus (Spec (CommRingCat.of k)) I).X) (h : T ⟶ Q.X),
      Commute (z ≫ f.hom.hom) h := by
    intro T z h
    let K : Subgroup (T ⟶ (splitTorus (Spec (CommRingCat.of k)) I).X) :=
      { carrier := {w | Commute (w ≫ f.hom.hom) h}
        one_mem' := by
          change Commute (1 ≫ f.hom.hom) h
          rw [MonObj.one_comp]
          exact Commute.one_left h
        mul_mem' := fun {a b} ha hb => by
          change Commute ((a * b) ≫ f.hom.hom) h
          rw [MonObj.mul_comp]
          exact Commute.mul_left ha hb
        inv_mem' := fun {a} ha => by
          change Commute (a⁻¹ ≫ f.hom.hom) h
          rw [GrpObj.inv_comp]
          exact Commute.inv_left ha }
    have hz : z = ∏ j, z ≫ (CommGroupScheme.groupHom
        (splitTorus.proj (Spec (CommRingCat.of k)) I j ≫
          splitTorus.single (Spec (CommRingCat.of k)) I j)).hom.hom := by
      have hsum := comp_groupHom_sum z Finset.univ (fun j =>
        splitTorus.proj (Spec (CommRingCat.of k)) I j ≫
          splitTorus.single (Spec (CommRingCat.of k)) I j)
      rw [splitTorus.sum_proj_comp_single] at hsum
      exact (Category.comp_id z).symm.trans hsum
    have hzK : z ∈ K := by
      rw [hz]
      refine Subgroup.prod_mem K fun j _ => ?_
      have hj : (z ≫ (CommGroupScheme.groupHom
          (splitTorus.proj (Spec (CommRingCat.of k)) I j ≫
            splitTorus.single (Spec (CommRingCat.of k)) I j)).hom.hom) ≫ f.hom.hom =
          (z ≫ (CommGroupScheme.groupHom
            (splitTorus.proj (Spec (CommRingCat.of k)) I j)).hom.hom) ≫
            ((CommGroupScheme.groupHom (splitTorus.single (Spec (CommRingCat.of k)) I j) ≫
              e.inv ≫ i) ≫ q).hom.hom := by
        rw [comp_groupHom_comp (G := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I)
          (H := Gm (Spec (CommRingCat.of k)))
          (K := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I) z]
        simp only [f, Grp.comp_hom_hom, Category.assoc]
      change Commute (_ ≫ f.hom.hom) h
      rw [hj]
      exact hcent _ T _ h
    exact hzK
  have hf : IsCentral f := fun T x T' a h => by
    rw [← Category.assoc]
    exact hsplit T' (a ≫ x) h
  have hfe : e.hom ≫ f = i ≫ q := by
    simp only [f, Iso.hom_inv_id_assoc]
  rw [← hfe]
  exact hf.comp e.hom

end NoProperPseudoParabolicSplitTorusCentralSmooth

open NoProperPseudoParabolicSplitTorusCentral NoProperPseudoParabolicSplitTorusCentralSmooth in
/-- CGP Lemma 2.2.3 in the form used for Theorem C.2.3, from represented
products of smooth connected subgroups with a normal second factor and
unipotence of `U_G(λ)`. -/
theorem noProperPseudoParabolicSplitTorusCentral_of_smooth_statements
    (hprod : SmoothConnectedNormalFactorFppfProductExistenceStatement.{u})
    (hunip : DynamicUnipotentUnipotenceStatement.{u}) :
    NoProperPseudoParabolicSplitTorusCentralStatement.{u} := by
  intro k _ G _ _ _ hG U r hr Q q hq hQ S i hi
  have : IsAffineHom Q.X.hom := hQ.isAffineHom
  exact isCentral_comp_of_forall_commute q (fun ν T t h =>
    commute_of_mem_centralizer (ν ≫ q)
      (mem_centralizer_of_forall_mem_parabolic hunip hQ (ν ≫ q)
        (mem_parabolic_comp_of_fppfLocallyInProduct hq ν
          (fun _ x => fppfLocallyInProduct_of_noProper hprod hG hr ν x)) h) t) i hi

/-- The conditional reduction, as a proposition with its proof. -/
theorem noProperPseudoParabolicSplitTorusCentralSmoothReduction :
    NoProperPseudoParabolicSplitTorusCentralSmoothReductionStatement.{u} :=
  noProperPseudoParabolicSplitTorusCentral_of_smooth_statements

end Langlands.GroupScheme
