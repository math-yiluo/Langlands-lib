import Langlands.GroupScheme.Rational.NoProperPseudoParabolicSplitTorusCentralStatement
import Langlands.GroupScheme.SubgroupFunctor.NormalFactorProductExistenceStatement
import Langlands.GroupScheme.Dynamic.UnipotentUnipotenceStatement
import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Langlands.GroupScheme.Dynamic.LimitMap
import Langlands.GroupScheme.Dynamic.Functoriality
import Langlands.GroupScheme.Dynamic.SmoothProof
import Langlands.GroupScheme.Dynamic.UnipotentConnected
import Langlands.GroupScheme.SubgroupFunctor.FppfProductLaws
import Langlands.GroupScheme.CentralIsogeny.Basic
import Langlands.GroupScheme.Torus.Lattice

/-! # Split tori are central modulo the radical without proper pseudo-parabolics

The proof follows Conrad–Gabber–Prasad, Lemma 2.2.3: if `P_G(χ)R_{u,k}(G) = G`
for every cocharacter `χ`, then `P_Q(χ ≫ q) = Q` in the pseudo-reductive
quotient `Q`, so `U_Q(χ ≫ q)` is a smooth connected unipotent normal subgroup
of `Q`, hence trivial, and `χ ≫ q` is central.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The product existence and dynamic unipotence propositions imply that split
subtori become central modulo the radical when there is no proper
pseudo-parabolic subgroup. -/
def NoProperPseudoParabolicSplitTorusCentralReductionStatement : Prop :=
  NormalFactorFppfProductExistenceStatement.{u} →
    DynamicUnipotentUnipotenceStatement.{u} →
      NoProperPseudoParabolicSplitTorusCentralStatement.{u}

namespace NoProperPseudoParabolicSplitTorusCentral

/-- A point centralizing `χ` commutes with the image of every point of `𝔾_m`. -/
theorem commute_of_mem_centralizer {S : Scheme.{u}} {G : GroupScheme S}
    (χ : (Gm S).toGrp ⟶ G) {T : Over S} {g : T ⟶ G.X}
    (hg : g ∈ (Dynamic.centralizer χ).carrier T) (t : T ⟶ (Gm S).X) :
    Commute (t ≫ χ.hom.hom) g := by
  have h := congrArg (fun m => lift (𝟙 T) t ≫ m) ((Dynamic.mem_centralizer χ).mp hg)
  simp only [Dynamic.orbit, MonObj.comp_mul, GrpObj.comp_inv, lift_snd_assoc,
    lift_fst_assoc, Category.id_comp] at h
  exact mul_inv_eq_iff_eq_mul.mp h

variable {k : Type u} [Field k]

/-- In a pseudo-reductive group, a cocharacter whose dynamic parabolic subgroup
contains every point is centralized by every point: `U_Q(ν)` is a smooth connected
unipotent normal closed subgroup, hence trivial. -/
theorem mem_centralizer_of_forall_mem_parabolic
    (hunip : DynamicUnipotentUnipotenceStatement.{u})
    {Q : GroupScheme (Spec (CommRingCat.of k))} (hQ : IsPseudoReductive Q)
    (ν : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ Q)
    (hP : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ Q.X),
      g ∈ (Dynamic.parabolic ν).carrier T)
    {T : Over (Spec (CommRingCat.of k))} (g : T ⟶ Q.X) :
    g ∈ (Dynamic.centralizer ν).carrier T := by
  have : Smooth Q.X.hom := hQ.smooth
  have : IsAffineHom Q.X.hom := hQ.isAffineHom
  have : IsAffine Q.X.left := isAffine_of_isAffineHom Q.X.hom
  have hrep := Dynamic.Affine.isRepresentedBy_unipotentHom ν
  have hU : SubgroupFunctor.range (Dynamic.Affine.unipotentHom ν) = ⊥ :=
    hQ.hasTrivialUnipotentRadical _ _
      (Dynamic.Affine.isClosedSubgroup_unipotentHom ν)
      ((dynamicSmooth k Q ν _ _).2.2 hrep)
      (DynamicConnected.connectedSpace_of_isRepresentedBy_unipotent Q ν hrep)
      (hunip k Q ν _ _ hrep)
      (by
        rw [hrep.2]
        intro T' x u _ hu
        exact Dynamic.conj_mem_unipotent ν (hP T' x) hu)
  rw [hrep.2] at hU
  have h := Dynamic.mul_inv_limit_mem_unipotent ν ⟨g, hP T g⟩
  rw [hU, SubgroupFunctor.bot_carrier, Subgroup.mem_bot, mul_inv_eq_one] at h
  change g = Dynamic.limit ν ⟨g, hP T g⟩ at h
  rw [h]
  exact Dynamic.limit_mem_centralizer ν _

/-- Without a proper pseudo-parabolic subgroup, every point of `G` lies in the
fppf-local product of `P_G(χ)` and the radical. -/
theorem fppfLocallyInProduct_of_noProper
    (hprod : NormalFactorFppfProductExistenceStatement.{u})
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
  obtain ⟨P, p, hp⟩ := hprod k G inferInstance inferInstance _ _
    (Dynamic.Affine.parabolicHom χ) r (Dynamic.Affine.isClosedSubgroup_parabolicHom χ)
    hr.isClosedSubgroup hr.isNormal
  rw [(Dynamic.Affine.isRepresentedBy_parabolicHom χ).2] at hp
  have hpp : IsPseudoParabolicSubgroup p :=
    ⟨inferInstance, inferInstance, inferInstance, ⟨U, r, χ, hr, hp⟩⟩
  have := hG P p hpp
  refine (hp.mem_range_iff T x).mp ⟨x ≫ (inv p).hom.hom, ?_⟩
  change (x ≫ (inv p).hom.hom) ≫ p.hom.hom = x
  rw [Category.assoc, ← Grp.comp_hom_hom, IsIso.inv_hom_id, Grp.id_hom_hom,
    Category.comp_id]

/-- Without a proper pseudo-parabolic subgroup, the dynamic parabolic subgroup
of the image cocharacter in an fppf quotient by the radical contains every point. -/
theorem mem_parabolic_comp_of_noProper
    (hprod : NormalFactorFppfProductExistenceStatement.{u})
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [ConnectedSpace G.X.left] [IsAffineHom G.X.hom]
    (hG : ∀ (P : GroupScheme (Spec (CommRingCat.of k))) (i : P ⟶ G),
      IsPseudoParabolicSubgroup i → IsIso i)
    {U : GroupScheme (Spec (CommRingCat.of k))} {r : U ⟶ G} (hr : IsUnipotentRadical r)
    {Q : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom Q.X.hom] {q : G ⟶ Q}
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range r) q)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
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
  obtain ⟨V, v, hvf, hvs, hvl, p, n, hp, hn, hv⟩ :=
    fppfLocallyInProduct_of_noProper hprod hG hr χ x
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

end NoProperPseudoParabolicSplitTorusCentral

open NoProperPseudoParabolicSplitTorusCentral in
/-- CGP Lemma 2.2.3 in the form used for Theorem C.2.3: from represented
products with a normal factor and unipotence of `U_G(λ)`, split subtori become
central in a pseudo-reductive fppf quotient by the radical when no proper
pseudo-parabolic subgroup exists. -/
theorem noProperPseudoParabolicSplitTorusCentral_of_statements
    (hprod : NormalFactorFppfProductExistenceStatement.{u})
    (hunip : DynamicUnipotentUnipotenceStatement.{u}) :
    NoProperPseudoParabolicSplitTorusCentralStatement.{u} := by
  classical
  intro k _ G _ _ _ hG U r hr Q q hq hQ S i hi
  obtain ⟨⟨I, hI, ⟨e⟩⟩, -⟩ := hi
  have : IsAffineHom Q.X.hom := hQ.isAffineHom
  have : Fintype I := Fintype.ofFinite I
  -- Every cocharacter of `G` maps to a cocharacter of `Q` centralized by every point.
  have hcent : ∀ (ν : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
      (T : Over (Spec (CommRingCat.of k))) (t : T ⟶ (Gm (Spec (CommRingCat.of k))).X)
      (h : T ⟶ Q.X), Commute (t ≫ (ν ≫ q).hom.hom) h := fun ν T t h =>
    commute_of_mem_centralizer (ν ≫ q)
      (mem_centralizer_of_forall_mem_parabolic hunip hQ (ν ≫ q)
        (mem_parabolic_comp_of_noProper hprod hG hr hq ν) h) t
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

/-- The conditional reduction, as a proposition with its proof. -/
theorem noProperPseudoParabolicSplitTorusCentralReduction :
    NoProperPseudoParabolicSplitTorusCentralReductionStatement.{u} :=
  noProperPseudoParabolicSplitTorusCentral_of_statements

end Langlands.GroupScheme
