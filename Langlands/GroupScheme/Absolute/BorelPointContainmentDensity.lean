import Langlands.GroupScheme.Absolute.BorelPointContainmentStatement
import Langlands.GroupScheme.Absolute.BorelConjugacyProof
import Langlands.GroupScheme.Absolute.BorelTransport
import Langlands.AbelianScheme.AlgClosedIsogenyPointLifting
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-! # Rational points in Borel subgroups from a dense conjugation map -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace BorelPointContainment

variable {k : Type u} [Field k]

/-- The conjugation morphism `G × H ⟶ G`, `(x, h) ↦ x j(h) x⁻¹`. -/
def conjugation {G H : GroupScheme (Spec (CommRingCat.of k))} (j : H ⟶ G) :
    G.X ⊗ H.X ⟶ G.X :=
  fst G.X H.X * (snd G.X H.X ≫ j.hom.hom) * (fst G.X H.X)⁻¹

theorem lift_conjugation {G H : GroupScheme (Spec (CommRingCat.of k))} (j : H ⟶ G)
    {T : Over (Spec (CommRingCat.of k))} (x : T ⟶ G.X) (h : T ⟶ H.X) :
    lift x h ≫ conjugation j = x * (h ≫ j.hom.hom) * x⁻¹ := by
  simp only [conjugation, MonObj.comp_mul, GrpObj.comp_inv, lift_fst, lift_snd_assoc]

section Points

variable [IsAlgClosed k]

/-- Rational points of a scheme locally of finite type over an algebraically closed field are
determined by their underlying point. -/
theorem rationalPoint_ext {X : Over (Spec (CommRingCat.of k))} [LocallyOfFiniteType X.hom]
    {x y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X}
    (h : x.left (IsLocalRing.closedPoint k) = y.left (IsLocalRing.closedPoint k)) : x = y := by
  apply Over.OverMorphism.ext
  exact ext_of_apply_closedPoint_eq X.hom (by simp) (by simp) h

/-- Every closed point is the underlying point of a rational point. -/
theorem exists_rationalPoint_of_isClosed {X : Over (Spec (CommRingCat.of k))}
    [LocallyOfFiniteType X.hom] (z : X.left) (hz : IsClosed {z}) :
    ∃ x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X,
      x.left (IsLocalRing.closedPoint k) = z :=
  ⟨Over.homMk (pointOfClosedPoint X.hom z hz) (by simp), pointOfClosedPoint_apply _ _ _ _⟩

/-- The underlying point of a rational point is closed. -/
theorem isClosed_rationalPoint {X : Over (Spec (CommRingCat.of k))} [LocallyOfFiniteType X.hom]
    (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X) :
    IsClosed {x.left (IsLocalRing.closedPoint k)} :=
  ((pointEquivClosedPoint X.hom) ⟨x.left, by simp⟩).2

end Points

/-- Evaluation of a composite of rational points at the closed point. -/
theorem comp_left_apply {X Y : Over (Spec (CommRingCat.of k))}
    (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X) (f : X ⟶ Y) :
    (x ≫ f).left (IsLocalRing.closedPoint k) = f.left (x.left (IsLocalRing.closedPoint k)) :=
  rfl

section FixedLocus

variable {G : GroupScheme (Spec (CommRingCat.of k))} {Q : Over (Spec (CommRingCat.of k))}
  (a : SchemeAction G Q)

/-- The incidence locus `{(g, y) | g • y = y}` of `G × Q`, as a set of points: the preimage of
the diagonal under `(g, y) ↦ (g • y, y)`. -/
def incidence : Set (G.X ⊗ Q).left :=
  (lift a.hom (snd G.X Q)).left ⁻¹' Set.range (lift (𝟙 Q) (𝟙 Q)).left

/-- The set of points of `G` fixing some point of `Q`: the projection of the incidence locus. -/
def fixingLocus : Set G.X.left :=
  (fst G.X Q).left '' incidence a

theorem isClosed_incidence [IsSeparated Q.hom] : IsClosed (incidence a) := by
  have h : (lift (𝟙 Q) (𝟙 Q)).left = Limits.pullback.diagonal Q.hom := rfl
  refine IsClosed.preimage (lift a.hom (snd G.X Q)).left.continuous ?_
  rw [h]
  exact (Limits.pullback.diagonal Q.hom).isClosedEmbedding.isClosed_range

theorem isClosed_fixingLocus [IsProper Q.hom] : IsClosed (fixingLocus a) := by
  change IsClosed ((Limits.pullback.fst G.X.hom Q.hom) '' incidence a)
  exact (Limits.pullback.fst G.X.hom Q.hom).isClosedMap _ (isClosed_incidence a)

/-- A rational point fixing a rational point lies in the fixing locus. -/
theorem mem_fixingLocus_of_act_eq (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
    (y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Q) (hy : a.act g y = y) :
    g.left (IsLocalRing.closedPoint k) ∈ fixingLocus a := by
  refine ⟨(lift g y).left (IsLocalRing.closedPoint k), ?_, ?_⟩
  · refine ⟨y.left (IsLocalRing.closedPoint k), ?_⟩
    have e : y ≫ lift (𝟙 Q) (𝟙 Q) = lift g y ≫ lift a.hom (snd G.X Q) := by
      rw [comp_lift, comp_lift, Category.comp_id, lift_snd]
      change lift y y = lift (a.act g y) y
      rw [hy]
    have e' := congrArg (fun f => f.left (IsLocalRing.closedPoint k)) e
    simpa only [comp_left_apply] using e'
  · have e : lift g y ≫ fst G.X Q = g := lift_fst _ _
    have e' := congrArg (fun f => f.left (IsLocalRing.closedPoint k)) e
    simpa only [comp_left_apply] using e'

/-- A rational point in the fixing locus fixes a rational point. -/
theorem exists_act_eq_of_mem_fixingLocus [IsAlgClosed k] [LocallyOfFiniteType G.X.hom]
    [LocallyOfFiniteType Q.hom] [IsSeparated Q.hom]
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
    (hg : g.left (IsLocalRing.closedPoint k) ∈ fixingLocus a) :
    ∃ y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Q, a.act g y = y := by
  have : LocallyOfFiniteType (G.X ⊗ Q).hom := by
    rw [Over.tensorObj_hom]
    infer_instance
  have : JacobsonSpace (G.X ⊗ Q).left := LocallyOfFiniteType.jacobsonSpace (G.X ⊗ Q).hom
  obtain ⟨w₀, hw₀, hw₀g⟩ := hg
  let Z : Set (G.X ⊗ Q).left :=
    incidence a ∩ (fst G.X Q).left ⁻¹' {g.left (IsLocalRing.closedPoint k)}
  have hZ : IsClosed Z := (isClosed_incidence a).inter
    ((isClosed_rationalPoint g).preimage (fst G.X Q).left.continuous)
  obtain ⟨w, ⟨hwF, hwg⟩, hwc⟩ := nonempty_inter_closedPoints (Z := Z) ⟨w₀, hw₀, hw₀g⟩
    hZ.isLocallyClosed
  obtain ⟨x, hx⟩ := exists_rationalPoint_of_isClosed w hwc
  have hxg : x ≫ fst G.X Q = g := by
    apply rationalPoint_ext
    rw [comp_left_apply, hx]
    exact hwg
  refine ⟨x ≫ snd G.X Q, ?_⟩
  obtain ⟨v, hv⟩ := hwF
  apply rationalPoint_ext
  have h1 : x ≫ lift a.hom (snd G.X Q) ≫ fst Q Q = a.act g (x ≫ snd G.X Q) := by
    rw [lift_fst, SchemeAction.act, ← hxg, ← comp_lift, lift_fst_snd, Category.comp_id]
  have h2 : x ≫ lift a.hom (snd G.X Q) ≫ snd Q Q = x ≫ snd G.X Q := by
    rw [lift_snd]
  have e1 := congrArg (fun f => f.left (IsLocalRing.closedPoint k)) h1
  have e2 := congrArg (fun f => f.left (IsLocalRing.closedPoint k)) h2
  simp only [comp_left_apply, hx] at e1 e2
  have e3 : ∀ f : Q ⊗ Q ⟶ Q,
      (lift a.hom (snd G.X Q) ≫ f).left w = f.left ((lift (𝟙 Q) (𝟙 Q)).left v) := by
    intro f
    rw [hv]
    rfl
  have e4 : ∀ f : Q ⊗ Q ⟶ Q, lift (𝟙 Q) (𝟙 Q) ≫ f = 𝟙 Q →
      f.left ((lift (𝟙 Q) (𝟙 Q)).left v) = v := by
    intro f hf
    change (lift (𝟙 Q) (𝟙 Q) ≫ f).left v = v
    rw [hf]
    rfl
  rw [comp_left_apply x (snd G.X Q), hx, ← e1, ← e2, e3 (fst Q Q), e3 (snd Q Q),
    e4 _ (lift_fst _ _), e4 _ (lift_snd _ _)]

end FixedLocus

section Containment

variable [IsAlgClosed k]

/-- A rational point fixing a rational point of the flag quotient `G / B₀` lies in a Borel
subgroup, namely a conjugate of `B₀`. -/
theorem exists_isBorelSubgroup_of_act_eq {G B₀ : GroupScheme (Spec (CommRingCat.of k))}
    {i₀ : B₀ ⟶ G} (hi₀ : IsBorelSubgroup i₀) {Q : Over (Spec (CommRingCat.of k))}
    (q : G.X ⟶ Q) [LocallyOfFiniteType q.left] [Surjective q.left]
    (hfib : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range i₀).carrier T)
    (a : SchemeAction G Q)
    (hact : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
      a.act g (h ≫ q) = (g * h) ≫ q)
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
    (y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Q) (hy : a.act g y = y) :
    ∃ (B : GroupScheme (Spec (CommRingCat.of k))) (i : B ⟶ G)
      (b : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ B.X),
      IsBorelSubgroup i ∧ b ≫ i.hom.hom = g := by
  obtain ⟨m₀, hm₀⟩ := Langlands.exists_point_lift_of_locallyOfFiniteType_surjective q.left y.left
  have hmS : m₀ ≫ G.X.hom = 𝟙 (Spec (CommRingCat.of k)) := by
    rw [← Over.w q, ← Category.assoc, hm₀]
    exact Over.w y
  let m : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X := Over.homMk m₀ hmS
  have hm : m ≫ q = y := Over.OverMorphism.ext hm₀
  have hfix : m ≫ q = (g * m) ≫ q := by
    rw [← hact, hm, hy]
  obtain ⟨b, hb⟩ := SubgroupFunctor.mem_range.1 ((hfib _ m (g * m)).1 hfix)
  refine ⟨B₀, i₀ ≫ (G.innerIso m).hom, b, hi₀.comp_iso _, ?_⟩
  rw [Grp.comp_hom_hom, ← Category.assoc, hb, comp_innerIso_hom, constantPoint_self]
  group

/-- A rational point of a Borel subgroup fixes a rational point of the flag quotient `G / B₀`. -/
theorem exists_act_eq_of_isBorelSubgroup {G B₀ : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    {i₀ : B₀ ⟶ G} (hi₀ : IsBorelSubgroup i₀) {Q : Over (Spec (CommRingCat.of k))}
    (q : G.X ⟶ Q)
    (hfib : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range i₀).carrier T)
    (a : SchemeAction G Q)
    (hact : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
      a.act g (h ≫ q) = (g * h) ≫ q)
    {B : GroupScheme (Spec (CommRingCat.of k))} {i : B ⟶ G} (hi : IsBorelSubgroup i)
    (b : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ B.X) :
    ∃ y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Q, a.act (b ≫ i.hom.hom) y = y := by
  obtain ⟨g₁, φ, hφ⟩ := (borelConjugacy k G).2 B B₀ i i₀ hi hi₀
  refine ⟨g₁⁻¹ ≫ q, ?_⟩
  rw [hact]
  symm
  apply (hfib _ _ _).2
  apply SubgroupFunctor.mem_range.2
  refine ⟨b ≫ φ.hom.hom.hom, ?_⟩
  have e := congrArg (fun f : B ⟶ G => b ≫ f.hom.hom) hφ
  simp only [Grp.comp_hom_hom] at e
  rw [← Category.assoc, ← Category.assoc, comp_innerIso_hom, constantPoint_self] at e
  rw [← e]
  group

/-- **Lemma A.** If the conjugation map `G × H ⟶ G` of a subgroup `j : H ⟶ G` has dense range
and every rational point of `H` lies in a Borel subgroup of `G`, then every rational point of `G`
lies in a Borel subgroup of `G`. -/
theorem exists_isBorelSubgroup_of_denseRange {G H : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    [LocallyOfFiniteType H.X.hom] (j : H ⟶ G)
    (hdense : DenseRange (conjugation j).left)
    (hH : ∀ h : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X,
      ∃ (B : GroupScheme (Spec (CommRingCat.of k))) (i : B ⟶ G)
        (b : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ B.X),
        IsBorelSubgroup i ∧ b ≫ i.hom.hom = h ≫ j.hom.hom)
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :
    ∃ (B : GroupScheme (Spec (CommRingCat.of k))) (i : B ⟶ G)
      (b : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ B.X),
      IsBorelSubgroup i ∧ b ≫ i.hom.hom = g := by
  obtain ⟨B₀, i₀, hi₀, hproper⟩ := someBorelQuotientProper k G inferInstance
  obtain ⟨Q, q, hsep, hft, hqc, hsmooth, hsurj, hqqc, hfib⟩ :=
    smoothSubgroupQuotientExistence k G B₀ i₀ hi₀.isClosedSubgroup hi₀.smooth
  have := hsmooth
  have := hsurj
  have := hqqc
  have := hsep
  have := hft
  have : IsProper Q.hom := hproper Q q hsep hft hqc hsmooth hsurj hqqc hfib
  let a := Dynamic.flagQuotientSchemeAction G (SubgroupFunctor.range i₀) q hfib
  have hact : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
      a.act g (h ≫ q) = (g * h) ≫ q :=
    fun T g h => Dynamic.flagQuotientSchemeAction_act_lift G (SubgroupFunctor.range i₀) q hfib g h
  have : LocallyOfFiniteType (G.X ⊗ H.X).hom := by
    rw [Over.tensorObj_hom]
    infer_instance
  have : JacobsonSpace (G.X ⊗ H.X).left := LocallyOfFiniteType.jacobsonSpace (G.X ⊗ H.X).hom
  have hsub : closedPoints (G.X ⊗ H.X).left ⊆ (conjugation j).left ⁻¹' fixingLocus a := by
    intro w hw
    obtain ⟨z, hz⟩ := exists_rationalPoint_of_isClosed w hw
    obtain ⟨B, i, b, hi, hb⟩ := hH (z ≫ snd G.X H.X)
    have hconj : b ≫ (i ≫ (G.innerIso (z ≫ fst G.X H.X)).hom).hom.hom = z ≫ conjugation j := by
      rw [Grp.comp_hom_hom, ← Category.assoc, hb, comp_innerIso_hom, constantPoint_self]
      simp only [conjugation, MonObj.comp_mul, GrpObj.comp_inv, Category.assoc]
    obtain ⟨y, hy⟩ := exists_act_eq_of_isBorelSubgroup hi₀ q hfib a hact
      (hi.comp_iso (G.innerIso (z ≫ fst G.X H.X))) b
    rw [hconj] at hy
    have hmem := mem_fixingLocus_of_act_eq a _ y hy
    rwa [comp_left_apply, hz] at hmem
  have hC : IsClosed ((conjugation j).left ⁻¹' fixingLocus a) :=
    (isClosed_fixingLocus a).preimage (conjugation j).left.continuous
  have huniv : (conjugation j).left ⁻¹' fixingLocus a = Set.univ := by
    rw [← Set.univ_subset_iff, ← closure_closedPoints]
    exact hC.closure_subset_iff.2 hsub
  have hrange : Set.range (conjugation j).left ⊆ fixingLocus a := by
    rintro _ ⟨w, rfl⟩
    exact Set.eq_univ_iff_forall.1 huniv w
  have hF : fixingLocus a = Set.univ := by
    rw [← Set.univ_subset_iff, ← hdense.closure_range]
    exact (isClosed_fixingLocus a).closure_subset_iff.2 hrange
  obtain ⟨y, hy⟩ := exists_act_eq_of_mem_fixingLocus a g (hF ▸ Set.mem_univ _)
  exact exists_isBorelSubgroup_of_act_eq hi₀ q hfib a hact g y hy

end Containment

end BorelPointContainment

end Langlands.GroupScheme
