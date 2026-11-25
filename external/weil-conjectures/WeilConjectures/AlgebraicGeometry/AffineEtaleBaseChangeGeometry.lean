/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FullAffineEtaleSite
public import Mathlib.CategoryTheory.Sites.Continuous
import WeilConjectures.AlgebraicGeometry.AffineEtaleNormalizedCartesianSystem
import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# AffineEtaleBaseChangeGeometry

Source: Stacks Project, Étale Cohomology 0EYL; Sites 09YL.
(blueprint: lem-weil-pbc-affine-etale-base-change-system).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The categorical data occurring in an affine étale base-change system. -/
structure AffineEtaleBaseChangeSystemData
    {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) where
  U : ∀ (i j : I), i ≤ j → (D.obj (op i)).FullAffineEtale ⥤
    (D.obj (op j)).FullAffineEtale
  v : ∀ i : I, (D.obj (op i)).FullAffineEtale ⥤ c.pt.FullAffineEtale
  p : ∀ (i j : I) (h : i ≤ j),
    U i j h ⋙ fullAffineEtaleInclusion (D.obj (op j)) ⋙
      Etale.forget (D.obj (op j)) ⋙ Over.forget (D.obj (op j)) ⟶
    fullAffineEtaleInclusion (D.obj (op i)) ⋙
      Etale.forget (D.obj (op i)) ⋙ Over.forget (D.obj (op i))
  q : ∀ i : I,
    v i ⋙ fullAffineEtaleInclusion c.pt ⋙ Etale.forget c.pt ⋙ Over.forget c.pt ⟶
    fullAffineEtaleInclusion (D.obj (op i)) ⋙ Etale.forget (D.obj (op i)) ⋙
      Over.forget (D.obj (op i))
  gamma : ∀ (i j k : I) (h : i ≤ j) (h' : j ≤ k),
    U i j h ⋙ U j k h' ≅ U i k (h.trans h')
  delta : ∀ (i j : I) (h : i ≤ j), U i j h ⋙ v j ≅ v i

/-- The normalized cartesian, cocycle, and covering clauses of a base-change system. -/
def affineEtaleBaseChangeGeometry
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ (i : Iᵒᵖ), CompactSpace (D.obj i)]
    [∀ (i : Iᵒᵖ), QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (d : AffineEtaleBaseChangeSystemData D c) : Prop :=
      (∀ i : I, d.U i i le_rfl = 𝟭 _)
      ∧ (∀ (i j : I) (h : i ≤ j) (A : (D.obj (op i)).FullAffineEtale),
        IsPullback ((d.p i j h).app A) ((d.U i j h).obj A).obj.hom
          A.obj.hom (D.map (homOfLE h).op))
      ∧ (∀ (i : I) (A : (D.obj (op i)).FullAffineEtale),
        IsPullback ((d.q i).app A) ((d.v i).obj A).obj.hom A.obj.hom (c.π.app (op i)))
      ∧ (∀ (i k : I) (h : i ≤ k),
        HEq (d.gamma i i k le_rfl h) (Iso.refl (d.U i k h)))
      ∧ (∀ (i k : I) (h : i ≤ k),
        HEq (d.gamma i k k h le_rfl) (Iso.refl (d.U i k h)))
      ∧ (∀ i : I, HEq (d.delta i i le_rfl) (Iso.refl (d.v i)))
      ∧ (∀ (i j k : I) (h : i ≤ j) (h' : j ≤ k)
        (A : (D.obj (op i)).FullAffineEtale),
        ((d.gamma i j k h h').hom.app A).hom.left ≫ (d.p i k (h.trans h')).app A =
          (d.p j k h').app ((d.U i j h).obj A) ≫ (d.p i j h).app A)
      ∧ (∀ (i j : I) (h : i ≤ j) (A : (D.obj (op i)).FullAffineEtale),
        ((d.delta i j h).hom.app A).hom.left ≫ (d.q i).app A =
          (d.q j).app ((d.U i j h).obj A) ≫ (d.p i j h).app A)
      ∧ (∀ (i j k l : I) (h : i ≤ j) (h' : j ≤ k) (h'' : k ≤ l)
        (A : (D.obj (op i)).FullAffineEtale),
        (d.gamma j k l h' h'').hom.app ((d.U i j h).obj A) ≫
            (d.gamma i j l h (h'.trans h'')).hom.app A =
          (d.U k l h'').map ((d.gamma i j k h h').hom.app A) ≫
            (d.gamma i k l (h.trans h') h'').hom.app A)
      ∧ (∀ (i j k : I) (h : i ≤ j) (h' : j ≤ k)
        (A : (D.obj (op i)).FullAffineEtale),
        (d.v k).map ((d.gamma i j k h h').hom.app A) ≫
            (d.delta i k (h.trans h')).hom.app A =
          (d.delta j k h').hom.app ((d.U i j h).obj A) ≫ (d.delta i j h).hom.app A)
      ∧ (∀ (i j : I) (h : i ≤ j) (A : (D.obj (op i)).FullAffineEtale) (R : Presieve A),
        R ∈ fullAffineEtalePrecoverage (D.obj (op i)) A →
          R.map (d.U i j h) ∈ fullAffineEtalePrecoverage (D.obj (op j)) ((d.U i j h).obj A))
      ∧ (∀ (i j : I) (h : i ≤ j) (A B C : (D.obj (op i)).FullAffineEtale)
        (f : B ⟶ A) (g : C ⟶ A), PreservesLimit (cospan f g) (d.U i j h))
      ∧ (∀ (i : I) (A : (D.obj (op i)).FullAffineEtale) (R : Presieve A),
        R ∈ fullAffineEtalePrecoverage (D.obj (op i)) A →
          R.map (d.v i) ∈ fullAffineEtalePrecoverage c.pt ((d.v i).obj A))
      ∧ (∀ (i : I) (A B C : (D.obj (op i)).FullAffineEtale)
        (f : B ⟶ A) (g : C ⟶ A), PreservesLimit (cospan f g) (d.v i))
      ∧ (∀ (i j : I) (h : i ≤ j), (d.U i j h).IsContinuous
          (fullAffineEtaleTopology (D.obj (op i))) (fullAffineEtaleTopology (D.obj (op j))))
      ∧ (∀ i : I, (d.v i).IsContinuous
          (fullAffineEtaleTopology (D.obj (op i))) (fullAffineEtaleTopology c.pt))

private theorem cartesian_hom_ext
    {S T : Scheme.{u}} {f : T ⟶ S} {A : S.FullAffineEtale} {B C : T.FullAffineEtale}
    {p : B.obj.left ⟶ A.obj.left} (hp : IsPullback p B.obj.hom A.obj.hom f)
    {a b : C ⟶ B} (h : a.hom.left ≫ p = b.hom.left ≫ p) : a = b := by
  apply InducedCategory.hom_ext
  apply MorphismProperty.Over.Hom.ext
  apply hp.hom_ext h
  exact a.hom.w.trans b.hom.w.symm

/-- A natural cartesian realization of base change preserves finite étale covers and
pullbacks. Pullback uniqueness identifies its inclusion with ordinary étale base change;
cover preservation follows by lifting points in its cartesian arrow squares. The sheaf
condition on the image covering proves continuity. Source: Stacks 0EYL and Topologies
021C, 021D; the point-lifting argument is Mathlib Scheme.exists_preimage_of_isPullback. -/
private theorem cartesian_site_geometry
    {S T : Scheme.{u}} (f : T ⟶ S)
    (F : S.FullAffineEtale ⥤ T.FullAffineEtale)
    (p : F ⋙ fullAffineEtaleInclusion T ⋙ Etale.forget T ⋙ Over.forget T ⟶
      fullAffineEtaleInclusion S ⋙ Etale.forget S ⋙ Over.forget S)
    (hp : ∀ A : S.FullAffineEtale,
      IsPullback (p.app A) (F.obj A).obj.hom A.obj.hom f) :
    (∀ (A : S.FullAffineEtale) (R : Presieve A),
      R ∈ fullAffineEtalePrecoverage S A →
        R.map F ∈ fullAffineEtalePrecoverage T (F.obj A)) ∧
    (∀ (A B C : S.FullAffineEtale) (a : B ⟶ A) (b : C ⟶ A),
      PreservesLimit (cospan a b) F) ∧
    F.IsContinuous (fullAffineEtaleTopology S) (fullAffineEtaleTopology T) := by
  have hmap {A B : S.FullAffineEtale} (a : A ⟶ B) :
      IsPullback (p.app A) (F.map a).hom.left a.hom.left (p.app B) := by
    apply IsPullback.of_bot (v₁₂ := a.hom.left) (v₂₁ := (F.obj B).obj.hom)
        (v₂₂ := B.obj.hom) ?_ (p.naturality a).symm (hp B)
    change IsPullback (p.app A) ((F.map a).hom.left ≫ (F.obj B).obj.hom)
      (a.hom.left ≫ B.obj.hom) f
    have ha : a.hom.left ≫ B.obj.hom = A.obj.hom := a.hom.w
    have hFa : (F.map a).hom.left ≫ (F.obj B).obj.hom = (F.obj A).obj.hom :=
      (F.map a).hom.w
    rw [ha, hFa]
    exact hp A
  have hc : ∀ (A : S.FullAffineEtale) (R : Presieve A),
      R ∈ fullAffineEtalePrecoverage S A →
        R.map F ∈ fullAffineEtalePrecoverage T (F.obj A) := by
    rintro A R ⟨n, V, a, rfl, ha, hs⟩
    rw [Presieve.map_ofArrows]
    refine ⟨n, _, _, rfl, ?_, ?_⟩
    · intro i
      exact MorphismProperty.of_isPullback (P := @Etale) (hmap (a i)) (ha i)
    · intro x
      obtain ⟨i, y, hy⟩ := hs (p.app A x)
      obtain ⟨z, _, hz⟩ := Scheme.exists_preimage_of_isPullback (hmap (a i)) y x hy
      exact ⟨i, z, hz⟩
  let e : F ⋙ fullAffineEtaleInclusion T ≅
      fullAffineEtaleInclusion S ⋙ MorphismProperty.Over.pullback @Etale ⊤ f :=
    NatIso.ofComponents (fun A ↦ MorphismProperty.Over.isoMk (hp A).isoPullback
      ((hp A).isoPullback_hom_snd)) (by
        intro A B a
        apply MorphismProperty.Over.Hom.ext
        change (F.map a).hom.left ≫ (hp B).isoPullback.hom =
          (hp A).isoPullback.hom ≫
            pullback.lift (pullback.fst A.obj.hom f ≫ a.hom.left)
              (pullback.snd A.obj.hom f) _
        apply pullback.hom_ext
        · simp only [Category.assoc, pullback.lift_fst,
            IsPullback.isoPullback_hom_fst, IsPullback.isoPullback_hom_fst_assoc]
          exact p.naturality a
        · simp only [Category.assoc, pullback.lift_snd,
            IsPullback.isoPullback_hom_snd]
          exact (F.map a).hom.w)
  have hclosure (X : Scheme.{u}) :
      ObjectProperty.IsClosedUnderLimitsOfShape
        (fun A : X.Etale ↦ IsAffine A.left) WalkingCospan := ⟨by
    rintro A ⟨h⟩
    let G := Etale.forget X ⋙ Over.forget X
    have (j : WalkingCospan) : IsAffine ((h.diag ⋙ G).obj j) := h.prop_diag_obj j
    exact Scheme.isAffine_of_isLimit (G.mapCone h.toLimitPresentation.cone)
      (isLimitOfPreserves G h.isLimit)⟩
  have := hclosure S
  have := hclosure T
  have hi : PreservesLimitsOfShape WalkingCospan (fullAffineEtaleInclusion S) := by
    dsimp [fullAffineEtaleInclusion]
    infer_instance
  have hr : ReflectsLimitsOfShape WalkingCospan (fullAffineEtaleInclusion T) := by
    dsimp [fullAffineEtaleInclusion]
    infer_instance
  have hb : PreservesFiniteLimits (MorphismProperty.Over.pullback @Etale ⊤ f) :=
    inferInstance
  have hcomp : PreservesLimitsOfShape WalkingCospan
      (fullAffineEtaleInclusion S ⋙ MorphismProperty.Over.pullback @Etale ⊤ f) :=
    comp_preservesLimitsOfShape _ _
  have he : PreservesLimitsOfShape WalkingCospan (F ⋙ fullAffineEtaleInclusion T) :=
    preservesLimitsOfShape_of_natIso e.symm
  have hF : PreservesLimitsOfShape WalkingCospan F :=
    preservesLimitsOfShape_of_reflects_of_preserves _ (fullAffineEtaleInclusion T)
  have htop (X : Scheme.{u}) (J : Pretopology X.FullAffineEtale)
      (hJ : J.toPrecoverage = fullAffineEtalePrecoverage X) :
      fullAffineEtaleTopology X = J.toGrothendieck := by
    change (fullAffineEtalePrecoverage X).toGrothendieck = J.toGrothendieck
    rw [← hJ]
    apply le_antisymm
    · apply Precoverage.toGrothendieck_le_iff_le_toPrecoverage.mpr
      intro A R hR
      exact ⟨R, hR, Sieve.le_generate R⟩
    · intro A R hR
      obtain ⟨R', hR', hRR'⟩ := hR
      exact J.toPrecoverage.toGrothendieck.superset_covering
        (by rw [Sieve.generate_le_iff]; exact hRR')
        (J.toPrecoverage.generate_mem_toGrothendieck hR')
  refine ⟨hc, fun _ _ _ _ _ ↦ inferInstance, ⟨fun G ↦ ?_⟩⟩
  obtain ⟨J, hJ⟩ := fullAffineEtalePrecoverage_isPretopology S
  rw [htop S J hJ, Presieve.isSheaf_pretopology]
  intro A R hR
  rw [Presieve.IsSheafFor.comp_iff_of_preservesPairwisePullbacks]
  exact (isSheaf_iff_isSheaf_of_type _ _).mp G.property |>.isSheafFor_of_mem_precoverage
    (hc A R (hJ ▸ hR))

/-- Source: Stacks Project 0EYL, the base-change system used in its qcqs proof,
and Sites 00X1 for continuity.

Proof: the limit projections are affine by `AlgebraicGeometry.isAffineHom_π_app`.
Pullback along an affine morphism preserves affine domains and étale structure maps.
Choose restricted pullback for transitions, except that on equal indices choose the
identity, with identity first projection; choose restricted pullback along each cone
projection for `v`. The functor laws follow from the two pullback projections.
Pullback pasting identifies iterated transition pullbacks and transition-cone pullbacks
with the single pullback. Its unique comparison isomorphisms define `gamma` and `delta`;
on diagonal indices choose identity comparisons. Their projection equations follow from
this definition. In each associativity or cone cocycle both composites have the same
first and structure projections, so pullback uniqueness gives equality. Base change
preserves finite jointly surjective étale families, including the empty family, and
pasting preserves every cospan pullback. These facts pass to the full affine subcategories.
Cover preservation and preservation of their pairwise pullbacks imply continuity for
the generated topologies. This proves precisely the geometric clauses, with no sheaf
adjunction assertion.
(blueprint: lem-weil-pbc-affine-etale-base-change-geometry). -/
theorem exists_affineEtale_baseChange_geometry
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ (i : Iᵒᵖ), CompactSpace (D.obj i)]
    [∀ (i : Iᵒᵖ), QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c) :
    ∃ d : AffineEtaleBaseChangeSystemData D c, affineEtaleBaseChangeGeometry D c d := by
  have (i : Iᵒᵖ) : IsAffineHom (c.π.app i) := isAffineHom_π_app D c hc i
  obtain ⟨U, v, p, q, gamma, delta, hid, hp, hq, hγl, hγr, hδ,
    hγp, hδp⟩ := exists_affineEtale_normalized_cartesian_system D c
  refine ⟨⟨U, v, p, q, gamma, delta⟩, hid, hp, hq, hγl, hγr, hδ,
    hγp, hδp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j k l h h' h'' A
    apply cartesian_hom_ext (hp i l (h.trans (h'.trans h'')) A)
    change ((gamma j k l h' h'').hom.app ((U i j h).obj A)).hom.left ≫
        ((gamma i j l h (h'.trans h'')).hom.app A).hom.left ≫
          (p i l (h.trans (h'.trans h''))).app A =
      ((U k l h'').map ((gamma i j k h h').hom.app A)).hom.left ≫
        ((gamma i k l (h.trans h') h'').hom.app A).hom.left ≫
          (p i l ((h.trans h').trans h'')).app A
    have hn := (p k l h'').naturality ((gamma i j k h h').hom.app A)
    change ((U k l h'').map ((gamma i j k h h').hom.app A)).hom.left ≫
        (p k l h'').app ((U i k (h.trans h')).obj A) =
      (p k l h'').app ((U j k h').obj ((U i j h).obj A)) ≫
        ((gamma i j k h h').hom.app A).hom.left at hn
    simp only [hγp]
    rw [← Category.assoc _ ((p j l (h'.trans h'')).app ((U i j h).obj A))
      ((p i j h).app A), hγp]
    rw [← Category.assoc _ ((p k l h'').app ((U i k (h.trans h')).obj A))
      ((p i k (h.trans h')).app A), hn]
    simp only [Category.assoc, hγp]
  · intro i j k h h' A
    apply cartesian_hom_ext (hq i A)
    change ((v k).map ((gamma i j k h h').hom.app A)).hom.left ≫
        ((delta i k (h.trans h')).hom.app A).hom.left ≫ (q i).app A =
      ((delta j k h').hom.app ((U i j h).obj A)).hom.left ≫
        ((delta i j h).hom.app A).hom.left ≫ (q i).app A
    have hn := (q k).naturality ((gamma i j k h h').hom.app A)
    change ((v k).map ((gamma i j k h h').hom.app A)).hom.left ≫
        (q k).app ((U i k (h.trans h')).obj A) =
      (q k).app ((U j k h').obj ((U i j h).obj A)) ≫
        ((gamma i j k h h').hom.app A).hom.left at hn
    simp only [hδp]
    rw [← Category.assoc _ ((q j).app ((U i j h).obj A)) ((p i j h).app A), hδp]
    rw [← Category.assoc _ ((q k).app ((U i k (h.trans h')).obj A))
      ((p i k (h.trans h')).app A), hn]
    simp only [Category.assoc, hγp]
  · intro i j h
    exact (cartesian_site_geometry (D.map (homOfLE h).op) (U i j h) (p i j h)
      (hp i j h)).1
  · intro i j h
    exact (cartesian_site_geometry (D.map (homOfLE h).op) (U i j h) (p i j h)
      (hp i j h)).2.1
  · intro i
    exact (cartesian_site_geometry (c.π.app (op i)) (v i) (q i) (hq i)).1
  · intro i
    exact (cartesian_site_geometry (c.π.app (op i)) (v i) (q i) (hq i)).2.1
  · intro i j h
    exact (cartesian_site_geometry (D.map (homOfLE h).op) (U i j h) (p i j h)
      (hp i j h)).2.2
  · intro i
    exact (cartesian_site_geometry (c.π.app (op i)) (v i) (q i) (hq i)).2.2

end AlgebraicGeometry.Scheme
