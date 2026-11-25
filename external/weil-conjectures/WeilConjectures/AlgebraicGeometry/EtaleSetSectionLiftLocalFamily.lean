/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSetSectionComparison
import Mathlib.AlgebraicGeometry.Cover.Open
import WeilConjectures.AlgebraicGeometry.EtaleSetSectionComparisonLaws
import WeilConjectures.AlgebraicGeometry.EtaleSetSectionFiniteMatching
import Mathlib.CategoryTheory.Filtered.Final

/-! # Compatible local stage lifts of étale inverse-image sections
Source: Stacks Project, Étale Cohomology, Tag 09YQ, using Sites Tag 09YN. -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Source: Stacks Project, Étale Cohomology Tag 09YQ, finite affine-cover
reduction, using Sites Tag 09YN
(blueprint: lem-weil-pbc-sets-section-lift-local-family).
Proof: W₀ is qcqs since its structure map is quasi-compact and quasi-separated and
its base is qcqs. Choose a finite affine open cover V of W₀ and identify its finite
index type with Fin n. All V are étale over the base, with quasi-compact and
quasi-separated structure maps. Apply haff to the restrictions of t and choose one
common stage for the finitely many lifts. Comparison coherence preserves their images.
Choose finite affine refinements of the pairwise intersections; these exist because
W₀ is quasi-separated. The two restrictions to each such affine refinement have
identical limit images by naturality. Apply eventual equality on these finitely many
objects, then choose one later stage for all the equalities. Separatedness on each
refined intersection gives compatibility on that intersection, hence on every pair
of arrows with equal composites into W₀. The original covering stays covering under
base change at both the chosen stage and the limit. The local images are the original
restrictions of t by coherence. If n is zero, there are no representatives or overlap
equalities to choose; nonemptiness supplies a stage and all compatibility clauses
are vacuous. This lemma constructs only a compatible family, not a global section. -/
theorem etaleSetSectionLift_local_family
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (G : Sheaf (D.obj (op i₀)).smallEtaleTopology (Type (u + 1)))
    (W₀ : (D.obj (op i₀)).Etale) [QuasiCompact W₀.hom] [QuasiSeparated W₀.hom]
    (haff : ∀ (W : (D.obj (op i₀)).Etale) (_ : IsAffine W.left),
      QuasiCompact W.hom → QuasiSeparated W.hom →
      ∀ t : ((Scheme.etaleSetPullback (c.π.app (op i₀))).obj G).obj.obj
        (op ((MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))).obj W)),
      ∃ (j : Over (op i₀)) (s : ((Scheme.etaleSetPullback (D.map j.hom)).obj G).obj.obj
        (op ((MorphismProperty.Over.pullback @Etale ⊤ (D.map j.hom)).obj W))),
        (etaleSetSectionComparison (c.π.app j.left) (D.map j.hom)
          (c.π.app (op i₀)) (c.w j.hom) G W) s = t)
    (t : ((Scheme.etaleSetPullback (c.π.app (op i₀))).obj G).obj.obj
        (op ((MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))).obj W₀))) :
    ∃ (n : ℕ) (V : Fin n → (D.obj (op i₀)).Etale) (f : ∀ b, V b ⟶ W₀)
      (j : Over (op i₀))
      (s : ∀ b, ((Scheme.etaleSetPullback (D.map j.hom)).obj G).obj.obj
        (op ((MorphismProperty.Over.pullback @Etale ⊤ (D.map j.hom)).obj (V b)))),
      (∀ b, IsAffine (V b).left) ∧
      Sieve.ofArrows (fun b ↦
        (MorphismProperty.Over.pullback @Etale ⊤ (D.map j.hom)).obj (V b))
        (fun b ↦ (MorphismProperty.Over.pullback @Etale ⊤ (D.map j.hom)).map (f b)) ∈
        (D.obj j.left).smallEtaleTopology
          ((MorphismProperty.Over.pullback @Etale ⊤ (D.map j.hom)).obj W₀) ∧
      Sieve.ofArrows (fun b ↦
        (MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))).obj (V b))
        (fun b ↦ (MorphismProperty.Over.pullback @Etale ⊤
          (c.π.app (op i₀))).map (f b)) ∈ c.pt.smallEtaleTopology
          ((MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))).obj W₀) ∧
      (∀ (Y : (D.obj j.left).Etale) (b b' : Fin n)
        (a : Y ⟶ (MorphismProperty.Over.pullback @Etale ⊤ (D.map j.hom)).obj (V b))
        (a' : Y ⟶ (MorphismProperty.Over.pullback @Etale ⊤ (D.map j.hom)).obj (V b')),
        a ≫ (MorphismProperty.Over.pullback @Etale ⊤ (D.map j.hom)).map (f b) =
          a' ≫ (MorphismProperty.Over.pullback @Etale ⊤ (D.map j.hom)).map (f b') →
        ((Scheme.etaleSetPullback (D.map j.hom)).obj G).obj.map a.op (s b) =
          ((Scheme.etaleSetPullback (D.map j.hom)).obj G).obj.map a'.op (s b')) ∧
      (∀ b, (etaleSetSectionComparison (c.π.app j.left) (D.map j.hom)
        (c.π.app (op i₀)) (c.w j.hom) G (V b)) (s b) =
        ((Scheme.etaleSetPullback (c.π.app (op i₀))).obj G).obj.map
          ((MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))).map (f b)).op t)
        := by
  classical
  have : CompactSpace W₀.left :=
    @QuasiCompact.compactSpace_of_compactSpace W₀.left (D.obj (op i₀)) W₀.hom
      inferInstance (inferInstanceAs (CompactSpace (D.obj (op i₀))))
  let C := W₀.left.affineCover.finiteSubcover
  let n := Fintype.card C.I₀
  let e : Fin n ≃ C.I₀ := (Fintype.equivFin C.I₀).symm
  let V (b : Fin n) : (D.obj (op i₀)).Etale :=
    Scheme.Etale.mk (C.f (e b) ≫ W₀.hom)
  let f (b : Fin n) : V b ⟶ W₀ := MorphismProperty.Over.homMk (C.f (e b)) rfl
  have hV (b : Fin n) : IsAffine (V b).left := by
    change IsAffine (C.X (e b))
    dsimp [C, Scheme.OpenCover.finiteSubcover, Scheme.affineCover]
    infer_instance
  have hqc (b : Fin n) : QuasiCompact (V b).hom := by
    have : IsAffine (V b).left := hV b
    exact @quasiCompact_of_compactSpace (V b).left (D.obj (op i₀)) (V b).hom
      inferInstance (inferInstanceAs (QuasiSeparatedSpace (D.obj (op i₀))))
  have hqs (b : Fin n) : QuasiSeparated (V b).hom := by
    have : IsAffine (V b).left := hV b
    exact @QuasiSeparated.of_quasiSeparatedSpace (V b).left _ (V b).hom inferInstance
  have hcover : Sieve.ofArrows V f ∈ (D.obj (op i₀)).smallEtaleTopology W₀ := by
    apply (Scheme.ofArrows_mem_smallEtaleTopology_iff f).mpr
    change (⋃ b, Set.range (C.f (e b))) = Set.univ
    exact (e.surjective.iUnion_comp (fun b ↦ Set.range (C.f b))).trans C.iUnion_range
  have hbase (T : Scheme.{u}) (h : T ⟶ D.obj (op i₀)) :
      Sieve.ofArrows (fun b ↦ (MorphismProperty.Over.pullback @Etale ⊤ h).obj (V b))
        (fun b ↦ (MorphismProperty.Over.pullback @Etale ⊤ h).map (f b)) ∈
        T.smallEtaleTopology ((MorphismProperty.Over.pullback @Etale ⊤ h).obj W₀) := by
    have hh := (Scheme.coverPreserving_overPullback
      (P := @Etale) (Q := @Etale) (le_refl _) h).cover_preserve hcover
    rwa [Sieve.functorPushforward_ofArrows] at hh
  let E (j : Over (op i₀)) (W : (D.obj (op i₀)).Etale) :=
    ((Scheme.etaleSetPullback (D.map j.hom)).obj G).obj.obj
      (op ((MorphismProperty.Over.pullback @Etale ⊤ (D.map j.hom)).obj W))
  let r {j k : Over (op i₀)} (a : k ⟶ j) (W : (D.obj (op i₀)).Etale) :
      E j W ⟶ E k W :=
    etaleSetSectionComparison (D.map a.left) (D.map j.hom) (D.map k.hom)
      ((D.map_comp a.left j.hom).symm.trans
        (congrArg (fun t : k.left ⟶ op i₀ ↦ D.map t) a.w)) G W
  let q (j : Over (op i₀)) (W : (D.obj (op i₀)).Etale) :=
    etaleSetSectionComparison (c.π.app j.left) (D.map j.hom)
      (c.π.app (op i₀)) (c.w j.hom) G W
  let F := ((Scheme.etaleSetPullback (c.π.app (op i₀))).obj G).obj
  let B := MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))
  let tV (b : Fin n) := F.map (B.map (f b)).op t
  have hlift (b : Fin n) : ∃ (j : Over (op i₀)) (s : E j (V b)), q j (V b) s = tV b :=
    haff (V b) (hV b) (hqc b) (hqs b) (tV b)
  let J (b : Fin n) := (hlift b).choose
  let s₀ (b : Fin n) : E (J b) (V b) := (hlift b).choose_spec.choose
  have hs₀ (b : Fin n) : q (J b) (V b) (s₀ b) = tV b :=
    (hlift b).choose_spec.choose_spec
  obtain ⟨j, hj⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image J)
  let a (b : Fin n) : j ⟶ J b :=
    (hj (Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩)).some
  let s (b : Fin n) : E j (V b) := r (a b) (V b) (s₀ b)
  have hs (b : Fin n) : q j (V b) (s b) = tV b := by
    have h := congrArg (fun g ↦ g (s₀ b))
      ((etaleSetSectionComparisonLaws D c i₀ G (V b)).2.2 (J b) j (a b))
    exact h.trans (hs₀ b)
  have hmatch (Z : (D.obj (op i₀)).Etale) (b b' : Fin n)
      (p : Z ⟶ V b) (p' : Z ⟶ V b') (heq : p ≫ f b = p' ≫ f b') :
      q j Z (((Scheme.etaleSetPullback (D.map j.hom)).obj G).obj.map
        ((MorphismProperty.Over.pullback @Etale ⊤ (D.map j.hom)).map p).op (s b)) =
      q j Z (((Scheme.etaleSetPullback (D.map j.hom)).obj G).obj.map
        ((MorphismProperty.Over.pullback @Etale ⊤ (D.map j.hom)).map p').op (s b')) := by
    -- The comparison is the component of this composite natural transformation.
    let B₀ := MorphismProperty.Over.pullback @Etale ⊤ (D.map j.hom)
    let B₁ := MorphismProperty.Over.pullback @Etale ⊤ (c.π.app j.left)
    let H := (Scheme.etaleSetPullback (D.map j.hom)).obj G
    let K := (Scheme.etaleSetPullback (c.π.app (op i₀))).obj G
    have : B₁.IsContinuous ((D.obj j.left).smallGrothendieckTopology @Etale)
        (c.pt.smallGrothendieckTopology @Etale) :=
      Scheme.isContinuous_overPullback (P := @Etale) (Q := @Etale)
        (le_refl _) (c.π.app j.left)
    let η := (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      B₁ (Type (u + 1)) ((D.obj j.left).smallGrothendieckTopology @Etale)
      (c.pt.smallGrothendieckTopology @Etale)).unit.app H
    let β := (Classical.choose etaleSetInverseImageCompositionUnits.2.2
      (D.obj (op i₀)) (D.obj j.left) c.pt (D.map j.hom) (c.π.app j.left)).hom.app G
    let γ := eqToHom (congrArg
      (fun z : c.pt ⟶ D.obj (op i₀) ↦ (Scheme.etaleSetPullback z).obj G) (c.w j.hom))
    let δ := (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
      (c.π.app j.left) (D.map j.hom) (c.π.app (op i₀)) (c.w j.hom).symm).hom
    let α := Functor.whiskerLeft B₀.op η.hom ≫
      Functor.whiskerLeft (B₀ ⋙ B₁).op β.hom ≫
      Functor.whiskerLeft (B₀ ⋙ B₁).op γ.hom ≫
      Functor.whiskerRight (NatTrans.op δ) K.obj
    have hp := congrArg (fun g ↦ g (s b)) (α.naturality p.op).symm
    have hp' := congrArg (fun g ↦ g (s b')) (α.naturality p'.op).symm
    change F.map (B.map p).op (q j (V b) (s b)) = _ at hp
    change F.map (B.map p').op (q j (V b') (s b')) = _ at hp'
    rw [hs] at hp hp'
    apply hp.symm.trans
    apply Eq.trans _ hp'
    change F.map (B.map p).op (F.map (B.map (f b)).op t) =
      F.map (B.map p').op (F.map (B.map (f b')).op t)
    have hh := congrArg (fun z ↦ F.map (B.map z).op t) heq
    simpa only [Functor.map_comp, op_comp, types_comp_apply] using hh
  obtain ⟨l, d, hcompat⟩ :=
    etaleSetSection_finite_matching D c hc i₀ G W₀ V f hqc hqs j s hmatch
  refine ⟨n, V, f, l, (fun b ↦ r d (V b) (s b)), hV,
    hbase _ _, hbase _ _, hcompat, ?_⟩
  intro b
  have h := congrArg (fun g ↦ g (s b))
    ((etaleSetSectionComparisonLaws D c i₀ G (V b)).2.2 j l d)
  exact h.trans (hs b)

end AlgebraicGeometry
