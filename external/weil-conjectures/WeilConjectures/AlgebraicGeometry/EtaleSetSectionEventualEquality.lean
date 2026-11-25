/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSetSectionComparison
import WeilConjectures.AlgebraicGeometry.EtaleSetSectionAffineEventualEquality
import WeilConjectures.AlgebraicGeometry.EtaleFiniteAffineRestrictionDetection
import WeilConjectures.AlgebraicGeometry.EtaleSetSectionComparisonNaturality
import WeilConjectures.AlgebraicGeometry.EtaleSetSectionComparisonLaws
import Mathlib.CategoryTheory.Filtered.Final

/-! # An intermediate step in continuity of étale sections
Source: Stacks Project, Tag 09YQ. -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry


/-- Source: Stacks Project, Étale Cohomology, Theorem Tag 09YQ, proof via Tags 0EYL,
04HR, and 09YN, followed by finite affine-cover descent.
(blueprint: lem-weil-pbc-sets-section-eventual-equality).
Proof: directedness first moves the two sections to a common stage on the cofinal tail.
For an affine descended object, the affine-site colimit theorem and unit-compatible
inverse-image comparison turn the given limit equality into equality in the filtered
colimit of section sets. Equality in a filtered colimit holds at some later stage.
For general W₀, restrict to a finite affine cover. Apply the affine assertion to the
two restrictions on each member. Choose a common later stage for these finitely many
equalities. Separatedness of the sheaf on this covering then gives equality of the
two sections over the entire base changed W₀. The resulting arrows to the original
two stages and comparison coherence give the displayed equality. Empty covers need
no equalities and separatedness already gives uniqueness. -/
theorem etaleSetSectionEventualEquality
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (G : Sheaf (D.obj (op i₀)).smallEtaleTopology (Type (u + 1)))
    (W₀ : (D.obj (op i₀)).Etale) [QuasiCompact W₀.hom] [QuasiSeparated W₀.hom]
    (j k : Over (op i₀)) (s : ((Scheme.etaleSetPullback (D.map j.hom)).obj G).obj.obj
        (op ((MorphismProperty.Over.pullback @Etale ⊤ (D.map j.hom)).obj W₀)))
    (t : ((Scheme.etaleSetPullback (D.map k.hom)).obj G).obj.obj
        (op ((MorphismProperty.Over.pullback @Etale ⊤ (D.map k.hom)).obj W₀)))
 :
    (etaleSetSectionComparison (c.π.app j.left) (D.map j.hom)
      (c.π.app (op i₀)) (c.w j.hom) G W₀) s =
      (etaleSetSectionComparison (c.π.app k.left) (D.map k.hom)
        (c.π.app (op i₀)) (c.w k.hom) G W₀) t →
    ∃ (l : Over (op i₀)) (a : l ⟶ j) (b : l ⟶ k),
      (etaleSetSectionComparison (D.map a.left) (D.map j.hom) (D.map l.hom)
          ((D.map_comp a.left j.hom).symm.trans
            (congrArg (fun t : l.left ⟶ op i₀ ↦ D.map t) a.w)) G W₀) s =
        (etaleSetSectionComparison (D.map b.left) (D.map k.hom) (D.map l.hom)
          ((D.map_comp b.left k.hom).symm.trans
            (congrArg (fun t : l.left ⟶ op i₀ ↦ D.map t) b.w)) G W₀) t := by
  classical
  intro hst
  obtain ⟨n, V, v, haff, hqc, hqs, hdetect⟩ :=
    etale_finite_affine_restriction_detection W₀
  let E (j : Over (op i₀)) (W : (D.obj (op i₀)).Etale) :=
    ((Scheme.etaleSetPullback (D.map j.hom)).obj G).obj.obj
      (op ((MorphismProperty.Over.pullback @Etale ⊤ (D.map j.hom)).obj W))
  let r {j k : Over (op i₀)} (a : k ⟶ j) (W : (D.obj (op i₀)).Etale) :
      E j W ⟶ E k W :=
    etaleSetSectionComparison (D.map a.left) (D.map j.hom) (D.map k.hom)
      ((D.map_comp a.left j.hom).symm.trans
        (congrArg (fun t : k.left ⟶ op i₀ ↦ D.map t) a.w)) G W
  let res (j : Over (op i₀)) (a : Fin n) : E j W₀ ⟶ E j (V a) :=
    ((Scheme.etaleSetPullback (D.map j.hom)).obj G).obj.map
      ((MorphismProperty.Over.pullback @Etale ⊤ (D.map j.hom)).map (v a)).op
  have hlocal (a : Fin n) :
      ∃ (l : Over (op i₀)) (b : l ⟶ j) (d : l ⟶ k),
        r b (V a) (res j a s) = r d (V a) (res k a t) := by
    have : IsAffine (V a).left := haff a
    have : QuasiCompact (V a).hom := hqc a
    have : QuasiSeparated (V a).hom := hqs a
    apply etaleSetSectionAffineEventualEquality D c hc i₀ G (V a) j k
    let reslim := ((Scheme.etaleSetPullback (c.π.app (op i₀))).obj G).obj.map
      ((MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))).map (v a)).op
    have hj := congrArg (fun f ↦ f s)
      (etaleSetSectionComparison_naturality (c.π.app j.left) (D.map j.hom)
        (c.π.app (op i₀)) (c.w j.hom) G (v a))
    have hk := congrArg (fun f ↦ f t)
      (etaleSetSectionComparison_naturality (c.π.app k.left) (D.map k.hom)
        (c.π.app (op i₀)) (c.w k.hom) G (v a))
    exact hj.symm.trans ((congrArg reslim hst).trans hk)
  let L (x : Fin n) := (hlocal x).choose
  let A (x : Fin n) : L x ⟶ j := (hlocal x).choose_spec.choose
  let B (x : Fin n) : L x ⟶ k := (hlocal x).choose_spec.choose_spec.choose
  have heq (x : Fin n) :
      r (A x) (V x) (res j x s) = r (B x) (V x) (res k x t) :=
    (hlocal x).choose_spec.choose_spec.choose_spec
  obtain ⟨l, hl⟩ := IsCofiltered.inf_objs_exists
    (insert j (insert k (Finset.univ.image L)))
  let a : l ⟶ j := (hl (Finset.mem_insert_self _ _)).some
  let b : l ⟶ k := (hl (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))).some
  let d (x : Fin n) : l ⟶ L x := (hl (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
    (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩)))).some
  have hcomp {j k l : Over (op i₀)} (a : k ⟶ j) (b : l ⟶ k)
      (W : (D.obj (op i₀)).Etale) : r a W ≫ r b W = r (b ≫ a) W :=
    (etaleSetSectionComparisonLaws D c i₀ G W).2.1 j k l a b
  refine ⟨l, a, b, ?_⟩
  apply hdetect (D.obj l.left) (D.map l.hom)
    ((Scheme.etaleSetPullback (D.map l.hom)).obj G)
  intro x
  have hn₁ := congrArg (fun f ↦ f s)
    (etaleSetSectionComparison_naturality (D.map a.left) (D.map j.hom)
      (D.map l.hom) ((D.map_comp a.left j.hom).symm.trans
        (congrArg (fun t : l.left ⟶ op i₀ ↦ D.map t) a.w)) G (v x))
  have hn₂ := congrArg (fun f ↦ f t)
    (etaleSetSectionComparison_naturality (D.map b.left) (D.map k.hom)
      (D.map l.hom) ((D.map_comp b.left k.hom).symm.trans
        (congrArg (fun t : l.left ⟶ op i₀ ↦ D.map t) b.w)) G (v x))
  change res l x (r a W₀ s) = res l x (r b W₀ t)
  change res l x (r a W₀ s) = r a (V x) (res j x s) at hn₁
  change res l x (r b W₀ t) = r b (V x) (res k x t) at hn₂
  have h₁ : d x ≫ A x = a := by
    apply Over.OverMorphism.ext
    exact Subsingleton.elim _ _
  have h₂ : d x ≫ B x = b := by
    apply Over.OverMorphism.ext
    exact Subsingleton.elim _ _
  have hc₁ : r a (V x) (res j x s) =
      r (d x) (V x) (r (A x) (V x) (res j x s)) := by
    calc
      _ = r (d x ≫ A x) (V x) (res j x s) :=
        congrArg (fun z ↦ r z (V x) (res j x s)) h₁.symm
      _ = _ := (congrArg (fun f ↦ f (res j x s))
        (hcomp (A x) (d x) (V x))).symm
  have hc₂ : r b (V x) (res k x t) =
      r (d x) (V x) (r (B x) (V x) (res k x t)) := by
    calc
      _ = r (d x ≫ B x) (V x) (res k x t) :=
        congrArg (fun z ↦ r z (V x) (res k x t)) h₂.symm
      _ = _ := (congrArg (fun f ↦ f (res k x t))
        (hcomp (B x) (d x) (V x))).symm
  exact hn₁.trans (hc₁.trans
    ((congrArg (r (d x) (V x)) (heq x)).trans (hc₂.symm.trans hn₂.symm)))


end AlgebraicGeometry
