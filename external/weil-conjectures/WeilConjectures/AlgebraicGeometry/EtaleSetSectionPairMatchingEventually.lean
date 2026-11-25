/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSetSectionComparison
import WeilConjectures.AlgebraicGeometry.EtaleSetSectionComparisonLaws
import WeilConjectures.AlgebraicGeometry.EtaleSetSectionEventualEquality
import WeilConjectures.AlgebraicGeometry.EtaleSetSectionComparisonNaturality
import WeilConjectures.AlgebraicGeometry.EtalePairRestrictionDetection

/-! # One overlap equation remains effective at later stages
Source: Stacks Project, Tags 03Q4 and 09YQ, finite overlap reduction.
(blueprint: lem-weil-pbc-sets-section-pair-matching-eventually). -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Source: Stacks Project, Tags 03Q4 and 09YQ, finite overlap reduction.
(blueprint: lem-weil-pbc-sets-section-pair-matching-eventually).
Proof: fix the two objects and form their fibre product over W in the small étale
category. Cancellation against the qcqs structure map of W makes the two arrows to
W qcqs; base change and composition make the fibre product qcqs. Apply eventual
section equality to the restrictions along its two projections, using hmatch.
Thinness identifies the two witness arrows to j. At any later stage k, transport
this equality by the section comparison. Composition coherence and restriction
naturality identify it with the restrictions of the original sections transported
along e followed by d. Base change preserves the fibre product. Every pair of
arrows a,a' whose composites into the base change of W agree factors uniquely
through that base changed fibre product. Restriction along this factorization
proves the displayed equality. No finite common-stage choice is made here: this
is only the overlap equation for the two fixed objects. The same proof applies
when the two objects coincide, an overlap is empty, or a sheaf has no sections. -/
theorem etaleSetSection_pair_matching_eventually
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (G : Sheaf (D.obj (op i₀)).smallEtaleTopology (Type (u + 1)))
    (W : (D.obj (op i₀)).Etale) [QuasiCompact W.hom] [QuasiSeparated W.hom]
    (U V : (D.obj (op i₀)).Etale) (f : U ⟶ W) (g : V ⟶ W)
    [QuasiCompact U.hom] [QuasiSeparated U.hom]
    [QuasiCompact V.hom] [QuasiSeparated V.hom]
    (j : Over (op i₀))
    (s : ((Scheme.etaleSetPullback (D.map j.hom)).obj G).obj.obj
      (op ((MorphismProperty.Over.pullback @Etale ⊤ (D.map j.hom)).obj U)))
    (t : ((Scheme.etaleSetPullback (D.map j.hom)).obj G).obj.obj
      (op ((MorphismProperty.Over.pullback @Etale ⊤ (D.map j.hom)).obj V)))
    (hmatch : ∀ (Z : (D.obj (op i₀)).Etale)
      (p : Z ⟶ U) (p' : Z ⟶ V), p ≫ f = p' ≫ g →
      (etaleSetSectionComparison (c.π.app j.left) (D.map j.hom)
        (c.π.app (op i₀)) (c.w j.hom) G Z)
        (((Scheme.etaleSetPullback (D.map j.hom)).obj G).obj.map
          ((MorphismProperty.Over.pullback @Etale ⊤ (D.map j.hom)).map p).op s) =
      (etaleSetSectionComparison (c.π.app j.left) (D.map j.hom)
        (c.π.app (op i₀)) (c.w j.hom) G Z)
        (((Scheme.etaleSetPullback (D.map j.hom)).obj G).obj.map
          ((MorphismProperty.Over.pullback @Etale ⊤ (D.map j.hom)).map p').op t)) :
    ∃ (l : Over (op i₀)) (d : l ⟶ j),
      ∀ (k : Over (op i₀)) (e : k ⟶ l) (Y : (D.obj k.left).Etale)
        (a : Y ⟶ (MorphismProperty.Over.pullback @Etale ⊤ (D.map k.hom)).obj U)
        (a' : Y ⟶ (MorphismProperty.Over.pullback @Etale ⊤ (D.map k.hom)).obj V),
        a ≫ (MorphismProperty.Over.pullback @Etale ⊤ (D.map k.hom)).map f =
          a' ≫ (MorphismProperty.Over.pullback @Etale ⊤ (D.map k.hom)).map g →
        ((Scheme.etaleSetPullback (D.map k.hom)).obj G).obj.map a.op
          ((etaleSetSectionComparison (D.map (e ≫ d).left) (D.map j.hom) (D.map k.hom)
            ((D.map_comp (e ≫ d).left j.hom).symm.trans
              (congrArg (fun t : k.left ⟶ op i₀ ↦ D.map t) (e ≫ d).w)) G U) s) =
        ((Scheme.etaleSetPullback (D.map k.hom)).obj G).obj.map a'.op
          ((etaleSetSectionComparison (D.map (e ≫ d).left) (D.map j.hom) (D.map k.hom)
            ((D.map_comp (e ≫ d).left j.hom).symm.trans
              (congrArg (fun t : k.left ⟶ op i₀ ↦ D.map t) (e ≫ d).w)) G V) t) := by
  classical
  obtain ⟨Z, p, q, hqc, hqs, hpq, hdetect⟩ :=
    etale_pair_restriction_detection W U V f g
  let := hqc
  let := hqs
  let E (j : Over (op i₀)) (A : (D.obj (op i₀)).Etale) :=
    ((Scheme.etaleSetPullback (D.map j.hom)).obj G).obj.obj
      (op ((MorphismProperty.Over.pullback @Etale ⊤ (D.map j.hom)).obj A))
  let r {j k : Over (op i₀)} (a : k ⟶ j) (A : (D.obj (op i₀)).Etale) :
      E j A ⟶ E k A :=
    etaleSetSectionComparison (D.map a.left) (D.map j.hom) (D.map k.hom)
      ((D.map_comp a.left j.hom).symm.trans
        (congrArg (fun t : k.left ⟶ op i₀ ↦ D.map t) a.w)) G A
  let res (j : Over (op i₀)) {A B : (D.obj (op i₀)).Etale} (v : A ⟶ B) :
      E j B ⟶ E j A :=
    ((Scheme.etaleSetPullback (D.map j.hom)).obj G).obj.map
      ((MorphismProperty.Over.pullback @Etale ⊤ (D.map j.hom)).map v).op
  obtain ⟨l, d, d', heq⟩ := etaleSetSectionEventualEquality D c hc i₀ G Z
    j j (res j p s) (res j q t) (hmatch Z p q hpq)
  have hd : d' = d := by
    apply Over.OverMorphism.ext
    exact Subsingleton.elim _ _
  subst d'
  change r d Z (res j p s) = r d Z (res j q t) at heq
  refine ⟨l, d, ?_⟩
  intro k e Y a a' ha
  apply hdetect (D.obj k.left) (D.map k.hom)
    ((Scheme.etaleSetPullback (D.map k.hom)).obj G)
    (r (e ≫ d) U s) (r (e ≫ d) V t) ?_ Y a a' ha
  have hcomp : r d Z ≫ r e Z = r (e ≫ d) Z :=
    (etaleSetSectionComparisonLaws D c i₀ G Z).2.1 j l k d e
  have hn₁ := congrArg (fun z ↦ z s)
    (etaleSetSectionComparison_naturality (D.map (e ≫ d).left) (D.map j.hom)
      (D.map k.hom) ((D.map_comp (e ≫ d).left j.hom).symm.trans
        (congrArg (fun t : k.left ⟶ op i₀ ↦ D.map t) (e ≫ d).w)) G p)
  have hn₂ := congrArg (fun z ↦ z t)
    (etaleSetSectionComparison_naturality (D.map (e ≫ d).left) (D.map j.hom)
      (D.map k.hom) ((D.map_comp (e ≫ d).left j.hom).symm.trans
        (congrArg (fun t : k.left ⟶ op i₀ ↦ D.map t) (e ≫ d).w)) G q)
  change res k p (r (e ≫ d) U s) = r (e ≫ d) Z (res j p s) at hn₁
  change res k q (r (e ≫ d) V t) = r (e ≫ d) Z (res j q t) at hn₂
  have ht := congrArg (r e Z) heq
  have hc₁ := congrArg (fun z ↦ z (res j p s)) hcomp
  have hc₂ := congrArg (fun z ↦ z (res j q t)) hcomp
  exact hn₁.trans (hc₁.symm.trans (ht.trans (hc₂.trans hn₂.symm)))

end AlgebraicGeometry
