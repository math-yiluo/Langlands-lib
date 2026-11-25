/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSetSectionComparison
import WeilConjectures.AlgebraicGeometry.EtaleSetSectionPairMatchingEventually
import Mathlib.CategoryTheory.Filtered.Final

/-! # Finite matching equations become effective at a stage
Source: Stacks Project, Tags 03Q4 and 09YQ, finite overlap reduction.
(blueprint: lem-weil-pbc-sets-section-finite-matching). -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Source: Stacks Project, Tags 03Q4 and 09YQ, finite overlap reduction, using
section eventual equality on qcqs objects.
(blueprint: lem-weil-pbc-sets-section-finite-matching).
Proof: for each pair b,b', form the fibre product Z = V b ×_W V b' in the
small etale category of the base. Its structure morphism is qcqs: the maps
V b → W are qcqs by cancellation against the qcqs structure map of W, and
quasi-compact and quasi-separated morphisms are stable under base change and
composition. Restrict the two stage sections to Z. The hypothesis applied to
its projections says that their limit images agree. Apply section eventual
equality on Z to obtain a later stage at which they agree. The two arrows back
to j agree because the indexing preorder is thin. Choose a common predecessor
of j and the finitely many stages, using cofilteredness. Composition coherence
preserves all equations there, and naturality identifies them with restrictions
of the transported sections. Base change preserves each fibre product. Thus any
two stage arrows with equal composites into W factor through its base changed
fibre product. Restricting its equality along this factorization proves the
claimed matching equation. If n = 0 there are no pairs: take l = j and its
identity arrow, and the matching condition has no instances. This statement
requires no covering, no affine lifting hypothesis, and no global limit section;
it only makes finitely many given matching equations effective. -/
theorem etaleSetSection_finite_matching
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (G : Sheaf (D.obj (op i₀)).smallEtaleTopology (Type (u + 1)))
    (W : (D.obj (op i₀)).Etale) [QuasiCompact W.hom] [QuasiSeparated W.hom]
    {n : ℕ} (V : Fin n → (D.obj (op i₀)).Etale) (f : ∀ b, V b ⟶ W)
    (hqc : ∀ b, QuasiCompact (V b).hom) (hqs : ∀ b, QuasiSeparated (V b).hom)
    (j : Over (op i₀))
    (s : ∀ b, ((Scheme.etaleSetPullback (D.map j.hom)).obj G).obj.obj
      (op ((MorphismProperty.Over.pullback @Etale ⊤ (D.map j.hom)).obj (V b))))
    (hmatch : ∀ (Z : (D.obj (op i₀)).Etale) (b b' : Fin n)
      (p : Z ⟶ V b) (p' : Z ⟶ V b'), p ≫ f b = p' ≫ f b' →
      (etaleSetSectionComparison (c.π.app j.left) (D.map j.hom)
        (c.π.app (op i₀)) (c.w j.hom) G Z)
        (((Scheme.etaleSetPullback (D.map j.hom)).obj G).obj.map
          ((MorphismProperty.Over.pullback @Etale ⊤ (D.map j.hom)).map p).op (s b)) =
      (etaleSetSectionComparison (c.π.app j.left) (D.map j.hom)
        (c.π.app (op i₀)) (c.w j.hom) G Z)
        (((Scheme.etaleSetPullback (D.map j.hom)).obj G).obj.map
          ((MorphismProperty.Over.pullback @Etale ⊤ (D.map j.hom)).map p').op (s b'))) :
    ∃ (l : Over (op i₀)) (d : l ⟶ j),
      ∀ (Y : (D.obj l.left).Etale) (b b' : Fin n)
        (a : Y ⟶ (MorphismProperty.Over.pullback @Etale ⊤ (D.map l.hom)).obj (V b))
        (a' : Y ⟶ (MorphismProperty.Over.pullback @Etale ⊤ (D.map l.hom)).obj (V b')),
        a ≫ (MorphismProperty.Over.pullback @Etale ⊤ (D.map l.hom)).map (f b) =
          a' ≫ (MorphismProperty.Over.pullback @Etale ⊤ (D.map l.hom)).map (f b') →
        ((Scheme.etaleSetPullback (D.map l.hom)).obj G).obj.map a.op
          ((etaleSetSectionComparison (D.map d.left) (D.map j.hom) (D.map l.hom)
            ((D.map_comp d.left j.hom).symm.trans
              (congrArg (fun t : l.left ⟶ op i₀ ↦ D.map t) d.w)) G (V b)) (s b)) =
        ((Scheme.etaleSetPullback (D.map l.hom)).obj G).obj.map a'.op
          ((etaleSetSectionComparison (D.map d.left) (D.map j.hom) (D.map l.hom)
            ((D.map_comp d.left j.hom).symm.trans
              (congrArg (fun t : l.left ⟶ op i₀ ↦ D.map t) d.w)) G (V b')) (s b')) := by
  classical
  have hpair (x : Fin n × Fin n) := by
    letI := hqc x.1
    letI := hqc x.2
    letI := hqs x.1
    letI := hqs x.2
    exact etaleSetSection_pair_matching_eventually D c hc i₀ G W
      (V x.1) (V x.2) (f x.1) (f x.2) j (s x.1) (s x.2)
      (fun Z p p' h ↦ hmatch Z x.1 x.2 p p' h)
  let L (x : Fin n × Fin n) := (hpair x).choose
  let A (x : Fin n × Fin n) : L x ⟶ j := (hpair x).choose_spec.choose
  obtain ⟨l, hl⟩ := IsCofiltered.inf_objs_exists (insert j (Finset.univ.image L))
  let d : l ⟶ j := (hl (Finset.mem_insert_self _ _)).some
  let e (x : Fin n × Fin n) : l ⟶ L x :=
    (hl (Finset.mem_insert_of_mem
      (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩))).some
  refine ⟨l, d, ?_⟩
  intro Y b b' a a' ha
  have hw : e (b, b') ≫ A (b, b') = d := by
    apply Over.OverMorphism.ext
    exact Subsingleton.elim _ _
  have heq := (hpair (b, b')).choose_spec.choose_spec l (e (b, b')) Y a a' ha
  simpa only [← hw] using heq


end AlgebraicGeometry
