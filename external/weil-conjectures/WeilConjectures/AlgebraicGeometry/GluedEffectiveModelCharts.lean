/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.PullbackCarrier
import WeilConjectures.AlgebraicGeometry.DescendedOverlapGlueData
import WeilConjectures.AlgebraicGeometry.FpqcMorphismsDescend
import WeilConjectures.AlgebraicGeometry.GluedEffectiveModelChartsPullback

/-!
# Gluing local effective models along descended overlaps

Source: Stacks Project, Descent, Tag 0AP4, construction of the descended open overlaps.
(blueprint: lem-pd-glued-effective-model-charts).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace CategoryTheory.Over.DescentDatum

/-- Descended pairwise intersections determine the inverse images of glued charts. -/
private theorem glued_chart_preimage
    {V : Scheme.{u}} (G : Scheme.GlueData.{u}) (U : G.J → V.Opens)
    (hcover : ∀ x : V, ∃ i, x ∈ U i)
    (q : ∀ i, (U i).toScheme ⟶ G.U i) (q₀ : V ⟶ G.glued)
    (hcomm : ∀ i, q i ≫ G.ι i = (U i).ι ≫ q₀)
    (hlift : ∀ k i, ∃ r : Limits.pullback (U k).ι (U i).ι ⟶ G.V (k, i),
      IsPullback r (pullback.fst (U k).ι (U i).ι) (G.f k i) (q k)) :
    ∀ i, q₀ ⁻¹ᵁ (G.ι i).opensRange = U i := by
  intro i
  ext x
  constructor
  · intro hx
    obtain ⟨k, hxk⟩ := hcover x
    let xk : (U k).toScheme := ⟨x, hxk⟩
    obtain ⟨z, hz⟩ := hx
    have heq : G.ι k (q k xk) = G.ι i z := by
      rw [← Scheme.Hom.comp_apply, hcomm k]
      exact hz.symm
    obtain ⟨y, hy, _⟩ := (G.ι_eq_iff k i (q k xk) z).mp heq
    obtain ⟨r, hr⟩ := hlift k i
    obtain ⟨a, _, ha⟩ := Scheme.exists_preimage_of_isPullback hr y xk hy
    have hab := congrArg (fun m : Limits.pullback (U k).ι (U i).ι ⟶ V => m a)
      (pullback.condition (f := (U k).ι) (g := (U i).ι))
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, ha] at hab
    change x = ((pullback.snd (U k).ι (U i).ι) a).val at hab
    rw [hab]
    exact ((pullback.snd (U k).ι (U i).ι) a).property
  · intro hx
    refine ⟨q i (⟨x, hx⟩ : (U i).toScheme), ?_⟩
    rw [← Scheme.Hom.comp_apply, hcomm i]
    rfl

/-- Local effective models embed into one scheme, and their charts pull back to the given opens.
Source: Stacks Project, Descent, Tag 0AP4, proof, through the construction of the glued scheme.
(blueprint: lem-pd-glued-effective-model-charts).

Proof: For each pair i,j, take the inverse image of U_j inside U_i. Compatibility of the
restricted transports with D, followed by inverse transport, shows that this open is
invariant under E_i. Since the square for q_i is cartesian, q_i is an fpqc covering and
its double overlap has the canonical transport. Descent of compatible opens (03N0) gives
an open W_ij of W_i pulling back to this intersection. On this intersection the identity
is compatible with both data; descent of morphisms (02W0) gives an isomorphism W_ij to
W_ji. Descend the inverse too. Faithfulness proves the inverse identities and the triple
cocycle, while uniqueness of descended opens identifies the triple overlaps. Use scheme
gluing for these opens and transitions. The structure maps to Y glue because their
restrictions agree; the resulting chart maps j_i are open immersions and cover W. The
maps q_i followed by j_i agree on the intersections of the U_i, so glue to q on V.
The chart square is cartesian: both its source and the inverse image of the chart are
obtained by gluing the intersections with all the U_j, with the same transition maps,
and their local identifications are the cartesian squares for the descended opens.
If the index type is empty, the covering hypothesis forces V empty; take the empty
scheme over Y. This construction asserts only the chart squares, not global effectivity
or transport invariance of q. -/
theorem exists_glued_effective_model_charts
    {X Y : Scheme.{u}} {p : X ⟶ Y}
    (hp : Presieve.singleton p ∈ Scheme.fpqcPrecoverage Y)
    {V : Over X} (D : Over.DescentDatum p V)
    {I : Type u} (U : I → V.left.Opens)
    (hcover : ∀ x : V.left, ∃ i, x ∈ U i)
    (E : ∀ i, Over.DescentDatum p (Over.mk ((U i).ι ≫ V.hom)))
    (hcompat : ∀ (i : I) {T : Scheme.{u}} (f₁ f₂ : T ⟶ X)
      (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ Over.mk ((U i).ι ≫ V.hom)),
      ((E i).transport f₁ f₂ h a).left ≫ (U i).ι =
        (D.transport f₁ f₂ h (Over.homMk (a.left ≫ (U i).ι)
          (by simpa only [Over.mk_hom, Category.assoc] using Over.w a))).left)
    (W : I → Over Y) (q : ∀ i, (U i).toScheme ⟶ (W i).left)
    (hcart : ∀ i, IsPullback (q i) ((U i).ι ≫ V.hom) (W i).hom p)
    (hinv : ∀ (i : I) {T : Scheme.{u}} (f₁ f₂ : T ⟶ X)
      (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ Over.mk ((U i).ι ≫ V.hom)),
      ((E i).transport f₁ f₂ h a).left ≫ q i = a.left ≫ q i) :
    ∃ (W₀ : Over Y) (q₀ : V.left ⟶ W₀.left) (j : ∀ i, (W i).left ⟶ W₀.left),
      (∀ i, IsOpenImmersion (j i)) ∧
      (∀ w : W₀.left, ∃ i, ∃ z : (W i).left, j i z = w) ∧
      (∀ i, j i ≫ W₀.hom = (W i).hom) ∧
      (∀ i, IsPullback (q i) (U i).ι (j i) q₀) := by
  obtain ⟨Z, f, t, hf, hdiag, ht, ⟨t', ht', hcoc⟩, hlift⟩ :=
    exists_descended_overlap_glue_data hp D U E hcompat W q hcart hinv
  have hq (i : I) : Presieve.singleton (q i) ∈ Scheme.fpqcPrecoverage (W i).left := by
    rw [← Presieve.ofArrows_pUnit.{0}] at hp ⊢
    exact Precoverage.mem_coverings_of_isPullback (fun _ : PUnit.{1} => p) hp
      (W i).hom (fun _ => q i) (fun _ => (U i).ι ≫ V.hom) (fun _ => hcart i)
  have hbase (i k : I) : f i k ≫ (W i).hom = t i k ≫ f k i ≫ (W k).hom := by
    obtain ⟨r, hr, hr₂⟩ := hlift i k
    have hqr : Presieve.singleton r ∈ Scheme.fpqcPrecoverage (Z (i, k)) := by
      have hqi := hq i
      rw [← Presieve.ofArrows_pUnit.{0}] at hqi ⊢
      exact Precoverage.mem_coverings_of_isPullback (fun _ : PUnit.{1} => q i) hqi
        (f i k) (fun _ => r) (fun _ => pullback.fst (U i).ι (U k).ι) (fun _ => hr)
    obtain ⟨hsurj, hflat⟩ :=
      (Scheme.singleton_mem_precoverage_iff (P := @Flat) r).mp hqr.2
    have : Surjective r := ⟨hsurj⟩
    have : Flat r := hflat
    have : Epi r := Flat.epi_of_flat_of_surjective r
    apply (cancel_epi r).mp
    calc
      r ≫ f i k ≫ (W i).hom =
          pullback.fst (U i).ι (U k).ι ≫ q i ≫ (W i).hom := by
        simpa only [Category.assoc] using congrArg (fun a => a ≫ (W i).hom) hr.w
      _ = pullback.fst (U i).ι (U k).ι ≫ (U i).ι ≫ V.hom ≫ p := by
        rw [(hcart i).w]; simp only [Category.assoc]
      _ = pullback.snd (U i).ι (U k).ι ≫ (U k).ι ≫ V.hom ≫ p := by
        rw [pullback.condition_assoc]
      _ = pullback.snd (U i).ι (U k).ι ≫ q k ≫ (W k).hom := by
        rw [(hcart k).w]; simp only [Category.assoc]
      _ = r ≫ t i k ≫ f k i ≫ (W k).hom := by
        simpa only [Category.assoc] using congrArg (fun a => a ≫ (W k).hom) hr₂.symm
  let G : Scheme.GlueData := {
    J := I
    U := fun i => (W i).left
    V := Z
    f := f
    f_open := hf
    f_mono := fun i k => by
      have := hf i k
      infer_instance
    f_id := hdiag
    t := t
    t_id := ht
    t' := t'
    t_fac := ht'
    cocycle := hcoc }
  have : HasMulticoequalizer G.toGlueData.diagram :=
    Scheme.GlueData.instHasMulticoequalizerDiagram G
  let a : G.glued ⟶ Y := Multicoequalizer.desc G.toGlueData.diagram Y
    (fun i => (W i).hom) (fun ik => hbase ik.1 ik.2)
  have hagree (i k : I) : pullback.fst (U i).ι (U k).ι ≫ q i ≫ G.ι i =
      pullback.snd (U i).ι (U k).ι ≫ q k ≫ G.ι k := by
    obtain ⟨r, hr, hr₂⟩ := hlift i k
    calc
      pullback.fst (U i).ι (U k).ι ≫ q i ≫ G.ι i =
          r ≫ f i k ≫ G.ι i := by
        simpa only [Category.assoc] using congrArg (fun a => a ≫ G.ι i) hr.w.symm
      _ = r ≫ t i k ≫ f k i ≫ G.ι k := by
        rw [← G.glue_condition i k]
      _ = pullback.snd (U i).ι (U k).ι ≫ q k ≫ G.ι k := by
        simpa only [Category.assoc] using congrArg (fun a => a ≫ G.ι k) hr₂
  have hU : TopologicalSpace.IsOpenCover U := by
    change iSup U = ⊤
    apply top_le_iff.mp
    intro x hx
    exact TopologicalSpace.Opens.mem_iSup.mpr (hcover x)
  let 𝒰 := V.left.openCoverOfIsOpenCover U hU
  let q₀ : V.left ⟶ G.glued := 𝒰.glueMorphisms (fun i => q i ≫ G.ι i) hagree
  have hcomm (i : I) : q i ≫ G.ι i = (U i).ι ≫ q₀ :=
    (𝒰.ι_glueMorphisms (fun i => q i ≫ G.ι i) hagree i).symm
  have hpreimage := glued_chart_preimage G U hcover q q₀ hcomm
    (fun k i => by
      obtain ⟨r, hr, _⟩ := hlift k i
      exact ⟨r, hr⟩)
  refine ⟨Over.mk a, q₀, G.ι, G.ι_isOpenImmersion, G.ι_jointly_surjective, ?_, ?_⟩
  · intro i
    exact Multicoequalizer.π_desc G.toGlueData.diagram Y
      (fun i => (W i).hom) (fun ik => hbase ik.1 ik.2) i
  · exact glued_model_chart_pullbacks (I := I) U W q (Over.mk a) q₀ G.ι hcart
      G.ι_isOpenImmersion G.ι_jointly_surjective
      (fun i => Multicoequalizer.π_desc G.toGlueData.diagram Y
        (fun i => (W i).hom) (fun ik => hbase ik.1 ik.2) i) hcomm hpreimage

end CategoryTheory.Over.DescentDatum
