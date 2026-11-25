/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.AlgebraicGeometry.Finite.FinitePresentationFamilyDescent
import WeilConjectures.AlgebraicGeometry.Finite.FinitePresentationArrowsDescent
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.AlgebraicGeometry.Curve.GenericModelAux
import WeilConjectures.AlgebraicGeometry.DescendFinite
import WeilConjectures.AlgebraicGeometry.DescendSurjective
import WeilConjectures.AlgebraicGeometry.EtaleInverseLimitDescent
import WeilConjectures.AlgebraicGeometry.EventuallyProper
import WeilConjectures.AlgebraicGeometry.IsOpenImmersion.OpenImmersionInverseLimitDescent
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.DescendSmoothQcqs
import Mathlib.Order.Filter.AtTopBot.Finite
public import Mathlib.Basic.Finite.Prod
public import Mathlib.Basic.Finite.Sigma
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Data.Fintype.Shrink

/-!
# Common-stage descent of finite chains with a finite comparison

Source: Stacks Project, Limits, Tags 01ZM, 01ZO, 07RR, 07RP, 0EUU, 0C0C and 081F.
-/

@[expose] public section

universe u v
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

private theorem chain_over_square {S R : Scheme.{u}} (b : R ⟶ S)
    {X Y : Over S} (f : X ⟶ Y) :
    IsPullback (pullback.fst X.hom b) ((Over.pullback b).map f).left f.left
      (pullback.fst Y.hom b) := by
  refine IsPullback.of_bot ?_ (by simp) (IsPullback.of_hasPullback Y.hom b)
  simpa [Over.w f] using IsPullback.of_hasPullback X.hom b

private theorem chain_property_iff (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {S R : Scheme.{u}} (b : R ⟶ S) {X Y : Over S} (f : X ⟶ Y)
    {X' Y' : Scheme.{u}} (x : X' ⟶ X.left) (y : Y' ⟶ Y.left)
    (px : X' ⟶ R) (py : Y' ⟶ R) (g : X' ⟶ Y')
    (hx : IsPullback x px X.hom b) (hy : IsPullback y py Y.hom b)
    (hxy : g ≫ y = x ≫ f.left) (hg : g ≫ py = px) :
    P ((Over.pullback b).map f).left ↔ P g := by
  have he : hx.isoPullback.hom ≫ ((Over.pullback b).map f).left =
      g ≫ hy.isoPullback.hom := by
    apply pullback.hom_ext
    · simpa [Over.pullback_map_left] using hxy.symm
    · simpa [Over.pullback_map_left] using hg.symm
  rw [← P.cancel_left_of_respectsIso hx.isoPullback.hom _, he,
    P.cancel_right_of_respectsIso]

private theorem chain_property_comp (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] {S T R : Scheme.{u}}
    (p : T ⟶ S) (q : R ⟶ T) {X Y : Over S} (f : X ⟶ Y)
    (hf : P ((Over.pullback p).map f).left) :
    P ((Over.pullback (q ≫ p)).map f).left := by
  let a := pullback.map X.hom (q ≫ p) X.hom p (𝟙 _) q (𝟙 _) (by simp) (by simp)
  let b := pullback.map Y.hom (q ≫ p) Y.hom p (𝟙 _) q (𝟙 _) (by simp) (by simp)
  have h : IsPullback a ((Over.pullback (q ≫ p)).map f).left
      ((Over.pullback p).map f).left b := by
    apply IsPullback.flip
    apply IsPullback.of_bot (t := (chain_over_square p f).flip) (s := ?_) ?_
    · simpa [a, b] using (chain_over_square (q ≫ p) f).flip
    · apply pullback.hom_ext <;> simp [a, b, Over.pullback_map_left]
  exact P.of_isPullback h hf

private theorem chain_eventually (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange]
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (i₀ : I)
    {X Y : Over (D.obj (op i₀))} (f : X ⟶ Y)
    (h : ∃ (i : I) (hi : i₀ ≤ i),
      P ((Over.pullback (D.map (homOfLE hi).op)).map f).left) :
    ∀ᶠ i in Filter.atTop, ∀ hi : i₀ ≤ i,
      P ((Over.pullback (D.map (homOfLE hi).op)).map f).left := by
  obtain ⟨i, hi, hP⟩ := h
  apply Filter.eventually_atTop.mpr
  refine ⟨i, fun j hij hj ↦ ?_⟩
  have he : D.map (homOfLE hj).op =
      D.map (homOfLE hij).op ≫ D.map (homOfLE hi).op := by
    rw [← D.map_comp]
    congr 1
  rw [he]
  exact chain_property_comp P _ _ f hP

private theorem chain_proper_stage
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    [CompactSpace (D.obj (op i₀))] [QuasiSeparatedSpace (D.obj (op i₀))]
    (X Y : Over (D.obj (op i₀)))
    [CompactSpace X.left] [QuasiSeparatedSpace X.left]
    [CompactSpace Y.left] [QuasiSeparatedSpace Y.left]
    (f : X ⟶ Y) [LocallyOfFiniteType f.left]
    (hf : IsProper ((Over.pullback (c.π.app (op i₀))).map f).left) :
    ∃ (i : I) (hi : i₀ ≤ i),
      IsProper ((Over.pullback (D.map (homOfLE hi).op)).map f).left := by
  have hf' : IsProper (pullback.map X.hom (c.π.app (op i₀)) Y.hom
      (c.π.app (op i₀)) f.left (𝟙 _) (𝟙 _) (by simp [Over.w f]) (by simp)) := by
    simpa [Over.pullback_map_left, pullback.map] using hf
  obtain ⟨i, hi, h⟩ := exists_isProper_baseChange_of_isLimit D c hc i₀
    X.hom Y.hom f.left (Over.w f) hf'
  refine ⟨i, hi, ?_⟩
  simpa [Over.pullback_map_left, pullback.map] using h

/-- Descend edges between specified vertex models. No equations between different
edges are imposed; all edges are morphisms over the base. -/
private theorem chain_descend_edges
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {i j : I} (a : i ⟶ j), IsAffineHom (D.map a)]
    [∀ i : I, CompactSpace (D.obj i)]
    [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (i : I)
    {J : Type v} (V : J → Scheme.{u}) (q : ∀ a, V a ⟶ D.obj i)
    [∀ a, LocallyOfFinitePresentation (q a)] [∀ a, QuasiCompact (q a)]
    [∀ a, QuasiSeparated (q a)]
    (X : J → Scheme.{u}) (p : ∀ a, X a ⟶ c.pt) (h : ∀ a, X a ⟶ V a)
    (H : ∀ a, IsPullback (h a) (p a) (q a) (c.π.app i))
    {K : Type v} [Finite K] (s t : K → J)
    (f : ∀ a, X (s a) ⟶ X (t a)) (hf : ∀ a, f a ≫ p (t a) = p (s a)) :
    ∃ (j : I) (b : j ⟶ i)
      (g : ∀ a, pullback (q (s a)) (D.map b) ⟶ pullback (q (t a)) (D.map b)),
      (∀ a, g a ≫ pullback.snd _ _ = pullback.snd _ _) ∧
      ∀ a, isPullbackLift D c b (H (s a)) ≫ g a =
        f a ≫ isPullbackLift D c b (H (t a)) := by
  let ψ (a : K) : pullback (q (s a)) (c.π.app i) ⟶ V (t a) :=
    (H (s a)).isoPullback.inv ≫ f a ≫ h (t a)
  have hψ (a : K) : ψ a ≫ q (t a) =
      pullback.fst (q (s a)) (c.π.app i) ≫ q (s a) := by
    calc
      ψ a ≫ q (t a) =
          (H (s a)).isoPullback.inv ≫ f a ≫ p (t a) ≫ c.π.app i := by
        simp only [ψ, Category.assoc, (H (t a)).w]
      _ = (H (s a)).isoPullback.inv ≫ p (s a) ≫ c.π.app i := by
        rw [← Category.assoc (f a), hf a]
      _ = pullback.snd (q (s a)) (c.π.app i) ≫ c.π.app i := by
        rw [← Category.assoc, IsPullback.isoPullback_inv_snd]
      _ = _ := pullback.condition.symm
  obtain ⟨j, b, θ, hθ, heq⟩ := exists_finitePresentation_arrows_stage D c hc i
    (fun a ↦ V (s a)) (fun a ↦ V (t a)) (fun a ↦ q (s a)) (fun a ↦ q (t a)) ψ hψ
  let g (a : K) := pullback.lift (θ a) (pullback.snd (q (s a)) (D.map b))
    (hθ a |>.trans (pullback.condition))
  refine ⟨j, b, g, fun a ↦ by simp [g], fun a ↦ ?_⟩
  apply pullback.hom_ext
  · simp only [Category.assoc, g, pullback.lift_fst]
    have he : isPullbackLift D c b (H (s a)) =
        (H (s a)).isoPullback.hom ≫
          pullback.map (q (s a)) (c.π.app i) (q (s a)) (D.map b)
            (𝟙 _) (c.π.app j) (𝟙 _) (by simp) (by simp) := by
      apply pullback.hom_ext <;> simp
    rw [he, Category.assoc, heq a]
    simp [ψ]
  · simp only [Category.assoc, g, pullback.lift_snd, isPullbackLift_snd]
    simpa only [Category.assoc] using
      congrArg (fun z ↦ z ≫ c.π.app j) (hf a).symm

private theorem chain_lift_natural
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {i j : I} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) {i j : I} (b : j ⟶ i)
    {X Y : Over (D.obj i)} (f : X ⟶ Y)
    {X' Y' : Scheme.{u}} (x : X' ⟶ X.left) (y : Y' ⟶ Y.left)
    (px : X' ⟶ c.pt) (py : Y' ⟶ c.pt) (g : X' ⟶ Y')
    (hx : IsPullback x px X.hom (c.π.app i))
    (hy : IsPullback y py Y.hom (c.π.app i))
    (hxy : x ≫ f.left = g ≫ y) (hg : g ≫ py = px) :
    isPullbackLift D c b hx ≫ ((Over.pullback (D.map b)).map f).left =
      g ≫ isPullbackLift D c b hy := by
  apply pullback.hom_ext
  · simpa only [Category.assoc, Over.pullback_map_left, pullback.lift_fst,
      isPullbackLift_fst_assoc, isPullbackLift_fst] using hxy
  · simpa only [Category.assoc, Over.pullback_map_left, pullback.lift_snd,
      isPullbackLift_snd] using
      congrArg (fun m ↦ m ≫ c.π.app j) hg.symm

private theorem chain_sigma_compact {J : Type v} [Finite J]
    (V : J → Scheme.{u}) [∀ a, CompactSpace (V a)] : CompactSpace (∐ V : Scheme.{u}) := by
  let V' (k : Shrink.{u} J) := V ((equivShrink.{u, v} J).symm k)
  let e : (∐ V') ≅ ∐ V := Sigma.reindex (equivShrink.{u, v} J).symm V
  exact ((sigmaMk V').trans (Scheme.homeoOfIso e)).compactSpace

private theorem chain_sigma_qs {J : Type v} [Finite J]
    (V : J → Scheme.{u}) [∀ a, QuasiSeparatedSpace (V a)] :
    QuasiSeparatedSpace (∐ V : Scheme.{u}) := by
  classical
  let V' (k : Shrink.{u} J) := V ((equivShrink.{u, v} J).symm k)
  let e : (∐ V') ≅ ∐ V := Sigma.reindex (equivShrink.{u, v} J).symm V
  have hqs : QuasiSeparatedSpace (Σ a, V' a) := by
    constructor
    intro U W hU hcU hW hcW
    have h (a : Shrink.{u} J) : IsCompact (Sigma.mk a ⁻¹' (U ∩ W)) := by
      rw [Set.preimage_inter]
      exact QuasiSeparatedSpace.inter_isCompact _ _
        (hU.preimage continuous_sigmaMk)
        (Topology.IsClosedEmbedding.sigmaMk.isCompact_preimage hcU)
        (hW.preimage continuous_sigmaMk)
        (Topology.IsClosedEmbedding.sigmaMk.isCompact_preimage hcW)
    have he : U ∩ W = ⋃ a, Sigma.mk a '' (Sigma.mk a ⁻¹' (U ∩ W)) := by
      apply Set.Subset.antisymm
      · rintro ⟨a, x⟩ hx
        exact Set.mem_iUnion.mpr ⟨a, x, hx, rfl⟩
      · rintro x hx
        obtain ⟨a, y, hy, rfl⟩ := Set.mem_iUnion.mp hx
        exact hy
    rw [he]
    exact isCompact_iUnion fun a ↦ (h a).image continuous_sigmaMk
  exact (quasiSeparatedSpace_congr ((sigmaMk V').trans (Scheme.homeoOfIso e))).mp hqs

private theorem chain_fp_arrow {S : Scheme.{u}} (X Y : Over S) (f : X ⟶ Y)
    [LocallyOfFinitePresentation X.hom] [LocallyOfFinitePresentation Y.hom] :
    LocallyOfFinitePresentation f.left := by
  have : LocallyOfFinitePresentation (f.left ≫ Y.hom) := by
    rw [Over.w f]
    infer_instance
  exact locallyOfFinitePresentation_of_comp f.left Y.hom

/-- Spread finitely many chains `A → B → C → lim D`, and a finite surjection from
`∐ A` to a specified finite-presentation model, to one common stage. The assertions
on arrows are precisely the limit properties stable under the cited descent results.
No generic point, radicial cover, field extension or fibre geometry is involved.

Source: Stacks Project, Limits, Tags 01ZM, 01ZO, 07RR, 07RP, 0EUU, 0C0C and 081F;
the diagram-descent paragraph of More on Morphisms, Tag 0GK7.
(blueprint: lem-weil-pbc-finite-presentation-chain-descent)

Proof: Descend the finite family A, B, C by 01ZM(1), together with the already
specified model E. Descend A→B, B→C and A→E by 01ZM(2) at a common stage. Their
structure equations agree after the limit pullback, so 01ZM(3) makes them agree
at a common later stage. Take the coproduct of the A models; universality of
scheme coproducts identifies its limit pullback with the supplied coproduct.
All these models and their arrows are of finite presentation and qcqs. Apply
finite descent 01ZO and surjectivity descent 07RR to its comparison with E,
finite descent 01ZO and etale descent 07RP to the C structure maps, open immersion
descent 0EUU to A→B, and smooth descent 0C0C and proper descent 081F to B→C.
There are finitely many conditions, so a common later stage satisfies them all;
base change preserves every condition already obtained. Pullback cancellation
and the arrow equations supply the three object comparisons, their compatibility
with the two chain arrows, and the cartesian square for the coproduct comparison.
This argument also covers an empty family, since its coproduct is initial and
all indexed conditions are vacuous.
-/
theorem exists_finitePresentation_chain_stage
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (i₀ : Iᵒᵖ)
    (E : Scheme.{u}) (e : E ⟶ D.obj i₀)
    [LocallyOfFinitePresentation e] [QuasiCompact e] [QuasiSeparated e]
    {κ : Type v} [Finite κ] (A B C : κ → Scheme.{u})
    (j₀ : ∀ i, A i ⟶ B i) (p₀ : ∀ i, B i ⟶ C i)
    (t₀ : ∀ i, C i ⟶ c.pt)
    [∀ i, LocallyOfFinitePresentation (j₀ i ≫ p₀ i ≫ t₀ i)]
    [∀ i, QuasiCompact (j₀ i ≫ p₀ i ≫ t₀ i)]
    [∀ i, QuasiSeparated (j₀ i ≫ p₀ i ≫ t₀ i)]
    [∀ i, LocallyOfFinitePresentation (p₀ i ≫ t₀ i)]
    [∀ i, QuasiCompact (p₀ i ≫ t₀ i)]
    [∀ i, QuasiSeparated (p₀ i ≫ t₀ i)]
    [∀ i, LocallyOfFinitePresentation (t₀ i)]
    [∀ i, QuasiCompact (t₀ i)] [∀ i, QuasiSeparated (t₀ i)]
    (ν₀ : (∐ A) ⟶ pullback e (c.π.app i₀))
    (hν₀ : IsFinite ν₀ ∧ Surjective ν₀)
    (hcomm : ∀ i, Sigma.ι A i ≫ ν₀ ≫ pullback.snd _ _ =
      j₀ i ≫ p₀ i ≫ t₀ i)
    (ht₀ : ∀ i, IsFinite (t₀ i) ∧ Etale (t₀ i))
    (hj₀ : ∀ i, IsOpenImmersion (j₀ i))
    (hp₀ : ∀ i, Smooth (p₀ i) ∧ IsProper (p₀ i)) :
    ∃ (i : Iᵒᵖ) (a : i ⟶ i₀)
      (T Y Ybar : κ → Scheme.{u}) (t : ∀ k, T k ⟶ D.obj i)
      (j : ∀ k, Y k ⟶ Ybar k) (p : ∀ k, Ybar k ⟶ T k)
      (ν : (∐ Y) ⟶ pullback e (D.map a)),
      IsFinite ν ∧ Surjective ν ∧
      (∀ k, Sigma.ι Y k ≫ ν ≫ pullback.snd _ _ = j k ≫ p k ≫ t k) ∧
      (∀ k, IsFinite (t k) ∧ Etale (t k)) ∧
      (∀ k, IsOpenImmersion (j k)) ∧ (∀ k, Smooth (p k) ∧ IsProper (p k)) ∧
      ∃ (hA : ∀ k, A k ⟶ Y k) (hB : ∀ k, B k ⟶ Ybar k)
        (hC : ∀ k, C k ⟶ T k),
        (∀ k, IsPullback (hA k) (j₀ k ≫ p₀ k ≫ t₀ k)
            (j k ≫ p k ≫ t k) (c.π.app i) ∧
          IsPullback (hB k) (p₀ k ≫ t₀ k) (p k ≫ t k) (c.π.app i) ∧
          IsPullback (hC k) (t₀ k) (t k) (c.π.app i) ∧
          hA k ≫ j k = j₀ k ≫ hB k ∧ hB k ≫ p k = p₀ k ≫ hC k) ∧
        ∃ aE : pullback e (c.π.app i₀) ⟶ pullback e (D.map a),
          IsPullback (Limits.Sigma.map hA) ν₀ ν aE ∧
            aE ≫ pullback.snd _ _ = pullback.snd _ _ ≫ c.π.app i := by
  classical
  let L := κ ⊕ κ ⊕ κ
  let X : L → Scheme.{u} := Sum.elim A (Sum.elim B C)
  let r : ∀ k, X k ⟶ c.pt :=
    Sum.rec (fun k ↦ j₀ k ≫ p₀ k ≫ t₀ k) (Sum.rec (fun k ↦ p₀ k ≫ t₀ k) t₀)
  have hrfp : ∀ k, LocallyOfFinitePresentation (r k) := by
    rintro (k | k | k) <;> dsimp [r] <;> infer_instance
  have hrqc : ∀ k, QuasiCompact (r k) := by
    rintro (k | k | k) <;> dsimp [r] <;> infer_instance
  have hrqs : ∀ k, QuasiSeparated (r k) := by
    rintro (k | k | k) <;> dsimp [r] <;> infer_instance
  obtain ⟨i, V, q, h, hfp, hqc, hqs, H⟩ :=
    @exists_finitePresentation_family_stage.{u, v} Iᵒᵖ inferInstance inferInstance D
      inferInstance inferInstance inferInstance c hc L inferInstance X r hrfp hrqc hrqs
  have := hfp
  have := hqc
  have := hqs
  let i₁ := IsCofiltered.min i i₀
  let b : i₁ ⟶ i := IsCofiltered.minToLeft i i₀
  let a : i₁ ⟶ i₀ := IsCofiltered.minToRight i i₀
  let V₁ (k : L) : Scheme.{u} := pullback (q k) (D.map b)
  let q₁ (k : L) : V₁ k ⟶ D.obj i₁ := pullback.snd _ _
  let h₁ (k : L) : X k ⟶ V₁ k := isPullbackLift D c b (H k)
  have H₁ (k : L) : IsPullback (h₁ k) (r k) (q₁ k) (c.π.app i₁) :=
    isPullback_isPullbackLift b (H k)
  have hq₁fp : ∀ k, LocallyOfFinitePresentation (q₁ k) := fun k ↦ inferInstance
  have hq₁qc : ∀ k, QuasiCompact (q₁ k) := fun k ↦ inferInstance
  have hq₁qs : ∀ k, QuasiSeparated (q₁ k) := fun k ↦ inferInstance
  let E₁ : Scheme.{u} := pullback e (D.map a)
  let e₁ : E₁ ⟶ D.obj i₁ := pullback.snd _ _
  let hE₁ : pullback e (c.π.app i₀) ⟶ E₁ :=
    isPullbackLift D c a (IsPullback.of_hasPullback e (c.π.app i₀))
  have HE₁ : IsPullback hE₁ (pullback.snd _ _) e₁ (c.π.app i₁) :=
    isPullback_isPullbackLift a (IsPullback.of_hasPullback e (c.π.app i₀))
  let J := Option L
  let W : J → Scheme.{u} := Option.rec E₁ V₁
  let w : ∀ k, W k ⟶ D.obj i₁ := Option.rec e₁ q₁
  let Z : J → Scheme.{u} := Option.rec (pullback e (c.π.app i₀)) X
  let z : ∀ k, Z k ⟶ c.pt := Option.rec (pullback.snd _ _) r
  let hZ : ∀ k, Z k ⟶ W k := Option.rec hE₁ h₁
  have HW : ∀ k, IsPullback (hZ k) (z k) (w k) (c.π.app i₁) :=
    Option.rec HE₁ H₁
  have hwfp : ∀ k, LocallyOfFinitePresentation (w k) := by
    rintro (_ | k)
    · exact inferInstanceAs (LocallyOfFinitePresentation (pullback.snd e (D.map a)))
    · exact hq₁fp k
  have hwqc : ∀ k, QuasiCompact (w k) := by
    rintro (_ | k)
    · exact inferInstanceAs (QuasiCompact (pullback.snd e (D.map a)))
    · exact hq₁qc k
  have hwqs : ∀ k, QuasiSeparated (w k) := by
    rintro (_ | k)
    · exact inferInstanceAs (QuasiSeparated (pullback.snd e (D.map a)))
    · exact hq₁qs k
  let s : L → J := Sum.elim (fun k ↦ some (.inl k))
    (Sum.elim (fun k ↦ some (.inr (.inl k))) (fun k ↦ some (.inl k)))
  let t : L → J := Sum.elim (fun k ↦ some (.inr (.inl k)))
    (Sum.elim (fun k ↦ some (.inr (.inr k))) (fun _ ↦ none))
  let f : ∀ k, Z (s k) ⟶ Z (t k) :=
    Sum.rec j₀ (Sum.rec p₀ (fun k ↦ Sigma.ι A k ≫ ν₀))
  have hf : ∀ k, f k ≫ z (t k) = z (s k) := by
    rintro (k | k | k)
    · rfl
    · rfl
    · exact hcomm k
  obtain ⟨i₂, b₂, g, hgw, hg⟩ :=
    @chain_descend_edges.{u, v} Iᵒᵖ inferInstance inferInstance D
      inferInstance inferInstance inferInstance c hc i₁ J W w hwfp hwqc hwqs
      Z z hZ HW L inferInstance s t f hf
  let hpb₂ (k : J) : HasPullback (w k) (D.map b₂) :=
    (inferInstance : HasLimitsOfShape WalkingCospan Scheme.{u}).has_limit _
  let W₂ (k : J) : Scheme.{u} :=
    @pullback Scheme.{u} inferInstance (W k) (D.obj i₂) (D.obj i₁)
      (w k) (D.map b₂) (hpb₂ k)
  let w₂ (k : J) : W₂ k ⟶ D.obj i₂ :=
    @pullback.snd Scheme.{u} inferInstance (W k) (D.obj i₂) (D.obj i₁)
      (w k) (D.map b₂) (hpb₂ k)
  let h₂ (k : J) : Z k ⟶ W₂ k := isPullbackLift D c b₂ (HW k)
  have H₂ (k : J) : IsPullback (h₂ k) (z k) (w₂ k) (c.π.app i₂) :=
    isPullback_isPullbackLift b₂ (HW k)
  let Y (k : κ) : Scheme.{u} := W₂ (some (.inl k))
  let Ybar (k : κ) : Scheme.{u} := W₂ (some (.inr (.inl k)))
  let T (k : κ) : Scheme.{u} := W₂ (some (.inr (.inr k)))
  let hA₂ (k : κ) : A k ⟶ Y k := h₂ (some (.inl k))
  let j (k : κ) : Y k ⟶ Ybar k := g (.inl k)
  let p (k : κ) : Ybar k ⟶ T k := g (.inr (.inl k))
  let t₂ (k : κ) : T k ⟶ D.obj i₂ := w₂ (some (.inr (.inr k)))
  let ν : (∐ Y) ⟶ W₂ none := Sigma.desc (fun k ↦ g (.inr (.inr k)))
  have hjw (k : κ) : j k ≫ w₂ (some (.inr (.inl k))) = w₂ (some (.inl k)) :=
    hgw (.inl k)
  have hpw (k : κ) : p k ≫ t₂ k = w₂ (some (.inr (.inl k))) :=
    hgw (.inr (.inl k))
  have hνw : ν ≫ w₂ none = Sigma.desc (fun k ↦ w₂ (some (.inl k))) := by
    apply Sigma.hom_ext
    intro k
    simp only [ν, Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc]
    exact hgw (.inr (.inr k))
  have hw₂fp : ∀ k, LocallyOfFinitePresentation (w₂ k) := by
    intro k
    exact @MorphismProperty.pullback_snd Scheme.{u} inferInstance @LocallyOfFinitePresentation
      (W k) (D.obj i₂) (D.obj i₁) (w k) (D.map b₂) (hpb₂ k) inferInstance (hwfp k)
  have hw₂qc : ∀ k, QuasiCompact (w₂ k) := by
    intro k
    exact @MorphismProperty.pullback_snd Scheme.{u} inferInstance @QuasiCompact
      (W k) (D.obj i₂) (D.obj i₁) (w k) (D.map b₂) (hpb₂ k) inferInstance (hwqc k)
  have hw₂qs : ∀ k, QuasiSeparated (w₂ k) := by
    intro k
    exact @MorphismProperty.pullback_snd Scheme.{u} inferInstance @QuasiSeparated
      (W k) (D.obj i₂) (D.obj i₁) (w k) (D.map b₂) (hpb₂ k) inferInstance (hwqs k)
  have hw₂compact : ∀ k, CompactSpace (W₂ k) := by
    intro k
    exact @QuasiCompact.compactSpace_of_compactSpace (W₂ k) (D.obj i₂)
      (w₂ k) (hw₂qc k) inferInstance
  have hw₂space : ∀ k, QuasiSeparatedSpace (W₂ k) := by
    intro k
    exact @quasiSeparatedSpace_of_quasiSeparated (W₂ k) (D.obj i₂)
      (w₂ k) inferInstance (hw₂qs k)
  let O (k : J) : Over (D.obj i₂) := Over.mk (w₂ k)
  let OY (k : κ) := O (some (.inl k))
  let OB (k : κ) := O (some (.inr (.inl k)))
  let OT (k : κ) := O (some (.inr (.inr k)))
  let OS : Over (D.obj i₂) := Over.mk (𝟙 _)
  let FJ (k : κ) : OY k ⟶ OB k := Over.homMk (j k) (hjw k)
  let FP (k : κ) : OB k ⟶ OT k := Over.homMk (p k) (hpw k)
  let FT (k : κ) : OT k ⟶ OS := Over.homMk (t₂ k) (Category.comp_id _)
  have hYcompact : ∀ k, CompactSpace (Y k) := fun k ↦ hw₂compact (some (.inl k))
  have hYspace : ∀ k, QuasiSeparatedSpace (Y k) := fun k ↦ hw₂space (some (.inl k))
  have : CompactSpace (∐ Y : Scheme.{u}) := chain_sigma_compact Y
  have : QuasiSeparatedSpace (∐ Y : Scheme.{u}) := chain_sigma_qs Y
  let qY : (∐ Y) ⟶ D.obj i₂ := Sigma.desc (fun k ↦ w₂ (some (.inl k)))
  have : LocallyOfFinitePresentation qY :=
    IsZariskiLocalAtSource.sigmaDesc fun k ↦ hw₂fp (some (.inl k))
  let OSigma : Over (D.obj i₂) := Over.mk qY
  let Fν : OSigma ⟶ O none := Over.homMk ν hνw
  have Hσ : IsPullback (Limits.Sigma.map hA₂)
      (ν₀ ≫ pullback.snd _ _) qY (c.π.app i₂) := by
    have hq : Sigma.desc (fun k ↦ j₀ k ≫ p₀ k ≫ t₀ k) =
        ν₀ ≫ pullback.snd _ _ := by
      apply Sigma.hom_ext
      intro k
      simpa using (hcomm k).symm
    rw [← hq]
    exact isPullback_sigmaDesc _ _ _ _ (fun k ↦ H₂ (some (.inl k)))
  have hνeq : ν₀ ≫ h₂ none =
      Limits.Sigma.map hA₂ ≫ ν := by
    apply Sigma.hom_ext
    intro k
    simp only [ν, Sigma.ι_map_assoc, Sigma.ι_comp_desc]
    exact (hg (.inr (.inr k))).symm
  have hjlim (k : κ) : IsOpenImmersion
      ((Over.pullback (c.π.app i₂)).map (FJ k)).left := by
    apply (chain_property_iff @IsOpenImmersion (c.π.app i₂) (FJ k)
      (h₂ (some (.inl k))) (h₂ (some (.inr (.inl k))))
      (j₀ k ≫ p₀ k ≫ t₀ k) (p₀ k ≫ t₀ k) (j₀ k)
      (H₂ (some (.inl k))) (H₂ (some (.inr (.inl k))))
      (hg (.inl k)).symm rfl).mpr
    exact hj₀ k
  have hplim (k : κ) : (@Smooth ⊓ @IsProper : MorphismProperty Scheme.{u})
      ((Over.pullback (c.π.app i₂)).map (FP k)).left := by
    apply (chain_property_iff (@Smooth ⊓ @IsProper) (c.π.app i₂) (FP k)
      (h₂ (some (.inr (.inl k)))) (h₂ (some (.inr (.inr k))))
      (p₀ k ≫ t₀ k) (t₀ k) (p₀ k)
      (H₂ (some (.inr (.inl k)))) (H₂ (some (.inr (.inr k))))
      (hg (.inr (.inl k))).symm rfl).mpr
    exact hp₀ k
  have htlim (k : κ) : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u})
      ((Over.pullback (c.π.app i₂)).map (FT k)).left := by
    apply (chain_property_iff (@IsFinite ⊓ @Etale) (c.π.app i₂) (FT k)
      (h₂ (some (.inr (.inr k)))) (c.π.app i₂) (t₀ k) (𝟙 _) (t₀ k)
      (H₂ (some (.inr (.inr k)))) (IsPullback.id_vert _)
      (H₂ (some (.inr (.inr k)))).w.symm (Category.comp_id _)).mpr
    exact ht₀ k
  have hνlim : (@IsFinite ⊓ @Surjective : MorphismProperty Scheme.{u})
      ((Over.pullback (c.π.app i₂)).map Fν).left := by
    apply (chain_property_iff (@IsFinite ⊓ @Surjective) (c.π.app i₂) Fν
      (Limits.Sigma.map hA₂) (h₂ none)
      (ν₀ ≫ pullback.snd _ _) (pullback.snd _ _) ν₀ Hσ (H₂ none) hνeq rfl).mpr
    exact hν₀
  have hOYcompact (k : κ) : CompactSpace (OY k).left := hw₂compact (some (.inl k))
  have hOBcompact (k : κ) : CompactSpace (OB k).left :=
    hw₂compact (some (.inr (.inl k)))
  have hOTcompact (k : κ) : CompactSpace (OT k).left :=
    hw₂compact (some (.inr (.inr k)))
  have hOYspace (k : κ) : QuasiSeparatedSpace (OY k).left := hw₂space (some (.inl k))
  have hOBspace (k : κ) : QuasiSeparatedSpace (OB k).left :=
    hw₂space (some (.inr (.inl k)))
  have hOTspace (k : κ) : QuasiSeparatedSpace (OT k).left :=
    hw₂space (some (.inr (.inr k)))
  have hOYfp (k : κ) : LocallyOfFinitePresentation (OY k).hom :=
    hw₂fp (some (.inl k))
  have hOBfp (k : κ) : LocallyOfFinitePresentation (OB k).hom :=
    hw₂fp (some (.inr (.inl k)))
  have hOTfp (k : κ) : LocallyOfFinitePresentation (OT k).hom :=
    hw₂fp (some (.inr (.inr k)))
  have hOSfp : LocallyOfFinitePresentation OS.hom :=
    inferInstanceAs (LocallyOfFinitePresentation (𝟙 (D.obj i₂)))
  have hOScompact : CompactSpace OS.left := inferInstanceAs (CompactSpace (D.obj i₂))
  have hOSspace : QuasiSeparatedSpace OS.left :=
    inferInstanceAs (QuasiSeparatedSpace (D.obj i₂))
  have hOSigmafp : LocallyOfFinitePresentation OSigma.hom :=
    IsZariskiLocalAtSource.sigmaDesc fun k ↦ hw₂fp (some (.inl k))
  have hOSigmacompact : CompactSpace OSigma.left := chain_sigma_compact Y
  have hOSigmaspace : QuasiSeparatedSpace OSigma.left := chain_sigma_qs Y
  have hOEfp : LocallyOfFinitePresentation (O none).hom := hw₂fp none
  have hOEcompact : CompactSpace (O none).left := hw₂compact none
  have hOEspace : QuasiSeparatedSpace (O none).left := hw₂space none
  have hJfp (k : κ) : LocallyOfFinitePresentation (FJ k).left :=
    chain_fp_arrow _ _ _
  have hPfp (k : κ) : LocallyOfFinitePresentation (FP k).left :=
    chain_fp_arrow _ _ _
  have hTfp (k : κ) : LocallyOfFinitePresentation (FT k).left :=
    chain_fp_arrow _ _ _
  have hνfp : LocallyOfFinitePresentation Fν.left := chain_fp_arrow _ _ _
  have hνevent : ∀ᶠ l in Filter.atTop, ∀ hl : i₂.unop ≤ l,
      (@IsFinite ⊓ @Surjective : MorphismProperty Scheme.{u})
        ((Over.pullback (D.map (homOfLE hl).op)).map Fν).left := by
    have hfin := chain_eventually @IsFinite D i₂.unop Fν
      (exists_isFinite_baseChange_stage D c hc i₂.unop OSigma (O none) Fν hνlim.1)
    have hsur := chain_eventually @Surjective D i₂.unop Fν
      (exists_surjective_of_isLimit D c hc i₂.unop OSigma (O none) Fν hνlim.2)
    filter_upwards [hfin, hsur] with l hf hs using fun hl ↦ ⟨hf hl, hs hl⟩
  have hjevent (k : κ) : ∀ᶠ l in Filter.atTop, ∀ hl : i₂.unop ≤ l,
      IsOpenImmersion ((Over.pullback (D.map (homOfLE hl).op)).map (FJ k)).left := by
    obtain ⟨l, hl, h⟩ := IsOpenImmersion.eventually_of_inverseLimit D c hc i₂.unop
      (OY k) (OB k) (FJ k) (hjlim k)
    apply chain_eventually @IsOpenImmersion D i₂.unop (FJ k)
    exact ⟨l, hl, h l le_rfl⟩
  have hpevent (k : κ) : ∀ᶠ l in Filter.atTop, ∀ hl : i₂.unop ≤ l,
      (@Smooth ⊓ @IsProper : MorphismProperty Scheme.{u})
        ((Over.pullback (D.map (homOfLE hl).op)).map (FP k)).left := by
    obtain ⟨l, hl, h⟩ := exists_eventually_smooth_of_isLimit_qcqs D c hc i₂.unop
      (OB k) (OT k) (FP k) (hplim k).1
    have hsm := chain_eventually @Smooth D i₂.unop (FP k) ⟨l, hl, h l le_rfl⟩
    have hpr := chain_eventually @IsProper D i₂.unop (FP k)
      (chain_proper_stage D c hc i₂.unop (OB k) (OT k) (FP k) (hplim k).2)
    filter_upwards [hsm, hpr] with l hs hp using fun hl ↦ ⟨hs hl, hp hl⟩
  have htevent (k : κ) : ∀ᶠ l in Filter.atTop, ∀ hl : i₂.unop ≤ l,
      (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u})
        ((Over.pullback (D.map (homOfLE hl).op)).map (FT k)).left := by
    have hfin := chain_eventually @IsFinite D i₂.unop (FT k)
      (exists_isFinite_baseChange_stage D c hc i₂.unop (OT k) OS (FT k) (htlim k).1)
    have het := chain_eventually @Etale D i₂.unop (FT k)
      (Etale.exists_stage_of_inverseLimit D c hc i₂.unop (OT k) OS (FT k) (htlim k).2)
    filter_upwards [hfin, het] with l hf he using fun hl ↦ ⟨hf hl, he hl⟩
  obtain ⟨l, hl, hνl, hjl, hpl, htl⟩ :=
    ((Filter.eventually_ge_atTop i₂.unop).and
      (hνevent.and ((Filter.eventually_all.mpr hjevent).and
        ((Filter.eventually_all.mpr hpevent).and
          (Filter.eventually_all.mpr htevent))))).exists
  let d : op l ⟶ i₂ := (homOfLE hl).op
  let hpb₃ (k : J) : HasPullback (w₂ k) (D.map d) :=
    (inferInstance : HasLimitsOfShape WalkingCospan Scheme.{u}).has_limit _
  let W₃ (k : J) : Scheme.{u} :=
    @pullback Scheme.{u} inferInstance (W₂ k) (D.obj (op l)) (D.obj i₂)
      (w₂ k) (D.map d) (hpb₃ k)
  let w₃ (k : J) : W₃ k ⟶ D.obj (op l) :=
    @pullback.snd Scheme.{u} inferInstance (W₂ k) (D.obj (op l)) (D.obj i₂)
      (w₂ k) (D.map d) (hpb₃ k)
  let h₃ (k : J) : Z k ⟶ W₃ k := isPullbackLift D c d (H₂ k)
  have H₃ (k : J) : IsPullback (h₃ k) (z k) (w₃ k) (c.π.app (op l)) :=
    isPullback_isPullbackLift d (H₂ k)
  let Y₃ (k : κ) : Scheme.{u} := W₃ (some (.inl k))
  let B₃ (k : κ) : Scheme.{u} := W₃ (some (.inr (.inl k)))
  let T₃ (k : κ) : Scheme.{u} := W₃ (some (.inr (.inr k)))
  let hA₃ (k : κ) : A k ⟶ Y₃ k := h₃ (some (.inl k))
  let j₃ (k : κ) : Y₃ k ⟶ B₃ k := ((Over.pullback (D.map d)).map (FJ k)).left
  let p₃ (k : κ) : B₃ k ⟶ T₃ k := ((Over.pullback (D.map d)).map (FP k)).left
  let t₃ (k : κ) : T₃ k ⟶ D.obj (op l) := w₃ (some (.inr (.inr k)))
  have hj₃w (k : κ) : j₃ k ≫ w₃ (some (.inr (.inl k))) = w₃ (some (.inl k)) :=
    Over.w ((Over.pullback (D.map d)).map (FJ k))
  have hp₃w (k : κ) : p₃ k ≫ t₃ k = w₃ (some (.inr (.inl k))) :=
    Over.w ((Over.pullback (D.map d)).map (FP k))
  have hchain (k : κ) : j₃ k ≫ p₃ k ≫ t₃ k = w₃ (some (.inl k)) := by
    rw [hp₃w, hj₃w]
  have hj₃ (k : κ) : h₃ (some (.inl k)) ≫ j₃ k =
      j₀ k ≫ h₃ (some (.inr (.inl k))) :=
    chain_lift_natural D c d (FJ k)
      (h₂ (some (.inl k))) (h₂ (some (.inr (.inl k))))
      (j₀ k ≫ p₀ k ≫ t₀ k) (p₀ k ≫ t₀ k) (j₀ k)
      (H₂ (some (.inl k))) (H₂ (some (.inr (.inl k)))) (hg (.inl k)) rfl
  have hp₃ (k : κ) : h₃ (some (.inr (.inl k))) ≫ p₃ k =
      p₀ k ≫ h₃ (some (.inr (.inr k))) :=
    chain_lift_natural D c d (FP k)
      (h₂ (some (.inr (.inl k)))) (h₂ (some (.inr (.inr k))))
      (p₀ k ≫ t₀ k) (t₀ k) (p₀ k)
      (H₂ (some (.inr (.inl k)))) (H₂ (some (.inr (.inr k))))
      (hg (.inr (.inl k))) rfl
  have ht₃ (k : κ) : IsFinite (t₃ k) ∧ Etale (t₃ k) := by
    apply (chain_property_iff (@IsFinite ⊓ @Etale) (D.map d) (FT k)
      (pullback.fst _ _) (D.map d) (t₃ k) (𝟙 _) (t₃ k)
      (IsPullback.of_hasPullback _ _) (IsPullback.id_vert _) ?_ (by simp)).mp
        (htl k hl)
    exact pullback.condition.symm
  let q₃ : (∐ Y₃) ⟶ D.obj (op l) := Sigma.desc (fun k ↦ w₃ (some (.inl k)))
  have Hσ₃ : IsPullback
      (Limits.Sigma.map (fun k ↦ pullback.fst (w₂ (some (.inl k))) (D.map d)))
      q₃ qY (D.map d) :=
    isPullback_sigmaDesc _ _ _ _ (fun k ↦ IsPullback.of_hasPullback _ _)
  let ν₃ : (∐ Y₃) ⟶ W₃ none :=
    Hσ₃.isoPullback.hom ≫ ((Over.pullback (D.map d)).map Fν).left
  have hν₃w : ν₃ ≫ w₃ none = q₃ := by
    change Hσ₃.isoPullback.hom ≫
      ((Over.pullback (D.map d)).map Fν).left ≫
        ((Over.pullback (D.map d)).obj (O none)).hom = q₃
    rw [Over.w]
    exact Hσ₃.isoPullback_hom_snd
  have hν₃prop : IsFinite ν₃ ∧ Surjective ν₃ := by
    exact (MorphismProperty.cancel_left_of_respectsIso
      (@IsFinite ⊓ @Surjective) Hσ₃.isoPullback.hom _).mpr (hνl hl)
  let a₃ : op l ⟶ i₀ := d ≫ b₂ ≫ a
  let eback : W₃ none ⟶ E :=
    pullback.fst (w₂ none) (D.map d) ≫
      pullback.fst (w none) (D.map b₂) ≫ pullback.fst e (D.map a)
  have HE₃ : IsPullback eback (w₃ none) e (D.map a₃) := by
    have hh := (IsPullback.of_hasPullback (w₂ none) (D.map d)).paste_horiz
      ((IsPullback.of_hasPullback (w none) (D.map b₂)).paste_horiz
        (IsPullback.of_hasPullback e (D.map a)))
    simpa [eback, w₃, w₂, w, e₁, a₃, Functor.map_comp] using hh
  let νfinal : (∐ Y₃) ⟶ pullback e (D.map a₃) := ν₃ ≫ HE₃.isoPullback.hom
  let aE : pullback e (c.π.app i₀) ⟶ pullback e (D.map a₃) :=
    h₃ none ≫ HE₃.isoPullback.hom
  have haE : aE ≫ pullback.snd _ _ = pullback.snd _ _ ≫ c.π.app (op l) := by
    change h₃ none ≫ HE₃.isoPullback.hom ≫ pullback.snd _ _ = _
    rw [HE₃.isoPullback_hom_snd, (H₃ none).w]
  have HEfinal : IsPullback aE (pullback.snd e (c.π.app i₀))
      (pullback.snd e (D.map a₃)) (c.π.app (op l)) := by
    exact (H₃ none).of_iso (Iso.refl _) HE₃.isoPullback (Iso.refl _) (Iso.refl _)
      (by simp [aE])
      ((Category.comp_id (z none)).trans (Category.id_comp (z none)).symm)
      (by simp) (by simp)
  have Hσfinal : IsPullback (Limits.Sigma.map hA₃)
      (ν₀ ≫ pullback.snd _ _) q₃ (c.π.app (op l)) := by
    have hq : Sigma.desc (fun k ↦ j₀ k ≫ p₀ k ≫ t₀ k) =
        ν₀ ≫ pullback.snd _ _ := by
      apply Sigma.hom_ext
      intro k
      simpa using (hcomm k).symm
    rw [← hq]
    exact isPullback_sigmaDesc _ _ _ _ (fun k ↦ H₃ (some (.inl k)))
  have hνfinalw : νfinal ≫ pullback.snd _ _ = q₃ := by
    simp only [νfinal, Category.assoc, IsPullback.isoPullback_hom_snd, hν₃w]
  have hνeq₃ : Limits.Sigma.map hA₃ ≫ ν₃ =
      ν₀ ≫ h₃ none := by
    have hcomp : Limits.Sigma.map hA₃ =
        isPullbackLift D c d Hσ ≫ Hσ₃.isoPullback.inv := by
      rw [Iso.eq_comp_inv]
      apply pullback.hom_ext
      · simp only [Category.assoc, IsPullback.isoPullback_hom_fst,
          isPullbackLift_fst]
        apply Sigma.hom_ext
        intro k
        simp only [Sigma.ι_map_assoc, Sigma.ι_map]
        exact congrArg (fun m ↦ m ≫ Sigma.ι Y k)
          (isPullbackLift_fst d (H₂ (some (.inl k))))
      · simp only [Category.assoc, IsPullback.isoPullback_hom_snd,
          isPullbackLift_snd]
        apply Sigma.hom_ext
        intro k
        simp only [q₃, Sigma.ι_map_assoc, Sigma.ι_comp_desc]
        change isPullbackLift D c d (H₂ (some (.inl k))) ≫
          pullback.snd (w₂ (some (.inl k))) (D.map d) = _
        rw [isPullbackLift_snd]
        exact congrArg (fun m ↦ m ≫ c.π.app (op l)) (hcomm k).symm
    rw [hcomp]
    simp only [ν₃, Category.assoc, Iso.inv_hom_id_assoc]
    exact chain_lift_natural D c d Fν
      (Limits.Sigma.map hA₂) (h₂ none)
      (ν₀ ≫ pullback.snd e (c.π.app i₀)) (pullback.snd e (c.π.app i₀)) ν₀
      Hσ (H₂ none) hνeq.symm rfl
  have Hνfinal : IsPullback (Limits.Sigma.map hA₃)
      ν₀ νfinal aE := by
    apply IsPullback.of_bot (t := HEfinal) (s := ?_) ?_
    · simpa only [hνfinalw] using Hσfinal
    · simpa only [νfinal, aE, ← Category.assoc] using
        congrArg (fun m ↦ m ≫ HE₃.isoPullback.hom) hνeq₃
  refine ⟨op l, a₃, T₃, Y₃, B₃, t₃, j₃, p₃, νfinal, ?_, ?_, ?_, ht₃,
    fun k ↦ hjl k hl, fun k ↦ hpl k hl,
    fun k ↦ h₃ (some (.inl k)), fun k ↦ h₃ (some (.inr (.inl k))),
    fun k ↦ h₃ (some (.inr (.inr k))), ?_, aE, Hνfinal, haE⟩
  · have := hν₃prop.1
    exact inferInstanceAs (IsFinite (ν₃ ≫ HE₃.isoPullback.hom))
  · have := hν₃prop.2
    exact inferInstanceAs (Surjective (ν₃ ≫ HE₃.isoPullback.hom))
  · intro k
    calc
      Sigma.ι Y₃ k ≫ νfinal ≫ pullback.snd _ _ = Sigma.ι Y₃ k ≫ q₃ :=
        congrArg (fun m ↦ Sigma.ι Y₃ k ≫ m) hνfinalw
      _ = w₃ (some (.inl k)) := Sigma.ι_comp_desc _ _
      _ = j₃ k ≫ p₃ k ≫ t₃ k := (hchain k).symm
  · intro k
    exact ⟨by simpa only [hchain] using H₃ (some (.inl k)),
      by simpa only [hp₃w] using H₃ (some (.inr (.inl k))),
      H₃ (some (.inr (.inr k))), hj₃ k, hp₃ k⟩

end AlgebraicGeometry
