/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleGraphPresentation
public import WeilConjectures.AlgebraicGeometry.EtaleProperOpenExchangeCube
import WeilConjectures.AlgebraicGeometry.EtaleGraphComparisonOpenShrink
import WeilConjectures.AlgebraicGeometry.EtaleGraphComparisonProperAmbient

/-! # Pairwise product-graph normalization of étale presentation comparisons

Source: Stacks Project, more-etale.tex, Tags 0F7B, 0F7C, 0F7D and 0F7J;
`LowerShriekComposition.lean`, lines 193--268, product-graph formula, extended to two
proper/open/proper presentations.
(auxiliary; not a blueprint node).

The auxiliary declarations construct the literal fibre products and the displayed lambda
maps. Only their geometric properties and the final comparison equation are postponed.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

namespace EtaleGraphPresentation.PairwiseProduct

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (s t : EtaleGraphPresentation f)

/-- The proper ambient product. Source: Stacks Tag 0F7J, product diagrams
(auxiliary; not a blueprint node). -/
abbrev P : Scheme.{u} := pullback s.p t.p

/-- The product of the supporting opens over the base. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
abbrev U : Scheme.{u} := pullback (s.e ≫ s.p) (t.e ≫ t.p)

/-- The graph of the two proper first factors. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
def a : X ⟶ U s t := pullback.lift s.a t.a (s.fac.trans t.fac.symm)

/-- The actual product of the open immersions, over the identity of the base.
Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
def b : U s t ⟶ P s t :=
  pullback.map (s.e ≫ s.p) (t.e ≫ t.p) s.p t.p s.e t.e (𝟙 Y)
    (Category.comp_id _) (Category.comp_id _)

/-- The structural map of the product. Its other expression is `pullback.condition`.
Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
def p : P s t ⟶ Y := pullback.fst s.p t.p ≫ s.p

/-- The first supporting neighborhood. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
abbrev O₁ : Scheme.{u} := pullback (pullback.fst s.p t.p) s.e

/-- The second supporting neighborhood. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
abbrev O₂ : Scheme.{u} := pullback (pullback.snd s.p t.p) t.e

/-- The projection equations defining the induced maps to both neighborhoods.
Source: Stacks Tag 0F7J, product diagram
(auxiliary; not a blueprint node).
Proof: project the defining pullback map onto each factor. The two `pullback.map`
projection equations identify these composites with the products of the open maps. -/
theorem b_projections :
    b s t ≫ pullback.fst s.p t.p = pullback.fst (s.e ≫ s.p) (t.e ≫ t.p) ≫ s.e ∧
    b s t ≫ pullback.snd s.p t.p = pullback.snd (s.e ≫ s.p) (t.e ≫ t.p) ≫ t.e := by
  constructor <;> simp [b]

/-- The canonical map to the first neighborhood. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
def v₁ : U s t ⟶ O₁ s t :=
  pullback.lift (b s t) (pullback.fst (s.e ≫ s.p) (t.e ≫ t.p)) (b_projections s t).1

/-- The canonical map to the second neighborhood. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
def v₂ : U s t ⟶ O₂ s t :=
  pullback.lift (b s t) (pullback.snd (s.e ≫ s.p) (t.e ≫ t.p)) (b_projections s t).2

/-- The first neighborhood graph. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
def z₁ : X ⟶ O₁ s t := a s t ≫ v₁ s t

/-- The second neighborhood graph. Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
def z₂ : X ⟶ O₂ s t := a s t ≫ v₂ s t

/-- The geometric properties of the explicitly constructed product diagram.
Source: Stacks Tags 01W3, 01W4 and 01W6 and the product diagrams of Tag 0F7J
(auxiliary; not a blueprint node). -/
structure Geometry : Prop where
  properA : IsProper (a s t)
  openB : IsOpenImmersion (b s t)
  properP : IsProper (p s t)
  openV₁ : IsOpenImmersion (v₁ s t)
  openV₂ : IsOpenImmersion (v₂ s t)
  properZ₁ : IsProper (z₁ s t)
  properZ₂ : IsProper (z₂ s t)
  fac : a s t ≫ b s t ≫ p s t = f
  z₁_q : z₁ s t ≫ pullback.snd (pullback.fst s.p t.p) s.e = s.a
  z₂_q : z₂ s t ≫ pullback.snd (pullback.snd s.p t.p) t.e = t.a
  v₁_b : v₁ s t ≫ pullback.fst (pullback.fst s.p t.p) s.e = b s t
  v₂_b : v₂ s t ≫ pullback.fst (pullback.snd s.p t.p) t.e = b s t

/-- The products form a proper/open/proper presentation, with both neighborhood graphs proper.
Source: Stacks Tags 01W3 (composition), 01W4 (base change), 01W6 (proper to separated),
and 0F7J, product diagrams
(auxiliary; not a blueprint node).
Proof: the ambient projections and the neighborhood projections are proper by base change;
composition makes p proper. The map b is the product of the two open immersions, so is
open by base change and composition. Each vν followed by the corresponding open
neighborhood inclusion is b, so cancellation of open immersions makes vν open.
The first projection U -> s.U is separated: it is a base change of t.e followed by t.p,
a composite of separated maps. Its composite with a is s.a, so proper-to-separated
makes a proper. Likewise zν followed by the proper neighborhood projection qν is aν,
so proper-to-separated makes zν proper. All remaining equations follow by the pullback
projection identities and s.fac, t.fac.
This argument does not suppose f proper or either supporting open quasi-compact. -/
theorem geometry : Geometry s t := by
  have hb : IsOpenImmersion (b s t) := by
    exact MorphismProperty.pullbackMap (P := @IsOpenImmersion)
      inferInstance inferInstance rfl rfl
  have hv₁ : IsOpenImmersion (v₁ s t) := by
    have : IsOpenImmersion
        (v₁ s t ≫ pullback.fst (pullback.fst s.p t.p) s.e) := by
      simpa [v₁] using hb
    exact IsOpenImmersion.of_comp _ (pullback.fst (pullback.fst s.p t.p) s.e)
  have hv₂ : IsOpenImmersion (v₂ s t) := by
    have : IsOpenImmersion
        (v₂ s t ≫ pullback.fst (pullback.snd s.p t.p) t.e) := by
      simpa [v₂] using hb
    exact IsOpenImmersion.of_comp _ (pullback.fst (pullback.snd s.p t.p) t.e)
  have hz₁ : z₁ s t ≫ pullback.snd (pullback.fst s.p t.p) s.e = s.a := by
    simp [z₁, v₁, a]
  have hz₂ : z₂ s t ≫ pullback.snd (pullback.snd s.p t.p) t.e = t.a := by
    simp [z₂, v₂, a]
  have ha : IsProper (a s t) := by
    have : IsProper
        (a s t ≫ pullback.fst (s.e ≫ s.p) (t.e ≫ t.p)) := by
      simpa [a] using s.properA
    exact IsProper.of_comp _ (pullback.fst (s.e ≫ s.p) (t.e ≫ t.p))
  refine ⟨ha, hb, ?_, hv₁, hv₂, ?_, ?_, ?_, hz₁, hz₂, ?_, ?_⟩
  · dsimp [p]
    infer_instance
  · have : IsProper (z₁ s t ≫ pullback.snd (pullback.fst s.p t.p) s.e) := by
      rw [hz₁]
      infer_instance
    exact IsProper.of_comp _ (pullback.snd (pullback.fst s.p t.p) s.e)
  · have : IsProper (z₂ s t ≫ pullback.snd (pullback.snd s.p t.p) t.e) := by
      rw [hz₂]
      infer_instance
    exact IsProper.of_comp _ (pullback.snd (pullback.snd s.p t.p) t.e)
  · simpa [a, b, p] using s.fac
  · simp [v₁]
  · simp [v₂]

/-- The product presentation with exactly the constructed maps; only its proofs use geometry.
Source: Stacks Tag 0F7J
(auxiliary; not a blueprint node). -/
def presentation : EtaleGraphPresentation f where
  U := U s t
  P := P s t
  a := a s t
  e := b s t
  p := p s t
  properA := (geometry s t).properA
  openE := (geometry s t).openB
  properP := (geometry s t).properP
  fac := (geometry s t).fac

end EtaleGraphPresentation.PairwiseProduct

/-- The displayed lambda word for one projection of the product presentation.
The first exchange is Gamma_D. The shrinking isomorphism is Gamma_E with its identity-open
factor removed; its inverse has the orientation in lambda. Both squares are Cartesian, so
these are exactly the normalized maps of lem-pur-etale-proper-open-exchange-cube.
Source: Stacks Tags 0F7B--0F7D and 0F7J
(auxiliary; not a blueprint node). -/
def etaleProductGraphLambda
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (s t : EtaleGraphPresentation f)
    {O : Scheme.{u}} (pr : t.P ⟶ s.P) [IsProper pr]
    (q : O ⟶ s.U) (j : O ⟶ t.P) [IsOpenImmersion j]
    (v : t.U ⟶ O) [IsOpenImmersion v] (z : X ⟶ O) [IsProper z]
    (Dsq : IsPullback q j s.e pr)
    (hz : z ≫ q = s.a) (hp : pr ≫ s.p = t.p)
    (hav : t.a ≫ v = z) (hvb : v ≫ j = t.e) :
    s.functor A ≅ t.functor A :=
  Functor.isoWhiskerRight
      (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) z q s.a hz).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (openImmersionLowerShriekLowerStarExchangeIso A Dsq) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) pr s.p t.p hp)) ≪≫
    Functor.isoWhiskerRight
      (rightDerivedLowerStarCompOpenImmersionLowerShriekIso A t.a v z hav).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        ((mapDerivedCategoryOpenImmersionLowerShriekComp (ModuleCat.{u + 1} A) v j).symm ≪≫
          mapDerivedCategoryOpenImmersionLowerShriekCongr (ModuleCat.{u + 1} A) hvb) _)

namespace EtaleGraphPresentation.PairwiseProduct

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (s t : EtaleGraphPresentation f)

/-- Lambda₁, with the literal first product projection and its pullback neighborhood.
Source: Stacks Tags 0F7B--0F7D and 0F7J
(auxiliary; not a blueprint node). -/
def lambda₁ (A : Type (u + 1)) [CommRing A] [Finite A] :
    s.functor A ≅ (presentation s t).functor A :=
  letI := (geometry s t).openV₁
  letI := (geometry s t).properZ₁
  etaleProductGraphLambda A s (presentation s t) (pullback.fst s.p t.p)
    (pullback.snd (pullback.fst s.p t.p) s.e)
    (pullback.fst (pullback.fst s.p t.p) s.e) (v₁ s t) (z₁ s t)
    (IsPullback.of_hasPullback (pullback.fst s.p t.p) s.e).flip
    (geometry s t).z₁_q rfl rfl (geometry s t).v₁_b

/-- Lambda₂, with the second product projection and the same product structural map.
Source: Stacks Tags 0F7B--0F7D and 0F7J
(auxiliary; not a blueprint node). -/
def lambda₂ (A : Type (u + 1)) [CommRing A] [Finite A] :
    t.functor A ≅ (presentation s t).functor A :=
  letI := (geometry s t).openV₂
  letI := (geometry s t).properZ₂
  etaleProductGraphLambda A t (presentation s t) (pullback.snd s.p t.p)
    (pullback.snd (pullback.snd s.p t.p) t.e)
    (pullback.fst (pullback.snd s.p t.p) t.e) (v₂ s t) (z₂ s t)
    (IsPullback.of_hasPullback (pullback.snd s.p t.p) t.e).flip
    (geometry s t).z₂_q pullback.condition.symm rfl (geometry s t).v₂_b

end EtaleGraphPresentation.PairwiseProduct

private theorem comparisonFromOpen_productGraphLambda
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (s t : EtaleGraphPresentation f) {O : Scheme.{u}}
    (pr : t.P ⟶ s.P) [IsProper pr]
    (q : O ⟶ s.U) (j : O ⟶ t.P) [IsOpenImmersion j]
    (v : t.U ⟶ O) [IsOpenImmersion v] (z : X ⟶ O) [IsProper z]
    (sq : IsPullback q j s.e pr) (hz : z ≫ q = s.a) (hp : pr ≫ s.p = t.p)
    (hav : t.a ≫ v = z) (hvb : v ≫ j = t.e) :
    etaleGraphComparisonFromOpen A c s ≪≫
        etaleProductGraphLambda A s t pr q j v z sq hz hp hav hvb =
      etaleGraphComparisonFromOpen A c t := by
  let H : EtaleGraphPresentation f := {
    U := O
    P := t.P
    a := z
    e := j
    p := t.p
    fac := by
      rw [← hp]
      calc
        z ≫ j ≫ pr ≫ s.p = z ≫ (q ≫ s.e) ≫ s.p := by
          rw [sq.w]
          simp only [Category.assoc]
        _ = f := by simpa only [← Category.assoc, hz] using s.fac }
  let l : s.functor A ≅ H.functor A :=
    Functor.isoWhiskerRight
        (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) z q s.a hz).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (openImmersionLowerShriekLowerStarExchangeIso A sq) _ ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _
          (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) pr s.p t.p hp))
  let r : H.functor A ≅ t.functor A :=
    Functor.isoWhiskerRight
        (rightDerivedLowerStarCompOpenImmersionLowerShriekIso A t.a v z hav).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          ((mapDerivedCategoryOpenImmersionLowerShriekComp
              (ModuleCat.{u + 1} A) v j).symm ≪≫
            mapDerivedCategoryOpenImmersionLowerShriekCongr (ModuleCat.{u + 1} A) hvb) _)
  have hl : etaleGraphComparisonFromOpen A c s ≪≫ l =
      etaleGraphComparisonFromOpen A c H :=
    etaleGraphComparisonFromOpen_properAmbient A c s H pr q sq hz hp
  have hr : etaleGraphComparisonFromOpen A c H ≪≫ r =
      etaleGraphComparisonFromOpen A c t :=
    etaleGraphComparisonFromOpen_openShrink A c H t.a v t.e hav hvb
  calc
    _ = (etaleGraphComparisonFromOpen A c s ≪≫ l) ≪≫ r := by
      simp only [etaleProductGraphLambda, l, r, H, Iso.trans_assoc]
    _ = etaleGraphComparisonFromOpen A c t := by rw [hl, hr]

/-- The specified pairwise graph comparison is lambda₂⁻¹ lambda₁.
Source: Stacks Tags 0F7B, 0F7C, 0F7D and 0F7J; the explicit product-graph comparison in
`LowerShriekComposition.lean`, lines 193--268, extended to two proper/open/proper
presentations (auxiliary; not a blueprint node).

Proof:
1. The theorem PairwiseProduct.geometry checks the product presentation and the two proper
neighborhood graphs, using proper base change, composition and proper-to-separated.
2. Fix the supplied open-then-proper c, and form P₁ ×_Y P₂ ×_Y c.Z. The three supporting
opens and all their intersections have proper graph lifts by the same argument.
3. For nested supporting opens W inside V, horizontal pasting of normalized Gamma gives
sigma(i,W) = sigma(i,V) sigma(V,W). Cancel the common invertible shrinking map to compute
pair comparisons through the intersection of all three opens.
4. Insert the direct-image compositors and the Cartesian Gamma maps to form A_i from each
presentation to its supporting-neighborhood word. Shrink to the total intersection,
obtaining E_i into a common functor H; E_0 for c is independent of the index 1 or 2.
5. Project the triple product to Pν ×_Y c.Z. Let tau_i be the direct-image compositor
followed by Gamma for this proper projection, and tau_W the analogous intersection map.
6. Vertical pasting in the grid with rows X, W', W and horizontal pasting in the grid with
rows W' -> N_i' -> T and W -> N_i -> Tν give tau_i sigma_i = Rz(sigma_i') tau_W.
The interchange of the two Gamma factors is naturality. Vertical pasting in the successive
projection squares likewise identifies the two A_i formulas, with their fixed compositors.
7. Invert the shrinking maps and cancel. The same map Dν takes both E_0 downstairs and
E_ν downstairs to their triple-product versions.
8. Unpack the recorded graph-model B formula: its two side words are those A_i, and its
middle word is sigma_ν sigma_0⁻¹. Cartesian normalization identifies its exchange maps
with these Gamma maps. Therefore B_(ν,c) = E_ν⁻¹ E_0, and C_(2,1) = E_2⁻¹ E_1.
9. Repeat the two projection-grid equations for the projection to P₁ ×_Y P₂. Downstairs
the two A_ν followed by inverse shrinking are exactly lambda₁ and lambda₂ as defined here:
the shrinking is Gamma_E⁻¹, followed by the canonical open compositor.
10. Shrink once more to the total intersection. The same invertible map D then satisfies
E_ν = D lambda_ν for both indices. Cancellation gives C_(2,1) = lambda₂⁻¹ lambda₁.
All maps are the specified compositors and normalized Cartesian interchanges. Finite A is
used only for unbounded interchange; neither quasi-compactness nor Noetherianity is used.
This compares presentations of one map and states no compatibility of two scheme maps. -/
theorem etalePairwiseProductGraphNormalization
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (s t : EtaleGraphPresentation f) :
    etaleGraphComparison A c s t =
      EtaleGraphPresentation.PairwiseProduct.lambda₁ s t A ≪≫
        (EtaleGraphPresentation.PairwiseProduct.lambda₂ s t A).symm := by
  let r := EtaleGraphPresentation.PairwiseProduct.presentation s t
  have h₁ : etaleGraphComparisonFromOpen A c s ≪≫
      EtaleGraphPresentation.PairwiseProduct.lambda₁ s t A =
        etaleGraphComparisonFromOpen A c r := by
    let := (EtaleGraphPresentation.PairwiseProduct.geometry s t).openV₁
    let := (EtaleGraphPresentation.PairwiseProduct.geometry s t).properZ₁
    exact comparisonFromOpen_productGraphLambda A c s r _ _ _ _ _ _ _ _ _ _
  have h₂ : etaleGraphComparisonFromOpen A c t ≪≫
      EtaleGraphPresentation.PairwiseProduct.lambda₂ s t A =
        etaleGraphComparisonFromOpen A c r := by
    let := (EtaleGraphPresentation.PairwiseProduct.geometry s t).openV₂
    let := (EtaleGraphPresentation.PairwiseProduct.geometry s t).properZ₂
    exact comparisonFromOpen_productGraphLambda A c t r _ _ _ _ _ _ _ _ _ _
  change (etaleGraphComparisonFromOpen A c s).symm ≪≫
    etaleGraphComparisonFromOpen A c t = _
  have h := congrArg
    (fun k ↦ k ≪≫ (EtaleGraphPresentation.PairwiseProduct.lambda₂ s t A).symm)
    (h₁.trans h₂.symm)
  simp only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl] at h
  rw [← h]
  simp only [Iso.symm_self_id_assoc]

end AlgebraicGeometry.Etale
