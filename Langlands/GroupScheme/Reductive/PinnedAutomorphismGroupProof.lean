import Langlands.GroupScheme.Reductive.PinnedAutomorphismGroupStatement
import Langlands.GroupScheme.Reductive.PinnedWeylInner
import Langlands.GroupScheme.Reductive.StarActionIndependenceProof
import Langlands.GroupScheme.Reductive.SplitWeylRationality
import Langlands.GroupScheme.Absolute.QuotientNormalizer
import Langlands.GroupScheme.Absolute.CocharacterDescentGroup
import Langlands.GroupScheme.DominantHomFlatProof
import Langlands.GroupScheme.Rational.InnerDiscrepancy

/-! # Proof: the automorphism group of a pinned split reductive field group -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace PinnedAutomorphismGroup

variable {k : Type u} [Field k]
  {G A : GroupScheme (Spec (CommRingCat.of k))}
  {q : G ⟶ A} (hq : IsAdjointQuotient q)

/-! ### The inner action as an injective homomorphism -/

/-- A point over a test scheme obtained from a base point by restriction is the
constant point. -/
theorem comp_eq_constantPoint {H : GroupScheme (Spec (CommRingCat.of k))}
    {W : Over (Spec (CommRingCat.of k))} (t : W ⟶ Over.mk (𝟙 (Spec (CommRingCat.of k))))
    (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X) :
    t ≫ x = H.constantPoint x W := by
  unfold constantPoint
  congr 1
  apply Over.OverMorphism.ext
  simpa using Over.w t

/-- The action of `A(k)` on `G`, as a group homomorphism to `Aut G`. -/
def innerHom : (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A.X) →* CategoryTheory.Aut G where
  toFun x := Aut.of (hq.innerAction.basePointIso x)
  map_one' := by
    apply Aut.ext
    apply Iso.ext
    apply hom_ext_points
    intro W g
    rw [AutomorphicAction.comp_basePointIso_hom, constantPoint_one,
      AutomorphicAction.act_one_left]
    change g = g ≫ (𝟙 G : G ⟶ G).hom.hom
    rw [Grp.id_hom_hom, Category.comp_id]
  map_mul' x y := by
    apply Aut.ext
    apply Iso.ext
    apply hom_ext_points
    intro W g
    rw [AutomorphicAction.comp_basePointIso_hom, constantPoint_mul,
      AutomorphicAction.act_mul_left]
    change _ = g ≫ ((hq.innerAction.basePointIso y).hom ≫
      (hq.innerAction.basePointIso x).hom).hom.hom
    rw [Grp.comp_hom_hom, ← Category.assoc, AutomorphicAction.comp_basePointIso_hom,
      AutomorphicAction.comp_basePointIso_hom]

theorem innerHom_apply (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A.X) :
    innerHom hq x = Aut.of (hq.innerAction.basePointIso x) := rfl

/-- Faithfulness of the inner action makes the homomorphism injective. -/
theorem innerHom_injective : Function.Injective (innerHom (G := G) hq) := by
  intro x y hxy
  apply hq.innerAction_isFaithful x y
  intro W t g
  have h := congrArg (fun σ : CategoryTheory.Aut G => g ≫ σ.asIso.hom.hom.hom) hxy
  simp only [innerHom_apply, AutomorphicAction.comp_basePointIso_hom] at h
  rw [comp_eq_constantPoint, comp_eq_constantPoint]
  exact h

/-! ### Normality of the inner subgroup -/

/-- An automorphism of `G` carries central points to central points. -/
theorem comp_mem_center (σ : CategoryTheory.Aut G) {T : Over (Spec (CommRingCat.of k))}
    {c : T ⟶ G.X} (hc : c ∈ (center G).carrier T) :
    c ≫ σ.asIso.hom.hom.hom ∈ (center G).carrier T := by
  rw [mem_center]
  intro T' a y
  have hid : σ.asIso.inv.hom.hom ≫ σ.asIso.hom.hom.hom = 𝟙 G.X := by
    rw [← Grp.comp_hom_hom, Iso.inv_hom_id, Grp.id_hom_hom]
  have hy : (y ≫ σ.asIso.inv.hom.hom) ≫ σ.asIso.hom.hom.hom = y := by
    rw [Category.assoc, hid, Category.comp_id]
  have hcomm := hc T' a (y ≫ σ.asIso.inv.hom.hom)
  change (a ≫ c ≫ σ.asIso.hom.hom.hom) * y = y * (a ≫ c ≫ σ.asIso.hom.hom.hom)
  rw [← hy, ← Category.assoc, ← MonObj.mul_comp, ← MonObj.mul_comp, hcomm.eq]

include hq in
/-- Composing an automorphism with the quotient map kills the centre. -/
theorem killsCenter_comp (σ : CategoryTheory.Aut G) : KillsCenter (σ.asIso.hom ≫ q) := by
  intro T c hc
  rw [Grp.comp_hom_hom, ← Category.assoc]
  exact hq.killsCenter T _ (comp_mem_center σ hc)

/-- Conjugating the action of a point of `A(k)` by an automorphism `σ` of `G` gives
the action of the image of the point under the automorphism of `A` induced by `σ`. -/
theorem conj_innerHom (σ : CategoryTheory.Aut G)
    (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A.X) :
    innerHom hq (x ≫ (hq.desc (σ.asIso.hom ≫ q) (killsCenter_comp hq σ)).hom.hom) =
      σ * innerHom hq x * σ⁻¹ := by
  let := hq.flat
  let := hq.surjective
  let := hq.isConnectedReductive.isAffineHom
  let := hq.isAdjoint.isSemisimple.isConnectedReductive.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsAffine A.X.left := isAffine_of_isAffineHom A.X.hom
  let σA := hq.desc (σ.asIso.hom ≫ q) (killsCenter_comp hq σ)
  have hσA : q ≫ σA = σ.asIso.hom ≫ q := hq.comp_desc _ _
  apply Aut.ext
  apply Iso.ext
  apply hom_ext_points
  intro W g
  change g ≫ (hq.innerAction.basePointIso (x ≫ σA.hom.hom)).hom.hom.hom =
    ((g ≫ σ.asIso.inv.hom.hom) ≫ (hq.innerAction.basePointIso x).hom.hom.hom) ≫ σ.asIso.hom.hom.hom
  rw [AutomorphicAction.comp_basePointIso_hom, AutomorphicAction.comp_basePointIso_hom,
    ← constantPoint_comp]
  apply AutomorphicAction.hom_ext_of_local_quotient_lift q (A.constantPoint x W)
  intro V b h hb
  have hid : σ.asIso.inv.hom.hom ≫ σ.asIso.hom.hom.hom = 𝟙 G.X := by
    rw [← Grp.comp_hom_hom, Iso.inv_hom_id, Grp.id_hom_hom]
  have hl : b ≫ A.constantPoint x W ≫ σA.hom.hom = (h ≫ σ.asIso.hom.hom.hom) ≫ q.hom.hom := by
    rw [← Category.assoc, hb, Category.assoc, ← Grp.comp_hom_hom, hσA, Grp.comp_hom_hom,
      Category.assoc]
  rw [hq.innerAction.naturality, hl, hq.innerAction_act_lift, ← Category.assoc,
    hq.innerAction.naturality, hb, hq.innerAction_act_lift, MonObj.mul_comp, MonObj.mul_comp,
    GrpObj.inv_comp, Category.assoc, Category.assoc, hid, Category.comp_id]

/-- The image of the inner homomorphism is normal in `Aut G`. -/
theorem conj_mem_range (σ : CategoryTheory.Aut G)
    (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A.X) :
    σ * innerHom hq x * σ⁻¹ ∈ (innerHom hq).range :=
  ⟨_, conj_innerHom hq σ x⟩

/-! ### Inner automorphisms normalizing the pinned torus -/

variable [IsAffineHom G.X.hom] (p : SplitPinning G)

/-- If the action of a point of `A(k)` normalizes the pinned torus through `t`, then
some point of `G(k)` normalizes it through the same `t`. The point of `A(k)` is lifted
after base change to an algebraic closure, and the resulting normalizing point is
descended by rationality of the Weyl group of a split maximal torus. -/
theorem exists_isNormalizingPoint (z : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A.X)
    (t : p.torus ≅ p.torus)
    (ht : p.inclusion ≫ (hq.innerAction.basePointIso z).hom =
      CommGroupScheme.groupHom t.hom ≫ p.inclusion) :
    ∃ n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      IsNormalizingPoint p.inclusion n t := by
  let b := algebraBaseMap k (AlgebraicClosure k)
  let qK := (GroupScheme.baseChange b).map q
  have hp := DominantHomFlat.baseChange_isPullback b q
  have : LocallyOfFinitePresentation q.hom.hom.left := hq.locallyOfFinitePresentation
  have : Surjective q.hom.hom.left := hq.surjective
  have : LocallyOfFiniteType qK.hom.hom.left :=
    MorphismProperty.of_isPullback hp.flip (inferInstance : LocallyOfFiniteType q.hom.hom.left)
  have : Surjective qK.hom.hom.left :=
    MorphismProperty.of_isPullback hp.flip ‹Surjective q.hom.hom.left›
  obtain ⟨h, hh⟩ := exists_rationalPointLift qK (baseChangeBasePoint b A z)
  have key : (GroupScheme.baseChange b).map (hq.innerAction.basePointIso z).hom =
      (((GroupScheme.baseChange b).obj G).innerIso h).hom := by
    apply hom_ext_points
    intro W x
    apply (baseChangePointsEquiv b G W).injective
    rw [baseChangePointsEquiv_comp, comp_innerIso_hom, map_mul, map_mul, map_inv,
      AutomorphicAction.comp_basePointIso_hom]
    have hlift : baseChangePointsEquiv b G W
        (((GroupScheme.baseChange b).obj G).constantPoint h W) ≫ q.hom.hom =
        A.constantPoint z ((Over.map b).obj W) := by
      rw [← baseChangePointsEquiv_comp, constantPoint_comp, hh,
        baseChangePointsEquiv_constantPoint]
    rw [← hlift, hq.innerAction_act_lift]
  have hn' : IsNormalizingPoint ((GroupScheme.baseChange b).map p.inclusion) h
      ((CommGroupScheme.baseChange b).mapIso t) := by
    unfold IsNormalizingPoint
    rw [← key, ← Functor.map_comp, ht, Functor.map_comp]
    rfl
  obtain ⟨n, σ, hn, hσ⟩ := splitMaximalTorusWeylRationality k (AlgebraicClosure k) G
    p.isConnectedReductive p.torus p.isSplitTorus p.inclusion p.isMaximalTorus h _ hn'
  have : (Over.pullback b).Faithful := GaloisCocharacterDescent.faithful_algebraPullback k _
  have hst : σ = t := by
    apply Iso.ext
    have h1 := congrArg (fun e => (CommGroupScheme.groupHom e.hom).hom.hom) hσ
    change (Over.pullback b).map (CommGroupScheme.groupHom σ.hom).hom.hom =
      (Over.pullback b).map (CommGroupScheme.groupHom t.hom).hom.hom at h1
    have h2 := (Over.pullback b).map_injective h1
    exact congrArg Additive.ofMul (Grp.hom_ext _ _ h2)
  exact ⟨n, hst ▸ hn⟩

/-- A pinned lift of a based automorphism that is the action of a point of `A(k)` is
the identity: its torus automorphism comes from a Weyl element, and a based Weyl
element is trivial. -/
theorem eq_one_of_innerHom_eq_lift (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A.X)
    (θ : p.basedRootDatumAut) (h : innerHom hq x = p.basedRootDatumAutLift θ) : θ = 1 := by
  have hsq : p.inclusion ≫ (hq.innerAction.basePointIso x).hom =
      CommGroupScheme.groupHom (p.basedRootDatumAutTorusLift θ).asIso.hom ≫ p.inclusion := by
    have h' : hq.innerAction.basePointIso x = (p.basedRootDatumAutLift θ).asIso :=
      congrArg Aut.asIso h
    rw [h']
    exact p.basedRootDatumAutLift_square θ
  obtain ⟨n, hn⟩ := exists_isNormalizingPoint hq p x _ hsq
  obtain ⟨w, hw, hwχ⟩ := StarActionIndependence.exists_weyl_of_isNormalizingPoint p hn
  have hθ : θ.val = w := by
    apply StarActionIndependence.equiv_ext_of_weightMap
    intro χ
    rw [hwχ, ← RootPairing.Equiv.weightEquiv_apply, ← p.basedRootDatumAutTorusLift_character θ]
    rfl
  apply Subtype.ext
  exact p.eq_one_of_weyl_of_based θ.val (by rw [hθ]; exact hw) θ.property

/-- An automorphism normalizing the pinned torus is the action of a point of `A(k)`
followed by a pinned lift of a based automorphism. -/
theorem exists_eq_innerHom_mul_lift_of_normalizes (f : CategoryTheory.Aut G)
    (t : p.torus ≅ p.torus)
    (hf : p.inclusion ≫ f.asIso.hom = CommGroupScheme.groupHom t.hom ≫ p.inclusion) :
    ∃ (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A.X) (θ : p.basedRootDatumAut),
      f = innerHom hq x * p.basedRootDatumAutLift θ := by
  let : IsClosedImmersion p.inclusion.hom.hom.left := p.isMaximalTorus.2.1
  have hG := p.isConnectedReductive
  let δ : p.rootDatum.Aut := rootDatumEquivOfTorusCompatibleIso hG hG p.isSplitTorus
    p.isSplitTorus p.isMaximalTorus p.isMaximalTorus f.asIso t hf p.isRootDatum p.isRootDatum
  have hδ (χ : characterLattice p.torus) : δ.weightMap χ = t.hom ≫ χ :=
    rootDatumEquivOfTorusCompatibleIso_weightMap hG hG p.isSplitTorus
      p.isSplitTorus p.isMaximalTorus p.isMaximalTorus f.asIso t hf p.isRootDatum p.isRootDatum χ
  let θ := p.basedRootDatumProjection δ⁻¹
  have hW : θ.val * δ ∈ p.rootDatum.weylGroup := by
    have h := p.basedRootDatumProjection_correction δ⁻¹
    rwa [inv_inv] at h
  let tθ := (p.basedRootDatumAutTorusLift θ).asIso
  have hθχ (χ : characterLattice p.torus) : θ.val.weightMap χ = tθ.inv ≫ χ := by
    rw [← RootPairing.Equiv.weightEquiv_apply, ← p.basedRootDatumAutTorusLift_character θ]
    rfl
  have hinv : p.inclusion ≫ (p.basedRootDatumAutLift θ).asIso.inv =
      CommGroupScheme.groupHom tθ.inv ≫ p.inclusion := by
    rw [Iso.comp_inv_eq, Category.assoc, p.basedRootDatumAutLift_square θ,
      ← Category.assoc]
    change p.inclusion = CommGroupScheme.groupHom (tθ.inv ≫ tθ.hom) ≫ p.inclusion
    rw [Iso.inv_hom_id]
    exact (Category.id_comp _).symm
  have hf' : p.inclusion ≫ (f * (p.basedRootDatumAutLift θ)⁻¹).asIso.hom =
      CommGroupScheme.groupHom (tθ.symm ≪≫ t).hom ≫ p.inclusion := by
    change p.inclusion ≫ (p.basedRootDatumAutLift θ).asIso.inv ≫ f.asIso.hom = _
    rw [← Category.assoc, hinv, Category.assoc, hf, ← Category.assoc]
    rfl
  have hσ : characterAut (tθ.symm ≪≫ t) ∈ weylImage p.inclusion := by
    apply p.isRootDatum.abstractWeylImage_le
    refine ⟨(θ.val * δ)⁻¹, inv_mem hW, ?_⟩
    rw [map_inv, inv_eq_iff_eq_inv, eq_inv_iff_mul_eq_one, map_mul]
    apply LinearEquiv.ext
    intro χ
    simp only [LinearEquiv.mul_apply, RootPairing.Equiv.weightHom_apply,
      RootPairing.Equiv.weightEquiv_apply, characterAut_apply, hδ, hθχ, Iso.trans_inv,
      Iso.symm_inv, Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]
    rfl
  obtain ⟨x, hx⟩ := p.exists_adjointPoint_of_weylImage hq
    (f * (p.basedRootDatumAutLift θ)⁻¹).asIso (tθ.symm ≪≫ t) hf' hσ
  refine ⟨x, θ, ?_⟩
  have hx' : innerHom hq x = f * (p.basedRootDatumAutLift θ)⁻¹ := Aut.ext hx
  rw [hx', inv_mul_cancel_right]

/-- Every automorphism of `G` is the action of a point of `A(k)` followed by a pinned
lift of a based automorphism. The pinned torus is first moved back by conjugacy of
maximal split tori. -/
theorem exists_eq_innerHom_mul_lift (σ : CategoryTheory.Aut G) :
    ∃ (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A.X) (θ : p.basedRootDatumAut),
      σ = innerHom hq x * p.basedRootDatumAutLift θ := by
  have hG := p.isConnectedReductive
  have : Smooth G.X.hom := hG.smooth
  have : ConnectedSpace G.X.left := hG.connectedSpace
  obtain ⟨g, e, hge⟩ := smoothMaximalSplitTorusConjugacy k G p.torus p.torus
    (p.inclusion ≫ σ.asIso.hom) p.inclusion
    ((p.isMaximalTorus.comp_iso σ.asIso).isMaximalSplitTorus p.isSplitTorus)
    (p.isMaximalTorus.isMaximalSplitTorus p.isSplitTorus)
  let a : CategoryTheory.Aut G := Aut.of (G.innerIso g)
  obtain ⟨x, θ, hxθ⟩ := exists_eq_innerHom_mul_lift_of_normalizes hq p (a * σ)
    (CommGroupScheme.isoOfGroupIso e) (by
      change p.inclusion ≫ σ.asIso.hom ≫ (G.innerIso g).hom = e.hom ≫ p.inclusion
      rw [← Category.assoc]
      exact hge)
  refine ⟨(g ≫ q.hom.hom)⁻¹ * x, θ, ?_⟩
  have hg : innerHom hq (g ≫ q.hom.hom) = a :=
    congrArg Aut.of (SplitPinning.innerAction_basePointIso_lift hq g)
  rw [map_mul, map_inv, hg, mul_assoc, ← hxθ, inv_mul_cancel_left]

end PinnedAutomorphismGroup

open PinnedAutomorphismGroup in
/-- **Automorphisms of a pinned split reductive group** (Conrad, *Reductive group
schemes* (2014), Proposition 7.1.6). -/
theorem pinnedAutomorphismGroup : PinnedAutomorphismGroupStatement.{u} := by
  intro k _ G A _ p q hq
  classical
  let inn := innerHom (G := G) hq
  let L := p.basedRootDatumAutLift
  have hE : ∀ σ : CategoryTheory.Aut G, ∃ θ : p.basedRootDatumAut, σ * (L θ)⁻¹ ∈ inn.range := by
    intro σ
    obtain ⟨x, θ, hxθ⟩ := exists_eq_innerHom_mul_lift hq p σ
    exact ⟨θ, x, by rw [hxθ, mul_inv_cancel_right]⟩
  have hU : ∀ (σ : CategoryTheory.Aut G) (θ θ' : p.basedRootDatumAut),
      σ * (L θ)⁻¹ ∈ inn.range → σ * (L θ')⁻¹ ∈ inn.range → θ = θ' := by
    intro σ θ θ' h₁ h₂
    obtain ⟨x, hx⟩ := h₁
    obtain ⟨y, hy⟩ := h₂
    have hxy : inn (y⁻¹ * x) = L (θ' * θ⁻¹) := by
      rw [map_mul, map_inv, hx, hy, map_mul, map_inv]
      group
    have h1 := eq_one_of_innerHom_eq_lift hq p _ _ hxy
    exact (mul_inv_eq_one.mp h1).symm
  let π₀ : CategoryTheory.Aut G → p.basedRootDatumAut := fun σ => Classical.choose (hE σ)
  have hπ₀ (σ : CategoryTheory.Aut G) : σ * (L (π₀ σ))⁻¹ ∈ inn.range :=
    Classical.choose_spec (hE σ)
  have hmul (σ τ : CategoryTheory.Aut G) : π₀ (σ * τ) = π₀ σ * π₀ τ := by
    have h3 : σ * (τ * (L (π₀ τ))⁻¹) * σ⁻¹ ∈ inn.range := by
      obtain ⟨y, hy⟩ := hπ₀ τ
      rw [← hy]
      exact conj_mem_range hq σ y
    have heq : σ * τ * (L (π₀ σ * π₀ τ))⁻¹ =
        (σ * (τ * (L (π₀ τ))⁻¹) * σ⁻¹) * (σ * (L (π₀ σ))⁻¹) := by
      rw [map_mul]
      group
    exact hU _ _ _ (hπ₀ _) (heq ▸ mul_mem h3 (hπ₀ σ))
  let π : CategoryTheory.Aut G →* p.basedRootDatumAut := MonoidHom.mk' π₀ hmul
  refine ⟨inn, π, fun x => rfl, innerHom_injective hq, ?_, ?_⟩
  · ext σ
    rw [MonoidHom.mem_ker]
    change π₀ σ = 1 ↔ σ ∈ inn.range
    constructor
    · intro h
      have h' := hπ₀ σ
      rwa [h, map_one, inv_one, mul_one] at h'
    · intro h
      refine (hU σ 1 (π₀ σ) ?_ (hπ₀ σ)).symm
      rwa [map_one, inv_one, mul_one]
  · intro θ
    change π₀ (L θ) = θ
    refine (hU (L θ) θ (π₀ (L θ)) ?_ (hπ₀ _)).symm
    rw [mul_inv_cancel]
    exact one_mem _

end Langlands.GroupScheme
