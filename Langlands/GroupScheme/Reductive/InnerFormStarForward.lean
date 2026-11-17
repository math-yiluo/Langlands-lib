import Langlands.GroupScheme.Reductive.InnerFormStarActionStatement
import Langlands.GroupScheme.Reductive.PinnedInnerWeylCriterion
import Langlands.GroupScheme.Reductive.PinnedIsoAlignment
import Langlands.GroupScheme.Rational.InnerDiscrepancyGaloisPull
import Mathlib.FieldTheory.IsSepClosed

/-! # Inner forms have equivalent star actions -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.InnerFormStarForward

local instance baseChangeAffine (k K : Type u) [Field k] [Field K] [Algebra k K]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

section Comparison

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  (d : GaloisPinningData k K G) (d' : GaloisPinningData k K H)
  (E : (GroupScheme.baseChange (algebraBaseMap k K)).obj G ≅
    (GroupScheme.baseChange (algebraBaseMap k K)).obj H)
  (φ : d.toSplitPinning.torus ≅ d'.toSplitPinning.torus)

/-- Canonical Galois transport of the torus comparison. -/
def pullTorusIso (σ : K ≃ₐ[k] K) :
    d.toSplitPinning.torus ≅ d'.toSplitPinning.torus :=
  (CommGroupScheme.descentBaseChangeIso (algebraBaseMap k K) (galoisBaseMap k K σ)
    (galoisBaseMap_over k K σ) d.torus).symm ≪≫
    (CommGroupScheme.baseChange (galoisBaseMap k K σ)).mapIso φ ≪≫
      CommGroupScheme.descentBaseChangeIso (algebraBaseMap k K) (galoisBaseMap k K σ)
        (galoisBaseMap_over k K σ) d'.torus

/-- The discrepancy on the target group between a comparison and its Galois pullback. -/
def twistIso (σ : K ≃ₐ[k] K) :
    (GroupScheme.baseChange (algebraBaseMap k K)).obj H ≅
      (GroupScheme.baseChange (algebraBaseMap k K)).obj H :=
  E.symm ≪≫ Descent.pullIso (galoisBaseMap k K σ) (galoisBaseMap_over k K σ)
    (galoisBaseMap_over k K σ) E

/-- The corresponding discrepancy on the chosen target torus. -/
def twistTorusIso (σ : K ≃ₐ[k] K) :
    d'.toSplitPinning.torus ≅ d'.toSplitPinning.torus :=
  φ.symm ≪≫ pullTorusIso d d' φ σ

/-- The discrepancy normalizes the target torus through its transported comparison. -/
theorem inclusion_comp_twistIso
    (sq : d.toSplitPinning.inclusion ≫ E.hom =
      CommGroupScheme.groupHom φ.hom ≫ d'.toSplitPinning.inclusion)
    (σ : K ≃ₐ[k] K) :
    d'.toSplitPinning.inclusion ≫ (twistIso E σ).hom =
      CommGroupScheme.groupHom (twistTorusIso d d' φ σ).hom ≫
        d'.toSplitPinning.inclusion := by
  have ha := galoisBaseMap_over k K σ
  have sq' : d'.toSplitPinning.inclusion ≫ E.inv =
      CommGroupScheme.groupHom φ.inv ≫ d.toSplitPinning.inclusion := by
    rw [Iso.comp_inv_eq, Category.assoc, sq, ← Category.assoc]
    change _ = CommGroupScheme.groupHom (φ.inv ≫ φ.hom) ≫ _
    rw [Iso.inv_hom_id]
    exact (Category.id_comp _).symm
  have nd := descentBaseChangeIso_naturality (algebraBaseMap k K) (galoisBaseMap k K σ) ha
    d.inclusion
  have nd' := descentBaseChangeIso_naturality (algebraBaseMap k K) (galoisBaseMap k K σ) ha
    d'.inclusion
  have ndinv : d.toSplitPinning.inclusion ≫
      (descentBaseChangeIso (algebraBaseMap k K) (galoisBaseMap k K σ) ha G).inv =
      (descentBaseChangeIso (algebraBaseMap k K) (galoisBaseMap k K σ) ha
        d.torus.toGrp).inv ≫
        (GroupScheme.baseChange (galoisBaseMap k K σ)).map
          ((GroupScheme.baseChange (algebraBaseMap k K)).map d.inclusion) := by
    rw [Iso.comp_inv_eq, Category.assoc, nd, Iso.inv_hom_id_assoc]
    rfl
  have e1 : (twistIso E σ).hom = E.inv ≫
      (descentBaseChangeIso (algebraBaseMap k K) (galoisBaseMap k K σ) ha G).inv ≫
      (GroupScheme.baseChange (galoisBaseMap k K σ)).map E.hom ≫
      (descentBaseChangeIso (algebraBaseMap k K) (galoisBaseMap k K σ) ha H).hom := rfl
  have e2 : CommGroupScheme.groupHom (twistTorusIso d d' φ σ).hom =
      CommGroupScheme.groupHom φ.inv ≫
      (descentBaseChangeIso (algebraBaseMap k K) (galoisBaseMap k K σ) ha
        d.torus.toGrp).inv ≫
      (GroupScheme.baseChange (galoisBaseMap k K σ)).map
        (CommGroupScheme.groupHom φ.hom) ≫
      (descentBaseChangeIso (algebraBaseMap k K) (galoisBaseMap k K σ) ha
        d'.torus.toGrp).hom := rfl
  rw [e1, e2]
  rw [reassoc_of% sq', reassoc_of% ndinv, ← Functor.map_comp_assoc]
  change _ ≫ _ ≫ (GroupScheme.baseChange (galoisBaseMap k K σ)).map
    (d.toSplitPinning.inclusion ≫ E.hom) ≫ _ = _
  rw [sq, Functor.map_comp_assoc]
  change _ ≫ _ ≫ _ ≫ (GroupScheme.baseChange (galoisBaseMap k K σ)).map
    ((GroupScheme.baseChange (algebraBaseMap k K)).map d'.inclusion) ≫ _ = _
  rw [nd']
  simp only [Category.assoc]
  rfl

variable [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType H.X.hom]

/-- The full root action of the discrepancy measures the difference between ordinary
Galois actions after conjugation by the comparison of root data. -/
theorem galoisAction_eq_twist_mul
    (e : RootPairing.Equiv d.toSplitPinning.rootDatum d'.toSplitPinning.rootDatum)
    (he : ∀ χ, e.weightMap χ = φ.inv ≫ χ) (σ : K ≃ₐ[k] K)
    (w : d'.toSplitPinning.rootDatum.Aut)
    (hw : ∀ χ, w.weightMap χ = (twistTorusIso d d' φ σ).inv ≫ χ) :
    d'.galoisAction σ = w * StarActionIndependence.conjAut e (d.galoisAction σ) := by
  have hψ (χ : characterLattice d.toSplitPinning.torus) :
      (pullTorusIso d d' φ σ).inv ≫
          characterLattice.galoisRepresentation k K d.torus σ χ =
        characterLattice.galoisRepresentation k K d'.torus σ (φ.inv ≫ χ) := by
    rw [characterLattice.galoisRepresentation_apply,
      characterLattice.galoisRepresentation_apply]
    exact StarActionIndependence.descentTransport_inv_comp (T := d.torus) (T' := d'.torus)
      (algebraBaseMap k K) (galoisBaseMap k K σ) (galoisBaseMap_over k K σ) φ χ
  apply StarActionIndependence.equiv_ext_of_weightMap
  intro y
  obtain ⟨χ, rfl⟩ := e.weightEquiv.surjective y
  change (d'.galoisAction σ).weightMap (e.weightMap χ) =
    w.weightMap (e.weightMap ((d.galoisAction σ).weightMap
      (e.weightEquiv.symm (e.weightEquiv χ))))
  rw [LinearEquiv.symm_apply_apply, StarActionIndependence.galoisAction_weightMap_apply,
    StarActionIndependence.galoisAction_weightMap_apply, he, he, hw]
  change _ = ((pullTorusIso d d' φ σ).inv ≫ φ.hom) ≫
    (φ.inv ≫ characterLattice.galoisRepresentation k K d.torus σ χ)
  rw [Category.assoc, Iso.hom_inv_id_assoc, hψ]

/-- A based torus-compatible comparison with inner Galois discrepancy intertwines stars. -/
theorem starAction_intertwine
    (sq : d.toSplitPinning.inclusion ≫ E.hom =
      CommGroupScheme.groupHom φ.hom ≫ d'.toSplitPinning.inclusion)
    (e : RootPairing.Equiv d.toSplitPinning.rootDatum d'.toSplitPinning.rootDatum)
    (he : ∀ χ, e.weightMap χ = φ.inv ≫ χ)
    (hb : ∀ a, a ∈ d.toSplitPinning.base.support ↔
      e.indexEquiv a ∈ d'.toSplitPinning.base.support)
    (σ : K ≃ₐ[k] K)
    (hinner : IsFppfInnerEquivalent E (Descent.pullIso (galoisBaseMap k K σ)
      (galoisBaseMap_over k K σ) (galoisBaseMap_over k K σ) E)) :
    e.comp (d.starAction σ).val = (d'.starAction σ).val.comp e := by
  let F := twistIso E σ
  let τ := twistTorusIso d d' φ σ
  have hs : d'.toSplitPinning.inclusion ≫ F.hom =
      CommGroupScheme.groupHom τ.hom ≫ d'.toSplitPinning.inclusion :=
    inclusion_comp_twistIso d d' E φ sq σ
  have hsinv : d'.toSplitPinning.inclusion ≫ F.inv =
      CommGroupScheme.groupHom τ.inv ≫ d'.toSplitPinning.inclusion := by
    rw [Iso.comp_inv_eq, Category.assoc, hs, ← Category.assoc]
    change _ = CommGroupScheme.groupHom (τ.inv ≫ τ.hom) ≫ _
    rw [Iso.inv_hom_id]
    exact (Category.id_comp _).symm
  let w : d'.toSplitPinning.rootDatum.Aut :=
    rootDatumEquivOfTorusCompatibleIso d'.isConnectedReductive d'.isConnectedReductive
      d'.isSplitTorus d'.isSplitTorus d'.isMaximalTorus d'.isMaximalTorus
      F.symm τ.symm hsinv d'.isRootDatum d'.isRootDatum
  have hwχ (χ : characterLattice d'.toSplitPinning.torus) : w.weightMap χ = τ.inv ≫ χ :=
    rootDatumEquivOfTorusCompatibleIso_weightMap d'.isConnectedReductive
      d'.isConnectedReductive d'.isSplitTorus d'.isSplitTorus d'.isMaximalTorus
      d'.isMaximalTorus F.symm τ.symm hsinv d'.isRootDatum d'.isRootDatum χ
  have hl : IsFppfLocallyInner F := by
    simpa only [F, twistIso, IsFppfInnerEquivalent, Iso.symm_symm_eq] using hinner.inv
  have hw := d'.toSplitPinning.mem_weylGroup_of_locallyInner F τ hs w hwχ hl
  have heq := galoisAction_eq_twist_mul d d' φ e he σ w hwχ
  apply StarActionIndependence.comp_basedRootDatumProjection d.toSplitPinning
    d'.toSplitPinning e hb
  rw [heq, mul_inv_cancel_right]
  exact hw

end Comparison

section Forward

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType H.X.hom]
  (d : GaloisPinningData k K G) (d' : GaloisPinningData k K H)

/-- A comparison with inner Galois discrepancy yields a based equivalence intertwining
all star actions, even if the original comparison does not preserve the chosen tori. -/
theorem exists_basedEquiv_of_innerEquivalent_pullIso
    (E : (GroupScheme.baseChange (algebraBaseMap k K)).obj G ≅
      (GroupScheme.baseChange (algebraBaseMap k K)).obj H)
    (hE : ∀ σ : K ≃ₐ[k] K, IsFppfInnerEquivalent E
      (Descent.pullIso (galoisBaseMap k K σ) (galoisBaseMap_over k K σ)
        (galoisBaseMap_over k K σ) E)) :
    ∃ e : RootPairing.Equiv d.toSplitPinning.rootDatum d'.toSplitPinning.rootDatum,
      (∀ a, a ∈ d.toSplitPinning.base.support ↔
        e.indexEquiv a ∈ d'.toSplitPinning.base.support) ∧
      ∀ σ : K ≃ₐ[k] K, e.comp (d.starAction σ).val = (d'.starAction σ).val.comp e := by
  obtain ⟨g, φ, e, hs, he, hb⟩ :=
    d.toSplitPinning.exists_inner_comp_based d'.toSplitPinning E
  let F := E ≪≫ ((GroupScheme.baseChange (algebraBaseMap k K)).obj H).innerIso g
  have hFE : IsFppfInnerEquivalent F E := by
    simpa only [F, IsFppfInnerEquivalent, Iso.trans_assoc, Iso.symm_symm_eq] using
      (isFppfLocallyInner_innerIso _ g).transport E.symm
  refine ⟨e, hb, fun σ => ?_⟩
  apply starAction_intertwine d d' F φ hs e he hb σ
  exact hFE.trans ((hE σ).trans
    ((hFE.pullIso (galoisBaseMap k K σ) (galoisBaseMap_over k K σ)).symm))

end Forward

/-- A natural inner local isomorphism over a separable field extension determines a
based equivalence of absolute root data intertwining all absolute star actions. -/
theorem of_localIso {k L : Type u} [Field k] [Field L] [Algebra k L]
    [Algebra.IsSeparable k L]
    {G H A : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]
    {q : G ⟶ A} (hq : IsAdjointQuotient q)
    (d : GaloisPinningData k (SeparableClosure k) G)
    (d' : GaloisPinningData k (SeparableClosure k) H)
    (e : LocalGroupIso G H (ringTest k L))
    (he : e.HasInnerDiscrepancy hq.innerAction) :
    ∃ f : RootPairing.Equiv d.toSplitPinning.rootDatum d'.toSplitPinning.rootDatum,
      (∀ a, a ∈ d.toSplitPinning.base.support ↔
        f.indexEquiv a ∈ d'.toSplitPinning.base.support) ∧
      ∀ σ : SeparableClosure k ≃ₐ[k] SeparableClosure k,
        f.comp (d.starAction σ).val = (d'.starAction σ).val.comp f := by
  let r := ringTestMap k (IsSepClosed.lift : L →ₐ[k] SeparableClosure k)
  let eK := e.refine r
  let E := eK.toBaseChangeIso
  have hE : (LocalGroupIso.ofBaseChangeIso (U := ringTest k (SeparableClosure k)) E).HasInnerDiscrepancy hq.innerAction := by
    change (LocalGroupIso.ofBaseChangeIso eK.toBaseChangeIso).HasInnerDiscrepancy _
    rw [LocalGroupIso.ofBaseChangeIso_toBaseChangeIso]
    exact he.refine r
  apply exists_basedEquiv_of_innerEquivalent_pullIso d d' E
  intro σ
  exact hq.innerEquivalent_pullIso_of_innerDiscrepancy E hE (ringTestMap k σ.toAlgHom)

/-- The absolute star-equivalence consequence of every separable inner local comparison. -/
def AbsoluteInnerComparisonStatement : Prop :=
  ∀ {k L : Type u} [Field k] [Field L] [Algebra k L] [Algebra.IsSeparable k L]
    {G H A : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]
    {q : G ⟶ A} (hq : IsAdjointQuotient q)
    (d : GaloisPinningData k (SeparableClosure k) G)
    (d' : GaloisPinningData k (SeparableClosure k) H)
    (e : LocalGroupIso G H (ringTest k L))
    (_he : e.HasInnerDiscrepancy hq.innerAction),
    ∃ f : RootPairing.Equiv d.toSplitPinning.rootDatum d'.toSplitPinning.rootDatum,
      (∀ a, a ∈ d.toSplitPinning.base.support ↔
        f.indexEquiv a ∈ d'.toSplitPinning.base.support) ∧
      ∀ σ : SeparableClosure k ≃ₐ[k] SeparableClosure k,
        f.comp (d.starAction σ).val = (d'.starAction σ).val.comp f

/-- The absolute comparison statement follows from the constructed local comparison. -/
theorem absoluteInnerComparison : AbsoluteInnerComparisonStatement.{u} := by
  intro k L _ _ _ _ G H A _ _ _ _ q hq d d' e he
  exact of_localIso hq d d' e he

end Langlands.GroupScheme.InnerFormStarForward
