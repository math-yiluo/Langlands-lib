import Langlands.GroupScheme.Rational.GaloisBorelFaceTorusProduct
import Langlands.GroupScheme.Rational.FullOrbitWeilRankOne
import Langlands.GroupScheme.SimplyConnected.TypeD4CubicLeafField

/-! # The central and leaf parts of the signed trialitarian diagram -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.RootDatumNegation

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
set_option maxRecDepth 3000

section Faces

variable {F : Type u} [Field F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] (p : GaloisPinningData F (SeparableClosure F) G)

local notation "E" => SeparableClosure F
local notation "TE" => Functor.obj (CommGroupScheme.baseChange (algebraBaseMap F E)) p.torus

/-- A stable subset of the signed based action supplies a simply connected
derived-Levi group with the specified zero face of the original pinning. -/
theorem GaloisPinningData.exists_derivedSimpleFace
    (hsc : IsSimplyConnected G) (ht : IsMaximalTorus p.inclusion)
    (hs : ∀ σ : E ≃ₐ[F] E, p.galoisAction σ = (p.starAction σ).val ∨
      p.galoisAction σ = negAut p.toSplitPinning.rootDatum * (p.starAction σ).val)
    (J : Set p.base.support) (hJ : ∀ σ a, p.starSupport σ a ∈ J ↔ a ∈ J) :
    ∃ (ν : cocharacterLattice TE) (L : GaloisBorelFaceDerived p ν) (_ : L.RootModel),
      ∀ a : p.base.support, p.rootDatum.root' a.val ν = 0 ↔ a ∈ J := by
  classical
  obtain ⟨m, ν, hm, hν⟩ := p.exists_faceCocharacter J
  have hsig (σ : E ≃ₐ[F] E) (a : p.base.support) :
      latticePairing TE (p.rootDatum.root (p.starSupport σ a).val) ν =
        latticePairing TE (p.rootDatum.root a.val) ν := by
    rw [hν, hν, hJ σ a]
  obtain ⟨L⟩ := exists_galoisBorelFaceDerived p hsc ht ν hs hsig
  have hval (a : p.base.support) :
      p.rootDatum.root' a.val ν = if a ∈ J then 0 else m := by
    change p.rootDatum.toLinearMap (p.rootDatum.root a.val) ν = _
    rw [p.isRootDatum.1]
    exact hν a
  have hn (a : p.base.support) : 0 ≤ p.rootDatum.root' a.val ν := by
    rw [hval]
    split_ifs <;> omega
  obtain ⟨R⟩ := L.nonempty_rootModel (isSplitTorus_baseChange_separableClosure L.torus_maximal.1) hn
  refine ⟨ν, L, R, fun a => ?_⟩
  rw [hval]
  by_cases ha : a ∈ J <;> simp [ha, hm.ne']

end Faces

namespace TitsIndexData

variable {F : Type u} [Field F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G)

local notation "E" => SeparableClosure F

/-- The fork vertex is fixed, and its complement is stable under star. -/
theorem star_central_label_iff_of_D4
    (e : d.Vertex ≃ Fin 4) (hD : ∀ a b, d.cartan a b = CartanMatrix.D 4 (e a) (e b))
    (σ : E ≃ₐ[F] E) (a : d.Vertex) :
    e (d.star σ a) = 1 ↔ e a = 1 := by
  let c := e.symm 1
  have hc : e c = 1 := e.apply_symm_apply 1
  have hs : d.star σ c = c :=
    d.star_fixes_center_of_D (by decide) e hD σ c (by rw [hc]; decide)
  constructor
  · intro ha
    have h : d.star σ a = d.star σ c := e.injective (by rw [ha, hs, hc])
    have h' := congrArg (d.star σ⁻¹) h
    rw [← d.star_mul, ← d.star_mul, inv_mul_cancel, d.star_one, d.star_one] at h'
    simpa only [h'] using hc
  · intro ha
    have h : a = c := e.injective (ha.trans hc.symm)
    rw [h, hs, hc]

section Leaf

variable {p : GaloisPinningData F (SeparableClosure F) G}
  {ν : cocharacterLattice
    ((CommGroupScheme.baseChange (algebraBaseMap F (SeparableClosure F))).obj p.torus)}
  {L : GaloisBorelFaceDerived p ν} (R : L.RootModel)

attribute [local instance] GaloisBorelFaceDerived.derivedAffine GaloisBorelFaceDerived.derivedFiniteType

local notation "bE" => algebraBaseMap F E
local notation "DE" => Functor.obj (GroupScheme.baseChange bE) L.derived

private theorem cartanD4_leaf_pairing_eq_zero :
    ∀ i j : Fin 4, i ≠ 1 → j ≠ 1 → i ≠ j → CartanMatrix.D 4 i j = 0 := by
  decide

include R in
/-- A derived face on the three trialitarian leaves is the Weil restriction
of a simply connected rank-one group from the exact field of any one leaf. -/
theorem exists_rankOneWeil_of_D4_leafFace
    (e : d.Vertex ≃ Fin 4) (hD : ∀ a b, d.cartan a b = CartanMatrix.D 4 (e a) (e b))
    (hno : ¬ ∃ a : d.Vertex, e a ≠ 1 ∧ ∀ σ : E ≃ₐ[F] E, d.star σ a = a)
    (v : d.Vertex ≃ p.base.support)
    (hpair : ∀ a b, p.rootDatum.pairing (v a).val (v b).val = d.cartan a b)
    (hstar : ∀ σ a, (v (d.star σ a)).val = (p.starAction σ).val.indexEquiv (v a).val)
    (hs : ∀ σ : E ≃ₐ[F] E, p.galoisAction σ = (p.starAction σ).val ∨
      p.galoisAction σ = negAut p.toSplitPinning.rootDatum * (p.starAction σ).val)
    (hz : ∀ a : p.base.support, p.rootDatum.root' a.val ν = 0 ↔ e (v.symm a) ≠ 1)
    (a : d.Vertex) (ha : e a ≠ 1) :
    ∃ (_ : FiniteDimensional F (d.starVertexField a))
      (A : GroupScheme (Spec (CommRingCat.of (d.starVertexField a : Type u))))
      (_ : IsAffine A.X.left) (_ : IsAffineHom A.X.hom) (_ : LocallyOfFiniteType A.X.hom)
      (dA : TitsIndexData A),
      IsSimplyConnected A ∧ IsAbsolutelyAlmostSimple A ∧ Nonempty (dA.Vertex ≃ Fin 1) ∧
        Nonempty (AffineWeil.groupScheme F (d.starVertexField a) A ≅ L.derived) := by
  let hsc := isSimplyConnectedFieldExtension F E L.derived L.isSimplyConnected
  let D := hsc.almostSimpleProduct
  let hsem := hsc.isSemisimple
  let : Smooth L.derived.X.hom := L.isSimplyConnected.isSemisimple.isConnectedReductive.smooth
  let : Smooth (DE).X.hom := hsem.isConnectedReductive.smooth
  let : IsAffineHom (DE).X.hom := hsem.isConnectedReductive.isAffineHom
  let w : R.face.base.support ≃ {x : d.Vertex // e x ≠ 1} :=
    R.simpleEquiv.trans (v.symm.subtypeEquiv hz)
  have hw (x : R.face.base.support) : v (w x).val = (R.simpleEquiv x).val :=
    v.apply_symm_apply (R.simpleEquiv x).val
  have hd (x y : R.face.base.support) (hne : x ≠ y) :
      R.rootDatum.pairing x.val y.val = 0 := by
    have hc (z : R.face.base.support) :
        (R.face.indexEquiv z.val).val = (v (w z).val).val :=
      congrArg (fun s : p.base.support => s.val) (hw z).symm
    have hxy : e (w x).val ≠ e (w y).val :=
      fun h => hne (w.injective (Subtype.ext (e.injective h)))
    rw [R.face.pairing_eq, hc x, hc y, hpair, hD]
    exact cartanD4_leaf_pairing_eq_zero _ _ (w x).property (w y).property hxy
  let f := w.symm.trans (Equiv.ofBijective (R.factorIndex D hsem)
    ⟨R.factorIndex_injective_of_diagonal D hsem hd, R.factorIndex_surjective D hsem⟩)
  let i := f ⟨a, ha⟩
  have hperm (σ : E ≃ₐ[F] E) (x : {a : d.Vertex // e a ≠ 1}) :
      D.galoisFactorIndex σ (f x) =
        f ⟨d.star σ x.val, (not_congr (d.star_central_label_iff_of_D4 e hD σ x.val)).mpr
          x.property⟩ := by
    let y : {a : d.Vertex // e a ≠ 1} :=
      ⟨d.star σ x.val, (not_congr (d.star_central_label_iff_of_D4 e hD σ x.val)).mpr x.property⟩
    change D.galoisFactorIndex σ (R.factorIndex D hsem (w.symm x)) =
      R.factorIndex D hsem (w.symm y)
    apply (R.factorIndex_galois D hsem σ (w.symm x) (w.symm y) (hs σ) ?_).symm
    rw [← hw, ← hw, w.apply_symm_apply, w.apply_symm_apply]
    exact Subtype.ext (hstar σ x.val)
  have hall : D.galoisFactorOrbit i = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro j
    obtain ⟨x, rfl⟩ := f.surjective j
    obtain ⟨σ, hσ⟩ :=
      d.star_transitive_on_D4_leaves_of_no_fixed_leaf e hD hno a x.val ha x.property
    exact ⟨σ, (hperm σ ⟨a, ha⟩).trans (congrArg f (Subtype.ext hσ))⟩
  have hstab : D.galoisFactorStabilizer i = d.starVertexStabilizer a := by
    ext σ
    change D.galoisFactorIndex σ (f ⟨a, ha⟩) = f ⟨a, ha⟩ ↔ d.star σ a = a
    rw [hperm]
    exact ⟨fun h => congrArg Subtype.val (f.injective h),
      fun h => congrArg f (Subtype.ext h)⟩
  have hfield : D.factorStabilizerField i = d.starVertexField a :=
    congrArg IntermediateField.fixedField hstab
  obtain ⟨q, ⟨eq⟩⟩ := R.exists_rankOneFactorPinning D hsem hd (w.symm ⟨a, ha⟩)
  have hW := D.exists_rankOneWeilRestriction_of_fullOrbit i hall q eq
  rw [← hfield]
  exact ⟨inferInstance, hW⟩

end Leaf

end TitsIndexData
end Langlands.GroupScheme
