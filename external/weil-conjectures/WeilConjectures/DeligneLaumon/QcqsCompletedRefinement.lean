/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.FieldShriekCompositionNormalization
import WeilConjectures.SixFunctors.PurCompactSupport.RefinementOpenScalarSquare
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Finite.FiniteRingRefinementCoordinatesCore
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingPullbackComparison
import WeilConjectures.SmoothPurity.Qcqs.QcqsCompactSupportFiniteComparison
import WeilConjectures.DeligneLaumon.QcqsCompactSupportOpenComplete
import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated
import all WeilConjectures.SmoothPurity.Qcqs.QcqsCompactSupportNormalizedIsoExistence

/-! # Normalized completed refinement comparisons

Source: Stacks 0F7B and 0F7J; Bhatt--Scholze Definition 6.7.6.
(blueprint: lem-zl-qcqs-completed-refinement).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open PurCompactSupport

attribute [local irreducible] HasDerivedCategory.standard

private theorem finite_refinement_isIso
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f}
    (r : c.Refinement d) (n : ℕ)
    (M : proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E (n + 1)))
    (hM : intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) X M)
    (hi : (finite l E (n + 1) (Nat.succ_pos n)).pull (c.i ≫ r.hom) =
      proEtaleRingCompositeCoefficients c.i r.hom
        ((finite l E (n + 1) (Nat.succ_pos n)).ring d.Z)
        ((finite l E (n + 1) (Nat.succ_pos n)).ring c.Z)
        ((finite l E (n + 1) (Nat.succ_pos n)).ring X)
        ((finite l E (n + 1) (Nat.succ_pos n)).pull r.hom)
        ((finite l E (n + 1) (Nat.succ_pos n)).pull c.i)) :
    IsIso ((refinementOpenMap (finite l E (n + 1) (Nat.succ_pos n)) r hi).app M) := by
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let : Finite A := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  obtain ⟨a, ha⟩ := hM.1.bddBelow
  obtain ⟨b, hb⟩ := hM.1.bddAbove
  have hv : ∀ i : ℤ, (i < min a b ∨ b < i) →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj M) := by
    intro i hi
    by_contra hz
    rcases hi with hi | hi
    · exact (not_lt_of_ge (ha hz)) (lt_of_lt_of_le hi (min_le_left _ _))
    · exact (not_lt_of_ge (hb hz)) hi
  obtain ⟨L, ⟨eL⟩⟩ := ((finiteRing_constructibleDerived_origin X A).2.2.1 M).mpr
    ⟨hM.2, min a b, b, min_le_right _ _, hv⟩
  obtain ⟨a₀, b₀, _, hvan⟩ := L.property.2
  let LP : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} A))) :=
    ⟨L.obj, ⟨a₀, (DerivedCategory.isGE_iff L.obj a₀).2
      (fun i hi ↦ hvan i (Or.inl hi))⟩⟩
  -- Retain an actual etale origin, so the finite comparison has its canonical normalization.
  let O : FrobeniusExchange.CompactOrigin A X := { K := M, L := LP, alpha := eL }
  have hg := (proEtaleConstantRingCompositeCoefficients_eq r.hom d.g A).symm
  obtain ⟨ε, hε, _⟩ :=
    ConstructibleExceptionalCoefficients.finite_ring_refinement_coordinates_canonical
      l E n r O hi hg
  have hres : IsIso (refinementRestriction (finite l E (n + 1) (Nat.succ_pos n))
      r hi M) := by
    obtain ⟨θ, hθ, hiso, _⟩ :=
      exists_refinementRestriction (finite l E (n + 1) (Nat.succ_pos n)) r hi
    let := hiso
    rw [← hθ]
    infer_instance
  have heq : (refinementOpenMap (finite l E (n + 1) (Nat.succ_pos n)) r hi).app M =
      ε.hom := by
    apply ((openDerivedAdjunction (finite l E (n + 1) (Nat.succ_pos n)) d.i).homEquiv
      _ _).injective
    apply (cancel_mono (refinementRestriction
      (finite l E (n + 1) (Nat.succ_pos n)) r hi M)).1
    exact (refinementOpenMap_normalization
      (finite l E (n + 1) (Nat.succ_pos n)) r hi M).trans hε.symm
  rw [heq]
  infer_instance

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (K₀ : Type u) [Field K₀] (hl : IsUnit (l : K₀))
  {X Y : Scheme.{u}} {f : X ⟶ Y}
  [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
  [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
  [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
  [f.IsOver (Spec (.of K₀))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

include hl in
/-- A proper refinement has its open-adjunction-normalized completed comparison.
Source: Stacks 0F7B, 0F7J, and Bhatt--Scholze Definition 6.7.6 and Lemma 6.7.7
(blueprint: lem-zl-qcqs-completed-refinement).

Proof: for the square c.i followed by r.hom equals d.i, the canonical restriction
map is proper base change followed by the clopen-support identification over X.
The open adjunction transposes its inverse composed with the open unit to the
map epsilon from d.i_! K to Rr_* c.i_! K. On the normalized strict reduction
system its evaluations are the finite proper/open comparisons, hence invertible.
The completed cone has zero reductions and is complete, so epsilon is invertible.
Push epsilon inverse along d.g and insert the inverse canonical proper compositor
for r.hom followed by d.g. This is rho, and the transpose equation and compositor
formula are exactly SfCompletedRefinementSpec. Finite-type schemes over the field
are qcqs; this construction requires no separatedness of their structure maps.
For empty X both extension objects are zero and the same normalization applies. -/
theorem sfQcqsCompletedRefinement_exists
    {c d : Compactification f} (r : c.Refinement d)
    (K : sfIntegralConstructibleCategory l E X) :
    ∃ ρ : (image (completed l E) c).obj K.obj ≅
        (image (completed l E) d).obj K.obj,
      SfCompletedRefinementSpec l E r K.obj ρ := by
  let hi := completedPull_comp l E c.i r.hom
  let α := (refinementOpenMap (completed l E) r hi).app K.obj
  let : QuasiCompact d.i := d.quasiCompact_openImmersion inferInstance
  -- View the inner proper/open composite as compact support for d.i itself.
  let q : Compactification d.i :=
    { Z := c.Z
      g := r.hom
      i := c.i
      comm := r.i_hom.symm
      isProper := inferInstance
      isOpenImmersion := inferInstance }
  have hred (n : ℕ) : IsIso ((scalarReductionDerivedExtension l E d.Z n).map α) := by
    let a := reduction l E (n + 1) (Nat.le_add_left 1 n)
    let S := finite l E (n + 1) (Nat.succ_pos n)
    let hS := (proEtaleConstantRingCompositeCoefficients_eq c.i r.hom
      (Padic.coefficientExtensionRing l E (n + 1))).symm
    have hM : intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) X
        ((pbcDerivedExtend (a.map X)).obj K.obj) := by
      obtain ⟨_, _, _, hK⟩ := K.property.2
      let A := Padic.coefficientExtensionRing l E (n + 1)
      let : Finite A := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
      have : ObjectProperty.IsClosedUnderIsomorphisms
          (intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) X) :=
        (proEtale_bounded_constructible_isTriangulated X A).1
      exact ObjectProperty.prop_of_iso _ ((finiteReductionIso l E X n).app K.obj).symm
        (hK n).1
    have := finite_refinement_isIso l E r n ((pbcDerivedExtend (a.map X)).obj K.obj) hM hS
    have := openComparison_isIso a d.i K.obj
    have hcomp : IsIso ((pbcDerivedExtend (a.map d.Z)).map α ≫
        (comparison a q).app K.obj) := by
      rw [comparison_factorization]
      change IsIso ((pbcDerivedExtend (a.map d.Z)).map α ≫
        (properComparison a r.hom).app
          ((openExtension (completed l E) c.i).mapDerivedCategory.obj K.obj) ≫
        (push S r.hom).map ((openComparison a c.i).app K.obj))
      rw [show (pbcDerivedExtend (a.map d.Z)).map α ≫
          (properComparison a r.hom).app
            ((openExtension (completed l E) c.i).mapDerivedCategory.obj K.obj) ≫
          (push S r.hom).map ((openComparison a c.i).app K.obj) = _ from
        refinementOpenMap_scalar a r hi hS K.obj]
      infer_instance
    have := (sfQcqsCompactSupport_finiteComparison l E K₀ hl q K).2 n
    have : IsIso ((pbcDerivedExtend (a.map d.Z)).map α) :=
      IsIso.of_isIso_comp_right _ ((comparison a q).app K.obj)
    exact (NatIso.isIso_map_iff (finiteReductionIso l E d.Z n) α).mp this
  have hcomplete := sfQcqsCompactSupport_open_complete l E K₀ hl d K
  let τ := (sfQcqsCompactSupportRealization l E K₀ hl q).app K
  have : ObjectProperty.IsClosedUnderIsomorphisms (sfIntegralConstructible l E d.Z) :=
    sfIntegralConstructible_isClosedUnderIsomorphisms l E d.Z
  have htarget : sfIntegralConstructible l E d.Z
      ((push (completed l E) r.hom).obj
        ((openExtension (completed l E) c.i).mapDerivedCategory.obj K.obj)) :=
    ObjectProperty.prop_of_iso _ τ.symm
      ((sfCompactSupportFiniteIntegralFunctor l K₀ hl q E).obj K).property
  -- A complete source with these reductions is constructible; its complete cone is zero.
  have hsource := constructible_of_complete_reduction_isos l E d.Z hcomplete htarget
    (fun n ↦ @asIso _ _ _ _ ((scalarReductionDerivedExtension l E d.Z n).map α) (hred n))
  have : IsIso α := constructible_isIso_of_reductions l E d.Z α hsource htarget hred
  let ε := asIso α
  let ρ := ((geometricPushComposition (completed l E) r.hom d.g
      (completedPull_comp l E r.hom d.g) ≪≫
        eqToIso (congrArg (fun h ↦ push (completed l E) h) r.hom_g)).symm.app _) ≪≫
      (push (completed l E) d.g).mapIso ε.symm
  refine ⟨ρ, ε, ?_, rfl⟩
  exact refinementOpenMap_normalization (completed l E) r hi K.obj

end WeilConjectures
