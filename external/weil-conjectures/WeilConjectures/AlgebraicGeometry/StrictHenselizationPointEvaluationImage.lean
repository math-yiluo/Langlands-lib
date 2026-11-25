/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluation
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationPointed
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

/-! # Image of pointed evaluation

Source: Stacks Project, Tags 04GW and 04HX.
(blueprint: lem-weil-pbc-strict-henselization-point-evaluation-image).
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- Evaluation of a section at a field-valued point of an étale morphism is
separable over the base residue field. Source: Stacks Project, Tag 04GW.
Factor the point through its residue field, use étaleness of the induced residue-field
extension, then map the resulting separable element into Ω. -/
private theorem affine_eval_mem
    {X S : Scheme.{v}} {Ω : Type v} [Field Ω]
    (g : X ⟶ S) [Etale g] (s : Spec (.of Ω) ⟶ X)
    (b : Γ(X, ⊤))
    [Algebra (S.residueField (g (s (IsLocalRing.closedPoint Ω)))) Ω]
    (hbase : algebraMap (S.residueField (g (s (IsLocalRing.closedPoint Ω)))) Ω =
      (descResidueField (stalkClosedPointTo (s ≫ g))).hom) :
    (ΓSpecIso (.of Ω)).hom (s.appTop b) ∈
      separableClosure (S.residueField (g (s (IsLocalRing.closedPoint Ω)))) Ω := by
  let q := s (IsLocalRing.closedPoint Ω)
  let p := g q
  let F := S.residueField p
  let L := X.residueField q
  let m := g.residueFieldMap q
  let e := X.descResidueField (stalkClosedPointTo s)
  let : Algebra F L := m.hom.toAlgebra
  have hm : m.hom.Etale := g.etale_residueFieldMap q
  let : Algebra.Etale F L := by
    rw [← RingHom.etale_algebraMap, RingHom.algebraMap_toAlgebra]
    exact hm
  have hsep : Algebra.IsSeparable F L :=
    (Algebra.FormallyEtale.iff_isSeparable F L).mp inferInstance
  have hcomp : m ≫ e = descResidueField (stalkClosedPointTo (s ≫ g)) := by
    rw [descResidueField_stalkClosedPointTo_comp]
  have hbase' : algebraMap F Ω =
      (descResidueField (stalkClosedPointTo (s ≫ g))).hom := by
    simpa [F, p, q] using hbase
  let a : L →ₐ[F] Ω :=
    { e.hom with
      commutes' r := by
        have hh : CommRingCat.ofHom (algebraMap F L) ≫ e =
            CommRingCat.ofHom (algebraMap F Ω) := by
          have hbcat : CommRingCat.ofHom (algebraMap F Ω) =
              descResidueField (stalkClosedPointTo (s ≫ g)) := by
            exact congrArg CommRingCat.ofHom hbase'
          rw [hbcat]
          change CommRingCat.ofHom (algebraMap F L) ≫ e =
            descResidueField (stalkClosedPointTo (s ≫ g))
          change m ≫ e = descResidueField (stalkClosedPointTo (s ≫ g))
          exact hcomp
        exact congrArg (fun f => f.hom r) hh }
  let z := (X.fromSpecResidueField q).appTop b
  let w := (ΓSpecIso L).hom z
  have hz : IsSeparable F (a w) :=
    (Algebra.IsSeparable.isSeparable F w).map a a.injective
  have hzmem : a w ∈ separableClosure F Ω := mem_separableClosure_iff.mpr hz
  have heval : (ΓSpecIso (.of Ω)).hom (s.appTop b) = a w := by
    have hf := descResidueField_stalkClosedPointTo_fromSpecResidueField Ω X s
    rw [← hf, Hom.comp_appTop]
    exact congrArg (fun t ↦ t ((X.fromSpecResidueField q).appTop b))
      (ΓSpecIso_naturality e)
  rw [heval]
  exact hzmem


/-- Pointed evaluation lands in the relative separable closure.
(blueprint: lem-weil-pbc-strict-henselization-point-evaluation-image).
Source: Stacks Project, Tag 04HX. Represent a colimit element by an affine pointed
étale neighbourhood; its residue extension is finite separable over the base residue
field, so its chosen embedding into Ω lands in the relative separable closure. -/
theorem strictHenselizationPointEvaluation_mem
    {Y : Scheme.{v}} {Ω : Type v} [Field Ω] [IsAlgClosed Ω]
    (barY : Spec (.of Ω) ⟶ Y)
    [Algebra (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω]
    (hΩ : algebraMap (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω =
      (descResidueField (stalkClosedPointTo barY)).hom)
    (a : strictHenselization barY) :
    strictHenselizationPointEvaluation barY a ∈
      separableClosure (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω := by
  classical
  have := (strictHenselizationAffineProperties barY).2.1
  obtain ⟨j, b, rfl⟩ := Concrete.isColimit_exists_rep
    (strictHenselizationAffineDiagram barY)
    (isColimitSmallStrictHenselizationCocone barY) a
  let n := (equivSmallModel.{v} (strictHenselizationNeighbourhoods barY)).inverse.obj j.unop
  let V := Spec (unop n.1.left)
  let z : Spec (.of Ω) ⟶ V := n.2.left
  let g : V ⟶ Y := n.1.hom
  have hfac : z ≫ g = barY := Over.w n.2
  have heval : V.Γevaluation (z (IsLocalRing.closedPoint Ω)) ≫
      descResidueField (stalkClosedPointTo z) = z.appTop ≫ (ΓSpecIso (.of Ω)).hom := by
    dsimp [Γevaluation, evaluation]
    rw [Category.assoc, residue_descResidueField]
    simpa using germ_stalkClosedPointTo z ⊤ trivial
  have hc : strictHenselizationPointEvaluation barY
      ((smallStrictHenselizationCocone barY).ι.app j b) =
      (z.appTop ≫ (ΓSpecIso (.of Ω)).hom) b := by
    exact ConcreteCategory.congr_hom
      ((isColimitSmallStrictHenselizationCocone barY).fac
        (strictHenselizationPointCocone barY) j) b
  rw [hc, ← heval]
  let F := Y.residueField (g (z (IsLocalRing.closedPoint Ω)))
  let L := V.residueField (z (IsLocalRing.closedPoint Ω))
  let f := g.residueFieldMap (z (IsLocalRing.closedPoint Ω))
  let e := descResidueField (stalkClosedPointTo z)
  let : Algebra F L := f.hom.toAlgebra
  let : Algebra F Ω := (f ≫ e).hom.toAlgebra
  have : Etale g := n.1.prop
  have : Algebra.IsSeparable F L := inferInstance
  let emb : L →ₐ[F] Ω := { e.hom with commutes' := fun _ ↦ rfl }
  have hsep := (Algebra.IsSeparable.isSeparable F (V.Γevaluation _ b)).map emb emb.injective
  apply mem_separableClosure_iff.mpr
  obtain ⟨hp, hh⟩ := SpecToEquivOfField_eq_iff.mp
    (congrArg (SpecToEquivOfField Ω Y) hfac)
  dsimp [SpecToEquivOfField] at hp hh
  rw [descResidueField_stalkClosedPointTo_comp] at hh
  let eqv := (Y.residueFieldCongr hp).commRingCatIsoToRingEquiv
  have hmaps : (algebraMap (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω).comp
      eqv.toRingHom = algebraMap F Ω := by
    change (algebraMap (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω).comp
      (Y.residueFieldCongr hp).hom.hom = (f ≫ e).hom
    rw [hΩ]
    exact congrArg CommRingCat.Hom.hom hh.symm
  exact hsep.of_equiv_equiv eqv (RingEquiv.refl Ω) hmaps

end AlgebraicGeometry.Scheme
