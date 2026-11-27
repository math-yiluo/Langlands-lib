import Langlands.GroupScheme.Rational.NumberFieldTypeE7HasseInputs
import Langlands.GroupScheme.Rational.QuasiSplitInnerFormModelIndex
import Langlands.GroupScheme.Rational.QuasiSplitInnerFormBaseChange
import Langlands.GroupScheme.Rational.CentralQuadraticSplittingLift
import Langlands.GroupScheme.SimplyConnected.TypeE7CenterKernel
import Langlands.GroupScheme.Rational.QuasiSplitInnerFormExistenceProof
import Langlands.GroupScheme.Reductive.TitsIndexSeparableScalarExtension
import Langlands.GroupScheme.CentralIsogeny.FiniteKernelQuotient
import Langlands.GroupScheme.CentralIsogeny.FiniteGaloisCoefficientLift
import Langlands.GroupScheme.Rational.SimplyConnectedHasseAlmostSimple

/-! # Totally complex quadratic splitting fields in type `E_7`: reduction to the totally complex
vanishing -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

/-- The adjoint quotient of a semisimple field group is a central isogeny. -/
theorem IsAdjointQuotient.isCentralIsogeny {k : Type u} [Field k]
    {G A : GroupScheme (Spec (CommRingCat.of k))} {q : G ⟶ A} (hq : IsAdjointQuotient q)
    (hG : IsSemisimple G) : IsCentralIsogeny q := by
  obtain ⟨Z, z, hz, hfin⟩ := hG.hasFiniteCenter
  have : IsFinite Z.X.hom := hfin
  have hA := hq.isAdjoint.isSemisimple.isConnectedReductive
  have : IsAffineHom G.X.hom := hq.isConnectedReductive.isAffineHom
  have : IsAffineHom A.X.hom := hA.isAffineHom
  let i : kernel q ≅ Z := hq.kernelCenter.isRepresentedBy.isoOfIsRepresentedBy hz.isRepresentedBy
  have : IsIso i.hom.hom.hom.left :=
    inferInstanceAs (IsIso (((Grp.forget (Over _)) ⋙ Over.forget _).map i.hom))
  have : IsFinite (kernel q).X.hom := by
    rw [← Over.w i.hom.hom.hom]
    infer_instance
  have : Flat q.hom.hom.left := hq.flat
  have : Surjective q.hom.hom.left := hq.surjective
  have : QuasiCompact q.hom.hom.left := inferInstance
  exact ⟨⟨isFinite_of_finite_kernel q, hq.flat, hq.surjective⟩, hq.locallyOfFinitePresentation,
    hq.kernelCenter.isCentral⟩

/-- Platonov–Rapinchuk, Proposition 6.16, item (2), in type `E_7` over number fields: if first
cohomology of quasi-split simply connected groups of type `E_7` vanishes over every totally
complex number field, then every simply connected absolutely almost-simple group of type `E_7`
over a number field becomes quasi-split over a totally complex quadratic extension. -/
def NumberFieldTypeE7QuadraticSplittingReductionStatement : Prop :=
  NumberFieldTotallyComplexTypeE7Statement.{u} →
    NumberFieldTypeE7QuadraticSplittingFieldStatement.{u}

/-- The quadratic splitting field statement in type `E_7` follows from the totally complex
vanishing. The group is an inner twist of its quasi-split model `H` by an adjoint cocycle; the
centre of `H` is `μ_2`; over a totally complex quadratic extension `E` killing the obstruction
class in the Brauer group, the cocycle lifts to `H_E`, where it is trivial by the totally complex
vanishing, so `G_E` is isomorphic to `H_E`. -/
theorem numberFieldTypeE7QuadraticSplittingReduction :
    NumberFieldTypeE7QuadraticSplittingReductionStatement.{u} := by
  intro hvan F _ _ G _ _ d e hsc habs hE7
  obtain ⟨qf⟩ := quasiSplitInnerFormExistence F G hsc.isSemisimple.isConnectedReductive
  have hHred := qf.isQuasiSplit.isConnectedReductive
  have : IsAffineHom qf.model.X.hom := hHred.isAffineHom
  have : Smooth qf.model.X.hom := hHred.smooth
  have hscH := qf.isSimplyConnected_model hsc
  have habsH := qf.isAbsolutelyAlmostSimple_model habs
  obtain ⟨dH⟩ := titsIndexExistence F qf.model hscH.isSemisimple
  obtain ⟨φ, hφ⟩ := qf.exists_vertexEquiv_cartan d dH
  let eH : dH.Vertex ≃ Fin 7 := φ.trans e
  have hE7H : ∀ a b, dH.cartan a b = CartanMatrix.E 7 (eH a) (eH b) := fun a b => by
    rw [← hφ a b, hE7]
    rfl
  obtain ⟨eZ⟩ := dH.nonempty_center_iso_of_typeE7 hscH eH hE7H qf.isAdjointQuotient.kernelCenter
  have hf := qf.isAdjointQuotient.isCentralIsogeny hscH.isSemisimple
  obtain ⟨L', _, _, _, _, _, _, ⟨dl⟩⟩ := hf.exists_finiteGalois_refine_galoisLift qf.cocycle
  let r := GaloisCocycle.coverMap F qf.carrier L'
  let qf' : QuasiSplitInnerForm G :=
    { model := qf.model
      isQuasiSplit := qf.isQuasiSplit
      adjoint := qf.adjoint
      quotient := qf.quotient
      isAdjointQuotient := qf.isAdjointQuotient
      isQuasiSplit_adjoint := qf.isQuasiSplit_adjoint
      carrier := L'
      localIso := qf.localIso.refine r
      cocycle := qf.cocycle.refine r
      hasDiscrepancy := LocalGroupIso.HasDiscrepancy.refine qf.hasDiscrepancy r }
  obtain ⟨E, hE2, hEc, N, _, _, _, _, _, _, _, _, ζ, hζ⟩ :=
    hf.exists_quadratic_isComplex_lift_of_galoisLift eZ dl
  have : FiniteDimensional F E := Module.finite_of_finrank_eq_succ hE2
  have : NumberField E := NumberField.of_module_finite F E
  have : NumberField.IsTotallyComplex E := ⟨hEc⟩
  have : Algebra.IsSeparable E (SeparableClosure F) :=
    Algebra.isSeparable_tower_top_of_isSeparable F E (SeparableClosure F)
  have : IsSepClosure E (SeparableClosure F) := ⟨inferInstance, inferInstance⟩
  let : Algebra E (SeparableClosure E) := (separableClosure E (AlgebraicClosure E)).algebra
  let c : SeparableClosure E ≃ₐ[E] SeparableClosure F :=
    IsSepClosure.equiv E (SeparableClosure E) (SeparableClosure F)
  let X := dH.separableScalarExtension E c
  let HE := (GroupScheme.baseChange (algebraBaseMap F E)).obj qf.model
  have : IsAffineHom HE.X.hom := by
    change IsAffineHom (CategoryTheory.Limits.pullback.snd qf.model.X.hom _)
    infer_instance
  have : LocallyOfFiniteType HE.X.hom := by
    change LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd qf.model.X.hom _)
    infer_instance
  have hscHE : IsSimplyConnected HE := (isSimplyConnected_fieldExtension_iff qf.model).mpr hscH
  have habsHE : IsAbsolutelyAlmostSimple HE :=
    IsAbsolutelyAlmostSimple.baseChange_of_algebraicExtension habsH
  have hE7HE : ∀ a b, X.index.cartan a b =
      CartanMatrix.E 7 ((X.vertices.symm.trans eH) a) ((X.vertices.symm.trans eH) b) := by
    intro a b
    have h := X.cartan_eq (X.vertices.symm a) (X.vertices.symm b)
    simp only [Equiv.apply_symm_apply] at h
    rw [h, hE7H]
    rfl
  have hqsHE : IsQuasiSplit HE := qf.isQuasiSplit.baseChange_of_algebraicExtension
  have hζt : ζ.IsTrivial :=
    hvan E HE X.index (X.vertices.symm.trans eH) hscHE habsHE hE7HE hqsHE N ζ
  have hξt : (GaloisCocycle.scalarExtension (K := E) (M := N) (qf.cocycle.refine r)).IsTrivial := by
    rw [← hζ]
    exact hζt.map _
  have hbc : (qf'.cocycle.baseChangePullback (algebraBaseMap F E)).IsTrivial :=
    GaloisCocycle.isTrivial_baseChange_of_scalarExtension _ hξt
  exact ⟨E, hE2, inferInstance, qf'.isQuasiSplit_baseChange_of_trivial E hbc⟩

end Langlands.GroupScheme
