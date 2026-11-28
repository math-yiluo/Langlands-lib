import Langlands.GroupScheme.Rational.CentralCubicSplittingLift
import Langlands.GroupScheme.Rational.NumberFieldTotallyComplexQuasiSplitTypeE6
import Langlands.GroupScheme.Rational.NumberFieldTypeE7QuadraticSplittingReduction
import Langlands.GroupScheme.Reductive.InnerFormStarForward
import Langlands.GroupScheme.Reductive.InnerStarWeights
import Langlands.GroupScheme.Reductive.QuasiSplitStarCriterionProof
import Langlands.GroupScheme.SimplyConnected.TypeE6InnerCenter

/-! # Cyclic cubic splitting of inner E6 from quasi-split vanishing -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- An inner simply connected absolutely almost simple E6 group over a
totally complex number field becomes split over some cyclic cubic extension. -/
def NumberFieldInnerTypeE6CubicSplittingStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F], IsTotallyComplex F →
    ∀ (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
      (d : TitsIndexData G) (e : d.Vertex ≃ Fin 6), IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
      (∀ a b, d.cartan a b = CartanMatrix.E 6 (e a) (e b)) →
      (∀ (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) (a : d.Vertex), d.star σ a = a) →
      ∃ (E : IntermediateField F (SeparableClosure F)) (_ : FiniteDimensional F E),
        IsGalois F E ∧ Module.finrank F E = 3 ∧
          HasSplitMaximalTorus ((GroupScheme.baseChange (algebraBaseMap F E)).obj G)

/-- The cyclic cubic splitting assertion follows from vanishing of first
cohomology of the quasi-split simply connected forms over totally complex
number fields. -/
theorem numberFieldInnerTypeE6CubicSplitting_of_quasiSplitVanishing
    (hvan : NumberFieldTotallyComplexQuasiSplitTypeE6VanishingStatement.{u}) :
    NumberFieldInnerTypeE6CubicSplittingStatement.{u} := by
  classical
  intro F _ _ hF G _ _ d e hsc habs hcart hinner
  let : IsTotallyComplex F := hF
  obtain ⟨qf⟩ := quasiSplitInnerFormExistence F G hsc.isSemisimple.isConnectedReductive
  let hred := qf.isQuasiSplit.isConnectedReductive
  let : IsAffineHom qf.model.X.hom := hred.isAffineHom
  let : Smooth qf.model.X.hom := hred.smooth
  have hscH := qf.isSimplyConnected_model hsc
  have habsH := qf.isAbsolutelyAlmostSimple_model habs
  obtain ⟨dH⟩ := titsIndexExistence F qf.model hscH.isSemisimple
  have hdsc : qf.localIso.HasInnerDiscrepancy qf.isAdjointQuotient.innerAction := by
    intro U a c
    refine ⟨qf.cocycle.toFun a c, ?_⟩
    intro W t g
    rw [← qf.cocycle.naturality t a c]
    exact qf.hasDiscrepancy (t ≫ a) (t ≫ c) g
  obtain ⟨φ, hbase, hφ⟩ := InnerFormStarForward.of_localIso
    qf.isAdjointQuotient dH.pinning d.pinning qf.localIso hdsc
  let v : dH.Vertex ≃ d.Vertex := φ.indexEquiv.subtypeEquiv hbase
  let eH := v.trans e
  have hcartH (a b : dH.Vertex) : dH.cartan a b = CartanMatrix.E 6 (eH a) (eH b) :=
    (φ.toHom.pairing (i := a.val) (j := b.val)).symm.trans (hcart (v a) (v b))
  have hinnerH (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) (a : dH.Vertex) :
      dH.star σ a = a := by
    apply v.injective
    apply Subtype.ext
    exact (congrArg (fun f => f.indexEquiv a.val) (hφ σ)).trans
      (congrArg Subtype.val (hinner σ (v a)))
  have hfull (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) :
      dH.pinning.starAction σ = 1 := by
    apply Subtype.ext
    apply StarActionIndependence.equiv_ext_of_weightMap
    exact dH.pinning.starAction_weight_of_inner hscH
      (fun τ a => congrArg Subtype.val (hinnerH τ a)) σ
  have hsplit : HasSplitMaximalTorus qf.model :=
    (quasiSplitStarCriterion F qf.model qf.isQuasiSplit dH.pinning).mpr hfull
  have hZ := typeE6InnerCenter F qf.model dH eH hscH hcartH hinnerH
    (kernel qf.quotient) (kernelι qf.quotient) qf.isAdjointQuotient.kernelCenter
  have hf := qf.isAdjointQuotient.isCentralIsogeny hscH.isSemisimple
  obtain ⟨L, _, _, _, _, _, _, hLift⟩ := hf.exists_finiteGalois_refine_galoisLift qf.cocycle
  let r := GaloisCocycle.coverMap F qf.carrier L
  let qf' : QuasiSplitInnerForm G :=
    { model := qf.model
      isQuasiSplit := qf.isQuasiSplit
      adjoint := qf.adjoint
      quotient := qf.quotient
      isAdjointQuotient := qf.isAdjointQuotient
      isQuasiSplit_adjoint := qf.isQuasiSplit_adjoint
      carrier := L
      localIso := qf.localIso.refine r
      cocycle := qf.cocycle.refine r
      hasDiscrepancy := LocalGroupIso.HasDiscrepancy.refine qf.hasDiscrepancy r }
  obtain ⟨E, hE, hGalE, hdeg, N, _, _, _, _, _, _, _, _, ζ, hζ⟩ :=
    totallyComplexCubicCentralLift F L qf.model qf.adjoint qf.quotient hf hZ qf'.cocycle hLift
  let : NumberField E := NumberField.of_module_finite F E
  let : IsTotallyComplex E := isTotallyComplex_of_algebra F E
  have : Algebra.IsSeparable E (SeparableClosure F) :=
    Algebra.isSeparable_tower_top_of_isSeparable F E (SeparableClosure F)
  have : IsSepClosure E (SeparableClosure F) := ⟨inferInstance, inferInstance⟩
  let : Algebra E (SeparableClosure E) := (separableClosure E (AlgebraicClosure E)).algebra
  let c := IsSepClosure.equiv E (SeparableClosure E) (SeparableClosure F)
  let X := dH.separableScalarExtension E c
  let HE := (GroupScheme.baseChange (algebraBaseMap F E)).obj qf.model
  let : IsAffineHom HE.X.hom := by
    change IsAffineHom (CategoryTheory.Limits.pullback.snd qf.model.X.hom _)
    infer_instance
  let : LocallyOfFiniteType HE.X.hom := by
    change LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd qf.model.X.hom _)
    infer_instance
  have hscHE := (isSimplyConnected_fieldExtension_iff (K := E) qf.model).mpr hscH
  have habsHE := habsH.baseChange_of_algebraicExtension (K := E)
  have hqsHE := qf.isQuasiSplit.baseChange_of_algebraicExtension (K := E)
  let eE := X.vertices.symm.trans eH
  have hcartE (a b : X.index.Vertex) : X.index.cartan a b = CartanMatrix.E 6 (eE a) (eE b) := by
    have h := X.cartan_eq (X.vertices.symm a) (X.vertices.symm b)
    simp only [Equiv.apply_symm_apply] at h
    exact h.trans (hcartH (X.vertices.symm a) (X.vertices.symm b))
  have hζtriv := hvan E inferInstance HE X.index eE hscHE habsHE hcartE hqsHE N ζ
  have hξtriv : (GaloisCocycle.scalarExtension (K := E) (M := N) qf'.cocycle).IsTrivial :=
    hζ ▸ (hζtriv.map _)
  have hbc := GaloisCocycle.isTrivial_baseChange_of_scalarExtension qf'.cocycle hξtriv
  let ε := qf'.baseChangeIsoOfTrivial E hbc
  obtain ⟨T, t, ht, hmax⟩ := hsplit
  let TE := (CommGroupScheme.baseChange (algebraBaseMap F E)).obj T
  let tE : TE.toGrp ⟶ HE := (GroupScheme.baseChange (algebraBaseMap F E)).map t
  have hm : IsMaximalTorus tE := (maximalTorusBaseChange F E qf.model T t hmax.1 hmax.2.1).mp hmax
  exact ⟨E, hE, hGalE, hdeg, _, tE ≫ ε.hom, ht.baseChange _, hm.comp_iso ε⟩

end Langlands.GroupScheme
