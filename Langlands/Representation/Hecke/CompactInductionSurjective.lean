import Langlands.Representation.Hecke.CompactInductionTensorMap
import Langlands.Representation.Hecke.CompactComparisonLocalSections

/-! The actual tensor comparison: surjectivity and categorical assembly. -/

noncomputable section

open CategoryTheory MeasureTheory MulOpposite

namespace Langlands.Hecke.Homomorphism

open Langlands.Algebra

universe uG v

variable {G : Type uG} [Group G] [TopologicalSpace G] [T2Space G]
  [NonarchimedeanGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  (μG : Measure G) [μG.IsHaarMeasure]
  (H : Subgroup G) [LocallyCompactSpace H] (hH : IsClosed (H : Set G))
  (μH : Measure H) [μH.IsHaarMeasure]

/-- The actual quotient lift is onto the original compact-induction space. -/
theorem compactComparisonLift_surjective
    {V : Type v} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ H V) (hρ : IsSmooth ρ) :
    Function.Surjective (compactComparisonLift μG H hH μH ρ hρ) := by
  let := rightModule μG μH H.subtype continuous_subtype_val
  let := heckeNonUnitalModule μH ρ hρ
  apply compactComparison_surjective_of_pure_values H μH ρ hρ hH
  intro T w
  exact ⟨NonUnitalModuleTensor.tmul (HeckeAlgebra μH) (HeckeAlgebra μG) V T w, rfl⟩

/-- Every component of the natural comparison is surjective. -/
theorem compactComparisonHom_surjective
    (W : Langlands.SmoothRep.{0, uG, v} ℂ H) :
    Function.Surjective (compactComparisonHom μG H hH μH W).hom.toAddMonoidHom :=
  compactComparisonLift_surjective μG H hH μH W.representation W.isSmooth

/-- The categorical component has the exact prescribed scalarized value. -/
theorem compactComparisonHom_dual
    (W : Langlands.SmoothRep.{0, uG, v} ℂ H)
    (T : HeckeAlgebra μG) (w : W) (g : G) (ell : W →ₗ[ℂ] ℂ) :
    ell (compactModularEvaluation μG H W
      ((compactComparisonHom μG H hH μH W).hom.toAddMonoidHom
        (tensorInductionTmul μG H μH W T w)) g) =
      ∫ h : H, T (((h : G) * g)⁻¹) * haarScale (h : G) *
        ell (W.representation h⁻¹ w) ∂μH :=
  compactComparisonValue_dual H hH μH W.representation W.isSmooth T w g ell


/-- A component becomes an isomorphism once its remaining injectivity property
is supplied; surjectivity and compatibility are intrinsic to the constructed map. -/
def compactComparisonComponentIsoOfInjective
    (W : Langlands.SmoothRep.{0, uG, v} ℂ H)
    (hI : Function.Injective (compactComparisonHom μG H hH μH W).hom.toAddMonoidHom) :
    (tensorInductionHeckeFunctor μG H μH).obj W ≅
      (compactModularHeckeFunctor μG H).obj W := by
  let f := compactComparisonHom μG H hH μH W
  let e := AddEquiv.ofBijective f.hom.toAddMonoidHom
    ⟨hI, compactComparisonHom_surjective μG H hH μH W⟩
  let finv : NonUnitalModuleHom (HeckeAlgebra μG)
      ((compactModularHeckeFunctor μG H).obj W).obj
      ((tensorInductionHeckeFunctor μG H μH).obj W).obj :=
    { toAddMonoidHom := e.symm.toAddMonoidHom
      map_smul' := by
        intro a x
        apply e.injective
        calc
          e (e.symm (a • x)) = a • x := e.apply_symm_apply _
          _ = a • e (e.symm x) := congrArg (a • ·) (e.apply_symm_apply x).symm
          _ = e (a • e.symm x) := (f.hom.map_smul a _).symm }
  exact
    { hom := f
      inv := ObjectProperty.homMk finv
      hom_inv_id := by
        apply ObjectProperty.hom_ext
        apply NonUnitalModuleHom.ext
        intro x
        exact e.symm_apply_apply x
      inv_hom_id := by
        apply ObjectProperty.hom_ext
        apply NonUnitalModuleHom.ext
        intro x
        exact e.apply_symm_apply x }

@[simp] theorem compactComparisonComponentIsoOfInjective_hom
    (W : Langlands.SmoothRep.{0, uG, v} ℂ H)
    (hI : Function.Injective (compactComparisonHom μG H hH μH W).hom.toAddMonoidHom) :
    (compactComparisonComponentIsoOfInjective μG H hH μH W hI).hom =
      compactComparisonHom μG H hH μH W := rfl

/-- Assembly of the fixed natural comparison, given only component injectivity. -/
def compactComparisonNatIsoOfInjective
    (hI : ∀ W : Langlands.SmoothRep.{0, uG, v} ℂ H,
      Function.Injective (compactComparisonHom μG H hH μH W).hom.toAddMonoidHom) :
    tensorInductionHeckeFunctor.{uG, v} μG H μH ≅
      compactModularHeckeFunctor.{uG, v} μG H :=
  NatIso.ofComponents
    (fun W => compactComparisonComponentIsoOfInjective μG H hH μH W (hI W))
    (fun f => (compactComparisonNatTrans μG H hH μH).naturality f)

/-- The assembled comparison retains its fixed elementary-tensor formula. -/
theorem compactComparisonNatIsoOfInjective_dual
    (hI : ∀ W : Langlands.SmoothRep.{0, uG, v} ℂ H,
      Function.Injective (compactComparisonHom μG H hH μH W).hom.toAddMonoidHom)
    (W : Langlands.SmoothRep.{0, uG, v} ℂ H)
    (T : HeckeAlgebra μG) (w : W) (g : G) (ell : W →ₗ[ℂ] ℂ) :
    ell (compactModularEvaluation μG H W
      (((compactComparisonNatIsoOfInjective μG H hH μH hI).hom.app W).hom.toAddMonoidHom
        (tensorInductionTmul μG H μH W T w)) g) =
      ∫ h : H, T (((h : G) * g)⁻¹) * haarScale (h : G) *
        ell (W.representation h⁻¹ w) ∂μH :=
  compactComparisonHom_dual μG H hH μH W T w g ell

end Langlands.Hecke.Homomorphism
