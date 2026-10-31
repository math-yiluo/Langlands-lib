import Langlands.Shimura.PEL.ReflexSectionPullback
import Langlands.Shimura.Unitary.CocharacterReflexField

/-! # The Harris CM base and the actual cocharacter reflex base -/

noncomputable section

open CategoryTheory AlgebraicGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

namespace Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof

variable {R R' : CommRingCat.{u}} {S : Scheme.{u}}

/-- Postcomposing a scheme structure map with `Spec.map` composes its scalar sections. -/
lemma secHom_postcomp_specMap (f : R ⟶ R') (p : S ⟶ Spec R') (U : S.Opens) :
    secHom (p ≫ Spec.map f) U = f ≫ secHom p U := by
  rw [← secHom_comp_appLE (Spec.map f) p ⊤ U
    (le_top.trans_eq p.preimage_top.symm)]
  have hf : secHom (Spec.map f) ⊤ = f ≫ (Scheme.ΓSpecIso R').inv := by
    change (Scheme.ΓSpecIso R).inv ≫ (Spec.map f).appTop = _
    exact (Scheme.ΓSpecIso_inv_naturality f).symm
  rw [hf, Category.assoc]
  rfl

end Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof

namespace Langlands.Shimura.CentralSimpleUnitaryData

open NumberField _root_.Algebra
open Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof

variable {E K A : Type}
    [Field E] [NumberField E] [IsTotallyReal E]
    [Field K] [NumberField K] [IsTotallyComplex K]
    [Algebra E K] [IsQuadraticExtension E K]
    [Ring A] [Algebra E A] [Algebra K A] [IsScalarTower E K A]
    [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ K A]
    {n : ℕ} (D : CentralSimpleUnitaryData E K A n)
    {L : Type} [Field L] [NumberField L] [IsCMField L]
    [IsQuadraticExtension ℚ L]
    {j : L →+* K} {τ₀ : L →+* ℂ}
    (C : HarrisSignatureCharts D.toSecondKindInvolution n (harrisCMSection E j τ₀))

/-- The actual Harris reflex field is contained in the distinguished CM image,
including the exceptional rational-reflex case. -/
theorem harrisCocharacterReflexField_le_distinguishedImage :
    D.kottwitzCocharacterReflexField C ≤ C.distinguishedImage := by
  rw [D.kottwitzCocharacterReflexField_eq_reflexField C
    (isCMSection_harrisCMSection E j τ₀)]
  exact (C.reflexField_le_fixedField).trans_eq (complexFixedField C.distinguishedImage)

/-- The scalar map from the actual cocharacter reflex field to the source CM field.
It is the inverse distinguished embedding on its image. -/
def harrisReflexToCM : D.kottwitzCocharacterReflexField C →ₐ[ℚ] K :=
  C.distinguishedEmbedding.toRatAlgHom.equivFieldRange.symm.toAlgHom.comp
    (IntermediateField.inclusion (D.harrisCocharacterReflexField_le_distinguishedImage C))

/-- The scalar map realizes the given inclusion of the reflex field in the complex numbers. -/
@[simp] theorem distinguishedEmbedding_harrisReflexToCM
    (a : D.kottwitzCocharacterReflexField C) :
    C.distinguishedEmbedding (D.harrisReflexToCM C a) = (a : ℂ) := by
  have h := C.distinguishedEmbedding.toRatAlgHom.equivFieldRange.apply_symm_apply
    (IntermediateField.inclusion (D.harrisCocharacterReflexField_le_distinguishedImage C) a)
  exact congrArg (fun z : C.distinguishedImage => (z : ℂ)) h

/-- The scalar map is uniquely determined by the distinguished complex embedding. -/
theorem harrisReflexToCM_unique
    (f : D.kottwitzCocharacterReflexField C →ₐ[ℚ] K)
    (hf : ∀ a, C.distinguishedEmbedding (f a) = (a : ℂ)) :
    f = D.harrisReflexToCM C := by
  ext a
  apply C.distinguishedEmbedding.injective
  rw [hf, D.distinguishedEmbedding_harrisReflexToCM C]

/-- Away from the exceptional case the scalar map is surjective. -/
theorem harrisReflexToCM_surjective
    (hn : 3 ≤ n ∨ ∃ τ, τ ≠ C.distinguished) :
    Function.Surjective (D.harrisReflexToCM C) := by
  intro a
  have ha : C.distinguishedEmbedding a ∈ D.kottwitzCocharacterReflexField C := by
    rw [D.kottwitzCocharacterReflexField_eq_distinguishedImage C hn]
    exact AlgHom.mem_fieldRange.mpr ⟨a, rfl⟩
  refine ⟨⟨C.distinguishedEmbedding a, ha⟩, ?_⟩
  apply C.distinguishedEmbedding.injective
  exact D.distinguishedEmbedding_harrisReflexToCM C _

/-- In the nonexceptional case this is an actual rational algebra equivalence. -/
def harrisReflexCMEquiv (hn : 3 ≤ n ∨ ∃ τ, τ ≠ C.distinguished) :
    D.kottwitzCocharacterReflexField C ≃ₐ[ℚ] K :=
  AlgEquiv.ofBijective (D.harrisReflexToCM C)
    ⟨(D.harrisReflexToCM C).injective, D.harrisReflexToCM_surjective C hn⟩

@[simp] theorem harrisReflexCMEquiv_apply
    (hn : 3 ≤ n ∨ ∃ τ, τ ≠ C.distinguished)
    (a : D.kottwitzCocharacterReflexField C) :
    D.harrisReflexCMEquiv C hn a = D.harrisReflexToCM C a := rfl

/-- The actual scheme map from the source CM base to the cocharacter reflex base. -/
def harrisCMToReflexBase :
    Spec (.of K) ⟶ Spec (.of (D.kottwitzCocharacterReflexField C)) :=
  Spec.map (CommRingCat.ofHom (D.harrisReflexToCM C).toRingHom)

/-- The distinguished complex points commute with the constructed base map. -/
theorem harrisCMToReflexBase_complex :
    Spec.map (CommRingCat.ofHom C.distinguishedEmbedding) ≫ D.harrisCMToReflexBase C =
      Spec.map (CommRingCat.ofHom
        (D.kottwitzCocharacterReflexField C).val.toRingHom) := by
  unfold harrisCMToReflexBase
  rw [← Spec.map_comp]
  congr 1
  ext a
  exact D.distinguishedEmbedding_harrisReflexToCM C a

variable {S T : Scheme.{0}} (p : S ⟶ Spec (.of K))

/-- The reflex structure morphism constructed from an actual Harris CM-base scheme. -/
def harrisReflexStructure :
    S ⟶ Spec (.of (D.kottwitzCocharacterReflexField C)) :=
  p ≫ D.harrisCMToReflexBase C

/-- The two structure maps remain related after arbitrary actual scheme base change. -/
theorem harrisReflexStructure_comp (f : T ⟶ S) :
    D.harrisReflexStructure C (f ≫ p) = f ≫ D.harrisReflexStructure C p := by
  exact Category.assoc f p (D.harrisCMToReflexBase C)

/-- The reflex coefficients on a CM-base scheme use this exact scalar homomorphism. -/
theorem secHom_harrisReflexStructure (U : S.Opens) :
    secHom (D.harrisReflexStructure C p) U =
      CommRingCat.ofHom (D.harrisReflexToCM C).toRingHom ≫ secHom p U :=
  secHom_postcomp_specMap _ p U

/-- The actual determinant sections are obtained from the same CM structure map. -/
theorem harrisReflexSectionDeterminant_CM
    {ι : Type} [Fintype ι] (a : ι → D.harrisHodgePELIntegralOrder C)
    (U : S.Opens) :
    D.harrisReflexSectionDeterminant C (isCMSection_harrisCMSection E j τ₀)
        (D.harrisReflexStructure C p) a U =
      MvPolynomial.map (secHom p U).hom
        (D.kottwitzReflexDeterminantBaseChange C
          (isCMSection_harrisCMSection E j τ₀) (fun i => (a i : A))
          (D.harrisReflexToCM C).toRingHom) := by
  unfold harrisReflexSectionDeterminant kottwitzReflexDeterminantBaseChange
  rw [D.secHom_harrisReflexStructure C p, MvPolynomial.map_map]
  rfl

end Langlands.Shimura.CentralSimpleUnitaryData
