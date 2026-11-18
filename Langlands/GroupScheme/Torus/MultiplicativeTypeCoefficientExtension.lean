import Langlands.GroupScheme.Torus.MultiplicativeTypeResidueExtension
import Langlands.GroupScheme.Torus.MultiplicativeTypeNoetherianLocalExtension
import Langlands.GroupScheme.Descent.FiniteCoefficientSplitExtension
import Langlands.GroupScheme.Torus.MultiplicativeTypeExtensionReduction
import Langlands.GroupScheme.Torus.LocalDiagonalizableHom

/-! # assembly over coefficient rings -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme.ExtensionReduction

/-- Compare field-level multiplicative type on the scheme residue fibre
with the canonical ideal-residue-field pullback over an affine spectrum. -/
theorem idealResidue_fieldMultiplicativeType
    {R : Type u} [CommRing R] (G : GroupScheme (Spec (CommRingCat.of R)))
    (p : PrimeSpectrum R)
    (hG : IsMultiplicativeType (RelativeIdentityComponent.residueFiber G p)) :
    IsMultiplicativeType ((baseChange (Spec.algebraMap R p.asIdeal.ResidueField)).obj G) := by
  let e := Scheme.Spec.residueFieldIso (CommRingCat.of R) p
  let : Algebra ((Spec (CommRingCat.of R)).residueField p) p.asIdeal.ResidueField :=
    e.hom.hom.toAlgebra
  let b := Spec.map e.hom
  have hres : Spec.map e.inv ≫ Spec.algebraMap R p.asIdeal.ResidueField =
      (Spec (CommRingCat.of R)).fromSpecResidueField p :=
    Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField (CommRingCat.of R) p
  have hcomp : Spec.map e.hom ≫ Spec.map e.inv = 𝟙 _ := by
    rw [← Spec.map_comp, e.inv_hom_id, Spec.map_id]
  have hb : b ≫ (Spec (CommRingCat.of R)).fromSpecResidueField p =
      Spec.algebraMap R p.asIdeal.ResidueField := by
    rw [← hres]
    change Spec.map e.hom ≫ (Spec.map e.inv ≫ Spec.algebraMap R p.asIdeal.ResidueField) = _
    rw [← Category.assoc, hcomp, Category.id_comp]
  have hext : IsMultiplicativeType
      ((baseChange b).obj (RelativeIdentityComponent.residueFiber G p)) :=
    IsMultiplicativeType.fieldExtension
      (k := (Spec (CommRingCat.of R)).residueField p) (K := p.asIdeal.ResidueField) hG
  exact IsMultiplicativeType.of_iso
    (Descent.pullbackComparison ((Spec (CommRingCat.of R)).fromSpecResidueField p)
      b (Spec.algebraMap R p.asIdeal.ResidueField) hb G).symm hext

/-- Field-level multiplicative type reflects to the model residue point
under an actual coefficient recovery isomorphism. -/
theorem modelResidue_fieldMultiplicativeType
    {C R : Type u} [CommRing C] [CommRing R] [Algebra C R]
    (H : GroupScheme (Spec (CommRingCat.of C)))
    (G : GroupScheme (Spec (CommRingCat.of R)))
    (e : G ≅ (baseChange (Spec.algebraMap C R)).obj H)
    (s : PrimeSpectrum R)
    (hG : IsMultiplicativeType ((baseChange (Spec.algebraMap R s.asIdeal.ResidueField)).obj G)) :
    IsMultiplicativeType ((baseChange (Spec.algebraMap C
      (PrimeSpectrum.comap (algebraMap C R) s).asIdeal.ResidueField)).obj H) := by
  let p := PrimeSpectrum.comap (algebraMap C R) s
  let φ := Ideal.ResidueField.map p.asIdeal s.asIdeal (algebraMap C R) rfl
  let : Algebra p.asIdeal.ResidueField s.asIdeal.ResidueField := φ.toAlgebra
  let b := Spec.algebraMap C R
  let spC := Spec.algebraMap C p.asIdeal.ResidueField
  let spR := Spec.algebraMap R s.asIdeal.ResidueField
  let a := Spec.map (CommRingCat.ofHom φ)
  have ha : a ≫ spC = spR ≫ b := by
    dsimp [a, spC, spR, b, Spec.algebraMap]
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp]
    congr 1
    ext c
    exact Ideal.ResidueField.map_algebraMap p.asIdeal s.asIdeal (algebraMap C R) rfl c
  let e' := Descent.pullbackComparison spC a (spR ≫ b) ha H ≪≫ baseChangeCompIso b spR H
  apply IsMultiplicativeType.of_fieldExtension (K := s.asIdeal.ResidueField)
  exact IsMultiplicativeType.of_iso e'
    (IsMultiplicativeType.of_iso ((baseChange spR).mapIso e).symm hG)

/-- Exact extensions with split endpoints are of relative multiplicative
type over any coefficient ring once every middle residue fibre is of
field-level multiplicative type. The three remaining proof inputs are explicit. -/
theorem ringExtension_of_fieldResidues
    (hcrit : MultiplicativeTypeFibralCriterionStatement.{u})
    (hdef : MultiplicativeTypeCompleteLocalDeformationStatement.{u})
    (hchar : ∀ (A : Type u) [CommRing A] [IsLocalRing A],
      CompleteLocalExtension.LocalCharacterSurjectivity A)
    (R : Type u) [CommRing R]
    (N G Q : GroupScheme (Spec (CommRingCat.of R)))
    [Flat G.X.hom] [LocallyOfFinitePresentation G.X.hom] [IsAffineHom G.X.hom]
    [Flat Q.X.hom] [LocallyOfFinitePresentation Q.X.hom] [IsAffineHom Q.X.hom]
    (i : N ⟶ G) (q : G ⟶ Q) (hi : Mono i.hom.hom)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q)
    (hN : RelativeMultiplicativeType.IsDiagonalizable N)
    (hQ : RelativeMultiplicativeType.IsDiagonalizable Q)
    (hfib : ∀ s : PrimeSpectrum R, IsMultiplicativeType
      ((baseChange (Spec.algebraMap R s.asIdeal.ResidueField)).obj G)) :
    RelativeMultiplicativeType.IsMultiplicativeType G := by
  classical
  let R₀ := ULift.{u} ℤ
  let : Algebra R₀ R := ULift.algebra' ℤ R
  have : IsNoetherianRing R₀ := isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsAffine Q.X.left := isAffine_of_isAffineHom Q.X.hom
  let := hi
  obtain ⟨D, -⟩ := Descent.FiniteCoefficient.exists_splitFlatAffineQuotientModel_of_quotient
    (R := R₀) (A := R) i q hq hN hQ (∅ : Finset R)
  have : IsNoetherianRing D.coefficients := D.noetherian
  have : Flat D.source.X.hom := D.sourceFlat
  have : LocallyOfFinitePresentation D.source.X.hom := D.sourceFinitePresentation
  have : IsAffineHom D.source.X.hom := D.sourceAffine
  let b := Spec.algebraMap D.coefficients R
  have hn (s : PrimeSpectrum R) :
      ∃ (U : Scheme.{u}) (_ : IsAffine U) (v : U ⟶ Spec (CommRingCat.of R)),
        Flat v ∧ LocallyOfFinitePresentation v ∧ s ∈ Set.range v ∧
          RelativeMultiplicativeType.IsDiagonalizable ((baseChange v).obj G) := by
    let p := PrimeSpectrum.comap (algebraMap D.coefficients R) s
    have hmodel : IsMultiplicativeType
        ((baseChange (Spec.algebraMap D.coefficients p.asIdeal.ResidueField)).obj D.source) :=
      modelResidue_fieldMultiplicativeType D.source G D.sourceIso s (hfib s)
    obtain ⟨U, hU, v, hvflat, hvfp, hvpoint, hvdiag⟩ :=
      noetherian_exists_diagonalizing_neighbourhood hcrit hdef hchar D.coefficients
        (kernel D.hom) D.source D.target (kernelι D.hom) D.hom
        D.toFlatAffineQuotientModel.isFppfQuotient_kernel
        D.kernelDiagonalizable D.targetDiagonalizable p hmodel
    let := hU
    let := hvflat
    let := hvfp
    let W := pullback v b
    let z : W ⟶ Spec (CommRingCat.of R) := pullback.snd v b
    have hzpoint : s ∈ Set.range z := by
      change s ∈ Set.range (pullback.snd v b)
      rw [Scheme.Pullback.range_snd]
      exact hvpoint
    let ec : (baseChange z).obj G ≅
        (baseChange (pullback.fst v b)).obj ((baseChange v).obj D.source) :=
      (baseChange z).mapIso D.sourceIso ≪≫
        Descent.pullbackComparison b z (pullback.fst v b ≫ v) pullback.condition.symm D.source ≪≫
          baseChangeCompIso v (pullback.fst v b) D.source
    exact ⟨W, inferInstance, z, inferInstance, inferInstance, hzpoint,
      RelativeMultiplicativeType.IsDiagonalizable.of_iso ec
        (hvdiag.baseChange (pullback.fst v b))⟩
  choose U hU v hvflat hvfp hvpoint hvdiag using hn
  let C : Scheme.Cover.{u} Scheme.fppfPrecoverage (Spec (CommRingCat.of R)) :=
    Scheme.Cover.mkOfCovers (PrimeSpectrum R) U v
      (fun s => by obtain ⟨w, hw⟩ := hvpoint s; exact ⟨s, w, hw⟩)
      (fun s => ⟨hvflat s, hvfp s⟩)
  exact ⟨C, hvdiag⟩

/-- The affine split-endpoint case follows from the three exact sibling
statements and the local character classification. -/
theorem affineSplit_of_fibral_deformation_field
    (hcrit : MultiplicativeTypeFibralCriterionStatement.{u})
    (hdef : MultiplicativeTypeCompleteLocalDeformationStatement.{u})
    (hfield : MultiplicativeTypeFieldExtensionStatement.{u})
    (hchar : ∀ (A : Type u) [CommRing A] [IsLocalRing A],
      CompleteLocalExtension.LocalCharacterSurjectivity A) :
    AffineSplitExtensionStatement.{u} := by
  intro S _ N G Q _ _ _ _ _ _ _ _ _ i q hi hq hN hQ hfib
  let b := S.isoSpec.inv
  let F := baseChange b
  have : Flat (F.obj G).X.hom := by
    change Flat (pullback.snd G.X.hom b)
    infer_instance
  have : LocallyOfFinitePresentation (F.obj G).X.hom := by
    change LocallyOfFinitePresentation (pullback.snd G.X.hom b)
    infer_instance
  have : IsAffineHom (F.obj G).X.hom := by
    change IsAffineHom (pullback.snd G.X.hom b)
    infer_instance
  have : Flat (F.obj Q).X.hom := by
    change Flat (pullback.snd Q.X.hom b)
    infer_instance
  have : LocallyOfFinitePresentation (F.obj Q).X.hom := by
    change LocallyOfFinitePresentation (pullback.snd Q.X.hom b)
    infer_instance
  have : IsAffineHom (F.obj Q).X.hom := by
    change IsAffineHom (pullback.snd Q.X.hom b)
    infer_instance
  let := hi
  have hi' : Mono (F.map i).hom.hom := by
    change Mono ((Over.pullback b).map i.hom.hom)
    infer_instance
  have hq' : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (F.map i)) (F.map q) := by
    change RelativeRoot.IsFppfQuotient (SubgroupFunctor.range ((baseChange b).map i))
      ((baseChange b).map q)
    simpa only [SubgroupFunctor.range_baseChangeHom] using hq.baseChange b
  have hG : RelativeMultiplicativeType.IsMultiplicativeType (F.obj G) :=
    ringExtension_of_fieldResidues hcrit hdef hchar Γ(S, ⊤) (F.obj N) (F.obj G) (F.obj Q)
      (F.map i) (F.map q) hi' hq' (hN.baseChange b) (hQ.baseChange b) (fun s =>
        idealResidue_fieldMultiplicativeType (F.obj G) s
          (residueFiber_fieldMultiplicativeType_of_extension hfield
            (F.obj N) (F.obj G) (F.obj Q) (F.map i) (F.map q) hi' hq'
            (hN.baseChange b) (hQ.baseChange b) (hfib.baseChange b) s))
  exact FpqcMultiplicativeType.of_fpqcBaseChange_of_fibralCriterion hcrit G b hG

/-- The full original target, conditional only on the three exact sibling
statements and the local character classification. -/
theorem fpqcExtension_of_fibral_deformation_field
    (hcrit : MultiplicativeTypeFibralCriterionStatement.{u})
    (hdef : MultiplicativeTypeCompleteLocalDeformationStatement.{u})
    (hfield : MultiplicativeTypeFieldExtensionStatement.{u})
    (hchar : ∀ (A : Type u) [CommRing A] [IsLocalRing A],
      CompleteLocalExtension.LocalCharacterSurjectivity A) :
    MultiplicativeTypeFpqcExtensionStatement.{u} :=
  fpqcExtension_of_fibral_and_affineSplit hcrit
    (affineSplit_of_fibral_deformation_field hcrit hdef hfield hchar)

/-- The published local character classification discharges the fourth
premise of the preceding assembly. -/
theorem fpqcExtension_of_threeStatements
    (hcrit : MultiplicativeTypeFibralCriterionStatement.{u})
    (hdef : MultiplicativeTypeCompleteLocalDeformationStatement.{u})
    (hfield : MultiplicativeTypeFieldExtensionStatement.{u}) :
    MultiplicativeTypeFpqcExtensionStatement.{u} := by
  apply fpqcExtension_of_fibral_deformation_field hcrit hdef hfield
  intro A _ _ M N _ _
  exact (CompleteLocalDeformation.restrictMap_bijective (R := A) M N).2

/-- An actual fppf diagonalizing cover for the extension group, conditional
on the three exact sibling statements. -/
def extensionDiagonalizingCover
    (hcrit : MultiplicativeTypeFibralCriterionStatement.{u})
    (hdef : MultiplicativeTypeCompleteLocalDeformationStatement.{u})
    (hfield : MultiplicativeTypeFieldExtensionStatement.{u})
    {S : Scheme.{u}} (N G Q : GroupScheme S)
    [Flat N.X.hom] [LocallyOfFinitePresentation N.X.hom] [IsAffineHom N.X.hom]
    [Flat G.X.hom] [LocallyOfFinitePresentation G.X.hom] [IsAffineHom G.X.hom]
    [Flat Q.X.hom] [LocallyOfFinitePresentation Q.X.hom] [IsAffineHom Q.X.hom]
    (i : N ⟶ G) (q : G ⟶ Q) (hi : Mono i.hom.hom)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q)
    (hN : RelativeMultiplicativeType.IsMultiplicativeType N)
    (hQ : RelativeMultiplicativeType.IsMultiplicativeType Q)
    (hfib : ConnectedOrCommutativeFibers G) :
    Σ (C : Scheme.Cover.{u} Scheme.fppfPrecoverage S),
      PLift (∀ j, RelativeMultiplicativeType.IsDiagonalizable ((baseChange (C.f j)).obj G)) := by
  let h := ((fpqcExtension_of_threeStatements hcrit hdef hfield S).2
    N G Q i q hi hq hN hQ hfib)
  exact ⟨Classical.choose h, ⟨Classical.choose_spec h⟩⟩

end Langlands.GroupScheme.ExtensionReduction
