import Langlands.Representation.Plancherel.DynamicCommonLeviIrreducibility
import Langlands.Representation.Plancherel.DynamicGalleryIrreducibilityOpen
import Langlands.Representation.Plancherel.DynamicOppositeGalleryProduct
import Langlands.Representation.Plancherel.DynamicOppositeRankOneProductReduction
import Langlands.Representation.Plancherel.DynamicSameChamberGalleryScalar

/-! # Full-unitary regularity and nonnegativity of the actual opposite scalar -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel

open Aubert.General Induction UnramifiedOperatorFamily
open DynamicCommonLeviComposition DynamicCommonLeviPresentations
open DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar

attribute [local instance]
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsAffine
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsTopologicalGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarLocallyCompactSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology2
  DynamicOppositeCanonicalScalar.centralizerClosedImmersion
  DynamicOppositeCanonicalScalar.centralizerAffine
  DynamicOppositeCanonicalScalar.centralizerFiniteType
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup2

set_option maxHeartbeats 1000000 in
private theorem exists_irreducible_representedGalleryInduction
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    {χ ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G}
    (hG : IsConnectedReductive G)
    (hψ : Dynamic.centralizer ψ = Dynamic.centralizer χ)
    {T : CommGroupScheme (Spec (CommRingCat.of F))} {a : T.toGrp ⟶ parameterScheme χ}
    (d : ParabolicData χ ψ T a)
    (A : SmoothRep.{0, u, uV} ℂ (levi χ)) (hA : A.IsIrreducible)
    (C : Subgroup (levi χ)) [C.Normal] (hC : C ≤ Subgroup.center (levi χ))
    [MeasurableSpace (levi χ ⧸ C)] [BorelSpace (levi χ ⧸ C)]
    (mu : Measure (levi χ ⧸ C)) [mu.IsHaarMeasure]
    (hsq : IsSquareIntegrableModCentralSubgroup C hC A.representation mu) :
    ∃ z : unramifiedCharacters (normCharacters χ),
      (representedInduction hG d
        ((SmoothRep.pullback (parameterHomeomorph χ) A).twist z.val.toMonoidHom
          (unramifiedCharacter_isOpen_ker (normCharacters χ) z))).IsIrreducible := by
  obtain ⟨D, _, ⟨z, hz⟩, hIrr⟩ :=
    DynamicCommonLeviIrreducibility.hasOpenIrreducibilityLocus χ ψ hψ A hG hA
      C hC mu hsq
  let B := A.twist (parameterTransport χ z).val.toMonoidHom
    (unramifiedCharacter_isOpen_ker (leviNormCharacters χ) (parameterTransport χ z))
  have hRep : (representedInduction hG d (SmoothRep.pullback (parameterHomeomorph χ) B)).IsIrreducible :=
    SmoothRep.isIrreducible_of_equiv (representedDynamicInductionEquiv hG d hψ B).symm
      (hIrr z hz)
  have htwist := congrArg
    (fun σ : SmoothRep.{0, u, uV} ℂ (rationalPoints (parameterScheme χ)) =>
      (representedInduction hG d σ).IsIrreducible)
    (intrinsicGalleryCoefficient_twist χ A z)
  exact ⟨z, htwist.mp hRep⟩

private theorem genericRankOneGalleryFactor_of_coordinates
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    {χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G} (hG : IsConnectedReductive G)
    {T : CommGroupScheme (Spec (CommRingCat.of F))} {a : T.toGrp ⟶ parameterScheme χ}
    (ha : IsSplitComponent a)
    (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
    (σ : SmoothRep.{0, u, uV} ℂ (rationalPoints (parameterScheme χ)))
    {x y : GalleryVertex χ}
    (h : HasGenericRankOneGalleryFactorCoordinates hG ha K hK σ x y) :
    HasGenericRankOneGalleryFactor hG ha K hK σ x y := by
  obtain ⟨p, r, n, e, g, hp, hr, hInv, hScalar⟩ := h
  exact ⟨p, ⟨r, n, hr, e⟩, g, hp, hInv, hScalar⟩

set_option maxHeartbeats 1800000 in
private theorem hasGenericRankOneGalleryFactors_of_squareIntegrable
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    {χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G} (hG : IsConnectedReductive G)
    {T : CommGroupScheme (Spec (CommRingCat.of F))} {a : T.toGrp ⟶ parameterScheme χ}
    (ha : IsSplitComponent a)
    (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
    (A : SmoothRep.{0, u, uV} ℂ (levi χ)) (hA : A.IsIrreducible)
    (C : Subgroup (levi χ)) [C.Normal] (hC : C ≤ Subgroup.center (levi χ))
    [MeasurableSpace (levi χ ⧸ C)] [BorelSpace (levi χ ⧸ C)]
    (mu : Measure (levi χ ⧸ C)) [mu.IsHaarMeasure]
    (hsq : IsSquareIntegrableModCentralSubgroup C hC A.representation mu) :
    HasGenericRankOneGalleryFactors χ hG ha K hK (SmoothRep.pullback (parameterHomeomorph χ) A) := by
  let σ := SmoothRep.pullback (parameterHomeomorph χ) A
  have hirr : σ.IsIrreducible :=
    (isIrreducible_comp_continuousMulEquiv_iff A.representation (parameterHomeomorph χ)).mpr hA
  have hadm : σ.IsAdmissible :=
    isAdmissible_comp_continuousMulEquiv A.representation (parameterHomeomorph χ) hsq.1
  intro x y hEdge
  apply genericRankOneGalleryFactor_of_coordinates hG ha K hK σ
  rcases hEdge with hChamber | hWall
  · exact hasGenericRankOneGalleryFactorCoordinates_of_sameChamber hG ha K hK σ hChamber hirr hadm
  · obtain ⟨wall⟩ := hWall
    let d := galleryVertexData hG ha x
    obtain ⟨z, hz⟩ := exists_irreducible_representedGalleryInduction hG x.property d A hA
      C hC mu hsq
    have hIrr := hasPrincipalRepresentedIrreducibilityLocus_of_one hG σ d hirr hadm z hz
    obtain ⟨p, hp, hOn⟩ := exists_galleryRegularIrreduciblePrincipalOpen hG σ ha x y hirr hadm hIrr
    exact hasGenericRankOneGalleryFactorCoordinates_of_wall hG ha K hK σ wall p hp
      (fun w hw => (hOn w hw).1) (fun w hw => (hOn w hw).2.1) (fun w hw => (hOn w hw).2.2)

set_option maxHeartbeats 1200000 in
private theorem denseRankOneProduct_of_squareIntegrable :
    ConditionalDynamicOppositeSquareIntegrableRankOneProductStatement.{u, uV} := by
  intro F _ _ _ _ G _ _ χ hRefl hCST hG K hK hPK hOppK A p q
    DForward DReverse hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ
    D hD hne hi C _ hC _ _ muM _ _ hsq
  have hA := DynamicOppositeSquareIntegrableForm.irreducible_of_locus χ hG A hne hi
  obtain ⟨T, a, ha⟩ := (splitComponentStatement F (parameterScheme χ)
    (parameterScheme_isConnectedReductive χ hG)).1
  have hP := DynamicOppositeSquareIntegrablePositivity.unitaryPositive_of_squareIntegrable
    χ hRefl hCST hG K hK hPK hOppK A p q hDForward hneForward hDForwardΩ
    hDReverse hneReverse hDReverseΩ hD hne hi C hC muM hsq
  exact hasDenseRankOneProduct_of_oppositeGallery χ hRefl hCST hG ha K hK hPK hOppK A p q
    hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hi hsq.1 hP.1
    (hasGenericRankOneGalleryFactors_of_squareIntegrable hG ha K hK A hA C hC muM hsq)

/-- The actual canonical opposite scalar is nonzero, and its inverse is
regular with nonnegative real value at every unitary unramified character. -/
theorem conditionalDynamicOppositeUnitaryScalar :
    ConditionalDynamicOppositeUnitaryScalarStatement.{u, uV} :=
  conditionalDynamicOppositeUnitaryScalar_of_denseRankOneProduct denseRankOneProduct_of_squareIntegrable

end Langlands.Plancherel
