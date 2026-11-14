import Langlands.GroupScheme.SimplyConnected.LocalAnisotropicAffineDiagramStatement
import Langlands.GroupScheme.Rational.QuasiSplitRelativeRootsNonempty
import Langlands.GroupScheme.Rational.MinimalPseudoParabolicConjugacyAssembly
import Langlands.Geometry.Building.QuasiSplitDerivativeAffineRootsStatement
import Langlands.Geometry.Building.QuasiSplitIndivisibleDerivativeLiftsStatement
import Langlands.Geometry.Building.UnramifiedSpecialApartmentChamberStatement
import Langlands.Geometry.Building.MaximalUnramifiedBuildingExistence
import Langlands.Geometry.Building.MaximalUnramifiedUniformizer
import Langlands.Geometry.Building.UnramifiedOmegaGaloisStable
import Langlands.Geometry.Building.RelativeIrreducibleAffineRoots
import Langlands.Geometry.Building.AnisotropicGaloisFixedTranslations
import Langlands.Geometry.Building.SymmetricRelativeDerivativeRoots
import Langlands.Geometry.Building.IntegerValuationTitsIndexCartan

/-! # A conditional reduction of the local anisotropic affine-diagram target -/

noncomputable section

universe u uA

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.LocalGalois.Separable

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.Geometry.Building

open AffineRootSystem GalleryGeometry

/-- Full derivatives with indivisible lifts and transitive chamber-simple roots
make a maximal split torus absolutely maximal, under the relative-root
irreducibility statement. -/
theorem isMaximalTorus_of_transitive_quasiSplit_derivatives
    {k : Type u} [Field k]
    {H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom H.X.hom]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    (i : S.toGrp ⟶ H) (hi : IsMaximalSplitTorus i)
    (hq : IsQuasiSplit H) (habs : IsAbsolutelyAlmostSimple H)
    (hIrr : RelativeRootSystemIrreducibleStatement.{u})
    {A : Type uA} [AddTorsor (TranslationSpace i) A]
    {Ψ : Set (A →ᵃ[ℝ] ℝ)} (hΨ : IsAffineRootSystemWithRankZero Ψ)
    (hderiv : derivativeRoots Ψ = Set.range (rootForm i))
    {c : A} (hc : IsRegular Ψ c)
    (hlift : HasIndivisibleDerivativeLifts Ψ)
    (htrans : HasTransitiveSimpleRoots Ψ (facet Ψ c)) :
    IsMaximalTorus i := by
  have hsymm := hΨ.hasSymmetricDerivativePairing_of_transitive_simpleRoots
    (V := TranslationSpace i) (A := A) (Ψ := Ψ) (c := c) hc hlift htrans
  have hroot : HasReducedSimplyLacedRelativeRootSystem i :=
    hasReducedSimplyLacedRelativeRootSystem_of_derivative_symmetry
      (k := k) (S := S) (G := H) (A := A) (Ψ := Ψ)
      i hi.isSplitSubtorus.1 hΨ hderiv hsymm
  exact quasiSplitSimplyLacedSplitting_of_relativeRootSystemIrreducible
    hIrr k H hq habs S i hi hroot

section Assembly

variable (k K : Type u) [Field k] [Field K] [Algebra k K] [IsGalois k K]
  [Algebra K (SeparableClosure k)] [IsScalarTower k K (SeparableClosure k)]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  [IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom]
  (d : TitsIndexData G) (i : T.toGrp ⟶ G)
  [Mono ((GroupScheme.baseChange (algebraBaseMap k K)).map i).hom.hom.left]
  {v : Valuation K (WithZero (Multiplicative ℤ))}
  (D : KPApartmentData
    (S := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
    ((GroupScheme.baseChange (algebraBaseMap k K)).map i)
    (IntegerValuation.order v))
  (C : CentralizerDatum
    (S := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
    ((GroupScheme.baseChange (algebraBaseMap k K)).map i))
  (hiK : IsMaximalSplitTorus
    (T := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
    ((GroupScheme.baseChange (algebraBaseMap k K)).map i))

include hiK

/-- Assemble the absolute affine Cartan matrix on a supplied apartment before
specializing the field or choosing apartment data. Absolute maximality is
deduced from transitivity and the two derivative hypotheses. -/
theorem exists_affineDiagramMatrix_of_quasiSplit_apartment
    (h6 : IntegerValuation.IsOmegaCompatible v D C)
    (hunit : ∃ t : Kˣ, IntegerValuation.order v t = 1)
    (hD : KPApartmentData.GaloisStable k K i D)
    (hq : IsQuasiSplit ((GroupScheme.baseChange (algebraBaseMap k K)).obj G))
    (habs : IsAbsolutelyAlmostSimple
      ((GroupScheme.baseChange (algebraBaseMap k K)).obj G))
    (haniso : IsAnisotropic G) (hic : IsClosedSubgroup i)
    (hIrr : RelativeRootSystemIrreducibleStatement.{u})
    (hderiv : derivativeRoots D.affineRoots =
      Set.range (rootForm
        (S := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
        ((GroupScheme.baseChange (algebraBaseMap k K)).map i)))
    (hlift : HasIndivisibleDerivativeLifts D.affineRoots)
    {c : D.Apartment} (hc : IsRegular D.affineRoots c)
    (hC : ∀ σ : K ≃ₐ[k] K,
      KPApartmentData.galoisAffineAction k K i D hD σ '' facet D.affineRoots c =
        facet D.affineRoots c) :
    ∃ N : Matrix (Option d.Vertex) (Option d.Vertex) ℤ,
      (∀ a b, N (some a) (some b) = d.cartan a b) ∧
      (∀ a, N a a = 2) ∧
      (∀ a b, a ≠ b → N a b ≤ 0) ∧
      (∀ a b, N a b = 0 ↔ N b a = 0) ∧
      (∃ m : Option d.Vertex → ℤ,
        (∀ a, 0 < m a) ∧ Matrix.vecMul m N = 0) ∧
      AffineCartan.IsVertexTransitive N := by
  let B : IntegerValuationBuildingData v
      ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) :=
    { isConnectedReductive := hq.1
      S := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T
      i := (GroupScheme.baseChange (algebraBaseMap k K)).map i
      isMaximalSplitTorus := hiK
      apartment := D
      centralizer := C
      isOmegaCompatible := h6 }
  have hΨ : IsAffineRootSystemWithRankZero D.affineRoots :=
    B.isAffineRootSystemWithRankZero_affineRoots hunit
  have hneRel := hq.relativeRoots_nonempty_of_isAbsolutelyAlmostSimple habs _ hiK
  obtain ⟨hne, hirr⟩ := nonempty_and_isIrreducibleRoots_of_isAlmostSimple
    (k := K)
    (S := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
    (G := (GroupScheme.baseChange (algebraBaseMap k K)).obj G)
    (i := (GroupScheme.baseChange (algebraBaseMap k K)).map i)
    (Ψ := D.affineRoots) hIrr habs.1 hiK hneRel hΨ hderiv
  let := (finite_simpleAffineRoots hΨ hc).fintype
  obtain ⟨htrans, hmat⟩ := KPApartmentData.chamberTransitivity_of_isAnisotropic
    (T := T) (G := G) (ω := IntegerValuation.order v) (c := c)
    k K i D hD haniso hic hiK.isSplitSubtorus.1 hΨ hirr hc hne hC
  have hiM := isMaximalTorus_of_transitive_quasiSplit_derivatives
    (k := K)
    (S := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
    (H := (GroupScheme.baseChange (algebraBaseMap k K)).obj G)
    (A := D.Apartment) (Ψ := D.affineRoots) (c := c)
    ((GroupScheme.baseChange (algebraBaseMap k K)).map i)
    hiK hq habs hIrr hΨ hderiv hc hlift htrans
  exact exists_transitive_titsIndexCartanExtension_of_integerValuation
    d B hunit hiM hc hne hirr hmat htrans

end Assembly

set_option maxHeartbeats 1600000 in
/-- The local anisotropic affine-diagram target follows from five explicit
supporting statements. Splitting is deduced after chamber transitivity, using
the full derivative set and indivisible lifts. None of the premises is
discharged by this reduction. -/
theorem localAnisotropicAffineDiagram_of_building_inputs
    (hSpecial : SpecialTorusExistenceStatement.{u})
    (hDeriv : QuasiSplitDerivativeAffineRootsStatement.{u})
    (hLift : QuasiSplitIndivisibleDerivativeLiftsStatement.{u})
    (hChamber : UnramifiedSpecialApartmentChamberStatement.{u})
    (hIrr : RelativeRootSystemIrreducibleStatement.{u}) :
    LocalAnisotropicAffineDiagramStatement.{u} := by
  intro F _ _ _ _ G _ _ d habs haniso
  let K := inertiaFixedField F
  let b := algebraBaseMap F K
  let H := (GroupScheme.baseChange b).obj G
  have hG : IsConnectedReductive G := habs.1.isSemisimple.isConnectedReductive
  obtain ⟨S, iS, hiS⟩ := exists_maximalSplitTorus G
  obtain ⟨T, iT, f, hf, hiTc, hiT⟩ := hSpecial F G hG S iS hiS
  let T_K := (CommGroupScheme.baseChange b).obj T
  let i_K : T_K.toGrp ⟶ H := (GroupScheme.baseChange b).map iT
  have habsK : IsAbsolutelyAlmostSimple H :=
    habs.baseChange_of_algebraicExtension (K := K)
  have hGK : IsConnectedReductive H := habsK.1.isSemisimple.isConnectedReductive
  let : IsAffineHom H.X.hom := hGK.isAffineHom
  let : Mono i_K.hom.hom.left := mono_of_isMaximalSplitTorus hiT
  have hq : IsQuasiSplit H := MaximalUnramified.isQuasiSplit F hGK
  obtain ⟨D, C, h6⟩ := quasiSplitIntegerApartmentExistence
    K (MaximalUnramified.valuation F)
    (MaximalUnramified.valuation_surjective F)
    (MaximalUnramified.valuationSubring_isHenselian F) H hq T_K i_K hiT
  have hD : KPApartmentData.GaloisStable F K iT D :=
    MaximalUnramified.galoisStable_of_isOmegaCompatible iT hiTc hGK hiT D C h6
  have hunit := MaximalUnramified.exists_order_eq_one F
  have hderiv : derivativeRoots D.affineRoots = Set.range (rootForm (S := T_K) i_K) :=
    hDeriv K (MaximalUnramified.valuation F)
      (MaximalUnramified.valuation_surjective F)
      (MaximalUnramified.valuationSubring_isHenselian F) H hq T_K i_K hiT D C h6
  have hlift : HasIndivisibleDerivativeLifts D.affineRoots :=
    hLift K (MaximalUnramified.valuation F)
      (MaximalUnramified.valuation_surjective F)
      (MaximalUnramified.valuationSubring_isHenselian F) H hq T_K i_K hiT D C h6
  obtain ⟨c, hc, hC⟩ :=
    hChamber F G hG S iS hiS T iT f hf hiTc hiT D C h6 hD
  exact exists_affineDiagramMatrix_of_quasiSplit_apartment
    (T := T) (G := G) F K d iT D C hiT h6 hunit hD hq habsK haniso hiTc
    hIrr hderiv hlift hc hC

/-- Choose the required absolute affine Cartan matrix, retaining all five
unproved supporting statements as explicit arguments. -/
def localAnisotropicAffineDiagramMatrixOfBuildingInputs
    (hSpecial : SpecialTorusExistenceStatement.{u})
    (hDeriv : QuasiSplitDerivativeAffineRootsStatement.{u})
    (hLift : QuasiSplitIndivisibleDerivativeLiftsStatement.{u})
    (hChamber : UnramifiedSpecialApartmentChamberStatement.{u})
    (hIrr : RelativeRootSystemIrreducibleStatement.{u})
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G)
    (habs : IsAbsolutelyAlmostSimple G) (haniso : IsAnisotropic G) :
    Matrix (Option d.Vertex) (Option d.Vertex) ℤ :=
  Classical.choose (localAnisotropicAffineDiagram_of_building_inputs
    hSpecial hDeriv hLift hChamber hIrr F G d habs haniso)

/-- The chosen matrix has all six properties of the exact host proposition. -/
theorem localAnisotropicAffineDiagramMatrixOfBuildingInputs_spec
    (hSpecial : SpecialTorusExistenceStatement.{u})
    (hDeriv : QuasiSplitDerivativeAffineRootsStatement.{u})
    (hLift : QuasiSplitIndivisibleDerivativeLiftsStatement.{u})
    (hChamber : UnramifiedSpecialApartmentChamberStatement.{u})
    (hIrr : RelativeRootSystemIrreducibleStatement.{u})
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G)
    (habs : IsAbsolutelyAlmostSimple G) (haniso : IsAnisotropic G) :
    let N := localAnisotropicAffineDiagramMatrixOfBuildingInputs
      hSpecial hDeriv hLift hChamber hIrr F G d habs haniso
    (∀ a b, N (some a) (some b) = d.cartan a b) ∧
      (∀ a, N a a = 2) ∧
      (∀ a b, a ≠ b → N a b ≤ 0) ∧
      (∀ a b, N a b = 0 ↔ N b a = 0) ∧
      (∃ m : Option d.Vertex → ℤ,
        (∀ a, 0 < m a) ∧ Matrix.vecMul m N = 0) ∧
      AffineCartan.IsVertexTransitive N :=
  Classical.choose_spec (localAnisotropicAffineDiagram_of_building_inputs
    hSpecial hDeriv hLift hChamber hIrr F G d habs haniso)

end Langlands.Geometry.Building
