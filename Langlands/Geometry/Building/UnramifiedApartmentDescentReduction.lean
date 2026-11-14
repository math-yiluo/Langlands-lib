import Langlands.Geometry.Building.UnramifiedApartmentDescentAssembly
import Langlands.Geometry.Building.UnramifiedAffineRootRestrictionStatement
import Langlands.Geometry.Building.MaximalUnramifiedApartmentInjective
import Langlands.Geometry.Building.QuasiSplitIntegerApartmentExistenceProof
import Langlands.GroupScheme.Rational.HenselianDiscreteQuasiSplitProof

/-! # A global reduction for apartment-compatible unramified descent -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 4000000
set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

open UnramifiedBuildingDescent

section RootRestriction

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [Smooth G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {iT : T.toGrp ⟶ G}
  [Mono ((GroupScheme.baseChange
    (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left]
  (hiT : IsMaximalSplitTorus
    (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
  (hE : RelativeRoot.HasOppositeFactorPairs
    (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
  (D : KPApartmentData
    (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)
    (IntegerValuation.order (MaximalUnramified.valuation F)))
  (B : ValuationBuildingData G) (f : B.S ⟶ T)
  (hcar : ∀ ψ : RootFunctionFamily B.S G, ψ ∈ B.apartment.carrier ↔
    ∃ x : D.Apartment, apartmentGaloisFixed D x ∧ ψ = apartmentRestriction hiT hE D B f x)
  (hinj : ∀ x y : D.Apartment, apartmentGaloisFixed D x → apartmentGaloisFixed D y →
    apartmentRestriction hiT hE D B f x = apartmentRestriction hiT hE D B f y → x = y)
  (hf : CommGroupScheme.groupHom f ≫ iT = B.i)
  (C : CentralizerDatum
    (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
  (h6 : IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) D C)

include hf C h6 in
/-- The global affine-root statement supplies the exact root equality needed by
our concrete fixed-lift apartment map. -/
theorem descentAffineMap_roots_of_unramifiedAffineRootRestriction
    (hR : UnramifiedAffineRootRestrictionStatement.{u}) :
    AffineRootSystem.restrictedRoots (descentAffineMap hiT hE D B f hcar hinj)
      D.affineRoots = B.affineRoots := by
  have ht := hR F G B.isConnectedReductive B.S B.i B.isMaximalSplitTorus T iT f hf
    hiT hE D C h6 B.apartment hcar
    (descentAffineMap hiT hE D B f hcar hinj)
    (fun w σ => descentAffineMap_fixed hiT hE D B f hcar hinj w σ)
    (fun w => descentPoint_val B (apartmentGaloisFixed D)
      (apartmentRestriction hiT hE D B f) hcar w)
    (LinearMap.ext fun _ => rfl)
  exact ht

end RootRestriction

/-- Six global inputs suffice for the exact apartment-compatible descent target.
Quasi-splitness, existence of the upper compatible class and upper apartment
injectivity are supplied by published proofs. -/
def UnramifiedApartmentDescentReductionStatement : Prop :=
  SpecialTorusExistenceStatement.{u} →
  UnramifiedValuationDescentStatement.{u} →
  ValuationBuildingApartmentAxiomsStatement.{u} →
  ChapterSevenBuildingAxiomsStatement.{u} →
  UnramifiedGaloisFixedBuildingPointStatement.{u} →
  UnramifiedAffineRootRestrictionStatement.{u} →
  UnramifiedApartmentDescentStatement.{u}

/-- Choose and descend the compatible upper class, identify the descended class
with the supplied apartment, and apply the eight-clause assembly. -/
theorem unramifiedApartmentDescentReduction :
    UnramifiedApartmentDescentReductionStatement.{u} := by
  intro hSpec hDesc hAx hCh7 hFix hRoots F _ _ _ _ G hG
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  intro B
  obtain ⟨T, iT, f, hf, hiTc, hiT⟩ := hSpec F G hG B.S B.i B.isMaximalSplitTorus
  have := mono_of_isMaximalSplitTorus hiT
  have hGK : IsConnectedReductive (baseChanged F (inertiaFixedField F) G) :=
    connectedReductiveFieldExtensionStatement F (inertiaFixedField F) G hG
  obtain ⟨D, C, h6⟩ := exists_omegaCompatible
    (unramifiedQuasiSplit_of_henselianDiscrete henselianDiscreteQuasiSplit)
    quasiSplitIntegerApartmentExistence iT hGK hiT
  have hE : RelativeRoot.HasOppositeFactorPairs
      (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
      ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT) :=
    (RelativeRoot.hasRankOneFactorization_iff_hasOppositeFactorPairs _
      hiT.isSplitSubtorus.1).mp
      (rootRankOneFactorization (inertiaFixedField F) (baseChanged F (inertiaFixedField F) G)
        hGK _ _ hiT)
  have hD : KPApartmentData.GaloisStable F (inertiaFixedField F) iT D :=
    MaximalUnramified.galoisStable_of_isOmegaCompatible iT hiTc hGK hiT D C h6
  obtain ⟨DS, CS, h6S, hcar, hinj, hnorm⟩ :=
    hDesc F G hG B.S B.i B.isMaximalSplitTorus T iT f hf hiT hE D C h6
  have hDS : DS = B.apartment :=
    omegaCompatibleApartmentUniqueness F G hG B.S B.i B.isMaximalSplitTorus B.centralizer DS
      B.apartment (h6S.of_centralizerDatum B.centralizer) B.isOmegaCompatible
  subst hDS
  have hroots := descentAffineMap_roots_of_unramifiedAffineRootRestriction
    hiT hE D B f hcar hinj hf C h6 hRoots
  let A : ApartmentDescentData B :=
    apartmentDescentData hiT hE D B f hcar hinj hroots hGK C h6 hD hf hnorm
      (fun x w hw a => filtration_le_comap_sharpFixer_of_torusFieldRestriction f hf
        B.isMaximalSplitTorus.isSplitSubtorus.1 hiT.isSplitSubtorus.1 hE D x B.apartment w hw a)
      (maximalUnramifiedApartmentInjective F (baseChanged F (inertiaFixedField F) G)
        (buildingData iT hGK hiT D C h6))
      (exists_satisfiesBuildingAxiom hAx hCh7 B)
      (hFix F G hG B.S B.i B.isMaximalSplitTorus T iT f hf hiT D C h6 hD)
  exact ⟨A.building, A.semilinear, A.embedding, A.apartment, A.injective,
    A.equivariant, A.apartment_compatible, A.fixed, A.surjective_fixed,
    A.special, A.facets, A.torus_units⟩

end Langlands.Geometry.Building
