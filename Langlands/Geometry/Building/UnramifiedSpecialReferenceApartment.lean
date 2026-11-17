import Langlands.Geometry.Building.SpecialTorusExistenceProof
import Langlands.Geometry.Building.IntegerValuationBuildingBasedTransport
import Langlands.Geometry.Building.ConjugateApartmentGaloisComparison
import Langlands.GroupScheme.Rational.SmoothMaximalSplitTorusConjugacyProof
import Langlands.GroupScheme.Rational.MinimalPseudoParabolicConjugacyAssembly

/-! # A genuine special reference apartment for a prescribed fixed building point -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.Geometry.Building

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (iT : T.toGrp ⟶ G)
  [Mono ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left]

local notation "K" => inertiaFixedField F
local notation "b" => algebraBaseMap F K
local notation "v" => MaximalUnramified.valuation F
local notation "T_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T
local notation "G_K" => baseChanged F K G
local notation "iT_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) iT

variable (D : KPApartmentData
  (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
  ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)
  (IntegerValuation.order (MaximalUnramified.valuation F)))
  (y : D.ReducedBuilding)

/-- A descended special reference apartment containing the given source torus,
with full V6, a canonically coefficient-fixed point above `y`, and a comparison
that preserves the same ambient rational-point action. -/
def SpecialReferenceRealization
    (S : CommGroupScheme (Spec (CommRingCat.of F))) (iS : S.toGrp ⟶ G) : Prop :=
  ∃ (T' : CommGroupScheme (Spec (CommRingCat.of F))) (j : T'.toGrp ⟶ G) (f : S ⟶ T'),
    CommGroupScheme.groupHom f ≫ j = iS ∧ IsClosedSubgroup j ∧
      ∃ hi' : IsMaximalSplitTorus
          (T := (CommGroupScheme.baseChange b).obj T')
          ((GroupScheme.baseChange b).map j),
        haveI := mono_of_isMaximalSplitTorus hi'
        ∃ (E : KPApartmentData (S := (CommGroupScheme.baseChange b).obj T')
              ((GroupScheme.baseChange b).map j) (IntegerValuation.order v))
          (C' : CentralizerDatum (S := (CommGroupScheme.baseChange b).obj T')
              ((GroupScheme.baseChange b).map j)),
          IntegerValuation.IsOmegaCompatible v E C' ∧
            ∃ (hE : KPApartmentData.GaloisStable F K j E) (q : E.ReducedBuilding)
              (r : E.ReducedBuilding ≃ D.ReducedBuilding),
              (∀ σ : K ≃ₐ[F] K, KPApartmentData.galoisQuotientAction F K j E hE σ q = q) ∧
                r q = y ∧ ∀ (g : rationalPoints G_K) (z : E.ReducedBuilding),
                  r (g • z) = g • r z

namespace KPApartmentData

/-- Put a prescribed maximal `F`-split torus into a genuine special reference
apartment, retaining the full centralizer compatibility and the prescribed
coefficient-fixed point through an equivariant quotient equivalence. -/
theorem specialReferenceRealization
    (hG : IsConnectedReductive G) (hiT : IsMaximalSplitTorus (T := T_K) iT_K)
    (C : CentralizerDatum (S := T_K) iT_K)
    (h6 : IntegerValuation.IsOmegaCompatible v D C)
    (hD : GaloisStable F K iT D)
    (hy : ∀ σ : K ≃ₐ[F] K, galoisQuotientAction F K iT D hD σ y = y)
    (S : CommGroupScheme (Spec (CommRingCat.of F))) (iS : S.toGrp ⟶ G)
    (hiS : IsMaximalSplitTorus iS) :
    SpecialReferenceRealization F G T iT D y S iS := by
  obtain ⟨T', j, f, hf, hj, hi'⟩ := specialTorusExistence F G hG S iS hiS
  let := mono_of_isMaximalSplitTorus hi'
  have hGK : IsConnectedReductive G_K :=
    connectedReductiveFieldExtensionStatement F K G hG
  let := hGK.isAffineHom
  let := hGK.smooth
  let := hGK.connectedSpace
  obtain ⟨g, e₀, he₀⟩ := smoothMaximalSplitTorusConjugacy K G_K T_K
    ((CommGroupScheme.baseChange b).obj T') iT_K ((GroupScheme.baseChange b).map j) hiT hi'
  let e := CommGroupScheme.isoOfGroupIso e₀
  have he : iT_K ≫ (GroupScheme.innerIso G_K g).hom =
      CommGroupScheme.groupHom e.hom ≫ (GroupScheme.baseChange b).map j := he₀
  let E := D.transport e (GroupScheme.innerIso G_K g) he
  let C' := C.basedTransport e (GroupScheme.innerIso G_K g) he
  have h6' : IntegerValuation.IsOmegaCompatible v E C' :=
    h6.transport_basedIso v C C' e (GroupScheme.innerIso G_K g) he
  let hE : GaloisStable F K j E :=
    galoisStable_transport_inner F K iT j e g he D hD
  obtain ⟨q, hq, hqfix⟩ :=
    exists_galoisFixed_conjugate_preimage F K iT j e g he D hD hE y hy
  exact ⟨T', j, f, hf, hj, hi', E, C', h6', hE, q,
    D.conjugateReducedBuildingEquiv e g he, hqfix, hq,
    D.conjugateReducedBuildingEquiv_smul e g he⟩

end KPApartmentData

/-- Every prescribed canonically coefficient-fixed point has a special reference
realization containing a maximal split torus over the original local field. -/
def UnramifiedSpecialReferenceApartmentStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (iT : T.toGrp ⟶ G),
    letI : IsAffineHom G.X.hom := hG.isAffineHom
    ∀ (hiT : IsMaximalSplitTorus
        (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
        ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)),
      haveI := mono_of_isMaximalSplitTorus hiT
      ∀ (D : KPApartmentData
          (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
          ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)
          (IntegerValuation.order (MaximalUnramified.valuation F)))
        (C : CentralizerDatum
          (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
          ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)),
        IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) D C →
        ∀ (hD : KPApartmentData.GaloisStable F (inertiaFixedField F) iT D)
          (y : D.ReducedBuilding),
          (∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
            KPApartmentData.galoisQuotientAction F (inertiaFixedField F) iT D hD σ y = y) →
          ∃ (S : CommGroupScheme (Spec (CommRingCat.of F))) (iS : S.toGrp ⟶ G),
            IsMaximalSplitTorus iS ∧ SpecialReferenceRealization F G T iT D y S iS

/-- Maximal split torus existence followed by the actual special-reference
construction, with no further geometric premise. -/
theorem unramifiedSpecialReferenceApartment :
    UnramifiedSpecialReferenceApartmentStatement.{u} := by
  intro F _ _ _ _ G hG T iT
  let := hG.isAffineHom
  intro hiT
  let := mono_of_isMaximalSplitTorus hiT
  intro D C h6 hD y hy
  let := hG.smooth
  obtain ⟨S, iS, hiS⟩ := exists_maximalSplitTorus G
  exact ⟨S, iS, hiS,
    KPApartmentData.specialReferenceRealization F G T iT D y hG hiT C h6 hD hy S iS hiS⟩

end Langlands.Geometry.Building
