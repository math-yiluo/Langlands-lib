import Langlands.Geometry.Building.UnramifiedSpecialApartmentStatement
import Langlands.Geometry.Building.RootValueTorusFieldRestriction
import Langlands.Geometry.Building.ValuationApartmentAxiomsExistenceStatement
import Langlands.Geometry.Building.QuasiSplitIntegerApartmentExistenceStatement
import Langlands.Geometry.Building.UnramifiedQuasiSplitReduction
import Langlands.GroupScheme.Rational.MinimalPseudoParabolicConjugacyAssembly
import Langlands.GroupScheme.Reductive.FieldExtensionProof
import Langlands.GroupScheme.Rational.RootRankOneFactorizationProof

/-! # Descent of the unramified valuation class and its apartment axioms -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

private instance unramifiedValuationDescentAffineHom {F : Type u} [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

/-- **Descent of the valuation of the root datum** (KP Construction 9.6.1, Lemma 9.6.3 and
Theorem 9.6.5). Let `K` be the maximal unramified extension of a nonarchimedean local field
`F`, `S` a maximal `F`-split torus of a connected reductive `F`-group `G`, and `T ⊇ S` an
`F`-torus with `T_K` a maximal `K`-split torus of `G_K`. Let `D` be an equipollence class of
valuations of the root datum of `(G_K, T_K)` satisfying V 6 for the order of `K`. Restricting
the `Aut(K/F)`-fixed points of `D` from `T_K` to `S` and then from `K` to `F` gives exactly
the members of an `N(F)`-stable equipollence class of valuations of the root datum of
`(G, S)`, which satisfies V 6 for `F`. -/
def UnramifiedValuationDescentStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (S : CommGroupScheme (Spec (CommRingCat.of F))) (iS : S.toGrp ⟶ G)
    (hiS : IsMaximalSplitTorus iS)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (iT : T.toGrp ⟶ G) (f : S ⟶ T),
    CommGroupScheme.groupHom f ≫ iT = iS →
    letI : IsAffineHom G.X.hom := hG.isAffineHom
    letI : Smooth G.X.hom := hG.smooth
    haveI := mono_of_isMaximalSplitTorus hiS
    ∀ (hiT : IsMaximalSplitTorus
        (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
        ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)),
      haveI := mono_of_isMaximalSplitTorus hiT
      haveI : Mono ((GroupScheme.baseChange
          (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left :=
        mono_of_isMaximalSplitTorus hiT
      ∀ (hE : RelativeRoot.HasOppositeFactorPairs
          (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
          ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
        (D : KPApartmentData
          (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
          ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)
          (IntegerValuation.order (MaximalUnramified.valuation F)))
        (C : CentralizerDatum
          (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
          ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)),
        IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) D C →
        let fixed : D.Apartment → Prop := fun x =>
          ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
            RootFunctionFamily.galoisAction F (inertiaFixedField F) T G σ x.val = x.val
        let φ : D.Apartment → RootFunctionFamily S G := fun x =>
          torusFieldRestrictedRootFunctionFamily (k := F) (K := inertiaFixedField F)
            hiS.isSplitSubtorus.1 hiT.isSplitSubtorus.1 hE
            (D.isRootDatumValuation_of_mem x.mem)
            ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f)
        ∃ (DS : KPApartmentData iS (localFieldOrder F)) (CS : CentralizerDatum iS),
          DS.IsOmegaCompatible CS ∧
          (∀ ψ : RootFunctionFamily S G, ψ ∈ DS.carrier ↔ ∃ x, fixed x ∧ ψ = φ x) ∧
          (∀ x y, fixed x → fixed y → φ x = φ y → x = y) ∧
          ∀ (n : normalizerPoints iS) (x : D.Apartment), fixed x →
            ∃ y, fixed y ∧
              D.apartmentMap y =
                (show rationalPoints ((GroupScheme.baseChange
                    (algebraBaseMap F (inertiaFixedField F))).obj G) from
                  rationalExtend F (inertiaFixedField F) G (n : rationalPoints G)) •
                  D.apartmentMap x ∧
              φ y = n • φ x

/-- **The apartment axioms for every compatible valuation class** (KP §9.5, Theorem 9.6.5
and §9.6.6, with the uniqueness of KP Proposition 6.2.6). For every connected reductive
group over a nonarchimedean local field, every `ValuationBuildingData` (a maximal split
torus, an `N(F)`-stable equipollence class of valuations of the root datum and the actual
centralizer, with V 6) satisfies V 7 and AS 2–AS 5. -/
def ValuationBuildingApartmentAxiomsStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (B : ValuationBuildingData G), B.SatisfiesApartmentAxioms

/-- The two new unramified-descent targets of this module. -/
def UnramifiedValuationDescentPackageStatement : Prop :=
  UnramifiedValuationDescentStatement.{u} ∧ ValuationBuildingApartmentAxiomsStatement.{u}

/-- The unramified-descent inputs suffice for KP Theorem 9.6.5 in the form of
`ValuationApartmentAxiomsExistenceStatement`. -/
def ValuationApartmentAxiomsExistenceReductionStatement : Prop :=
  UnramifiedQuasiSplitStatement.{u} →
  QuasiSplitIntegerApartmentExistenceStatement.{u} →
  SpecialTorusExistenceStatement.{u} →
  UnramifiedValuationDescentStatement.{u} →
  ValuationBuildingApartmentAxiomsStatement.{u} →
  ValuationApartmentAxiomsExistenceStatement.{u}

set_option maxHeartbeats 1600000 in
/-- Proof of the reduction: choose a maximal split torus and a special torus containing it,
take the quasi-split class over `K` with V 6, descend it, and apply the apartment axioms. -/
theorem valuationApartmentAxiomsExistenceReduction :
    ValuationApartmentAxiomsExistenceReductionStatement.{u} := by
  intro hQS hQSA hSpec hDesc hAx F _ _ _ _ G hG
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  obtain ⟨S, iS, hiS⟩ := exists_maximalSplitTorus G
  obtain ⟨T, iT, f, hf, -, hiT⟩ := hSpec F G hG S iS hiS
  have := mono_of_isMaximalSplitTorus hiS
  have := mono_of_isMaximalSplitTorus hiT
  have hGK : IsConnectedReductive (baseChanged F (inertiaFixedField F) G) :=
    connectedReductiveFieldExtensionStatement F (inertiaFixedField F) G hG
  have hqs : IsQuasiSplit (baseChanged F (inertiaFixedField F) G) :=
    hQS F (baseChanged F (inertiaFixedField F) G) hGK
  obtain ⟨D, C, h6⟩ := hQSA (inertiaFixedField F) (MaximalUnramified.valuation F)
    (MaximalUnramified.valuation_surjective F)
    (MaximalUnramified.valuationSubring_isHenselian F)
    (baseChanged F (inertiaFixedField F) G) hqs
    ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT) hiT
  have hE : RelativeRoot.HasOppositeFactorPairs
      (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
      ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT) :=
    (RelativeRoot.hasRankOneFactorization_iff_hasOppositeFactorPairs _
      hiT.isSplitSubtorus.1).mp
      (rootRankOneFactorization (inertiaFixedField F) (baseChanged F (inertiaFixedField F) G)
        hGK _ _ hiT)
  obtain ⟨DS, CS, h6S, -, -, -⟩ := hDesc F G hG S iS hiS T iT f hf hiT hE D C h6
  exact ⟨⟨hG, S, iS, hiS, DS, CS, h6S⟩, hAx F G _⟩

end Langlands.Geometry.Building
