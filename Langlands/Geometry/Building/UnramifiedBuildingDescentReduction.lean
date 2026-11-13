import Langlands.Geometry.Building.UnramifiedBuildingDescentStatement
import Langlands.Geometry.Building.UnramifiedValuationDescentStatement
import Langlands.Geometry.Building.UnramifiedQuotientLift
import Langlands.Geometry.Building.GaloisApartmentQuotientAction
import Langlands.Geometry.Building.ChapterSevenBuildingAxiomsStatement
import Langlands.Geometry.Building.RootValuationBuildingConstructionReduction
import Langlands.BruhatTits.SpecialCompact.LeviApartmentComparison
import Langlands.Geometry.Building.UnramifiedOmegaGaloisStable
import Langlands.Geometry.Building.UnramifiedFiltrationSharpFixer

/-! # Reduction of unramified building descent to focused Kaletha–Prasad inputs -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

private instance unramifiedBuildingDescentReductionAffineHom {F : Type u} [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

/-- **The apartment embeds in the building over `K`** (KP Proposition 7.6.3 and
Remark 7.6.5, applied over the maximal unramified extension `K` of a nonarchimedean local
field `F`). For every supplied building datum over `K` with its integer-valued valuation
(a maximal `K`-split torus of a connected reductive `K`-group, an equipollence class of
valuations of its root datum with V 6, and the actual centralizer), the map from the
apartment to the reduced building is injective. -/
def MaximalUnramifiedApartmentInjectiveStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (H : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))) [IsAffineHom H.X.hom]
    (C : MaximalUnramified.BuildingData F H),
    Function.Injective C.apartmentMap

/-- **Galois-fixed points of the building over `K`** (KP §9.2.3, Theorem 9.2.7 and
Proposition 9.3.4 with §9.3). Let `K` be the maximal unramified extension of a
nonarchimedean local field `F`, `S` a maximal `F`-split torus of a connected reductive
`F`-group `G`, and `T ⊇ S` an `F`-torus with `T_K` a maximal `K`-split torus of `G_K`. Let
`D` be an equipollence class of valuations of the root datum of `(G_K, T_K)` satisfying V 6
for the order of `K`, and stable under `Aut(K/F)`. Every point of the reduced building of `D`
fixed by the coefficient action of every element of `Aut(K/F)` is a `G(F)`-translate of the
image of an `Aut(K/F)`-fixed point of the apartment of `D`. -/
def UnramifiedGaloisFixedBuildingPointStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (S : CommGroupScheme (Spec (CommRingCat.of F))) (iS : S.toGrp ⟶ G),
    IsMaximalSplitTorus iS →
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of F))) (iT : T.toGrp ⟶ G) (f : S ⟶ T),
    CommGroupScheme.groupHom f ≫ iT = iS →
    letI : IsAffineHom G.X.hom := hG.isAffineHom
    ∀ (hiT : IsMaximalSplitTorus
        (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
        ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)),
      haveI := mono_of_isMaximalSplitTorus hiT
      haveI : Mono ((GroupScheme.baseChange
          (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left :=
        mono_of_isMaximalSplitTorus hiT
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
          ∃ (g : rationalPoints G) (x : D.Apartment),
            (∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
              RootFunctionFamily.galoisAction F (inertiaFixedField F) T G σ x.val = x.val) ∧
            (show rationalPoints ((GroupScheme.baseChange
                (algebraBaseMap F (inertiaFixedField F))).obj G) from
              rationalExtend F (inertiaFixedField F) G g) • D.apartmentMap x = y

/-- **Special points descend** (KP Proposition 9.9.2). In the setting of
`UnramifiedValuationDescentStatement`, let `DS` be an equipollence class of valuations of the
root datum of `(G, S)` whose members are exactly the field restrictions `φ x` of the
`Aut(K/F)`-fixed points `x` of the apartment of `D`. If the image of such a fixed point `x` is
a special point of the reduced building of `D`, then the corresponding point of the apartment
of `DS` is special for the affine roots of `DS`. -/
def UnramifiedSpecialPointDescentStatement : Prop :=
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
        ∀ (DS : KPApartmentData iS (localFieldOrder F)),
          (∀ ψ : RootFunctionFamily S G, ψ ∈ DS.carrier ↔ ∃ x, fixed x ∧ ψ = φ x) →
          ∀ (x : D.Apartment) (w : DS.Apartment), fixed x → w.val = φ x →
            D.IsSpecialBuildingPoint (D.apartmentMap x) →
            AffineRootSystem.IsSpecialPoint DS.affineRoots w

/-- The six published inputs and the three focused statements of this module imply
`UnramifiedBuildingDescentStatement`. -/
def UnramifiedBuildingDescentReductionStatement : Prop :=
  UnramifiedQuasiSplitStatement.{u} →
  QuasiSplitIntegerApartmentExistenceStatement.{u} →
  SpecialTorusExistenceStatement.{u} →
  UnramifiedValuationDescentStatement.{u} →
  ValuationBuildingApartmentAxiomsStatement.{u} →
  ChapterSevenBuildingAxiomsStatement.{u} →
  MaximalUnramifiedApartmentInjectiveStatement.{u} →
  UnramifiedGaloisFixedBuildingPointStatement.{u} →
  UnramifiedSpecialPointDescentStatement.{u} →
  UnramifiedBuildingDescentStatement.{u}

namespace UnramifiedBuildingDescent

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} (iT : T.toGrp ⟶ G)

variable (hGK : IsConnectedReductive (baseChanged F (inertiaFixedField F) G))
  (hiT : IsMaximalSplitTorus
    (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
  [Mono ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left]
  (D : KPApartmentData
    (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)
    (IntegerValuation.order (MaximalUnramified.valuation F)))
  (C : CentralizerDatum
    (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
  (h6 : IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) D C)

/-- The building datum over `K` on the apartment class `D` of the scalar extension `T_K`. -/
abbrev buildingData : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G) where
  isConnectedReductive := hGK
  S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T
  i := (GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT
  isMaximalSplitTorus := hiT
  apartment := D
  centralizer := C
  isOmegaCompatible := h6

variable {D} (hD : KPApartmentData.GaloisStable F (inertiaFixedField F) iT D)

set_option maxHeartbeats 1000000 in
/-- The coefficient action of `Aut(K/F)` on a Galois-stable class, packaged as
`SemilinearApartmentData`. -/
def semilinearData :
    MaximalUnramified.SemilinearApartmentData (buildingData iT hGK hiT D C h6) where
  apartment := KPApartmentData.galoisAction F (inertiaFixedField F) iT D hD
  normalizer_mem σ n :=
    rationalConjugate_mem_normalizerPoints F (inertiaFixedField F) iT σ n.property
  normalizer_smul σ n x := by
    have hn : normalizerGaloisAction F (inertiaFixedField F) iT σ n =
        ⟨rationalConjugate F (inertiaFixedField F) G σ n.val,
          rationalConjugate_mem_normalizerPoints F (inertiaFixedField F) iT σ n.property⟩ :=
      Subtype.ext (normalizerGaloisAction_coe F (inertiaFixedField F) iT σ n)
    rw [← hn]
    exact KPApartmentData.galoisAction_normalizer_smul F (inertiaFixedField F) iT D hD σ n x
  root σ a := ⟨characterLattice.galoisRepresentation F (inertiaFixedField F) T σ a.val,
    (mem_roots_galois_iff F (inertiaFixedField F) iT σ a.val).2 a.property⟩
  filtration_mem σ x a g hg :=
    (KPApartmentData.rationalConjugate_mem_filtration_iff F (inertiaFixedField F) iT D hD σ x
      a.val 0 g).2 hg



set_option maxHeartbeats 1600000 in
/-- The quotient action of `semilinearData` is the existing coefficient action
`KPApartmentData.galoisQuotientAction` on the same quotient. -/
theorem semilinearData_action_apply (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
    (y : D.ReducedBuilding) :
    (semilinearData iT hGK hiT C h6 hD).action σ y =
      KPApartmentData.galoisQuotientAction F (inertiaFixedField F) iT D hD σ y := by
  obtain ⟨g, x, rfl⟩ := D.exists_smul_apartmentMap y
  rw [KPApartmentData.galoisQuotientAction_smul, KPApartmentData.galoisQuotientAction_apartmentMap]
  exact ((semilinearData iT hGK hiT C h6 hD).action_smul σ g (D.apartmentMap x)).trans
    (congrArg _ ((semilinearData iT hGK hiT C h6 hD).action_apartmentMap σ x))

section Core

variable {iT} (B : ValuationBuildingData G)
  (fixed : D.Apartment → Prop) (φ : D.Apartment → RootFunctionFamily B.S G)
  (hcar : ∀ ψ : RootFunctionFamily B.S G, ψ ∈ B.apartment.carrier ↔ ∃ x, fixed x ∧ ψ = φ x)

set_option maxHeartbeats 800000 in
/-- A fixed apartment point over `K` whose restriction is the given point of `A(S)`. -/
def descentPoint (w : B.Apartment) : D.Apartment :=
  Classical.choose ((hcar w.val).1 w.mem)

set_option maxHeartbeats 800000 in
theorem descentPoint_fixed (w : B.Apartment) : fixed (descentPoint B fixed φ hcar w) :=
  (Classical.choose_spec ((hcar w.val).1 w.mem)).1

set_option maxHeartbeats 800000 in
theorem descentPoint_val (w : B.Apartment) : w.val = φ (descentPoint B fixed φ hcar w) :=
  (Classical.choose_spec ((hcar w.val).1 w.mem)).2

set_option maxHeartbeats 800000 in
theorem descentPoint_injective : Function.Injective (descentPoint B fixed φ hcar) :=
  fun w w' h => KPApartmentData.Apartment.ext (by
    rw [descentPoint_val B fixed φ hcar w, descentPoint_val B fixed φ hcar w', h])

variable (hinj : ∀ x y, fixed x → fixed y → φ x = φ y → x = y)

set_option maxHeartbeats 800000 in
include hinj in
theorem descentPoint_eq {x : D.Apartment} (hx : fixed x) (w : B.Apartment) (hw : w.val = φ x) :
    descentPoint B fixed φ hcar w = x :=
  hinj _ _ (descentPoint_fixed B fixed φ hcar w) hx
    ((descentPoint_val B fixed φ hcar w).symm.trans hw)

variable (hnorm : ∀ (n : normalizerPoints B.i) (x : D.Apartment), fixed x →
      ∃ y, fixed y ∧
        D.apartmentMap y =
          (show rationalPoints ((GroupScheme.baseChange
            (algebraBaseMap F (inertiaFixedField F))).obj G) from
          rationalExtend F (inertiaFixedField F) G (n : rationalPoints G)) • D.apartmentMap x ∧
        φ y = n • φ x)

set_option maxHeartbeats 800000 in
include hinj hnorm in
theorem descentPoint_normalizer (n : normalizerPoints B.i) (w : B.Apartment) :
    D.apartmentMap (descentPoint B fixed φ hcar (n • w)) =
      (show rationalPoints ((GroupScheme.baseChange
            (algebraBaseMap F (inertiaFixedField F))).obj G) from
          rationalExtend F (inertiaFixedField F) G (n : rationalPoints G)) •
        D.apartmentMap (descentPoint B fixed φ hcar w) := by
  obtain ⟨y, hy, hyD, hyφ⟩ := hnorm n _ (descentPoint_fixed B fixed φ hcar w)
  rw [descentPoint_eq B fixed φ hcar hinj hy (n • w)
    (by rw [KPApartmentData.val_smul, descentPoint_val B fixed φ hcar w, hyφ])]
  exact hyD

set_option maxHeartbeats 800000 in
include hinj hnorm in
theorem descentPoint_normalizer' (n : normalizerPoints B.i) (w : B.Apartment) :
    (buildingData iT hGK hiT D C h6).apartmentMap (descentPoint B fixed φ hcar (n • w)) =
      rationalExtend F (UnramifiedClosure F) G (n : rationalPoints G) •
        (buildingData iT hGK hiT D C h6).apartmentMap (descentPoint B fixed φ hcar w) :=
  descentPoint_normalizer B fixed φ hcar hinj hnorm n w

variable (hfilt : ∀ (x : D.Apartment) (w : B.Apartment), w.val = φ x →
      ∀ a : relativeRoots B.i,
        B.filtration w a 0 ≤ (D.sharpFixer {x}).comap (rationalExtend F (inertiaFixedField F) G))

set_option maxHeartbeats 800000 in
include hfilt in
theorem descentPoint_sharpFixer (w : B.Apartment) :
    B.sharpFixer {w} ≤
      ((buildingData iT hGK hiT D C h6).fixer
        ((buildingData iT hGK hiT D C h6).apartmentMap (descentPoint B fixed φ hcar w))).comap
        (rationalExtend F (UnramifiedClosure F) G) := by
  apply MaximalUnramified.sharpFixer_le_comap_of_rootFiltration
  intro a
  exact (hfilt _ w (descentPoint_val B fixed φ hcar w) a).trans
    (Subgroup.comap_mono (D.sharpFixer_le_reducedFixer _))

set_option maxHeartbeats 800000 in
/-- The scalar-extension map of reduced buildings, from the published quotient lift. -/
def descentMap : B.ReducedBuilding → (buildingData iT hGK hiT D C h6).ReducedBuilding :=
  MaximalUnramified.quotientLift B (buildingData iT hGK hiT D C h6) (descentPoint B fixed φ hcar)
    (descentPoint_normalizer' hGK hiT C h6 B fixed φ hcar hinj hnorm)
    (descentPoint_sharpFixer hGK hiT C h6 B fixed φ hcar hfilt)

set_option maxHeartbeats 800000 in
theorem descentMap_smul (g : rationalPoints G) (z : B.ReducedBuilding) :
    descentMap hGK hiT C h6 B fixed φ hcar hinj hnorm hfilt (g • z) =
      rationalExtend F (inertiaFixedField F) G g •
        descentMap hGK hiT C h6 B fixed φ hcar hinj hnorm hfilt z :=
  MaximalUnramified.quotientLift_smul B _ _ _ _ g z

set_option maxHeartbeats 800000 in
theorem descentMap_apartment (w : B.Apartment) :
    descentMap hGK hiT C h6 B fixed φ hcar hinj hnorm hfilt (B.apartmentMap w) =
      (buildingData iT hGK hiT D C h6).apartmentMap (descentPoint B fixed φ hcar w) :=
  MaximalUnramified.quotientLift_apartment B _ _ _ _ w

set_option maxHeartbeats 800000 in
theorem descentMap_injective (hK : Function.Injective D.apartmentMap)
    (hB : ∃ R : B.PolysimplicialRealization, B.SatisfiesBuildingAxiom R) :
    Function.Injective (descentMap hGK hiT C h6 B fixed φ hcar hinj hnorm hfilt) := by
  obtain ⟨R, hR⟩ := hB
  exact MaximalUnramified.quotientLift_injective B _ _ _ _ hR
    (descentPoint_injective B fixed φ hcar) hK

set_option maxHeartbeats 800000 in
theorem descentMap_surjective_fixed
    (hfixpt : ∀ y : D.ReducedBuilding,
      (∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
        KPApartmentData.galoisQuotientAction F (inertiaFixedField F) iT D hD σ y = y) →
      ∃ (g : rationalPoints G) (x : D.Apartment), fixed x ∧
        (show rationalPoints ((GroupScheme.baseChange
          (algebraBaseMap F (inertiaFixedField F))).obj G) from
          rationalExtend F (inertiaFixedField F) G g) • D.apartmentMap x = y)
    (y : (buildingData iT hGK hiT D C h6).ReducedBuilding)
    (hy : ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
      (semilinearData iT hGK hiT C h6 hD).action σ y = y) :
    ∃ z : B.ReducedBuilding, descentMap hGK hiT C h6 B fixed φ hcar hinj hnorm hfilt z = y := by
  obtain ⟨g, x, hx, rfl⟩ := hfixpt y fun σ =>
    (semilinearData_action_apply iT hGK hiT C h6 hD σ y).symm.trans (hy σ)
  refine ⟨g • B.apartmentMap ⟨φ x, (hcar (φ x)).2 ⟨x, hx, rfl⟩⟩, ?_⟩
  rw [descentMap_smul, descentMap_apartment, descentPoint_eq B fixed φ hcar hinj hx _ rfl]

set_option maxHeartbeats 800000 in
theorem descentMap_isSpecialPoint
    (hspec : ∀ (x : D.Apartment) (w : B.Apartment), fixed x → w.val = φ x →
      D.IsSpecialBuildingPoint (D.apartmentMap x) →
      AffineRootSystem.IsSpecialPoint B.affineRoots w)
    (z : B.ReducedBuilding)
    (hz : (buildingData iT hGK hiT D C h6).IsSpecialPoint
      (descentMap hGK hiT C h6 B fixed φ hcar hinj hnorm hfilt z)) :
    B.IsSpecialPoint z := by
  obtain ⟨g, w, rfl⟩ := B.exists_smul_apartmentMap z
  rw [descentMap_smul, descentMap_apartment] at hz
  have h1 : D.IsSpecialBuildingPoint (D.apartmentMap (descentPoint B fixed φ hcar w)) := by
    have h := KPApartmentData.IsSpecialBuildingPoint.smul _ hz
      (rationalExtend F (inertiaFixedField F) G g)⁻¹
    rwa [inv_smul_smul] at h
  exact KPApartmentData.IsSpecialBuildingPoint.smul _
    (B.apartment.isSpecialBuildingPoint_apartmentMap
      (hspec _ w (descentPoint_fixed B fixed φ hcar w) (descentPoint_val B fixed φ hcar w) h1)) g

set_option maxHeartbeats 800000 in
include hGK hiT C h6 hcar hinj hnorm hfilt in
/-- **Core of the reduction.** From an apartment class `D` over `K` whose `Aut(K/F)`-fixed
points restrict (through `φ`) exactly onto the apartment of `B`, with normalizer
compatibility, root-filtration comparison, injectivity of the upstairs apartment map,
common apartments for `B`, Galois-fixed points coming from fixed apartment points, and
descent of special points, the four conclusions of `UnramifiedBuildingDescentStatement`
hold for `B`. -/
theorem exists_descent (hK : Function.Injective D.apartmentMap)
    (hB : ∃ R : B.PolysimplicialRealization, B.SatisfiesBuildingAxiom R)
    (hfixpt : ∀ y : D.ReducedBuilding,
      (∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
        KPApartmentData.galoisQuotientAction F (inertiaFixedField F) iT D hD σ y = y) →
      ∃ (g : rationalPoints G) (x : D.Apartment), fixed x ∧
        (show rationalPoints ((GroupScheme.baseChange
          (algebraBaseMap F (inertiaFixedField F))).obj G) from
          rationalExtend F (inertiaFixedField F) G g) • D.apartmentMap x = y)
    (hspec : ∀ (x : D.Apartment) (w : B.Apartment), fixed x → w.val = φ x →
      D.IsSpecialBuildingPoint (D.apartmentMap x) →
      AffineRootSystem.IsSpecialPoint B.affineRoots w) :
    ∃ (C' : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G))
      (D' : MaximalUnramified.SemilinearApartmentData C')
      (e : B.ReducedBuilding → C'.ReducedBuilding),
      Function.Injective e ∧
      (∀ (g : rationalPoints G) (z : B.ReducedBuilding),
        e (g • z) = rationalExtend F (inertiaFixedField F) G g • e z) ∧
      (∀ y : C'.ReducedBuilding,
        (∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F, D'.action σ y = y) →
          ∃ z : B.ReducedBuilding, e z = y) ∧
      ∀ z : B.ReducedBuilding, C'.IsSpecialPoint (e z) → B.IsSpecialPoint z :=
  ⟨buildingData iT hGK hiT D C h6, semilinearData iT hGK hiT C h6 hD,
    descentMap hGK hiT C h6 B fixed φ hcar hinj hnorm hfilt,
    descentMap_injective hGK hiT C h6 B fixed φ hcar hinj hnorm hfilt hK hB,
    descentMap_smul hGK hiT C h6 B fixed φ hcar hinj hnorm hfilt,
    descentMap_surjective_fixed hGK hiT C h6 hD B fixed φ hcar hinj hnorm hfilt hfixpt,
    descentMap_isSpecialPoint hGK hiT C h6 B fixed φ hcar hinj hnorm hfilt hspec⟩

end Core

end UnramifiedBuildingDescent

namespace UnramifiedBuildingDescent

/-- The building axiom for an arbitrary `B`, from the apartment axioms and the Chapter 7
building axioms of its parahoric extension. -/
theorem exists_satisfiesBuildingAxiom (hAx : ValuationBuildingApartmentAxiomsStatement.{u})
    (hCh7 : ChapterSevenBuildingAxiomsStatement.{u})
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (B : ValuationBuildingData G) :
    ∃ R : B.PolysimplicialRealization, B.SatisfiesBuildingAxiom R := by
  obtain ⟨P, rfl⟩ := ParahoricBuildingData.exists_toValuationBuildingData_eq B
  obtain ⟨R, -, hR, -⟩ := hCh7 F G P (hAx F G P.toValuationBuildingData)
  exact ⟨R, hR⟩

set_option maxHeartbeats 1600000 in
/-- The quasi-split compatible class over `K` on the scalar extension of `T`. -/
theorem exists_omegaCompatible (hQS : UnramifiedQuasiSplitStatement.{u})
    (hQSA : QuasiSplitIntegerApartmentExistenceStatement.{u})
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of F))} (iT : T.toGrp ⟶ G)
    [Mono ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left]
    (hGK : IsConnectedReductive (baseChanged F (inertiaFixedField F) G))
    (hiT : IsMaximalSplitTorus
      (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
      ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)) :
    ∃ (D : KPApartmentData
        (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
        ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)
        (IntegerValuation.order (MaximalUnramified.valuation F)))
      (C : CentralizerDatum
        (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
        ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)),
      IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) D C :=
  hQSA (inertiaFixedField F) (MaximalUnramified.valuation F)
    (MaximalUnramified.valuation_surjective F)
    (MaximalUnramified.valuationSubring_isHenselian F)
    (baseChanged F (inertiaFixedField F) G) (hQS F (baseChanged F (inertiaFixedField F) G) hGK)
    ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT) hiT

end UnramifiedBuildingDescent

open UnramifiedBuildingDescent in
set_option maxHeartbeats 4000000 in
/-- Proof of the reduction: take a special torus `T ⊇ S` for the maximal split torus `S` of
`B`, the quasi-split compatible class `D` over `K` on `T_K`, which is Galois stable, and descend
it; the descended class is the apartment class of `B` by uniqueness, and the core lemma
`UnramifiedBuildingDescent.exists_descent` assembles the four conclusions. -/
theorem unramifiedBuildingDescentReduction :
    UnramifiedBuildingDescentReductionStatement.{u} := by
  intro hQS hQSA hSpec hDesc hAx hCh7 hInjK hFix hSpecial F _ _ _ _ G hG
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  intro B
  obtain ⟨T, iT, f, hf, hiTc, hiT⟩ := hSpec F G hG B.S B.i B.isMaximalSplitTorus
  have := mono_of_isMaximalSplitTorus hiT
  have hGK : IsConnectedReductive (baseChanged F (inertiaFixedField F) G) :=
    connectedReductiveFieldExtensionStatement F (inertiaFixedField F) G hG
  obtain ⟨D, C, h6⟩ := exists_omegaCompatible hQS hQSA iT hGK hiT
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
  refine exists_descent (hGK := hGK) (hiT := hiT) (C := C) (h6 := h6) (hD := hD) (B := B)
    (fixed := fun x => ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
      RootFunctionFamily.galoisAction F (inertiaFixedField F) T G σ x.val = x.val)
    (φ := fun x => torusFieldRestrictedRootFunctionFamily (k := F) (K := inertiaFixedField F)
      B.isMaximalSplitTorus.isSplitSubtorus.1 hiT.isSplitSubtorus.1 hE
      (D.isRootDatumValuation_of_mem x.mem)
      ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f))
    (hcar := ?_) (hinj := ?_) (hnorm := ?_) (hfilt := ?_) (hK := ?_) (hB := ?_)
    (hfixpt := ?_) (hspec := ?_)
  · exact hcar
  · exact hinj
  · exact hnorm
  · exact fun x w hw a => filtration_le_comap_sharpFixer_of_torusFieldRestriction f hf
      B.isMaximalSplitTorus.isSplitSubtorus.1 hiT.isSplitSubtorus.1 hE D x B.apartment w hw a
  · exact hInjK F (baseChanged F (inertiaFixedField F) G) (buildingData iT hGK hiT D C h6)
  · exact exists_satisfiesBuildingAxiom hAx hCh7 B
  · exact hFix F G hG B.S B.i B.isMaximalSplitTorus T iT f hf hiT D C h6 hD
  · exact hSpecial F G hG B.S B.i B.isMaximalSplitTorus T iT f hf hiT hE D C h6 B.apartment hcar

end Langlands.Geometry.Building
