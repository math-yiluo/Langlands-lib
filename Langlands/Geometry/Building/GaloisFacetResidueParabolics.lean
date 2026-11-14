import Langlands.Geometry.Building.GaloisIncidentFacets
import Langlands.BruhatTits.IntegralModels.IntegerFacetParabolicImages
import Langlands.GroupScheme.Descent.GaloisSubgroupTransport
import Langlands.GroupScheme.Absolute.ParabolicFieldExtensionProof
import Langlands.GroupScheme.Rational.ParabolicAmbientTransport
import Langlands.GroupScheme.Rational.MaximalLeviDynamicReduction
import Langlands.GroupScheme.Rational.NoProperParabolicSplitTorusContainment
import Langlands.GroupScheme.BaseChangeReflection

/-! # Rational residue parabolics at a maximal Gamma-facet -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 800000

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building.KPApartmentData

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G)

local notation "b" => algebraBaseMap k K
local notation "T_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T
local notation "G_K" => baseChanged k K G
local notation "i_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) i

private instance extendedAffine : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

variable [Mono (CategoryTheory.Functor.map
    (GroupScheme.baseChange (algebraBaseMap k K)) i).hom.hom.left]
  {v : Valuation K (WithZero (Multiplicative ℤ))}
  (D : KPApartmentData
    (S := CategoryTheory.Functor.obj (CommGroupScheme.baseChange (algebraBaseMap k K)) T)
    (CategoryTheory.Functor.map (GroupScheme.baseChange (algebraBaseMap k K)) i)
    (IntegerValuation.order v))
  (hD : GaloisStable k K i D)
  (hG : IsConnectedReductive (baseChanged k K G))
  (hi : IsMaximalSplitTorus
    (T := CategoryTheory.Functor.obj (CommGroupScheme.baseChange (algebraBaseMap k K)) T)
    (CategoryTheory.Functor.map (GroupScheme.baseChange (algebraBaseMap k K)) i))
  (C : CentralizerDatum
    (S := CategoryTheory.Functor.obj (CommGroupScheme.baseChange (algebraBaseMap k K)) T)
    (CategoryTheory.Functor.map (GroupScheme.baseChange (algebraBaseMap k K)) i))
  (h6 : IntegerValuation.IsOmegaCompatible v D C)

local notation "B" => integerBuildingData D hG hi C h6
local notation "rho" => galoisQuotientAction k K i D hD

include hG hi C h6


open Langlands.BruhatTits.IntegralModels


variable (R : Type u) [CommRing R] [IsDomain R] [Algebra R K] [IsFractionRing R K]
  [IsLocalRing R]
variable (E : GaloisFacet k K i D hD hG hi C h6)
variable (M : IntegerFacetModelData (K := K) (G := baseChanged k K G) (v := v)
  (integerBuildingData D hG hi C h6) R)
variable (Q : SpecialFibreQuotientData (R := R) (K := K) (G := baseChanged k K G)
  (M.model (K := K) (G := baseChanged k K G) (v := v) E.val))
variable (f : Type u) [Field f] [Algebra f (IsLocalRing.ResidueField R)]
variable (H : GroupScheme (Spec (CommRingCat.of f)))
variable (e : Q.quotient ≅ baseChanged f (IsLocalRing.ResidueField R) H)
variable
  (residueAction : (K ≃ₐ[k] K) →* (IsLocalRing.ResidueField R ≃ₐ[f] IsLocalRing.ResidueField R))

local notation "L" => IsLocalRing.ResidueField R
local notation "incAct" => galoisIncidentFacetAction k K i D hD hG hi C h6 E


/-- Transport the actual incident-facet image through the specified residue
quotient comparison. The image still uses all test schemes. -/
def residueFacetImage (F : (B).IncidentFacets E.val) :
    SubgroupFunctor (baseChanged f L H) :=
  (M.incidentParabolicImage (K := K) (G := baseChanged k K G) E.val Q F).comap e.inv

/-- The explicit coefficient compatibility still required of the supplied
actual models, their quotient comparison, and the residue coefficient action. -/
def HasGaloisResidueImageCompatibility : Prop :=
  ∀ (σ : K ≃ₐ[k] K) (F : (B).IncidentFacets E.val),
    residueFacetImage k K i D hD hG hi C h6 R E M Q f H e (incAct σ F) =
      SubgroupFunctor.galoisTransport f L H (residueAction σ)
        (residueFacetImage k K i D hD hG hi C h6 R E M Q f H e F)

private theorem residueFacetImage_injective
    (hbij : M.HasFacetParabolicOrderBijection (K := K) (G := baseChanged k K G) E.val Q) :
    Function.Injective (residueFacetImage k K i D hD hG hi C h6 R E M Q f H e) := by
  intro F F' h
  apply hbij.injective
  have hh := congrArg (fun P : SubgroupFunctor (baseChanged f L H) => P.comap e.hom) h
  simpa only [residueFacetImage, ← SubgroupFunctor.comap_comp,
    Iso.hom_inv_id, SubgroupFunctor.comap_id] using hh

/-- Under the actual facet-parabolic bijection and its coefficient
compatibility, maximality excludes every proper ground-residue parabolic.
Neither the models nor the two geometric compatibility inputs are constructed
by this implication. -/
theorem isIso_parabolic_of_maximalGaloisFacet
    (hunit : ∃ t : Kˣ, IntegerValuation.order v t = 1)
    (hmax : IsMaximalGaloisFacet k K i D hD hG hi C h6 E)
    (hQ : Q.IsReductiveQuotient (K := K) (G := baseChanged k K G)) (hH : IsConnectedReductive H)
    (hbij : M.HasFacetParabolicOrderBijection (K := K) (G := baseChanged k K G) E.val Q)
    (hcompat : HasGaloisResidueImageCompatibility k K i D hD hG hi C h6 R E M Q f H e
      residueAction)
    {P : GroupScheme (Spec (CommRingCat.of f))} (p : P ⟶ H)
    (hp : IsParabolicSubgroup p) : IsIso p := by
  let c := algebraBaseMap f L
  let pL := (GroupScheme.baseChange c).map p
  have hpL : IsParabolicSubgroup pL :=
    parabolicFieldExtensionStatement f L H hH P p hp
  have hpQ : IsParabolicSubgroup (pL ≫ e.inv) := hpL.comp_iso e.symm
  obtain ⟨F, hF⟩ := hbij.surjective (SubgroupFunctor.range (pL ≫ e.inv))
    ⟨_, _, hpQ, rfl⟩
  have hFimage : residueFacetImage k K i D hD hG hi C h6 R E M Q f H e F =
      SubgroupFunctor.range pL := by
    calc
      _ = (SubgroupFunctor.range (pL ≫ e.inv)).comap e.inv :=
        congrArg (fun A : SubgroupFunctor Q.quotient => A.comap e.inv) hF
      _ = _ := by
        simpa only [Iso.symm_hom, Iso.symm_inv, ← SubgroupFunctor.comap_comp,
          Iso.inv_hom_id, SubgroupFunctor.comap_id] using
          congrArg (fun A : SubgroupFunctor Q.quotient => A.comap e.inv)
            (SubgroupFunctor.range_comp_iso pL e.symm)
  have hfixed : ∀ σ : K ≃ₐ[k] K, incAct σ F = F := by
    intro σ
    apply residueFacetImage_injective k K i D hD hG hi C h6 R E M Q f H e hbij
    calc
      _ = SubgroupFunctor.galoisTransport f L H (residueAction σ)
          (residueFacetImage k K i D hD hG hi C h6 R E M Q f H e F) := hcompat σ F
      _ = SubgroupFunctor.galoisTransport f L H (residueAction σ)
          (SubgroupFunctor.range pL) :=
        congrArg (SubgroupFunctor.galoisTransport f L H (residueAction σ)) hFimage
      _ = SubgroupFunctor.range pL := by
        change SubgroupFunctor.descentTransport c (galoisBaseMap f L (residueAction σ))
          (galoisBaseMap_over f L (residueAction σ)) H (SubgroupFunctor.range pL) =
            SubgroupFunctor.range pL
        dsimp only [pL]
        rw [SubgroupFunctor.range_baseChangeHom]
        exact SubgroupFunctor.descentTransport_baseChange _ _ _ _ _
      _ = _ := hFimage.symm
  have hFE : F.val = E.val :=
    (isMaximalGaloisFacet_iff_no_other_fixed_incident k K i D hD hG hi C h6
      hunit E).mp hmax F hfixed
  have hFself : F = ⟨E.val, (B).facetPrecedes_refl E.val⟩ := Subtype.ext hFE
  have hfull : SubgroupFunctor.range pL = ⊤ := by
    calc
      _ = residueFacetImage k K i D hD hG hi C h6 R E M Q f H e F := hFimage.symm
      _ = residueFacetImage k K i D hD hG hi C h6 R E M Q f H e
          ⟨E.val, (B).facetPrecedes_refl E.val⟩ :=
        congrArg (residueFacetImage k K i D hD hG hi C h6 R E M Q f H e) hFself
      _ = ⊤ := by
        simpa only [residueFacetImage, SubgroupFunctor.comap_top] using
          congrArg (fun A : SubgroupFunctor Q.quotient => A.comap e.inv)
            (M.incidentParabolicImage_self (K := K) (G := baseChanged k K G) E.val Q hQ)
  have : IsClosedImmersion pL.hom.hom.left := hpL.isClosedSubgroup
  have : Mono pL.hom.hom := Over.mono_of_mono_left _
  have : IsIso pL := isIso_of_full_range pL inferInstance hfull
  have : Surjective c := (fieldExtension_fpqc f L).1
  have : Flat c := (fieldExtension_fpqc f L).2.1
  have : QuasiCompact c := (fieldExtension_fpqc f L).2.2
  exact isIso_of_baseChange c p

/-- The algebraic consequence for the prescribed maximal split torus of the
downstairs residue group: centrality and containment in every maximal torus. -/
theorem maximalSplitTorus_contained_of_maximalGaloisFacet
    (hunit : ∃ t : Kˣ, IntegerValuation.order v t = 1)
    (hmax : IsMaximalGaloisFacet k K i D hD hG hi C h6 E)
    (hQ : Q.IsReductiveQuotient (K := K) (G := baseChanged k K G)) (hH : IsConnectedReductive H)
    (hbij : M.HasFacetParabolicOrderBijection (K := K) (G := baseChanged k K G) E.val Q)
    (hcompat : HasGaloisResidueImageCompatibility k K i D hD hG hi C h6 R E M Q f H e
      residueAction)
    {S : CommGroupScheme (Spec (CommRingCat.of f))} {s : S.toGrp ⟶ H}
    (hs : IsMaximalSplitTorus s)
    {T' : CommGroupScheme (Spec (CommRingCat.of f))} {t : T'.toGrp ⟶ H}
    (ht : IsMaximalTorus t) :
    IsCentral s ∧ ∃ a : S ⟶ T', CommGroupScheme.groupHom a ≫ t = s ∧
      IsMaximalSplitTorus (CommGroupScheme.groupHom a) := by
  apply hs.exists_commFactor_of_noProperParabolic hH
  · intro P p hp
    exact isIso_parabolic_of_maximalGaloisFacet k K i D hD hG hi C h6 R E M Q f H e
      residueAction hunit hmax hQ hH hbij hcompat p hp
  · exact ht

/-- The conditional maximal-facet residue consequence on the actual supplied
models, quotient comparison, incident-facet bijection and coefficient maps. -/
def GaloisFacetResidueParabolicsStatement : Prop :=
  (∃ t : Kˣ, IntegerValuation.order v t = 1) →
    IsMaximalGaloisFacet k K i D hD hG hi C h6 E →
    Q.IsReductiveQuotient (K := K) (G := baseChanged k K G) →
    IsConnectedReductive H →
    M.HasFacetParabolicOrderBijection (K := K) (G := baseChanged k K G) E.val Q →
    HasGaloisResidueImageCompatibility k K i D hD hG hi C h6 R E M Q f H e residueAction →
    (∀ (P : GroupScheme (Spec (CommRingCat.of f))) (p : P ⟶ H),
      IsParabolicSubgroup p → IsIso p) ∧
    (∀ (S : CommGroupScheme (Spec (CommRingCat.of f))) (s : S.toGrp ⟶ H),
      IsMaximalSplitTorus s →
      ∀ (T' : CommGroupScheme (Spec (CommRingCat.of f))) (t : T'.toGrp ⟶ H),
        IsMaximalTorus t →
        IsCentral s ∧ ∃ a : S ⟶ T', CommGroupScheme.groupHom a ≫ t = s ∧
          IsMaximalSplitTorus (CommGroupScheme.groupHom a))

theorem galoisFacetResidueParabolics :
    GaloisFacetResidueParabolicsStatement k K i D hD hG hi C h6 R E M Q f H e
      residueAction := by
  intro hunit hmax hQ hH hbij hcompat
  constructor
  · intro P p hp
    exact isIso_parabolic_of_maximalGaloisFacet k K i D hD hG hi C h6 R E M Q f H e
      residueAction hunit hmax hQ hH hbij hcompat p hp
  · intro S s hs T' t ht
    exact maximalSplitTorus_contained_of_maximalGaloisFacet k K i D hD hG hi C h6 R E M Q
      f H e residueAction hunit hmax hQ hH hbij hcompat hs ht

end Langlands.Geometry.Building.KPApartmentData
