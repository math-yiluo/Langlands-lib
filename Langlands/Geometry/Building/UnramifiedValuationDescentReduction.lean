import Langlands.Geometry.Building.UnramifiedFixedLocusStatement
import Langlands.Geometry.Building.UnramifiedFixedNormalizerTransportReduction
import Langlands.Geometry.Building.UnramifiedSpecialApartmentStatement
import Langlands.Geometry.Building.UnramifiedApartmentGaloisStability
import Langlands.Geometry.Building.UnramifiedApartmentDescentTorsor
import Langlands.Geometry.Building.QuasiSplitApartmentShifts
import Langlands.Geometry.Building.MaximalUnramifiedRootRestriction
import Langlands.Geometry.Building.CentralizerDatumConstruction
import Langlands.Geometry.Building.SplitChevalleyApartment
import Langlands.BruhatTits.Cartan.CentralizerValuationComparisonProof
import Langlands.GroupScheme.Torus.LatticeBaseInvariants

/-! # Reduction of the unramified valuation descent to the Galois-fixed locus -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

section DescentTranslations

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] [Smooth G.X.hom]
  (i : S.toGrp ⟶ G) [Mono i.hom.hom.left] (t : S ⟶ T) (jT : T.toGrp ⟶ G)

local notation "b" => algebraBaseMap k K
local notation "T_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T
local notation "G_K" => baseChanged k K G
local notation "i_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) i
local notation "j_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) jT
local notation "t_K" => CategoryTheory.Functor.map (CommGroupScheme.baseChange b) t

private instance descentExtendedAffine : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

private instance descentExtendedSmooth : Smooth (G_K).X.hom := by
  change Smooth (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

/-- Pushed-forward real cocharacters of the original split torus are fixed by the actual
coefficient action. -/
theorem galoisCocharacterAction_descentCocharacterMap (hS : IsSplitTorus S.toGrp)
    (σ : K ≃ₐ[k] K) (v : V S) :
    galoisCocharacterAction k K T σ (descentCocharacterMap k K t hS v) =
      descentCocharacterMap k K t hS v := by
  induction v using TensorProduct.inductionOn with
  | tmul r ξ =>
    rw [descentCocharacterMap_tmul, galoisCocharacterAction_tmul,
      ← cocharacterLattice.baseChange_comp, cocharacterLattice.galoisRepresentation_baseChange]
  | add v w hv hw => simp only [map_add, hv, hw]

variable [Mono (CategoryTheory.Functor.map
    (GroupScheme.baseChange (algebraBaseMap k K)) jT).hom.hom.left]

/-- Torus-then-field restriction carries translation by a pushed-forward original real
cocharacter `v` to translation by `v`. -/
theorem torusFieldRestrictedRootFunctionFamily_descent_vadd (hS : IsSplitTorus S.toGrp)
    (hT : IsSplitTorus (T_K).toGrp) (hE : RelativeRoot.HasOppositeFactorPairs (T := T_K) j_K)
    {φ ψ : RootFunctionFamily T_K G_K} (hφ : IsRootDatumValuation (S := T_K) j_K φ)
    (hψ : IsRootDatumValuation (S := T_K) j_K ψ) (v : V S)
    (h : ψ = descentCocharacterMap k K t hS v +ᵥ φ) :
    torusFieldRestrictedRootFunctionFamily (G := G) (T := T_K) (j := j_K) hS hT hE hψ t_K =
      v +ᵥ torusFieldRestrictedRootFunctionFamily (G := G) (T := T_K) (j := j_K) hS hT hE hφ
        t_K := by
  have h1 := torusRestrictedRootFunctionFamily_congr (hS.baseChange b) hT hE h hψ
    (hφ.vadd (cocharacterMapReal t_K (splitCocharacterBaseChange (K := K) S hS v))) t_K
  have h2 := torusRestrictedRootFunctionFamily_vadd (hS.baseChange b) hT hE hφ t_K
    (splitCocharacterBaseChange (K := K) S hS v)
  change RootFunctionFamily.fieldRestrict (k := k) (K := K) (S := S) (G := G)
      (torusRestrictedRootFunctionFamily (T := T_K) (i := j_K) (hS.baseChange b) hT hE hψ t_K) =
    v +ᵥ RootFunctionFamily.fieldRestrict (k := k) (K := K) (S := S) (G := G)
      (torusRestrictedRootFunctionFamily (T := T_K) (i := j_K) (hS.baseChange b) hT hE hφ t_K)
  rw [h1, h2, RootFunctionFamily.fieldRestrict_vadd hS]

end DescentTranslations

private instance unramifiedDescentReductionAffineHom {F : Type u} [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

set_option maxHeartbeats 1600000 in
/-- **The descent from the fixed-locus inputs, for fixed data.** For the data of
`UnramifiedValuationDescentStatement`, a Galois-fixed point (`hfix`), the `N(F)`-transport
of Galois-fixed points (`hB`), V 6 on `Z(F)` (`hC`) and V 5 (`hD`) at the Galois-fixed points
give the conclusion of
`UnramifiedValuationDescentStatement`. All binders and hypotheses are stated explicitly. -/
theorem unramifiedValuationDescent_core
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    [IsAffineHom G.X.hom] [Smooth G.X.hom]
    (S : CommGroupScheme (Spec (CommRingCat.of F))) (iS : S.toGrp ⟶ G)
    (hiS : IsMaximalSplitTorus iS) [Mono iS.hom.hom.left]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (iT : T.toGrp ⟶ G) (f : S ⟶ T)
    (hf : CommGroupScheme.groupHom f ≫ iT = iS)
    (hiT : IsMaximalSplitTorus (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T) ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
    [Mono ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left]
    (hE : RelativeRoot.HasOppositeFactorPairs (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T) ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
    (D : KPApartmentData (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T) ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)
      (IntegerValuation.order (MaximalUnramified.valuation F)))
    (hfix : ∃ x : D.Apartment, ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
        RootFunctionFamily.galoisAction F (inertiaFixedField F) T G σ x.val = x.val)
    (hB : ∀ (n : normalizerPoints iS) (x : D.Apartment), (∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
        RootFunctionFamily.galoisAction F (inertiaFixedField F) T G σ x.val = x.val) →
      ∃ y : D.Apartment, (∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
        RootFunctionFamily.galoisAction F (inertiaFixedField F) T G σ y.val = y.val) ∧
        D.apartmentMap y = (show rationalPoints ((GroupScheme.baseChange
            (algebraBaseMap F (inertiaFixedField F))).obj G) from
          rationalExtend F (inertiaFixedField F) G (n : rationalPoints G)) • D.apartmentMap x ∧
        torusFieldRestrictedRootFunctionFamily (k := F) (K := inertiaFixedField F)
          hiS.isSplitSubtorus.1 hiT.isSplitSubtorus.1 hE (D.isRootDatumValuation_of_mem y.mem)
          ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f) =
          n • torusFieldRestrictedRootFunctionFamily (k := F) (K := inertiaFixedField F)
            hiS.isSplitSubtorus.1 hiT.isSplitSubtorus.1 hE (D.isRootDatumValuation_of_mem x.mem)
            ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f))
    (hC : ∀ (CS : CentralizerDatum iS) (x : D.Apartment), (∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
        RootFunctionFamily.galoisAction F (inertiaFixedField F) T G σ x.val = x.val) →
      IsCentralizerCompatible iS CS.j CS.s CS.bijective
        (torusFieldRestrictedRootFunctionFamily (k := F) (K := inertiaFixedField F)
          hiS.isSplitSubtorus.1 hiT.isSplitSubtorus.1 hE (D.isRootDatumValuation_of_mem x.mem)
          ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f)))
    (hD : ∀ x : D.Apartment, (∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
        RootFunctionFamily.galoisAction F (inertiaFixedField F) T G σ x.val = x.val) →
      ∀ a ∈ relativeRoots iS, ∀ g ∈ rootGroupPoints iS a, g ≠ 1 →
        ∀ g' ∈ rootGroupPoints iS (-a), ∀ g'' ∈ rootGroupPoints iS (-a),
          g' * g * g'' ∈ normalizerPoints iS →
            torusFieldRestrictedRootFunctionFamily (k := F) (K := inertiaFixedField F)
              hiS.isSplitSubtorus.1 hiT.isSplitSubtorus.1 hE (D.isRootDatumValuation_of_mem x.mem)
              ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f) (-a) g' +
              torusFieldRestrictedRootFunctionFamily (k := F) (K := inertiaFixedField F)
                hiS.isSplitSubtorus.1 hiT.isSplitSubtorus.1 hE (D.isRootDatumValuation_of_mem x.mem)
                ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f) a g = 0) :
    ∃ (DS : KPApartmentData iS (localFieldOrder F)) (CS : CentralizerDatum iS),
      DS.IsOmegaCompatible CS ∧
      (∀ ψ : RootFunctionFamily S G, ψ ∈ DS.carrier ↔
        ∃ x : D.Apartment, (∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
          RootFunctionFamily.galoisAction F (inertiaFixedField F) T G σ x.val = x.val) ∧
          ψ = torusFieldRestrictedRootFunctionFamily (k := F) (K := inertiaFixedField F)
            hiS.isSplitSubtorus.1 hiT.isSplitSubtorus.1 hE (D.isRootDatumValuation_of_mem x.mem)
            ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f)) ∧
      (∀ x y : D.Apartment, (∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
          RootFunctionFamily.galoisAction F (inertiaFixedField F) T G σ x.val = x.val) → (∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
          RootFunctionFamily.galoisAction F (inertiaFixedField F) T G σ y.val = y.val) →
        torusFieldRestrictedRootFunctionFamily (k := F) (K := inertiaFixedField F)
          hiS.isSplitSubtorus.1 hiT.isSplitSubtorus.1 hE (D.isRootDatumValuation_of_mem x.mem)
          ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f) =
          torusFieldRestrictedRootFunctionFamily (k := F) (K := inertiaFixedField F)
            hiS.isSplitSubtorus.1 hiT.isSplitSubtorus.1 hE (D.isRootDatumValuation_of_mem y.mem)
            ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f) → x = y) ∧
      ∀ (n : normalizerPoints iS) (x : D.Apartment), (∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
          RootFunctionFamily.galoisAction F (inertiaFixedField F) T G σ x.val = x.val) →
        ∃ y : D.Apartment, (∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
            RootFunctionFamily.galoisAction F (inertiaFixedField F) T G σ y.val = y.val) ∧
          D.apartmentMap y = (show rationalPoints ((GroupScheme.baseChange
            (algebraBaseMap F (inertiaFixedField F))).obj G) from
          rationalExtend F (inertiaFixedField F) G (n : rationalPoints G)) • D.apartmentMap x ∧
          torusFieldRestrictedRootFunctionFamily (k := F) (K := inertiaFixedField F)
            hiS.isSplitSubtorus.1 hiT.isSplitSubtorus.1 hE (D.isRootDatumValuation_of_mem y.mem)
            ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f) =
            n • torusFieldRestrictedRootFunctionFamily (k := F) (K := inertiaFixedField F)
              hiS.isSplitSubtorus.1 hiT.isSplitSubtorus.1 hE (D.isRootDatumValuation_of_mem x.mem)
              ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f) := by
  have hS : IsSplitTorus S.toGrp := hiS.isSplitSubtorus.1
  have hTK := hiT.isSplitSubtorus.1
  have hfactor : CommGroupScheme.groupHom ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f) ≫ (GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT =
      (GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iS := by
    rw [← hf, Functor.map_comp]
    rfl
  have hEbase : RelativeRoot.HasOppositeFactorPairs iS :=
    (RelativeRoot.hasRankOneFactorization_iff_hasOppositeFactorPairs iS hS).mp
      (rootRankOneFactorization F G hG S iS hiS)
  obtain ⟨x0, hx0⟩ := hfix
  -- restriction intertwines the pushed-forward translations
  have hφvadd : ∀ (x y : D.Apartment) (v : V S),
      y.val = descentCocharacterMap F (inertiaFixedField F) f hS v +ᵥ x.val →
        torusFieldRestrictedRootFunctionFamily (k := F) (K := inertiaFixedField F)
          hiS.isSplitSubtorus.1 hiT.isSplitSubtorus.1 hE (D.isRootDatumValuation_of_mem y.mem)
          ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f) =
          v +ᵥ torusFieldRestrictedRootFunctionFamily (k := F) (K := inertiaFixedField F)
            hiS.isSplitSubtorus.1 hiT.isSplitSubtorus.1 hE (D.isRootDatumValuation_of_mem x.mem)
            ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f) := by
    intro x y v h
    exact torusFieldRestrictedRootFunctionFamily_descent_vadd (K := inertiaFixedField F) f iT hS
      hTK hE x.isValuation y.isValuation v h
  -- the original-point normalizer shifts
  have hshift : ∀ n : normalizerPoints iS, ∃ v : V S,
      n • torusFieldRestrictedRootFunctionFamily (k := F) (K := inertiaFixedField F)
          hiS.isSplitSubtorus.1 hiT.isSplitSubtorus.1 hE (D.isRootDatumValuation_of_mem x0.mem)
          ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f) =
        v +ᵥ torusFieldRestrictedRootFunctionFamily (k := F) (K := inertiaFixedField F)
            hiS.isSplitSubtorus.1 hiT.isSplitSubtorus.1 hE (D.isRootDatumValuation_of_mem x0.mem)
            ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f) := by
    intro n
    obtain ⟨y, hy⟩ := hB n x0 hx0
    obtain ⟨v, hv⟩ :=
      unramified_exists_descent_vadd_of_galoisFixed hG hiS hf hiT D x0 y hx0 hy.1
    exact ⟨v, hy.2.2.symm.trans (hφvadd x0 y v hv)⟩
  let ψ := torusFieldRestrictedValuationOfOriginalPointShifts (K := inertiaFixedField F)
    (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T) iS hS hTK hE x0.isValuation ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f) hfactor
    hEbase (MaximalUnramified.realOrderCharacter F) x0.isSplitTorusCompatible
    (MaximalUnramified.realOrderCharacter_nontrivial_on_base F)
    ((torusFieldOriginalPointShifts_iff (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T) iS
      hS hTK hE x0.isValuation _ hfactor).mpr hshift) (hD x0 hx0)
  have hcompat : IsSplitTorusCompatible iS (localFieldOrder F) ψ.1 := by
    have h := torusFieldRestrictedRootFunctionFamily_isSplitTorusCompatible
      (K := inertiaFixedField F) (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T) iS hS hTK hE x0.isValuation ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f) hfactor
      (MaximalUnramified.realOrderCharacter F) x0.isSplitTorusCompatible
    have he : (fun t => (MaximalUnramified.realOrderCharacter F
        (Units.map (algebraMap F (inertiaFixedField F)).toMonoidHom t)).toAdd) =
        localFieldOrder F := funext (MaximalUnramified.realOrderCharacter_base F)
    rw [he] at h
    exact h
  let DS := KPApartmentData.ofNormalizerShifts (localFieldOrder F) ψ.1 ψ.2 hcompat hshift
  let CS : CentralizerDatum iS :=
    CentralizerDatum.ofValuationComparison
      Langlands.BruhatTits.Cartan.centralizerValuationComparison hG iS hiS
  -- the carrier is the set of restricted fixed points
  have hcarrier : ∀ ψ' : RootFunctionFamily S G, ψ' ∈ DS.carrier ↔
      ∃ x : D.Apartment, (∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
          RootFunctionFamily.galoisAction F (inertiaFixedField F) T G σ x.val = x.val) ∧
        ψ' = torusFieldRestrictedRootFunctionFamily (k := F) (K := inertiaFixedField F)
            hiS.isSplitSubtorus.1 hiT.isSplitSubtorus.1 hE (D.isRootDatumValuation_of_mem x.mem)
            ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f) := by
    intro ψ'
    constructor
    · rintro ⟨v, rfl⟩
      refine ⟨⟨descentCocharacterMap F (inertiaFixedField F) f hS v +ᵥ x0.val,
        D.vadd_mem x0.mem _⟩, ?_, ?_⟩
      · intro σ
        change RootFunctionFamily.galoisAction F (inertiaFixedField F) T G σ
            (descentCocharacterMap F (inertiaFixedField F) f hS v +ᵥ x0.val) =
          descentCocharacterMap F (inertiaFixedField F) f hS v +ᵥ x0.val
        rw [RootFunctionFamily.galoisAction_vadd, galoisCocharacterAction_descentCocharacterMap,
          hx0 σ]
      · exact (hφvadd x0 _ v rfl).symm
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨v, hv⟩ := unramified_exists_descent_vadd_of_galoisFixed hG hiS hf hiT D x0 x hx0 hx
      exact ⟨v, (hφvadd x0 x v hv).symm⟩
  refine ⟨DS, CS, ?_, hcarrier, ?_, hB⟩
  · -- V 6 over `F`
    have hψD : ψ.1 ∈ DS.carrier := AddAction.mem_orbit_self ψ.1
    exact (KPApartmentData.isCentralizerCompatible_iff_of_mem hψD).mpr (hC CS x0 hx0)
  · -- injectivity on fixed points
    intro x y hx hy hxy
    exact unramified_eq_of_torusFieldRestricted_eq hG hiS hf hiT hE D x y hx hy hxy

set_option maxHeartbeats 8000000 in
/-- `UnramifiedFixedCentralizerCompatibilityStatement` for fixed data, with explicit binders. -/
theorem unramifiedFixedCentralizerCompatibility_apply
    (hC : UnramifiedFixedCentralizerCompatibilityStatement.{u})
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    [IsAffineHom G.X.hom] [Smooth G.X.hom]
    (S : CommGroupScheme (Spec (CommRingCat.of F))) (iS : S.toGrp ⟶ G)
    (hiS : IsMaximalSplitTorus iS) [Mono iS.hom.hom.left]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (iT : T.toGrp ⟶ G) (f : S ⟶ T)
    (hf : CommGroupScheme.groupHom f ≫ iT = iS)
    (hiT : IsMaximalSplitTorus (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T) ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
    [Mono ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left]
    (hE : RelativeRoot.HasOppositeFactorPairs (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T) ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
    (D : KPApartmentData (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T) ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)
      (IntegerValuation.order (MaximalUnramified.valuation F)))
    (C : CentralizerDatum (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T) ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
    (hDC : IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) D C)
    (CS : CentralizerDatum iS) (x : D.Apartment) (hx : (∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
        RootFunctionFamily.galoisAction F (inertiaFixedField F) T G σ x.val = x.val)) :
    IsCentralizerCompatible iS CS.j CS.s CS.bijective
      (torusFieldRestrictedRootFunctionFamily (k := F) (K := inertiaFixedField F)
        hiS.isSplitSubtorus.1 hiT.isSplitSubtorus.1 hE (D.isRootDatumValuation_of_mem x.mem)
        ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f)) :=
  hC F G hG S iS hiS T iT f hf hiT hE D C hDC CS x hx

set_option maxHeartbeats 8000000 in
/-- `UnramifiedFixedOppositeStatement` for fixed data, with explicit binders. -/
theorem unramifiedFixedOpposite_apply
    (hD : UnramifiedFixedOppositeStatement.{u})
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    [IsAffineHom G.X.hom] [Smooth G.X.hom]
    (S : CommGroupScheme (Spec (CommRingCat.of F))) (iS : S.toGrp ⟶ G)
    (hiS : IsMaximalSplitTorus iS) [Mono iS.hom.hom.left]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (iT : T.toGrp ⟶ G) (f : S ⟶ T)
    (hf : CommGroupScheme.groupHom f ≫ iT = iS)
    (hiT : IsMaximalSplitTorus (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T) ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
    [Mono ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left]
    (hE : RelativeRoot.HasOppositeFactorPairs (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T) ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
    (D : KPApartmentData (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T) ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)
      (IntegerValuation.order (MaximalUnramified.valuation F)))
    (C : CentralizerDatum (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T) ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
    (hDC : IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) D C)
    (x : D.Apartment) (hx : (∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
        RootFunctionFamily.galoisAction F (inertiaFixedField F) T G σ x.val = x.val)) :
    ∀ a ∈ relativeRoots iS, ∀ g ∈ rootGroupPoints iS a, g ≠ 1 →
      ∀ g' ∈ rootGroupPoints iS (-a), ∀ g'' ∈ rootGroupPoints iS (-a),
        g' * g * g'' ∈ normalizerPoints iS →
          torusFieldRestrictedRootFunctionFamily (k := F) (K := inertiaFixedField F)
            hiS.isSplitSubtorus.1 hiT.isSplitSubtorus.1 hE (D.isRootDatumValuation_of_mem x.mem)
            ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f) (-a) g' +
            torusFieldRestrictedRootFunctionFamily (k := F) (K := inertiaFixedField F)
              hiS.isSplitSubtorus.1 hiT.isSplitSubtorus.1 hE (D.isRootDatumValuation_of_mem x.mem)
              ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f) a g = 0 :=
  hD F G hG S iS hiS T iT f hf hiT hE D C hDC x hx

set_option maxHeartbeats 8000000 in
/-- `UnramifiedGaloisFixedApartmentStatement` for fixed explicit data: a class with V 6 is
Galois-stable (`unramifiedGaloisStable_of_isOmegaCompatible`), so it has a fixed point. -/
theorem unramifiedGaloisFixedApartment_apply
    (hP : UnramifiedGaloisFixedApartmentStatement.{u})
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    [IsAffineHom G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (iT : T.toGrp ⟶ G)
    (hiT : IsMaximalSplitTorus (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T) ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
    [Mono ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left]
    (hE : RelativeRoot.HasOppositeFactorPairs (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T) ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
    (D : KPApartmentData (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T) ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)
      (IntegerValuation.order (MaximalUnramified.valuation F)))
    (C : CentralizerDatum (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T) ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
    (hDC : IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) D C) :
    ∃ x : D.Apartment, ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
      RootFunctionFamily.galoisAction F (inertiaFixedField F) T G σ x.val = x.val :=
  hP F G hG T iT hiT D (unramifiedGaloisStable_of_isOmegaCompatible hG iT hiT hE D C hDC)

/-- Internal proposition packaging the four-premise reduction proved below. The three new
fixed-locus inputs remain unproved; this proposition only records their implication to the
published descent statement. -/
def UnramifiedValuationDescentFixedLocusReductionStatement : Prop :=
  UnramifiedGaloisFixedApartmentStatement.{u} →
    UnramifiedFixedLeviTransportStatement.{u} →
    UnramifiedFixedCentralizerCompatibilityStatement.{u} →
    UnramifiedFixedOppositeStatement.{u} → UnramifiedValuationDescentStatement.{u}

set_option maxHeartbeats 8000000 in
/-- **Reduction of the descent to the fixed-locus inputs.** The existence of Galois-fixed
points in stable apartments (`UnramifiedGaloisFixedApartmentStatement`), the Levi transport
statement `UnramifiedFixedLeviTransportStatement` (through the bridge
`unramifiedFixedNormalizerTransport_of_leviTransport`), V 6 on `Z(F)` at the Galois-fixed points
and V 5 at the Galois-fixed points imply `UnramifiedValuationDescentStatement`. -/
theorem unramifiedValuationDescent_of_fixedLocus
    (hP : UnramifiedGaloisFixedApartmentStatement.{u})
    (hQ : UnramifiedFixedLeviTransportStatement.{u})
    (hC : UnramifiedFixedCentralizerCompatibilityStatement.{u})
    (hD : UnramifiedFixedOppositeStatement.{u}) :
    UnramifiedValuationDescentStatement.{u} := by
  intro F _ _ _ _ G hG S iS hiS T iT f hf
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  have := mono_of_isMaximalSplitTorus hiS
  intro hiT
  have : Mono ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left := mono_of_isMaximalSplitTorus hiT
  intro hE D C hDC fixed φ
  exact unramifiedValuationDescent_core F G hG S iS hiS T iT f hf hiT hE D
    (unramifiedGaloisFixedApartment_apply hP F G hG T iT hiT hE D C hDC)
    (fun n x hx => unramifiedFixedNormalizerTransport_of_leviTransport hQ F G hG S iS hiS T iT f hf hiT hE D C hDC n x hx)
    (fun CS x hx => unramifiedFixedCentralizerCompatibility_apply hC F G hG S iS hiS T iT f hf hiT hE D C hDC CS x hx)
    (fun x hx => unramifiedFixedOpposite_apply hD F G hG S iS hiS T iT f hf hiT hE D C hDC x hx)

end Langlands.Geometry.Building
