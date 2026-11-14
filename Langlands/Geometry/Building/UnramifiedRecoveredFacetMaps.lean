import Langlands.Geometry.Building.UnramifiedFacetResidueComparisons
import Langlands.GroupScheme.IntegralModel.RecoveredResidueDescent
import Langlands.BruhatTits.IntegralModels.UnramifiedNeutralModelDescent
import Langlands.GroupScheme.IntegralModel.UnramifiedSmoothDescentProof

/-! # Recovered residue maps on a maximal-unramified fixed facet -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing
open scoped ValuativeRel CategoryTheory.MonObj
open Langlands Langlands.LocalGalois Langlands.LocalGalois.Separable
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.GroupScheme.IntegralModel

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G H : GroupScheme (Spec (CommRingCat.of K))}
  {P : IntegralModel R K G} {N N' : IntegralModel R K H}
  {f : G ≅ H}

/-- Close an actual integral comparison along equality of its target model. -/
def Iso.changeTarget (e : P.Iso N f) (h : N = N') : P.Iso N' f :=
  h ▸ e

variable [IsLocalRing R]
  (a : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of R))
  (v : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K))
  (hva : v ≫ Spec.algebraMap R K = Spec.algebraMap R K ≫ a)
  (g : (GroupScheme.baseChange v).obj G ≅ H)
  (e : (P.twist a v hva).Iso N g)
  (h : N = N')
  (r : Spec (CommRingCat.of (ResidueField R)) ⟶
    Spec (CommRingCat.of (ResidueField R)))
  (hra : r ≫ residueBaseMap R = residueBaseMap R ≫ a)

/-- Closing the integral target specializes to the same equality transport
on the original special fibre. -/
theorem Iso.residueTwistIso_changeTarget :
    Iso.residueTwistIso P N' a v hva g (e.changeTarget h) r hra =
      Iso.residueTwistIso P N a v hva g e r hra ≪≫
        eqToIso (congrArg (fun N : IntegralModel R K H => N.specialFibre) h) := by
  subst N'
  simp [Iso.changeTarget]

/-- Index equality gives the original special-fibre equality directly. -/
theorem Iso.residueTwistIso_changeTarget_indexed
    {I : Type u} (models : I → IntegralModel R K H) {x y : I}
    (e : (P.twist a v hva).Iso (models x) g) (h : x = y) :
    Iso.residueTwistIso P (models y) a v hva g
        (e.changeTarget (congrArg models h)) r hra =
      Iso.residueTwistIso P (models x) a v hva g e r hra ≪≫
        eqToIso (congrArg (fun j => (models j).specialFibre) h) := by
  subst y
  simp [Iso.changeTarget]

/-- The residue comparison depends on the actual integral isomorphism,
independently of the presentation of its generic compatibility. -/
theorem Iso.residueTwistIso_congr
    (g' : (GroupScheme.baseChange v).obj G ≅ H)
    (e' : (P.twist a v hva).Iso N g') (he : e.iso = e'.iso) :
    Iso.residueTwistIso P N a v hva g e r hra =
      Iso.residueTwistIso P N a v hva g' e' r hra := by
  unfold Iso.residueTwistIso
  rw [he]

end Langlands.GroupScheme.IntegralModel

namespace Langlands.Geometry.Building.KPApartmentData

open Langlands.BruhatTits.IntegralModels

section General

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G)
  [Mono (CategoryTheory.Functor.map
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
  (R : Type u) [CommRing R] [IsDomain R] [Algebra R K] [IsFractionRing R K]
  (M : IntegerFacetModelData (K := K) (G := baseChanged k K G) (v := v)
    (integerBuildingData D hG hi C h6) R)
  (hpoints : ∀ J : (integerBuildingData D hG hi C h6).BuildingFacet,
    (M.model J).full.integralPoints = characterValuationKernel v (baseChanged k K G) ⊓
      (integerBuildingData D hG hi C h6).pointwiseFixer J.val)
  (E : GaloisFacet k K i D hD hG hi C h6)
  [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [IsSepClosed (ResidueField R)]
  (hv : ∀ (σ : K ≃ₐ[k] K) (x : K), v (σ x) = v x)
  (a : (K ≃ₐ[k] K) → (Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of R)))
  [∀ σ, IsIso (a σ)]
  (hσ : ∀ σ, galoisBaseMap k K σ ≫ Spec.algebraMap R K = Spec.algebraMap R K ≫ a σ)
  (f : Type u) [Field f] [Algebra f (ResidueField R)]
  (residueAction : (K ≃ₐ[k] K) →* (ResidueField R ≃ₐ[f] ResidueField R))
  (hra : ∀ σ, galoisBaseMap f (ResidueField R) (residueAction σ) ≫
    IntegralModel.residueBaseMap R = IntegralModel.residueBaseMap R ≫ a σ)

/-- Close an actual neutral integral comparison at its original fixed facet. -/
def fixedFacetNeutralGaloisIso (σ : K ≃ₐ[k] K) :
    ((M.model E.val).neutral.twist (a σ) (galoisBaseMap k K σ) (hσ σ)).Iso
      (M.model E.val).neutral (galoisDescentIso k K G σ) :=
  (neutralModelGaloisTwistIso k K i D hD hG hi C h6 R M hpoints σ (hv σ)
    (a σ) (hσ σ) E.val).changeTarget
      (congrArg (fun J => (M.model J).neutral)
        (galoisBuildingFacetAction_galoisFacet k K i D hD hG hi C h6 E σ))

/-- Specializing the closed integral comparison gives the published original
fixed-facet residue comparison. -/
theorem fixedFacetNeutralGaloisIso_residue (σ : K ≃ₐ[k] K) :
    IntegralModel.Iso.residueTwistIso (M.model E.val).neutral (M.model E.val).neutral
      (a σ) (galoisBaseMap k K σ) (hσ σ) (galoisDescentIso k K G σ)
      (fixedFacetNeutralGaloisIso k K i D hD hG hi C h6 R M hpoints E hv a hσ σ)
      (galoisBaseMap f (ResidueField R) (residueAction σ)) (hra σ) =
        fixedFacetResidueGaloisIso k K i D hD hG hi C h6 R M hpoints E hv a hσ f
          residueAction hra σ := by
  unfold fixedFacetNeutralGaloisIso fixedFacetResidueGaloisIso neutralResidueGaloisIso
  exact IntegralModel.Iso.residueTwistIso_changeTarget_indexed
    (P := (M.model E.val).neutral) (a σ) (galoisBaseMap k K σ) (hσ σ)
    (galoisDescentIso k K G σ)
    (galoisBaseMap f (ResidueField R) (residueAction σ)) (hra σ)
    (fun J => (M.model J).neutral)
    (neutralModelGaloisTwistIso k K i D hD hG hi C h6 R M hpoints σ (hv σ)
      (a σ) (hσ σ) E.val)
    (galoisBuildingFacetAction_galoisFacet k K i D hD hG hi C h6 E σ)

variable (O : Type u) [CommRing O] [IsDomain O] [Algebra O k] [IsFractionRing O k]
  [Algebra O R] [Algebra O K] [IsScalarTower O R K] [IsScalarTower O k K]
  [IsLocalRing O]
  (D0 : IntegralModel O k G)
  (s : (D0.baseChange R K).Iso (M.model E.val).neutral (CategoryTheory.Iso.refl _))
  (ha : ∀ σ, a σ ≫ Spec.algebraMap O R = Spec.algebraMap O R)
  (e : Spec (CommRingCat.of (ResidueField R)) ⟶ Spec (CommRingCat.of (ResidueField O)))
  (he : IntegralModel.residueBaseMap R ≫ Spec.algebraMap O R =
    e ≫ IntegralModel.residueBaseMap O)
  (hre : ∀ σ, galoisBaseMap f (ResidueField R) (residueAction σ) ≫ e = e)

include ha in
/-- Every actual downstairs residue map satisfies coefficient naturality with
the original fixed-facet residue comparison. -/
theorem fixedFacetResidueDescendedMap_naturality
    {H : GroupScheme (Spec (CommRingCat.of (ResidueField O)))}
    (q : D0.specialFibre ⟶ H) (σ : K ≃ₐ[k] K) :
    (fixedFacetResidueGaloisIso k K i D hD hG hi C h6 R M hpoints E hv a hσ f
      residueAction hra σ).hom ≫ IntegralModel.residueDescendedMap D0 R K s e he q =
      (GroupScheme.baseChange (galoisBaseMap f (ResidueField R) (residueAction σ))).map
          (IntegralModel.residueDescendedMap D0 R K s e he q) ≫
        (descentBaseChangeIso e (galoisBaseMap f (ResidueField R) (residueAction σ))
          (hre σ) H).hom := by
  let ψ : ((M.model E.val).neutral.twist (a σ) (galoisBaseMap k K σ) (hσ σ)).Iso
      (M.model E.val).neutral
      (descentBaseChangeIso (Spec.algebraMap k K) (galoisBaseMap k K σ)
        (galoisBaseMap_over k K σ) G) :=
    { iso := (fixedFacetNeutralGaloisIso k K i D hD hG hi C h6 R M hpoints E hv a hσ σ).iso
      generic_comm := by
        rw [← galoisDescentIso_def k K G σ]
        exact (fixedFacetNeutralGaloisIso k K i D hD hG hi C h6 R M hpoints E hv a hσ σ).generic_comm }
  have hn := IntegralModel.residueDescendedMap_naturality D0 R K (a σ) (ha σ)
    (galoisBaseMap k K σ) (galoisBaseMap_over k K σ) (hσ σ) s ψ e he
    (galoisBaseMap f (ResidueField R) (residueAction σ)) (hre σ) (hra σ) q
  have hc := IntegralModel.Iso.residueTwistIso_congr
    (P := (M.model E.val).neutral) (a σ) (galoisBaseMap k K σ) (hσ σ)
    (descentBaseChangeIso (Spec.algebraMap k K) (galoisBaseMap k K σ)
      (galoisBaseMap_over k K σ) G) ψ
    (galoisBaseMap f (ResidueField R) (residueAction σ)) (hra σ)
    (galoisDescentIso k K G σ)
    (fixedFacetNeutralGaloisIso k K i D hD hG hi C h6 R M hpoints E hv a hσ σ) rfl
  rw [hc, fixedFacetNeutralGaloisIso_residue k K i D hD hG hi C h6 R M hpoints E hv a hσ
    f residueAction hra σ] at hn
  exact hn

end General

end Langlands.Geometry.Building.KPApartmentData

namespace Langlands.GroupScheme.Descent.FiniteUnramified

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

local instance : Algebra ↥𝒪[F] (fixedFieldIntegers F) :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)
local instance : Algebra 𝓀[F] (ResidueField (fixedFieldIntegers F)) :=
  (residueToFixedField F).toAlgebra

/-- Canonical integer coefficient automorphisms fix the original integers. -/
theorem fixedIntegerBaseAut_over
    (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F) :
    fixedIntegerBaseAut F σ ≫ Spec.algebraMap ↥𝒪[F] (fixedFieldIntegers F) =
      Spec.algebraMap ↥𝒪[F] (fixedFieldIntegers F) := by
  change Spec.map (CommRingCat.ofHom _) ≫ Spec.map (CommRingCat.ofHom _) =
    Spec.map (CommRingCat.ofHom _)
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  apply congrArg (fun f => Spec.map (CommRingCat.ofHom f))
  apply RingHom.ext
  intro x
  apply Subtype.ext
  exact σ.commutes (x : F)

/-- The actual integer and residue extensions form the original coefficient
square used to specialize recovered models. -/
theorem fixedResidueBaseMap_square :
    IntegralModel.residueBaseMap (fixedFieldIntegers F) ≫
        Spec.algebraMap ↥𝒪[F] (fixedFieldIntegers F) =
      algebraBaseMap 𝓀[F] (ResidueField (fixedFieldIntegers F)) ≫
        IntegralModel.residueBaseMap ↥𝒪[F] := by
  change Spec.map (CommRingCat.ofHom _) ≫ Spec.map (CommRingCat.ofHom _) =
    Spec.map (CommRingCat.ofHom _) ≫ Spec.map (CommRingCat.ofHom _)
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp]
  apply congrArg (fun f => Spec.map (CommRingCat.ofHom f))
  apply RingHom.ext
  intro x
  exact (residueToFixedField_residue F x).symm

end Langlands.GroupScheme.Descent.FiniteUnramified

namespace Langlands.Geometry.Building.KPApartmentData

open Langlands.BruhatTits.IntegralModels
open Langlands.GroupScheme.Descent.FiniteUnramified

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

local instance : Algebra ↥𝒪[F] (fixedFieldIntegers F) :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)
local instance : IsScalarTower ↥𝒪[F] (fixedFieldIntegers F) (inertiaFixedField F) :=
  Valuation.HasExtension.instIsScalarTowerInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)
local instance : Algebra 𝓀[F] (ResidueField (fixedFieldIntegers F)) :=
  (residueToFixedField F).toAlgebra
local instance : IsDiscreteValuationRing (fixedFieldIntegers F) :=
  (separableUnramifiedArithmetic F).2.2.2.1
local instance : HenselianLocalRing (fixedFieldIntegers F) :=
  fixedFieldIntegersIsHenselian F
local instance : IsAlgClosed (ResidueField (fixedFieldIntegers F)) :=
  (fixedFieldResidueIsAlgClosure F).1

variable
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G)
  [Mono (CategoryTheory.Functor.map
    (GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))) i).hom.hom.left]
  (D : KPApartmentData
    (S := CategoryTheory.Functor.obj
      (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))) T)
    (CategoryTheory.Functor.map
      (GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))) i)
    (IntegerValuation.order (MaximalUnramified.valuation F)))
  (hD : GaloisStable F (inertiaFixedField F) i D)
  (hG : IsConnectedReductive (baseChanged F (inertiaFixedField F) G))
  (hi : IsMaximalSplitTorus
    (T := CategoryTheory.Functor.obj
      (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))) T)
    (CategoryTheory.Functor.map
      (GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))) i))
  (C : CentralizerDatum
    (S := CategoryTheory.Functor.obj
      (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))) T)
    (CategoryTheory.Functor.map
      (GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))) i))
  (h6 : IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) D C)

private instance recoveredFacet_extendedAffine :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom
    (algebraBaseMap F (inertiaFixedField F)))
  infer_instance

variable
  (M : IntegerFacetModelData (K := inertiaFixedField F)
    (G := baseChanged F (inertiaFixedField F) G) (v := MaximalUnramified.valuation F)
    (integerBuildingData D hG hi C h6) (fixedFieldIntegers F))
  (hpoints : ∀ E : (integerBuildingData D hG hi C h6).BuildingFacet,
    (M.model E).full.integralPoints =
      characterValuationKernel (MaximalUnramified.valuation F)
        (baseChanged F (inertiaFixedField F) G) ⊓
      (integerBuildingData D hG hi C h6).pointwiseFixer E.val)
  (E : GaloisFacet F (inertiaFixedField F) i D hD hG hi C h6)

local notation "𝕂" => inertiaFixedField F
local notation "𝓡" => fixedFieldIntegers F
local notation "L" => ResidueField (fixedFieldIntegers F)

/-- Close the actual neutral coefficient comparison using invariance of the
original Galois facet. -/
def unramifiedFixedFacetNeutralIso (σ : 𝕂 ≃ₐ[F] 𝕂) :
    ((M.model E.val).neutral.twist (fixedIntegerBaseAut F σ)
      (galoisBaseMap F 𝕂 σ) (fixedIntegerBaseAut_generic F σ)).Iso
        (M.model E.val).neutral (galoisDescentIso F 𝕂 G σ) :=
  fixedFacetNeutralGaloisIso F 𝕂 i D hD hG hi C h6 𝓡 M hpoints E
    (MaximalUnramified.valuation_galois F) (fixedIntegerBaseAut F)
    (fixedIntegerBaseAut_generic F) σ

/-- The closed integral comparison specializes to the existing canonical
fixed-facet residue comparison, with no comparison equality supplied. -/
theorem unramifiedFixedFacetNeutralIso_residue (σ : 𝕂 ≃ₐ[F] 𝕂) :
    IntegralModel.Iso.residueTwistIso (M.model E.val).neutral (M.model E.val).neutral
      (fixedIntegerBaseAut F σ) (galoisBaseMap F 𝕂 σ) (fixedIntegerBaseAut_generic F σ)
      (galoisDescentIso F 𝕂 G σ)
      (unramifiedFixedFacetNeutralIso F i D hD hG hi C h6 M hpoints E σ)
      (galoisBaseMap 𝓀[F] L (fixedResidueAction F σ)) (fixedResidueAction_square F σ) =
        unramifiedFixedFacetResidueIso F i D hD hG hi C h6 M hpoints E σ :=
  fixedFacetNeutralGaloisIso_residue F 𝕂 i D hD hG hi C h6 𝓡 M hpoints E
    (MaximalUnramified.valuation_galois F) (fixedIntegerBaseAut F)
    (fixedIntegerBaseAut_generic F) 𝓀[F] (fixedResidueAction F)
    (fixedResidueAction_square F) σ

include hpoints in
/-- The actual component model at an original fixed facet descends, using
the published smooth-model descent theorem and the proved full-point covariance. -/
theorem exists_unramifiedFixedFacetRecovery (hconn : GeometricallyConnected G.X.hom) :
    ∃ D0 : RelativeComponentModelData ↥𝒪[F] F G,
      Nonempty (UnramifiedComponentModelRecovery D0 (M.model E.val)) := by
  apply exists_unramified_componentModelRecovery IntegralModel.unramifiedSmoothModelDescent
    hconn (M.model E.val)
  intro σ g hg
  have hp := (full_integralPoints_galois_iff F 𝕂 i D hD hG hi C h6 𝓡 M hpoints σ
    (MaximalUnramified.valuation_galois F σ) E.val g).mpr hg
  simpa only [galoisBuildingFacetAction_galoisFacet F 𝕂 i D hD hG hi C h6 E σ] using hp

variable (D0 : RelativeComponentModelData ↥𝒪[F] F G)
  (s : UnramifiedComponentModelRecovery D0 (M.model E.val))

/-- Recover an actual original-residue map on the neutral special fibre of the
original fixed facet. -/
abbrev unramifiedFixedFacetDescendedMap
    {H : GroupScheme (Spec (CommRingCat.of 𝓀[F]))}
    (q : D0.neutral.specialFibre ⟶ H) :=
  IntegralModel.residueDescendedMap D0.neutral 𝓡 𝕂 s.neutralIso
    (algebraBaseMap 𝓀[F] L) (fixedResidueBaseMap_square F) q

/-- All integer and residue coefficient hypotheses are canonical, so any
recovered downstairs map satisfies the original fixed-facet residue square. -/
theorem unramifiedFixedFacetDescendedMap_naturality
    {H : GroupScheme (Spec (CommRingCat.of 𝓀[F]))}
    (q : D0.neutral.specialFibre ⟶ H) (σ : 𝕂 ≃ₐ[F] 𝕂) :
    (unramifiedFixedFacetResidueIso F i D hD hG hi C h6 M hpoints E σ).hom ≫
        unramifiedFixedFacetDescendedMap F i D hD hG hi C h6 M E D0 s q =
      (GroupScheme.baseChange (galoisBaseMap 𝓀[F] L (fixedResidueAction F σ))).map
          (unramifiedFixedFacetDescendedMap F i D hD hG hi C h6 M E D0 s q) ≫
        (descentBaseChangeIso (algebraBaseMap 𝓀[F] L)
          (galoisBaseMap 𝓀[F] L (fixedResidueAction F σ))
          (galoisBaseMap_over 𝓀[F] L (fixedResidueAction F σ)) H).hom :=
  fixedFacetResidueDescendedMap_naturality F 𝕂 i D hD hG hi C h6 𝓡 M hpoints E
    (MaximalUnramified.valuation_galois F) (fixedIntegerBaseAut F)
    (fixedIntegerBaseAut_generic F) 𝓀[F] (fixedResidueAction F)
    (fixedResidueAction_square F) ↥𝒪[F] D0.neutral s.neutralIso
    (fixedIntegerBaseAut_over F) (algebraBaseMap 𝓀[F] L) (fixedResidueBaseMap_square F)
    (fun σ => galoisBaseMap_over 𝓀[F] L (fixedResidueAction F σ)) q σ

/-- An original fixed facet has an actual downstairs component recovery whose
recovered residue maps all satisfy the original coefficient square. -/
def UnramifiedFixedFacetRecoveredMapsStatement : Prop :=
  GeometricallyConnected G.X.hom →
    ∃ (N0 : RelativeComponentModelData ↥𝒪[F] F G)
      (t : UnramifiedComponentModelRecovery N0 (M.model E.val)),
      ∀ (H : GroupScheme (Spec (CommRingCat.of 𝓀[F])))
        (q : N0.neutral.specialFibre ⟶ H) (σ : 𝕂 ≃ₐ[F] 𝕂),
        (unramifiedFixedFacetResidueIso F i D hD hG hi C h6 M hpoints E σ).hom ≫
            unramifiedFixedFacetDescendedMap F i D hD hG hi C h6 M E N0 t q =
          (GroupScheme.baseChange (galoisBaseMap 𝓀[F] L (fixedResidueAction F σ))).map
              (unramifiedFixedFacetDescendedMap F i D hD hG hi C h6 M E N0 t q) ≫
            (descentBaseChangeIso (algebraBaseMap 𝓀[F] L)
              (galoisBaseMap 𝓀[F] L (fixedResidueAction F σ))
              (galoisBaseMap_over 𝓀[F] L (fixedResidueAction F σ)) H).hom

theorem unramifiedFixedFacetRecoveredMaps :
    UnramifiedFixedFacetRecoveredMapsStatement F i D hD hG hi C h6 M hpoints E := by
  intro hconn
  obtain ⟨N0, ⟨t⟩⟩ :=
    exists_unramifiedFixedFacetRecovery F i D hD hG hi C h6 M hpoints E hconn
  refine ⟨N0, t, ?_⟩
  intro H q σ
  exact unramifiedFixedFacetDescendedMap_naturality F i D hD hG hi C h6 M hpoints E
    N0 t q σ

end Langlands.Geometry.Building.KPApartmentData
