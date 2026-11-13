import Langlands.Shimura.PEL.HarrisTaylorCMLevelTransport
import Langlands.Shimura.Coefficients.EtaleAssociatedTransportLaws

/-! # Laws for the transport maps of Harris's coefficient systems

The stage transition `cmHarrisStageTransportMap` of the coefficient system of a fixed level,
and four laws for the transport maps `cmHarrisTransportSheafMap` of
`Langlands.Shimura.PEL.HarrisTaylorCMLevelTransport`. Along an identity of scaled levels the
transport map is the stage transition, a transition of the coefficient system
`cmHarrisCoefficientSystem` of the level.
Shifting the exponents of a morphism of scaled levels does not change its transport maps. For the
identity of a level raised to a larger exponent, the transport map is the transition multiplied by
a power of the coefficient prime. For a morphism from a scaled level to itself whose translating
element lies in the level, the transport map is the same transition as for the identity. See
`HarrisTaylorCMLevelTransportLaws.md`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.Shimura.Coefficients Langlands.Geometry

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F] [IsCMField F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
  [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ F A]
  {n : ℕ} (D : CentralSimpleUnitaryData E F A n)

variable {L : Type} [Field L] [NumberField L] [IsCMField L]
  [IsQuadraticExtension ℚ L] [Algebra L F]
  {τ₀ : L →+* ℂ}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n
    (harrisCMSection E (algebraMap L F) τ₀))
  (preservation : pullbackTensorComparisonIsIsoStatement.{0})
  (composition : PullbackTensorCompositionStatement.{0})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{0})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{0})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{0})
  (symmetry : PullbackTensorSymmetryStatement.{0})
  (stability : PicardZeroPullbackStatement.{0})
  (square : MumfordBundlePicardZeroStatement.{0})
  (universality : PicardZeroUniversalBaseChangeStatement.{0})
  (dualityNaturality : DualAbelianBaseChangeNaturalityStatement.{0})
  (polarizationStability : PolarizationBaseChangeStatement.{0})
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  (htor : TorsionFiniteEtaleStatement.{0})

open Langlands.AlgebraicGeometry

variable (q : CMRepresentabilityStatement D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor)
  (existence : RelativeDualSchemeExistenceStatement.{0})
  (geometry : RelativeDualSchemeGeometryStatement.{0})
  (hRigid : ∀ U : SmallCMLevel D, CMGeometricCoarseRigidity D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    compatibility h htor U.obj)

local notation "schemes" => cmSchemeTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q

set_option quotPrecheck false in
local notation "normalTorsor" U:max V:max hVU:max => cmNormalGeometricTorsor_of_dominantCriterion
  D C preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor U V hVU q
  existence geometry (hRigid U) DominantUnramifiedEtaleProof.dominantUnramifiedEtale


variable {K : Type} [Field K] [NumberField K] (p : Global.FinitePlace ℚ)

local notation "Rcoeff" => HarrisCoefficientIntegers K p

variable [Module.Finite ℚ A]
  {W : Type} [AddCommGroup W] [Module K W] [Module.Finite K W]
  (ρ : (D.rationalInvolution.baseChange K).AlgebraicRepresentation W)

local notation "ℓ" => harrisCoefficientPrime p
local notation "hℓ" => harrisCoefficientPrime_ne_zero p
local notation "coeffLevel" U:max k:max => cmHarrisCoefficientLevel D ρ p U ℓ hℓ k
local notation "datumAt" => cmHarrisTransportDatumAt D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor q existence geometry hRigid p ρ
local notation "transportMap" => cmHarrisTransportSheafMap D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q existence geometry hRigid p ρ
local notation "system" U:max => cmHarrisCoefficientSystem D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p ℓ hℓ existence geometry
  (hRigid U)
local notation "covers" U:max => cmHarrisCoefficientEtaleDiagram D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p ℓ hℓ
  existence geometry (hRigid U)
local notation "coefficients" U:max => cmHarrisCoefficientDiagram D ρ p U ℓ hℓ
local notation "transportDatum" => cmNormalTransportDatum D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q existence geometry hRigid p

/-! ## The stage transition at a fixed level -/

/-- The stage transition of the coefficient system of a level `U` from stage `k` to stage
`k' ≤ k`, read through the restriction along a scheme map `φ` equal to the identity: the
identification of the restriction along `φ` with the restriction along the identity, then the
identification of the restriction along the identity with the sheaf itself, then the transition
map of the coefficient system `cmHarrisCoefficientSystem` of `U` from stage `k` to stage `k'`. -/
def cmHarrisStageTransportMap (U : SmallCMLevel D) {k' k : ℕ} (hk : k' ≤ k)
    (φ : (schemes).obj U ⟶ (schemes).obj U) [Etale φ] (e : φ = 𝟙 _) :
    (EtalePullback.restriction φ (ModuleCat.{0} Rcoeff)).obj ((system U).obj (op k)) ⟶
      (system U).obj (op k') :=
  (EtalePullback.restrictionCongr Rcoeff e).hom.app _ ≫
    (EtalePullback.restrictionId (ModuleCat.{0} Rcoeff)).hom.app _ ≫
      (system U).map (homOfLE hk).op

local notation "stageMap" => cmHarrisStageTransportMap D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q existence geometry hRigid p ρ

/-! ## Transport along an identity -/

/-- Along an identity of scaled levels and stages `k' ≤ k`, and a scheme map equal to the
identity, the transport map is the identification of the restriction along the identity followed
by the transition of the coefficient system of the level from stage `k` to stage `k'`. -/
theorem cmHarrisTransportSheafMap_id_le (Y : CMScaledLevel D ρ p) {k' k : ℕ} (hk : k' ≤ k)
    (φ : (schemes).obj Y.level ⟶ (schemes).obj Y.level)
    (hφ : φ = (schemes).map (CMScaledLevel.Hom.hom (𝟙 Y))) [Etale φ] (e : φ = 𝟙 _) :
    transportMap (𝟙 Y) hk φ hφ = stageMap Y.level hk φ e := by
  rw [cmHarrisStageTransportMap]
  have hφ₂ : 𝟙 ((schemes).obj Y.level) = (schemes).map (CMScaledLevel.Hom.hom (𝟙 Y)) :=
    (CategoryTheory.Functor.map_id _ _).symm
  have hcongr := cmHarrisTransportDatumAt_sheafMap_congr D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q existence geometry hRigid p ρ
    (𝟙 Y) hk e hφ hφ₂ (cmScaledTransportLevel D p ρ (𝟙 Y) k' k)
    (cmScaledTransportLevel_le D p ρ (𝟙 Y) k' k) (cmScaledTransportLevel_le_coeff D p ρ (𝟙 Y) k' k)
    (cmScaledTransportLevel_conj D p ρ (𝟙 Y) k' k)
  have hT : (cmScaledTransportLevel D p ρ (𝟙 Y) k' k).obj.subgroup ≤
      (coeffLevel Y.level k).obj.subgroup := fun x hx => by
    simpa using cmScaledTransportLevel_conj D p ρ (𝟙 Y) k' k x hx
  have hiso : IsIso (etaleCrossCoverMap _
      ((cmHarrisCoefficientGroups D ρ p Y.level ℓ hℓ).map (homOfLE hk).op).hom
      ((covers Y.level).transition (homOfLE hk).op)
      (𝟙 ((Action.res (ModuleCat Rcoeff)
        ((cmHarrisCoefficientGroups D ρ p Y.level ℓ hℓ).map (homOfLE hk).op).hom).obj
          ((coefficients Y.level).action (op k'))))) :=
    cmHarrisCoefficientSystem_comparison_isIso D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q Y.level ρ p ℓ hℓ existence
      geometry (hRigid Y.level) (homOfLE hk).op
  have hG1 := EtaleTransportDatum.sheafMap_id_transition
    (datumAt (𝟙 Y) hk (𝟙 _) hφ₂ (cmScaledTransportLevel D p ρ (𝟙 Y) k' k)
      (cmScaledTransportLevel_le D p ρ (𝟙 Y) k' k)
      (cmScaledTransportLevel_le_coeff D p ρ (𝟙 Y) k' k)
      (cmScaledTransportLevel_conj D p ρ (𝟙 Y) k' k))
    (normalTorsor Y.level (coeffLevel Y.level k')
      (cmHarrisCoefficientLevel_le D ρ p Y.level ℓ hℓ k')).property
    ((cmHarrisCoefficientGroups D ρ p Y.level ℓ hℓ).map (homOfLE hk).op).hom
    ((covers Y.level).transition (homOfLE hk).op)
    ((coefficients Y.level).transition (homOfLE hk).op)
    (MorphismProperty.Over.homMk ((schemes).map (smallCMInclusion D hT)) (by
      change (schemes).map (smallCMInclusion D hT) ≫
          (schemes).map (smallCMInclusion D (cmHarrisCoefficientLevel_le D ρ p Y.level ℓ hℓ k)) =
        (schemes).map (smallCMInclusion D (cmScaledTransportLevel_le D p ρ (𝟙 Y) k' k))
      rw [← Functor.map_comp, smallCMInclusion_trans])) ?_ ?_ ?_
  · refine hcongr.symm.trans ?_
    rw [hG1]
    rfl
  · apply MorphismProperty.Over.Hom.ext
    rw [MorphismProperty.Comma.comp_left]
    change (cmNormalTransportToSource D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q existence geometry hRigid _ _ hφ₂ _ _ _ _ _
        ).left ≫ pullback.fst _ _ = _
    rw [cmNormalTransportToSource_fst]
    change _ = (schemes).map (smallCMInclusion D _)
    congr 1
  · apply MorphismProperty.Over.Hom.ext
    change (schemes).map (smallCMInclusion D hT) ≫ (schemes).map (smallCMInclusion D _) =
      (schemes).map (smallCMInclusion D _)
    rw [← Functor.map_comp, smallCMInclusion_trans]
  · change cmHarrisTorsionTransport D ρ p (𝟙 Y) hk = _
    rw [cmHarrisTorsionTransport_id]
    rfl

/-! ## Shifting and raising exponents -/

omit [IsCMField F] [IsScalarTower E F A] [IsScalarTower ℚ F A] in
/-- Shifting both exponents of a morphism of scaled levels by `k₀` does not change its maps of
torsion coefficient modules. -/
theorem cmHarrisTorsionTransport_shift {X Y : CMScaledLevel D ρ p} (f : X ⟶ Y) (k₀ : ℕ)
    {k' k : ℕ} (hk : k' ≤ k) :
    cmHarrisTorsionTransport D ρ p (CMScaledLevel.Hom.shift D ρ p f k₀) hk =
      cmHarrisTorsionTransport D ρ p f hk := by
  ext x
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change (cmHarrisTorsionTransport D ρ p (CMScaledLevel.Hom.shift D ρ p f k₀) hk).hom
      (Submodule.Quotient.mk a) =
    (cmHarrisTorsionTransport D ρ p f hk).hom (Submodule.Quotient.mk a)
  rw [cmHarrisTorsionTransport_mk, cmHarrisTorsionTransport_mk, cmHarrisLatticeTransport_shift]

omit [Module.Finite ℚ A] in
/-- The transport map of the transport datum along a transporter of small CM levels depends on
the coefficient map only through its value: equal coefficient maps give equal transport maps. -/
theorem cmNormalTransportDatum_sheafMap_congr {V U : SmallCMLevel D} (b : V ⟶ U)
    (φ : (schemes).obj V ⟶ (schemes).obj U) (hφ : φ = (schemes).map b) [Etale φ]
    (U' : SmallCMLevel D) (hU' : U'.obj.subgroup ≤ U.obj.subgroup)
    [(U'.obj.subgroup.subgroupOf U.obj.subgroup).Normal]
    (V' : SmallCMLevel D) (hV' : V'.obj.subgroup ≤ V.obj.subgroup)
    [(V'.obj.subgroup.subgroupOf V.obj.subgroup).Normal]
    (T : SmallCMLevel D) (hT : T.obj.subgroup ≤ V.obj.subgroup)
    [(T.obj.subgroup.subgroupOf V.obj.subgroup).Normal]
    (hTV' : T.obj.subgroup ≤ V'.obj.subgroup)
    (hTU' : ∀ x ∈ T.obj.subgroup, b.hom.element⁻¹ * x * b.hom.element ∈ U'.obj.subgroup)
    (M : Action (ModuleCat Rcoeff) (SmallCMResidualGroup D U U'))
    (M' : Action (ModuleCat Rcoeff) (SmallCMResidualGroup D V V'))
    (c₁ c₂ : M.V ⟶ M'.V)
    (hc₁ : ∀ v : V.obj.subgroup,
      M.ρ (QuotientGroup.mk (smallCMTransporterConj D b v)) ≫ c₁ = c₁ ≫ M'.ρ (QuotientGroup.mk v))
    (hc₂ : ∀ v : V.obj.subgroup,
      M.ρ (QuotientGroup.mk (smallCMTransporterConj D b v)) ≫ c₂ = c₂ ≫ M'.ρ (QuotientGroup.mk v))
    (e : c₁ = c₂) (hY' : IsFiniteGeometricTorsor ((schemes).obj V) (normalTorsor V V' hV').val) :
    (transportDatum b φ hφ U' hU' V' hV' T hT hTV' hTU' M M' c₁ hc₁).sheafMap hY' =
      (transportDatum b φ hφ U' hU' V' hV' T hT hTV' hTU' M M' c₂ hc₂).sheafMap hY' := by
  subst e
  rfl

omit [Module.Finite ℚ A] in
/-- If the coefficient map `c₁` of the transport datum along a transporter of small CM levels is
`m • c₂`, its transport map is `m` times the transport map of the datum with coefficient map
`c₂`. -/
theorem cmNormalTransportDatum_sheafMap_nsmul {V U : SmallCMLevel D} (b : V ⟶ U)
    (φ : (schemes).obj V ⟶ (schemes).obj U) (hφ : φ = (schemes).map b) [Etale φ]
    (U' : SmallCMLevel D) (hU' : U'.obj.subgroup ≤ U.obj.subgroup)
    [(U'.obj.subgroup.subgroupOf U.obj.subgroup).Normal]
    (V' : SmallCMLevel D) (hV' : V'.obj.subgroup ≤ V.obj.subgroup)
    [(V'.obj.subgroup.subgroupOf V.obj.subgroup).Normal]
    (T : SmallCMLevel D) (hT : T.obj.subgroup ≤ V.obj.subgroup)
    [(T.obj.subgroup.subgroupOf V.obj.subgroup).Normal]
    (hTV' : T.obj.subgroup ≤ V'.obj.subgroup)
    (hTU' : ∀ x ∈ T.obj.subgroup, b.hom.element⁻¹ * x * b.hom.element ∈ U'.obj.subgroup)
    (M : Action (ModuleCat Rcoeff) (SmallCMResidualGroup D U U'))
    (M' : Action (ModuleCat Rcoeff) (SmallCMResidualGroup D V V'))
    (c₁ c₂ : M.V ⟶ M'.V)
    (hc₁ : ∀ v : V.obj.subgroup,
      M.ρ (QuotientGroup.mk (smallCMTransporterConj D b v)) ≫ c₁ = c₁ ≫ M'.ρ (QuotientGroup.mk v))
    (hc₂ : ∀ v : V.obj.subgroup,
      M.ρ (QuotientGroup.mk (smallCMTransporterConj D b v)) ≫ c₂ = c₂ ≫ M'.ρ (QuotientGroup.mk v))
    (m : ℕ) (e : c₁ = m • c₂)
    (hY' : IsFiniteGeometricTorsor ((schemes).obj V) (normalTorsor V V' hV').val) :
    (transportDatum b φ hφ U' hU' V' hV' T hT hTV' hTU' M M' c₁ hc₁).sheafMap hY' =
      m • (transportDatum b φ hφ U' hU' V' hV' T hT hTV' hTU' M M' c₂ hc₂).sheafMap hY' :=
  EtaleTransportDatum.sheafMap_eq_nsmul_of_refines
    (transportDatum b φ hφ U' hU' V' hV' T hT hTV' hTU' M M' c₁ hc₁)
    (transportDatum b φ hφ U' hU' V' hV' T hT hTV' hTU' M M' c₂ hc₂) hY' (𝟙 _)
    (Category.id_comp _) (Category.id_comp _) m e

/-- Shifting both exponents of a morphism of scaled levels by `k₀` does not change its transport
maps. -/
theorem cmHarrisTransportSheafMap_shift {X Y : CMScaledLevel D ρ p} (f : X ⟶ Y) (k₀ : ℕ)
    {k' k : ℕ} (hk : k' ≤ k) (φ : (schemes).obj X.level ⟶ (schemes).obj Y.level)
    (hφ : φ = (schemes).map (CMScaledLevel.Hom.hom f)) [Etale φ] :
    transportMap (CMScaledLevel.Hom.shift D ρ p f k₀) hk φ hφ = transportMap f hk φ hφ :=
  cmNormalTransportDatum_sheafMap_congr D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality dualityNaturality polarizationStability
    compatibility h htor q existence geometry hRigid p (CMScaledLevel.Hom.hom f) φ hφ
    (coeffLevel Y.level k) (cmHarrisCoefficientLevel_le D ρ p Y.level ℓ hℓ k)
    (coeffLevel X.level k') (cmHarrisCoefficientLevel_le D ρ p X.level ℓ hℓ k')
    (cmScaledTransportLevel D p ρ f k' k) (cmScaledTransportLevel_le D p ρ f k' k)
    (cmScaledTransportLevel_le_coeff D p ρ f k' k) (cmScaledTransportLevel_conj D p ρ f k' k)
    ((coefficients Y.level).action (op k)) ((coefficients X.level).action (op k'))
    (cmHarrisTorsionTransport D ρ p (CMScaledLevel.Hom.shift D ρ p f k₀) hk)
    (cmHarrisTorsionTransport D ρ p f hk)
    (fun v => cmHarrisTorsionTransport_comm D ρ p (CMScaledLevel.Hom.shift D ρ p f k₀) hk v
      (smallCMTransporterConj D (CMScaledLevel.Hom.hom f) v) rfl)
    (fun v => cmHarrisTorsionTransport_comm D ρ p f hk v
      (smallCMTransporterConj D (CMScaledLevel.Hom.hom f) v) rfl)
    (cmHarrisTorsionTransport_shift D p ρ f k₀ hk) _

/-- Along a scheme map equal to the identity, the transport map of the raise of the exponent of a
level `U` from `n` to `n' ≥ n` is `ℓ ^ (n' - n)` times the identification of the restriction
along the identity followed by the transition of the coefficient system of `U` from stage `k` to
stage `k'`; here `ℓ` is the coefficient prime. -/
theorem cmHarrisTransportSheafMap_raise (U : SmallCMLevel D) {n n' : ℕ} (hn : n ≤ n')
    {k' k : ℕ} (hk : k' ≤ k) (φ : (schemes).obj U ⟶ (schemes).obj U)
    (hφ : φ = (schemes).map (CMScaledLevel.Hom.hom (CMScaledLevel.raise D ρ p U hn)))
    [Etale φ] (e : φ = 𝟙 _) :
    transportMap (CMScaledLevel.raise D ρ p U hn) hk φ hφ =
      (ℓ ^ (n' - n)) • stageMap U hk φ e := by
  have hφ₀ : φ = (schemes).map (CMScaledLevel.Hom.hom (𝟙 (⟨U, n⟩ : CMScaledLevel D ρ p))) := hφ
  have := cmScaledTransportLevel_normal D p ρ (CMScaledLevel.raise D ρ p U hn) k' k
  have h1 := cmNormalTransportDatum_sheafMap_nsmul D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor q existence geometry hRigid p
    (CMScaledLevel.Hom.hom (CMScaledLevel.raise D ρ p U hn)) φ hφ
    (coeffLevel U k) (cmHarrisCoefficientLevel_le D ρ p U ℓ hℓ k)
    (coeffLevel U k') (cmHarrisCoefficientLevel_le D ρ p U ℓ hℓ k')
    (cmScaledTransportLevel D p ρ (CMScaledLevel.raise D ρ p U hn) k' k)
    (cmScaledTransportLevel_le D p ρ (CMScaledLevel.raise D ρ p U hn) k' k)
    (cmScaledTransportLevel_le_coeff D p ρ (CMScaledLevel.raise D ρ p U hn) k' k)
    (cmScaledTransportLevel_conj D p ρ (CMScaledLevel.raise D ρ p U hn) k' k)
    ((coefficients U).action (op k)) ((coefficients U).action (op k'))
    (cmHarrisTorsionTransport D ρ p (CMScaledLevel.raise D ρ p U hn) hk)
    (cmHarrisTorsionTransport D ρ p (𝟙 (⟨U, n⟩ : CMScaledLevel D ρ p)) hk)
    (fun v => cmHarrisTorsionTransport_comm D ρ p (CMScaledLevel.raise D ρ p U hn) hk v
      (smallCMTransporterConj D (CMScaledLevel.Hom.hom (CMScaledLevel.raise D ρ p U hn)) v) rfl)
    (fun v => cmHarrisTorsionTransport_comm D ρ p (𝟙 (⟨U, n⟩ : CMScaledLevel D ρ p)) hk v
      (smallCMTransporterConj D (CMScaledLevel.Hom.hom (CMScaledLevel.raise D ρ p U hn)) v) rfl)
    (ℓ ^ (n' - n)) (by rw [cmHarrisTorsionTransport_raise, cmHarrisTorsionTransport_id])
    (normalTorsor U (coeffLevel U k') (cmHarrisCoefficientLevel_le D ρ p U ℓ hℓ k')).property
  have h2 := cmHarrisTransportSheafMap_id_le D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor q existence geometry hRigid p ρ ⟨U, n⟩ hk φ hφ₀ e
  exact h1.trans (congrArg (fun x => (ℓ ^ (n' - n)) • x) h2)

/-! ## Transporters by elements of the level -/

omit [Module.Finite ℚ A] in
/-- The scheme map of a transporter `U ⟶ U` whose translating element lies in the level `U` is
the identity. -/
theorem cmSchemeTower_map_eq_id_of_mem {U : SmallCMLevel D} (b : U ⟶ U)
    (hb : b.hom.element ∈ U.obj.subgroup) : (schemes).map b = 𝟙 _ :=
  representedCMSchemeTower_map_eq_id_of_mem D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor _ b hb

omit [Module.Finite ℚ A] in
/-- The map of the common cover of a transport datum to the target torsor is the tower map of the
inclusion `T ≤ V'`. -/
theorem cmNormalTransportDatum_toTarget_left {V U : SmallCMLevel D} (b : V ⟶ U)
    (φ : (schemes).obj V ⟶ (schemes).obj U) (hφ : φ = (schemes).map b) [Etale φ]
    (U' : SmallCMLevel D) (hU' : U'.obj.subgroup ≤ U.obj.subgroup)
    [(U'.obj.subgroup.subgroupOf U.obj.subgroup).Normal]
    (V' : SmallCMLevel D) (hV' : V'.obj.subgroup ≤ V.obj.subgroup)
    [(V'.obj.subgroup.subgroupOf V.obj.subgroup).Normal]
    (T : SmallCMLevel D) (hT : T.obj.subgroup ≤ V.obj.subgroup)
    [(T.obj.subgroup.subgroupOf V.obj.subgroup).Normal]
    (hTV' : T.obj.subgroup ≤ V'.obj.subgroup)
    (hTU' : ∀ x ∈ T.obj.subgroup, b.hom.element⁻¹ * x * b.hom.element ∈ U'.obj.subgroup)
    (M : Action (ModuleCat Rcoeff) (SmallCMResidualGroup D U U'))
    (M' : Action (ModuleCat Rcoeff) (SmallCMResidualGroup D V V'))
    (c : M.V ⟶ M'.V)
    (hc : ∀ v : V.obj.subgroup,
      M.ρ (QuotientGroup.mk (smallCMTransporterConj D b v)) ≫ c = c ≫ M'.ρ (QuotientGroup.mk v)) :
    (transportDatum b φ hφ U' hU' V' hV' T hT hTV' hTU' M M' c hc).toTarget.left =
      (schemes).map (smallCMInclusion D hTV') :=
  rfl

omit [Module.Finite ℚ A] in
/-- Two transport data along transporters `b₁ b₂ : U ⟶ U` of a small CM level to itself, with
the same scheme map, levels, common level and coefficient modules, have the same transport map
when the translating element of `b₂` is that of `b₁` times an element `w` of the level and the
coefficient map of `b₂` is the action of the class of `w` followed by the coefficient map of
`b₁`. -/
theorem cmNormalTransportDatum_sheafMap_eq_of_mul {U : SmallCMLevel D} (b₁ b₂ : U ⟶ U)
    (φ : (schemes).obj U ⟶ (schemes).obj U) (hφ₁ : φ = (schemes).map b₁)
    (hφ₂ : φ = (schemes).map b₂) [Etale φ]
    (U' : SmallCMLevel D) (hU' : U'.obj.subgroup ≤ U.obj.subgroup)
    [(U'.obj.subgroup.subgroupOf U.obj.subgroup).Normal]
    (V' : SmallCMLevel D) (hV' : V'.obj.subgroup ≤ U.obj.subgroup)
    [(V'.obj.subgroup.subgroupOf U.obj.subgroup).Normal]
    (T : SmallCMLevel D) (hT : T.obj.subgroup ≤ U.obj.subgroup)
    [(T.obj.subgroup.subgroupOf U.obj.subgroup).Normal]
    (hTV' : T.obj.subgroup ≤ V'.obj.subgroup)
    (hTU'₁ : ∀ x ∈ T.obj.subgroup, b₁.hom.element⁻¹ * x * b₁.hom.element ∈ U'.obj.subgroup)
    (hTU'₂ : ∀ x ∈ T.obj.subgroup, b₂.hom.element⁻¹ * x * b₂.hom.element ∈ U'.obj.subgroup)
    (M : Action (ModuleCat Rcoeff) (SmallCMResidualGroup D U U'))
    (M' : Action (ModuleCat Rcoeff) (SmallCMResidualGroup D U V'))
    (c₁ c₂ : M.V ⟶ M'.V)
    (hc₁ : ∀ v : U.obj.subgroup,
      M.ρ (QuotientGroup.mk (smallCMTransporterConj D b₁ v)) ≫ c₁ = c₁ ≫ M'.ρ (QuotientGroup.mk v))
    (hc₂ : ∀ v : U.obj.subgroup,
      M.ρ (QuotientGroup.mk (smallCMTransporterConj D b₂ v)) ≫ c₂ = c₂ ≫ M'.ρ (QuotientGroup.mk v))
    (w : U.obj.subgroup)
    (hw : b₂.hom.element = b₁.hom.element * (w : D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ))
    (hc : c₂ = M.ρ (QuotientGroup.mk w) ≫ c₁)
    (hY' : IsFiniteGeometricTorsor ((schemes).obj U) (normalTorsor U V' hV').val) :
    (transportDatum b₂ φ hφ₂ U' hU' V' hV' T hT hTV' hTU'₂ M M' c₂ hc₂).sheafMap hY' =
      (transportDatum b₁ φ hφ₁ U' hU' V' hV' T hT hTV' hTU'₁ M M' c₁ hc₁).sheafMap hY' := by
  refine EtaleTransportDatum.sheafMap_eq_of_twist
    (transportDatum b₁ φ hφ₁ U' hU' V' hV' T hT hTV' hTU'₁ M M' c₁ hc₁)
    (transportDatum b₂ φ hφ₂ U' hU' V' hV' T hT hTV' hTU'₂ M M' c₂ hc₂) hY' (𝟙 _)
    (QuotientGroup.mk w⁻¹) ?_ ?_ ?_
  · rw [Category.id_comp]
    apply etaleObjectPullback_hom_ext
    change (cmNormalTransportToSource D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q existence geometry hRigid b₂ φ hφ₂ U' hU' T
        hT hTU'₂).left ≫ pullback.fst _ _ =
      ((cmNormalTransportToSource D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor q existence geometry hRigid b₁ φ hφ₁ U' hU' T
        hT hTU'₁) ≫ ((etaleTorsorPullbackFunctor φ (SmallCMResidualGroup D U U')).obj
          (normalTorsor U U' hU').val).ρ (QuotientGroup.mk w⁻¹)).left ≫ pullback.fst _ _
    rw [MorphismProperty.Comma.comp_left, Category.assoc, etaleTorsorPullbackFunctor_ρ_fst,
      cmNormalTransportToSource_fst, cmNormalTransportToSource_fst_assoc]
    change (schemes).map (smallCMTransporterRestrict D b₂ T U' hTU'₂) =
      (schemes).map (smallCMTransporterRestrict D b₁ T U' hTU'₁) ≫
        (schemes).map (smallCMNormalInverseArrow D U U' hU' w⁻¹)
    rw [← Functor.map_comp]
    congr 1
    apply ObjectProperty.hom_ext
    apply CompactOpenLevel.Arrow.ext
    change b₂.hom.element = b₁.hom.element *
      ((w⁻¹ : U.obj.subgroup) : D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ)⁻¹
    rw [hw]
    simp
  · rw [Category.id_comp]
    apply MorphismProperty.Over.Hom.ext
    rw [cmNormalTransportDatum_toTarget_left, cmNormalTransportDatum_toTarget_left]
  · change c₂ = M.ρ (QuotientGroup.mk w⁻¹)⁻¹ ≫ c₁
    rw [← QuotientGroup.mk_inv, inv_inv]
    exact hc

/-- Along a scheme map equal to the identity, the transport map of a morphism `f : Y ⟶ Y` of
scaled levels whose translating element lies in the level of `Y` is the identification of the
restriction along the identity followed by the transition of the coefficient system of the level
from stage `k` to stage `k'`. -/
theorem cmHarrisTransportSheafMap_eq_of_mem (Y : CMScaledLevel D ρ p) (f : Y ⟶ Y)
    (hf : (CMScaledLevel.Hom.hom f).hom.element ∈ Y.level.obj.subgroup) {k' k : ℕ}
    (hk : k' ≤ k) (φ : (schemes).obj Y.level ⟶ (schemes).obj Y.level)
    (hφ : φ = (schemes).map (CMScaledLevel.Hom.hom f)) [Etale φ] (e : φ = 𝟙 _) :
    transportMap f hk φ hφ = stageMap Y.level hk φ e := by
  have hφ₁ : φ = (schemes).map (CMScaledLevel.Hom.hom (𝟙 Y)) :=
    e.trans (CategoryTheory.Functor.map_id _ _).symm
  have hT₁ : (cmScaledTransportLevel D p ρ (𝟙 Y) k' k).obj.subgroup ≤
      (cmScaledTransportLevel D p ρ f k' k).obj.subgroup := by
    intro x hx
    rw [mem_cmScaledTransportLevel] at hx ⊢
    refine ⟨hx.1, ?_⟩
    have hx2 : x ∈ (coeffLevel Y.level k).obj.subgroup := by simpa using hx.2
    have hN := (cmHarrisCoefficientLevel_normal D ρ p Y.level ℓ hℓ k).conj_mem
      ⟨x, cmHarrisCoefficientLevel_le D ρ p Y.level ℓ hℓ k hx2⟩
      (by rw [Subgroup.mem_subgroupOf]; exact hx2) ⟨_, Y.level.obj.subgroup.inv_mem hf⟩
    rw [Subgroup.mem_subgroupOf] at hN
    simpa using hN
  have hTU'f : ∀ x ∈ (cmScaledTransportLevel D p ρ (𝟙 Y) k' k).obj.subgroup,
      (CMScaledLevel.Hom.hom f).hom.element⁻¹ * x * (CMScaledLevel.Hom.hom f).hom.element ∈
        (coeffLevel Y.level k).obj.subgroup :=
    fun x hx => ((mem_cmScaledTransportLevel D p ρ f k' k x).1 (hT₁ hx)).2
  have h1 := cmHarrisTransportDatumAt_sheafMap_eq D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor q existence geometry hRigid p ρ f hk φ hφ
    (cmScaledTransportLevel D p ρ (𝟙 Y) k' k) (cmScaledTransportLevel_le D p ρ (𝟙 Y) k' k)
    (cmScaledTransportLevel_le_coeff D p ρ (𝟙 Y) k' k) hTU'f
    (cmScaledTransportLevel D p ρ f k' k) (cmScaledTransportLevel_le D p ρ f k' k)
    (cmScaledTransportLevel_le_coeff D p ρ f k' k) (cmScaledTransportLevel_conj D p ρ f k' k) hT₁
  have hc : cmHarrisTorsionTransport D ρ p f hk =
      ((coefficients Y.level).action (op k)).ρ (QuotientGroup.mk ⟨_, hf⟩) ≫
        cmHarrisTorsionTransport D ρ p (𝟙 Y) hk := by
    ext x
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    change (cmHarrisTorsionTransport D ρ p f hk).hom (Submodule.Quotient.mk a) =
      (cmHarrisTorsionTransport D ρ p (𝟙 Y) hk).hom
        (((coefficients Y.level).ρ (op k) (QuotientGroup.mk ⟨_, hf⟩)).hom
          (Submodule.Quotient.mk a))
    rw [cmHarrisCoefficientDiagram_action_mk, cmHarrisTorsionTransport_mk,
      cmHarrisTorsionTransport_mk, cmHarrisLatticeTransport_id]
    congr 1
    apply Subtype.ext
    rw [cmHarrisLatticeTransport_coe, Nat.sub_self, pow_zero, one_smul]
    rfl
  have h2 := cmNormalTransportDatum_sheafMap_eq_of_mul D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q existence geometry hRigid p
    (CMScaledLevel.Hom.hom (𝟙 Y)) (CMScaledLevel.Hom.hom f) φ hφ₁ hφ
    (coeffLevel Y.level k) (cmHarrisCoefficientLevel_le D ρ p Y.level ℓ hℓ k)
    (coeffLevel Y.level k') (cmHarrisCoefficientLevel_le D ρ p Y.level ℓ hℓ k')
    (cmScaledTransportLevel D p ρ (𝟙 Y) k' k) (cmScaledTransportLevel_le D p ρ (𝟙 Y) k' k)
    (cmScaledTransportLevel_le_coeff D p ρ (𝟙 Y) k' k)
    (cmScaledTransportLevel_conj D p ρ (𝟙 Y) k' k) hTU'f
    ((coefficients Y.level).action (op k)) ((coefficients Y.level).action (op k'))
    (cmHarrisTorsionTransport D ρ p (𝟙 Y) hk) (cmHarrisTorsionTransport D ρ p f hk)
    (fun v => cmHarrisTorsionTransport_comm D ρ p (𝟙 Y) hk v
      (smallCMTransporterConj D (CMScaledLevel.Hom.hom (𝟙 Y)) v) rfl)
    (fun v => cmHarrisTorsionTransport_comm D ρ p f hk v
      (smallCMTransporterConj D (CMScaledLevel.Hom.hom f) v) rfl)
    ⟨_, hf⟩ (one_mul _).symm hc
    (normalTorsor Y.level (coeffLevel Y.level k')
      (cmHarrisCoefficientLevel_le D ρ p Y.level ℓ hℓ k')).property
  exact h1.symm.trans (h2.trans (cmHarrisTransportSheafMap_id_le D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q existence geometry hRigid p ρ
    Y hk φ hφ₁ e))

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
