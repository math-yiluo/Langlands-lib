import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakExpansionFactorNaturality
import Langlands.Representation.Plancherel.NormalizedProductCompactTensor

/-! # The signed factors on the compact product charts -/

noncomputable section

set_option maxHeartbeats 700000
set_option quotPrecheck false
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry MeasureTheory
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel Langlands.Induction
open scoped CategoryTheory.MonObj NNReal TensorProduct

namespace Langlands.Plancherel

open Aubert.General Induction

universe uG uV uI

section LinearMaps

variable {V W S T : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup S] [Module ℂ S] [AddCommGroup T] [Module ℂ T]

private theorem compactMap_apply_lift (e : V ≃ₗ[ℂ] S) (f : T ≃ₗ[ℂ] W)
    (A : V →ₗ[ℂ] T) (v : V) :
    (f.toLinearMap ∘ₗ A ∘ₗ e.symm.toLinearMap) (e v) = f (A v) :=
  congrArg (fun y => f (A y)) (e.symm_apply_apply v)

end LinearMaps
end Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz.WeakExpansion


universe u uV

open DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar RationalPointFamily

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {i : T.toGrp ⟶ G} {ν : cocharacterLattice T}

attribute [local instance] cFamilyAmbientAffine cFamilyLeviAffineHom cFamilyLeviAffine cFamilyLeviFiniteType
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsTopologicalGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarLocallyCompactSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology2

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (I I' : Finset (SimpleRoot i ν))
  {ζ : cocharacterLattice T} (hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ)
  {ζ' : cocharacterLattice T} (hζ' : IsStandardCocharacter i ν (rootSet i ν I') ζ')

set_option hygiene false in
local notation "𝐌" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (rootSet i ν I)) x}
set_option hygiene false in
local notation "M₀" => Standard.leviScheme i ν (rootSet i ν I)

set_option hygiene false in
local notation "νM" => leviRationalNormCharacters i ν I
set_option hygiene false in
local notation "ν₀" => fun a => (rationalNormCharacters M₀ a).toMul
set_option hygiene false in
local notation "eM" => leviRationalPointHomeomorph i ν I
set_option hygiene false in
local notation "Φ" => unramifiedCharactersHomeomorph eM ν₀

variable (n : normalizerPoints i)
  (hn : conjugatedLevi i ν (rootSet i ν I) n ≤ standardLevi i ν (rootSet i ν I'))
  (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
  (hCST : CentralSplitTorusCharacterStatement.{u})
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) (K : Subgroup (rationalPoints G)))

set_option hygiene false in
local notation "eₛ" => lowerLeviConjugation i ν (rootSet i ν I) (rootSet i ν I') hG hi hν
  (rootSet_subset i ν I) ζ hζ n hn
set_option hygiene false in
local notation "χs" => lowerCocharacter i ν (rootSet i ν I') ζ n
set_option hygiene false in
local notation "L" => lowerAmbient i ν (rootSet i ν I')
set_option hygiene false in
local notation "dM" => isSemidirectDecomposition_standard hG hi hν (rootSet_subset i ν I)
set_option hygiene false in
local notation "uM" => isClosed_standardUnipotentPoints i ν (rootSet i ν I)
set_option hygiene false in
local notation "pM" => isClosed_standardParabolicPoints_rootSet hG hi hν I
set_option hygiene false in
local notation "fM" => factorization_subtype (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK)
set_option hygiene false in
local notation "rM" => continuous_projection_standard hG hi hν (rootSet_subset i ν I) _
set_option hygiene false in
local notation "cM" => continuous_leviRationalNormCharacters i ν I
set_option hygiene false in
local notation "dL" => decomposition χs
set_option hygiene false in
local notation "uL" => radical_isClosed χs
set_option hygiene false in
local notation "pL" => parabolic_isClosed χs
set_option hygiene false in
local notation "rL" => projection_continuous χs
set_option hygiene false in
local notation "cL" => DynamicInducedOrbit.leviNormCharacters_continuous χs
set_option hygiene false in
local notation "νL" => leviNormCharacters χs
set_option hygiene false in
local notation "σ" => lowerUnramifiedCharacterConjugation hG hi hν I I' hζ n hn
set_option hygiene false in
local notation "α₊" => outerCentralizer_pos hG hi hν I' hζ'
set_option hygiene false in
local notation "α₋" => outerCentralizer_neg hG hi hν I' hζ'
set_option hygiene false in
local notation "X" => unramifiedCharacters ν₀
set_option hygiene false in
local notation "Y" => unramifiedCharacters νM
set_option hygiene false in
local notation "χL" => unramifiedCharacters νL
set_option hygiene false in
local notation "λγ" => ((RationalDynamicSource.gammaReal (CommGroupScheme.groupHom ζ' ≫ i) K hK : ℂ)⁻¹)

variable (A : SmoothRep.{0, u, uV} ℂ 𝐌)

set_option hygiene false in
local notation "Aₛ" => SmoothRep.pullback (eₛ).symm A
set_option hygiene false in
local notation "B(" z ")" => A.twist (z).val.toMonoidHom (unramifiedCharacter_isOpen_ker νM z)
set_option hygiene false in
local notation "Bᵛ(" z ")" => A.contragredient.twist (z).val.toMonoidHom (unramifiedCharacter_isOpen_ker νM z)
set_option hygiene false in
local notation "Bₛ(" z ")" => SmoothRep.pullback (G := 𝐌) (H := levi χs) (eₛ).symm (B(z))
set_option hygiene false in
local notation "Bₛ'(" z ")" => (Aₛ).twist (z).val.toMonoidHom (unramifiedCharacter_isOpen_ker νL z)
set_option hygiene false in
local notation "kₛ(" z ")" => twistPullbackEquiv hG hi hν I I' hζ n hn A z
set_option hygiene false in
local notation "kᵛₛ(" z ")" => twistPullbackEquiv hG hi hν I I' hζ n hn A.contragredient z
set_option hygiene false in
local notation "D" => cDomain hG hi hν I I' hζ hζ' n hn K hK A
set_option hygiene false in
local notation "D₊" => cFactorConvergenceRegion hG hi hν I I' hζ n hn ζ' α₊ K hK A
set_option hygiene false in
local notation "D₋" => cFactorConvergenceRegion hG hi hν I I' hζ n hn (-ζ') α₋ K hK A.contragredient

private def schemeDualTwist (x : X) : ((B(Φ x)).contragredient).representation.Equiv
    (Bᵛ(Φ (x⁻¹))).representation :=
  normalizedDualTwistEquiv νM A (Φ x)

set_option hygiene false in
local notation "dᵛ(" x ")" => schemeDualTwist I A x

/-- Convergence of the negative c-factor in the inverse parameter of the original smooth dual. -/
theorem cFactorDualConvergence (x : X) (hx : Φ x ∈ D) : x⁻¹ ∈ D₋ :=
  (cFactorConverges_iff_of_equiv hG hi hν I I' hζ n hn (-ζ') α₋ K hK (dᵛ(x))).mp hx.2

variable (K' : OpenSubgroup (rationalPoints L)) (hK' : IsCompact (K' : Set (rationalPoints L)))
  (hPK' : ∀ g : rationalPoints L, ∃ p : DynamicOppositeStandardIntertwining.parabolic χs,
    ∃ k : K', g = (p : rationalPoints L) * (k : rationalPoints L))

set_option hygiene false in
local notation "CS" => CompactInductionPicture dM K A
set_option hygiene false in
local notation "CSᵛ" => CompactInductionPicture dM K A.contragredient
set_option hygiene false in
local notation "CT" => CompactInductionPicture dL K' (Aₛ)
set_option hygiene false in
local notation "CTᵛ" => CompactInductionPicture dL K' (SmoothRep.pullback (eₛ).symm A.contragredient)
set_option hygiene false in
local notation "chartS" => normalizedCompactProductChart νM dM K uM pM hK fM cM rM A
set_option hygiene false in
local notation "chartT" => normalizedCompactProductChart νL dL K' uL pL hK' hPK' cL rL (Aₛ)
set_option hygiene false in
local notation "dbase" => SmoothRep.equivOfIso (contragredientPullbackIso (eₛ).symm A).symm

/-- The fixed source tensor chart for the actual c-family. -/
def cCompactSourceChart : CS ⊗[ℂ] CSᵛ ≃ₗ[ℂ] ProductInducedCompactPicture dM K A := chartS 1

/-- The fixed target tensor chart with the lower smooth-dual comparison and the source gamma. -/
def cCompactTargetMap : CT ⊗[ℂ] CTᵛ →ₗ[ℂ] ProductInducedCompactPicture dL K' (Aₛ) :=
  λγ • ((chartT 1).toLinearMap ∘ₗ
    TensorProduct.map LinearMap.id (compactInductionPictureEquiv dL K' dbase).toLinearMap)

set_option hygiene false in
local notation "κS(" z ")" => unramifiedNormalizedInductionCompactEquiv dM K uM pM hK fM νM cM rM z A
set_option hygiene false in
local notation "κSᵛ(" z ")" => normalizedDualCompactEquiv νM dM K uM pM hK fM cM rM A z
set_option hygiene false in
local notation "κT(" z ")" => unramifiedNormalizedInductionCompactEquiv dL K' uL pL hK' hPK' νL cL rL z (Aₛ)
set_option hygiene false in
local notation "κTᵛ(" z ")" => normalizedDualCompactEquiv νL dL K' uL pL hK' hPK' cL rL (Aₛ) z
set_option hygiene false in
local notation "F₊(" z ")" => cFactor hG hi hν I I' hζ n hn ζ' α₊ K hK hCST (B((z).val)) (z).property.1
set_option hygiene false in
local notation "FD(" z ")" => cDualFactor hG hi hν I I' hζ hζ' n hn K hK hCST (B((z).val)) (z).property.2
set_option hygiene false in
local notation "kT(" z ")" => normalizedInductionEquivOfEquiv dL uL (kₛ(z))
set_option hygiene false in
local notation "kTᵛ(" z ")" => normalizedInductionEquivOfEquiv dL uL
  (A := (Bₛ(z)).contragredient) (B := (Bₛ'(σ z)).contragredient) (smoothContragredientEquiv (kₛ(z)).symm)
set_option hygiene false in
local notation "δ" => compactInductionPictureEquiv dL K' dbase
set_option hygiene false in
local notation "κD(" z ")" => unramifiedNormalizedInductionCompactEquiv dL K' uL pL hK' hPK' νL cL rL
  (σ z) (SmoothRep.pullback (eₛ).symm A.contragredient)
set_option hygiene false in
local notation "kD(" z ")" => normalizedInductionEquivOfEquiv dL uL (kᵛₛ(z))
set_option hygiene false in
local notation "δT(" z ")" => normalizedInductionEquivOfEquiv dL uL
  (SmoothRep.equivOfIso (contragredientPullbackIso (eₛ).symm (B(z))).symm)
set_option hygiene false in
local notation "δS(" x ")" => normalizedInductionEquivOfEquiv dM uM (dᵛ(x))
set_option hygiene false in
local notation "δL(" x ")" => normalizedInductionEquivOfEquiv dL uL
  (cFactorLowerInducingEquiv hG hi hν I I' hζ n hn (dᵛ(x)))
set_option hygiene false in
local notation "OutDual(" x ")" => (normalizedInductionFunctor dL uL).obj
  (SmoothRep.pullback (eₛ).symm (B(Φ x)).contragredient)
set_option hygiene false in
local notation "targetDualLeft(" x ")" => (κTᵛ(σ (Φ x))).toLinearMap ∘ₗ
  (kTᵛ(Φ x)).toLinearMap ∘ₗ (δT(Φ x)).toLinearMap
set_option hygiene false in
local notation "targetDualRight(" x ")" => (δ).toLinearMap ∘ₗ (κD(Φ (x⁻¹))).toLinearMap ∘ₗ
  (kD(Φ (x⁻¹))).toLinearMap ∘ₗ (δL(x)).toLinearMap

private theorem compactDualOutput_left_eval (x : X) (f : OutDual(x)) (k : K') (v : A) :
    ((targetDualLeft(x) f).1.1 k).val v = (f.1.1 (k : rationalPoints L)).val v :=
  rfl

private theorem compactDualOutput_right_eval (x : X) (f : OutDual(x)) (k : K') (v : A) :
    ((targetDualRight(x) f).1.1 k).val v = (f.1.1 (k : rationalPoints L)).val v :=
  rfl

private theorem compactDualOutput_eq (x : X) (f : OutDual(x)) :
    targetDualLeft(x) f = targetDualRight(x) f := by
  apply compactPicture_ext
  intro k
  apply Subtype.ext
  apply LinearMap.ext
  intro v
  exact (compactDualOutput_left_eval hG hi hν I I' hζ n hn A K' hK' hPK' x f k v).trans
    (compactDualOutput_right_eval hG hi hν I I' hζ n hn A K' hK' hPK' x f k v).symm

set_option hygiene false in
local notation "Fplus" => cFactorOnCompact hG hi hν I I' hζ n hn ζ' α₊ K hK hPK hCST A K' hK' hPK'
set_option hygiene false in
local notation "Fminus" => cFactorOnCompact hG hi hν I I' hζ n hn (-ζ') α₋ K hK hPK hCST A.contragredient K' hK' hPK'
set_option hygiene false in
local notation "dconv" => cFactorDualConvergence hG hi hν I I' hζ hζ' n hn K hK A
set_option hygiene false in
local notation "κS'(" z ")" => unramifiedNormalizedInductionCompactEquiv dM K uM pM hK fM νM cM rM z A.contragredient
set_option hygiene false in
local notation "F₋(" C "," hC ")" => cFactor hG hi hν I I' hζ n hn (-ζ') α₋ K hK hCST (C) (hC)
set_option hygiene false in
local notation "FS" => cCompactSourceChart hG hi hν I K hK hPK A
set_option hygiene false in
local notation "FT" => cCompactTargetMap hG hi hν I I' hζ (ζ' := ζ') n hn K hK A K' hK' hPK'

set_option maxHeartbeats 1300000 in
/-- The positive compact factor restricts the actual normalized positive output. -/
theorem cFactorPlus_on_lift (x : X) (hx : Φ x ∈ D)
    (f : (normalizedInductionFunctor dM uM).obj (B(Φ x))) :
    Fplus ⟨x, hx.1⟩ (κS(Φ x) f) = κT(σ (Φ x)) (kT(Φ x) (F₊((⟨Φ x, hx⟩ : D)) f)) :=
  compactMap_apply_lift (κS(Φ x)).toLinearEquiv (κT(σ (Φ x))).toLinearEquiv
    ((kT(Φ x)).toLinearMap ∘ₗ F₊((⟨Φ x, hx⟩ : D))) f

set_option maxHeartbeats 1300000 in
/-- The negative compact factor gives the actual dual normalized output after the fixed
lower dual comparison. Its source is the inverse twist of the original dual. -/
theorem cFactorMinus_on_lift (x : X) (hx : Φ x ∈ D)
    (g : (normalizedInductionFunctor dM uM).obj (B(Φ x)).contragredient) :
    δ (Fminus ⟨x⁻¹, dconv x hx⟩ (κSᵛ(Φ x) g)) =
      κTᵛ(σ (Φ x)) (kTᵛ(Φ x) (FD((⟨Φ x, hx⟩ : D)) g)) := by
  let hneg := dconv x hx
  let w := Φ (x⁻¹)
  let u := δS(x) g
  let J := F₋(Bᵛ(w), hneg)
  let T := F₋((B(Φ x)).contragredient, hx.2) g
  have hN : J u = δL(x) T :=
    cFactor_natural hG hi hν I I' hζ n hn (-ζ') α₋ K hK hCST (dᵛ(x)) hx.2 hneg g
  have h₁ := compactMap_apply_lift (κS'(w)).toLinearEquiv (κD(w)).toLinearEquiv
    ((kD(w)).toLinearMap ∘ₗ J) u
  have h₂ := congrArg (fun l => δ l) h₁
  have h₃ := congrArg (fun t => δ (κD(w) (kD(w) t))) hN
  have h₄ := compactDualOutput_eq hG hi hν I I' hζ n hn A K' hK' hPK' x T
  exact h₂.trans (h₃.trans h₄.symm)

/-- On pure tensors the lower chart applies the fixed smooth-dual comparison and gamma. -/
theorem cCompactTargetMap_tmul (v : CT) (w : CTᵛ) :
    FT (v ⊗ₜ[ℂ] w) = λγ • chartT 1 (v ⊗ₜ[ℂ] δ w) :=
  by
    simp only [cCompactTargetMap, LinearMap.smul_apply, LinearMap.comp_apply,
      TensorProduct.map_tmul, LinearMap.id_apply, LinearEquiv.coe_coe,
      Representation.Equiv.coe_toLinearMap]

end Langlands.HarishChandraSchwartz.WeakExpansion
