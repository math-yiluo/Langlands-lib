import Langlands.Representation.Plancherel.DynamicCommonLeviReindex

/-! # Compact standard operators with another common-Levi base cocharacter -/

noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option quotPrecheck false
set_option hygiene false

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel.StandardIntertwining

open Aubert.General Induction DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar
open DynamicCommonLeviComposition DynamicCommonLeviCompact ActualCommonLeviTensor

universe u uV

attribute [local instance]
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsAffine
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsTopologicalGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarLocallyCompactSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup
  DynamicOppositeCanonicalScalar.centralizerClosedImmersion
  DynamicOppositeCanonicalScalar.centralizerAffine
  DynamicOppositeCanonicalScalar.centralizerFiniteType
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup2
  DynamicCommonLeviContinuation.radicalMeasurable DynamicCommonLeviContinuation.radicalBorel
  DynamicCommonLeviContinuation.intersectionMeasurable DynamicCommonLeviContinuation.intersectionBorel
  DynamicCommonLeviContinuation.quotientMeasurable DynamicCommonLeviContinuation.quotientBorel

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (χ ξ x y : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hξ : Dynamic.centralizer ξ = Dynamic.centralizer χ)
  (hx : Dynamic.centralizer x = Dynamic.centralizer χ)
  (hy : Dynamic.centralizer y = Dynamic.centralizer χ)
  (hG : IsConnectedReductive G)
  (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
  (hxK : ∀ g : rationalPoints G, ∃ p : parabolic x, ∃ k : K, g = (p : rationalPoints G) * (k : rationalPoints G))
  (hyK : ∀ g : rationalPoints G, ∃ p : parabolic y, ∃ k : K, g = (p : rationalPoints G) * (k : rationalPoints G))

local notation "Gpt" => rationalPoints G
local notation "e" => leviChange ξ χ hξ.symm
local notation "hM" => congrArg (fun C : SubgroupFunctor G => C.carrier (Over.mk (𝟙 (Spec (CommRingCat.of F))))) hξ
local notation "he" => leviChange_apply_coe ξ χ hξ.symm
local notation "ep" => parameterChangeIso ξ χ hξ.symm
local notation "τ" => rationalUnramifiedCharacterRestrict (ep).hom
local notation "X" => unramifiedCharacters (normCharacters χ)

omit [LocallyOfFiniteType G.X.hom] in
private theorem parameterTransport_apply (ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (z : unramifiedCharacters (normCharacters ψ)) (m : levi ψ) :
    (parameterTransport ψ z).val m = z.val ((parameterHomeomorph ψ).symm m) := rfl

omit [LocallyOfFiniteType G.X.hom] [ValuativeRel F] [IsNonarchimedeanLocalField F] in
private theorem parameterChangeIso_inversePoint (m : levi ξ) :
    rationalPoints.map (ep).hom ((parameterHomeomorph ξ).symm m) =
      (parameterHomeomorph χ).symm ((e) m) := by
  apply (parameterHomeomorph χ).injective
  rw [ContinuousMulEquiv.apply_symm_apply, parameterHomeomorph_parameterChangeIso,
    ContinuousMulEquiv.apply_symm_apply]

omit [LocallyOfFiniteType G.X.hom] in
/-- The actual character is reindexed by the identity of the literal Levi. -/
theorem parameterTransport_changeLevi (z : X) (m : levi ξ) :
    (parameterTransport ξ ((τ) z)).val m = (parameterTransport χ z).val ((e) m) := by
  have hr : ((τ) z).val ((parameterHomeomorph ξ).symm m) =
      z.val (rationalPoints.map (ep).hom ((parameterHomeomorph ξ).symm m)) :=
    rationalUnramifiedCharacterRestrict_apply (ep).hom z ((parameterHomeomorph ξ).symm m)
  have hp : z.val (rationalPoints.map (ep).hom ((parameterHomeomorph ξ).symm m)) =
      z.val ((parameterHomeomorph χ).symm ((e) m)) :=
    congrArg z.val (parameterChangeIso_inversePoint χ ξ hξ m)
  exact (parameterTransport_apply ξ ((τ) z) m).trans
    (hr.trans (hp.trans (parameterTransport_apply χ z ((e) m)).symm))

variable (A : SmoothRep.{0, u, uV} ℂ (levi χ)) (B : SmoothRep.{0, u, uV} ℂ (levi ξ))
  (eB : (SmoothRep.pullback (e) A).representation.Equiv B.representation)

local notation "hx'" => hx.trans hξ.symm
local notation "hy'" => hy.trans hξ.symm
local notation "d₀" => commonDecomposition χ x hx
local notation "d₁" => commonDecomposition χ y hy
local notation "d₀'" => commonDecomposition ξ x hx'
local notation "d₁'" => commonDecomposition ξ y hy'
local notation "u₀" => radical_isClosed x
local notation "u₁" => radical_isClosed y
local notation "q" => pairQuotientMeasure K hK x y
local notation "V₀" => CompactInductionPicture d₀ K A
local notation "V₁" => CompactInductionPicture d₁ K A
local notation "W₀" => CompactInductionPicture d₀' K B
local notation "W₁" => CompactInductionPicture d₁' K B
local notation "Az" z => twistObject χ z A
local notation "Bz" z => twistObject ξ ((τ) z) B
local notation "eBz" z => realizedTwistCoefficientEquiv χ ξ e A B eB τ (parameterTransport_changeLevi χ ξ hξ) z

/-- The compact coordinate change for a fixed parabolic with the common Levi. -/
def commonLeviCompactReindex : V₀ ≃ₗ[ℂ] W₀ :=
  compactPictureReindex hM e he A B eB d₀ d₀' K

include eB in
/-- The full-domain condition depends on the actual ordered pair and its
inducing representation, and is invariant under this change of coordinates. -/
theorem commonLeviFullDomain_reindex (z : X) :
    z ∈ pairFullDomainRegion χ K hK x hx y A ↔ (τ) z ∈ pairFullDomainRegion ξ K hK x hx' y B :=
  domain_eq_top_reindex hM e he (Az z) (Bz z) (eBz z) d₀ d₀' u₀ q

variable (sq : SquaredModulusCompatibility d₀ u₀ d₁ u₁)
  (sq' : SquaredModulusCompatibility d₀' u₀ d₁' u₁)

local notation "r₀" => commonLeviCompactReindex χ ξ x hξ hx K A B eB
local notation "r₁" => commonLeviCompactReindex χ ξ y hξ hy K A B eB
local notation "U" => pairFullDomainRegion χ K hK x hx y A
local notation "U'" => pairFullDomainRegion ξ K hK x hx' y B
local notation "F₀" => compactFamily χ hG K hK x hx hxK y hy hyK sq A
local notation "F₁" => compactFamily ξ hG K hK x hx' hxK y hy' hyK sq' B

set_option backward.isDefEq.respectTransparency.types false in
/-- In the fixed compact pictures, the two actual weak integrals commute
with the fixed Levi reindexing. Their quotient Haar measure is identical. -/
theorem commonLeviCompactFamily_reindex (z : U) (hz : (τ) z.val ∈ U') :
    (F₁ ⟨(τ) z.val, hz⟩).comp (r₀).toLinearMap = (r₁).toLinearMap.comp (F₀ z) :=
  compactIntegral_reindex_square hM e he A B eB d₀ d₀' K u₀ q d₁ d₁' u₁ (levi_isClosed χ)
    (Az z.val) (Bz z.val) (eBz z.val) (LinearEquiv.refl ℂ A) (LinearEquiv.refl ℂ B) (fun _ => rfl)
    (compactEquiv χ hG K hK x hx hxK z.val A) (compactEquiv χ hG K hK y hy hyK z.val A)
    (compactEquiv ξ hG K hK x hx' hxK ((τ) z.val) B) (compactEquiv ξ hG K hK y hy' hyK ((τ) z.val) B)
    (compactEquiv_eval χ hG K hK x hx hxK z.val A) (compactEquiv_eval χ hG K hK y hy hyK z.val A)
    (compactEquiv_eval ξ hG K hK x hx' hxK ((τ) z.val) B)
    (compactEquiv_eval ξ hG K hK y hy' hyK ((τ) z.val) B)
    (F₀ z) (F₁ ⟨(τ) z.val, hz⟩)
    (compactFamily_spec χ hG K hK x hx hxK y hy hyK sq A z)
    (compactFamily_spec ξ hG K hK x hx' hxK y hy' hyK sq' B ⟨(τ) z.val, hz⟩)

end Langlands.Plancherel.StandardIntertwining
