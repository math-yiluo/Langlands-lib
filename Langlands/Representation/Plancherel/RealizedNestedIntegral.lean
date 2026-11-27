import Langlands.Representation.Plancherel.RealizedNestedQuotientMeasure
import Langlands.Representation.Plancherel.NestedStandardIntertwiningStages
import Langlands.Representation.Plancherel.StandardIntertwiningMeasure

/-! # Weak integral restriction to a represented intermediate Levi -/

noncomputable section

set_option maxHeartbeats 3200000
set_option maxRecDepth 4096
set_option quotPrecheck false
set_option hygiene false

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj NNReal TensorProduct
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel.StandardIntertwining

open Aubert.General Induction
open DynamicOppositeStandardIntertwining DynamicCommonLeviComposition DynamicCommonLeviCompact
open DynamicCommonLeviContinuation DynamicOppositeCanonicalScalar
open QuotientIntegration

attribute [local instance]
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningIsAffine
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningT2Space
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningIsTopologicalGroup
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningT2Space2
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningLocallyCompactSpace
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningNonarchimedeanGroup
  DynamicOppositeStandardIntertwining.centralizerClosedImmersion
  DynamicOppositeStandardIntertwining.centralizerAffine
  DynamicOppositeCanonicalScalar.centralizerFiniteType
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology2
  DynamicCommonLeviContinuation.radicalMeasurable DynamicCommonLeviContinuation.radicalBorel
  DynamicCommonLeviContinuation.intersectionMeasurable DynamicCommonLeviContinuation.intersectionBorel
  DynamicCommonLeviContinuation.quotientMeasurable DynamicCommonLeviContinuation.quotientBorel

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G L : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  [IsAffineHom L.X.hom] [LocallyOfFiniteType L.X.hom]
  (o : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (j : L ⟶ G) (hj : (Dynamic.centralizer o).IsRepresentedBy j) (hjc : IsClosedSubgroup j)
  (x y : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (a b : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ L)
  (hx : Dynamic.parabolic x = Dynamic.extendFromCentralizer o j hj (Dynamic.parabolic a) ∧
    Dynamic.centralizer x = (Dynamic.centralizer a).map j ∧
    Dynamic.unipotent x = Dynamic.extendFromCentralizer o j hj (Dynamic.unipotent a))
  (hy : Dynamic.parabolic y = Dynamic.extendFromCentralizer o j hj (Dynamic.parabolic b) ∧
    Dynamic.centralizer y = (Dynamic.centralizer b).map j ∧
    Dynamic.unipotent y = Dynamic.extendFromCentralizer o j hj (Dynamic.unipotent b))

local notation "e" => RepresentedDynamicTransport.pointEquiv F (Dynamic.centralizer o) j hj hjc
local notation "QG" => QuotientSpace (U := radical x) (radical y)
local notation "QL" => QuotientSpace (U := radical a) (radical b)
local notation "E" => realizedNestedQuotientHomeomorph o j hj hjc x y a b hx hy
local notation "P" => parabolic x
local notation "P'" => parabolic a
local notation "du" => radical_isClosed x
local notation "du'" => radical_isClosed a
local notation "c" => HaarModulus.closedHalfCharacter (radical o) (radical_isClosed o)
  (levi o) (decomposition o).levi_le_normalizer

variable {M : Subgroup (rationalPoints G)} {M' : Subgroup (rationalPoints L)}
  (d : IsSemidirectDecomposition (parabolic x) M (radical x))
  (d' : IsSemidirectDecomposition (parabolic a) M' (radical a))
  (A : SmoothRep.{0, u, uV} ℂ M) (eM : M' ≃ₜ* M) (muG : Measure QG)

local notation "Al" => SmoothRep.pullback eM A
local notation "I" => (DynamicNormalization.leviTwistedInductionFunctor d du).obj A
local notation "Il" => (DynamicNormalization.leviTwistedInductionFunctor d' du').obj Al
local notation "rhoG" => leviInflatedInducingRepresentation d du A
local notation "rhoL" => leviInflatedInducingRepresentation d' du' Al

/-- The lower section obtained by evaluating the ambient stages restriction
at an outer argument. Both sections use the Levi-inflated normalization. -/
def RealizedRestrictionFormula (f : I) (g : rationalPoints G) (fl : Il) : Prop :=
  ∀ l : rationalPoints L,
    eval P' rhoL fl l = (↑(c (e l))⁻¹ : ℂ) • eval P rhoG f ((e l : rationalPoints G) * g)

set_option backward.isDefEq.respectTransparency.types false in
/-- Weak standard integration commutes with evaluation through an actual
represented intermediate Levi, with the pushforward of the exact ambient measure. -/
theorem HasIntegral.realized_restriction
    (hlim : Jacquet.Localization.IsLimitOfCompactSubgroups (radical y))
    {f : I} {J : rationalPoints G → A} (hf : HasIntegral d du (radical y) A muG f J)
    (g : rationalPoints G) (fl : Il) (hfl : RealizedRestrictionFormula o j hj hjc x a d d' A eM f g fl) :
    HasIntegral d' du' (radical b) Al (muG.map E) fl
      (fun l => (↑(c (e l))⁻¹ : ℂ) • J ((e l : rationalPoints G) * g)) := by
  intro l
  let w := (e l : rationalPoints G) * g
  let v := (↑(c (e l))⁻¹ : ℂ) • J w
  let flint := integrand d' du' (radical b) Al l fl
  change HarmonicAnalysis.SmoothWeakIntegral.HasIntegral
    (A.representation.comp eM.toMonoidHom) (muG.map E) flint v
  refine (HarmonicAnalysis.SmoothWeakIntegral.hasIntegral_comp_continuousMulEquiv_iff
    A.representation eM (muG.map E) flint v).mpr ?_
  refine (HarmonicAnalysis.SmoothWeakIntegral.hasIntegral_map_equiv_iff
    (ρ := A.representation) (E).toMeasurableEquiv muG flint v).mpr ?_
  have heq : (fun q : QG => flint ((E).toMeasurableEquiv q)) =
      (↑(c (e l))⁻¹ : ℂ) • integrand d du (radical y) A w f := by
    funext q
    obtain ⟨u, rfl⟩ := (E).symm.surjective q
    change flint ((E) ((E).symm u)) = _
    rw [Homeomorph.apply_symm_apply]
    induction u using Quotient.inductionOn with
    | h u =>
      obtain ⟨r, hr, hrep⟩ := exists_realizedNestedQuotient_representative o j hj hjc x y a b hx hy u
      let so : (radical y).subgroupOf (levi o) := ⟨e (u : rationalPoints L), by
        change ((e (u : rationalPoints L)) : rationalPoints G) ∈ radical y
        rw [← hr]
        exact r.property⟩
      have h0 : c (e (u : rationalPoints L)) = 1 :=
        outerHalfCharacter_one_on_innerTargetRadical (decomposition o) (radical_isClosed o)
          ((decomposition y).unipotent_le.trans
            (Dynamic.realized_parabolic_le o j hj b y hy.1 (Over.mk (𝟙 (Spec (CommRingCat.of F))))))
          hlim so
      rw [hrep]
      change eval P' rhoL fl ((u : rationalPoints L) * l) =
        (↑(c (e l))⁻¹ : ℂ) • eval P rhoG f ((r : rationalPoints G) * w)
      rw [hfl, map_mul, map_mul, h0, one_mul, Subgroup.coe_mul, ← mul_assoc, hr]
  rw [heq]
  exact (hf w).smul _

set_option backward.isDefEq.respectTransparency.types false in
/-- A surjective realized restriction reflects full convergence for the
prescribed lower quotient measure. -/
theorem realizedNested_domain_eq_top
    (hlim : Jacquet.Localization.IsLimitOfCompactSubgroups (radical y))
    (R : I →ₗ[ℂ] Il) (hR : Function.Surjective R)
    (hform : ∀ f, RealizedRestrictionFormula o j hj hjc x a d d' A eM f 1 (R f))
    (muL : Measure QL) (t : ℝ≥0) (ht : 0 < t) (he : muG.map E = t • muL)
    (hfull : domain d du (radical y) A muG = ⊤) :
    domain d' du' (radical b) Al muL = ⊤ := by
  have hfull' : domain d' du' (radical b) Al (muG.map E) = ⊤ := by
    apply Submodule.eq_top_iff'.mpr
    intro v
    obtain ⟨f, rfl⟩ := hR v
    have hf : f ∈ domain d du (radical y) A muG := hfull.symm ▸ Submodule.mem_top
    obtain ⟨J, hJ⟩ := (mem_domain d du (radical y) A muG f).mp hf
    exact (mem_domain d' du' (radical b) Al (muG.map E) (R f)).mpr
      ⟨_, HasIntegral.realized_restriction o j hj hjc x y a b hx hy d d' A eM muG hlim hJ 1 (R f) (hform f)⟩
  rw [he, domain_smul_measure d' du' (radical b) Al muL t ht.ne'] at hfull'
  exact hfull'

end Langlands.Plancherel.StandardIntertwining
