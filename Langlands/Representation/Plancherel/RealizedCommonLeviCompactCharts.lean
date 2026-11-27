import Langlands.Representation.Plancherel.RealizedFixedCompactRestriction
import Langlands.Representation.Plancherel.ActualCommonLeviTensor
import Langlands.Representation.Plancherel.DynamicOppositePairScalarProof

/-! # Compact charts for a realized common-Levi pair -/

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

universe u uV uZ

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

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {G L : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  [IsAffineHom L.X.hom] [LocallyOfFiniteType L.X.hom]
  (o : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (j : L ⟶ G) (hj : (Dynamic.centralizer o).IsRepresentedBy j) (hjc : IsClosedSubgroup j)
  (x : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) (a : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ L)
  (hx : Dynamic.parabolic x = Dynamic.extendFromCentralizer o j hj (Dynamic.parabolic a) ∧
    Dynamic.centralizer x = (Dynamic.centralizer a).map j ∧
    Dynamic.unipotent x = Dynamic.extendFromCentralizer o j hj (Dynamic.unipotent a))
  (hG : IsConnectedReductive G) (hL : IsConnectedReductive L)
  (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (ξ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ L)
  (hX : Dynamic.centralizer x = Dynamic.centralizer χ)
  (hA : Dynamic.centralizer a = Dynamic.centralizer ξ)
  (eM : levi ξ ≃ₜ* levi χ)
  (A : SmoothRep.{0, u, uV} ℂ (levi χ)) (B : SmoothRep.{0, u, uV} ℂ (levi ξ))
  (eB : (SmoothRep.pullback eM A).representation.Equiv B.representation)
  (pMap : unramifiedCharacters (normCharacters χ) → unramifiedCharacters (normCharacters ξ))
  (hpMap : ∀ z m, (parameterTransport ξ (pMap z)).val m = (parameterTransport χ z).val (eM m))

local notation "dG" => commonDecomposition χ x hX
local notation "dL" => commonDecomposition ξ a hA
local notation "X" => unramifiedCharacters (normCharacters χ)
local notation "Ag[" z "]" => twistObject χ z A
local notation "Bl[" z "]" => twistObject ξ (pMap z) B
local notation "Al[" z "]" => SmoothRep.pullback eM Ag[z]
local notation "IG[" z "]" => (DynamicNormalization.leviTwistedInductionFunctor dG
  (radical_isClosed x)).obj Ag[z]
local notation "IL[" z "]" => (DynamicNormalization.leviTwistedInductionFunctor dL
  (radical_isClosed a)).obj Al[z]

include hpMap in
set_option backward.isDefEq.respectTransparency.types false in
/-- The respective twists of the identified inducing representations use
one fixed linear map on the original carriers. -/
def realizedTwistCoefficientEquiv (z : X) : (Al[z]).representation.Equiv (Bl[z]).representation :=
  Representation.Equiv.mk eB.toLinearEquiv (fun m => by
    apply LinearMap.ext
    intro v
    change eB ((↑((parameterTransport χ z).val (eM m)) : ℂ) • A.representation (eM m) v) =
      (↑((parameterTransport ξ (pMap z)).val m) : ℂ) • B.representation m (eB v)
    exact ((map_smul eB.toLinearEquiv _ _).trans
      (congrArg (fun w => (↑((parameterTransport χ z).val (eM m)) : ℂ) • w)
        (LinearMap.congr_fun (eB.isIntertwining' m) v))).trans
      (congrArg (fun c : ℂˣ => (c : ℂ) • B.representation m (eB v)) (hpMap z m).symm))

local notation "eTw[" z "]" => realizedTwistCoefficientEquiv χ ξ eM A B eB pMap hpMap z

section Inflation

variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [LocallyCompactSpace Γ]
  [NonarchimedeanGroup Γ] {P M U : Subgroup Γ}
  (d : IsSemidirectDecomposition P M U) (du : IsClosed (U : Set Γ))
  {A₀ B₀ : SmoothRep.{0, u, uV} ℂ M} (f : A₀.representation.Equiv B₀.representation)

/-- Induce the inducing-fiber comparison in the Levi-inflated normalization. -/
def leviInflatedInductionEquivOfEquiv :
    ((DynamicNormalization.leviTwistedInductionFunctor d du).obj A₀).representation.Equiv
    ((DynamicNormalization.leviTwistedInductionFunctor d du).obj B₀).representation :=
  smoothInducedEquiv P (Representation.Equiv.mk f.toLinearEquiv
    (fun p => (Langlands.twistEquiv
      (HaarModulus.closedHalfCharacter U du M d.levi_le_normalizer) f).isIntertwining' (d.projection p)))

@[simp]
theorem leviInflatedInductionEquivOfEquiv_eval
    (v : (DynamicNormalization.leviTwistedInductionFunctor d du).obj A₀) (g : Γ) :
    eval P (leviInflatedInducingRepresentation d du B₀) (leviInflatedInductionEquivOfEquiv d du f v) g =
      f (eval P (leviInflatedInducingRepresentation d du A₀) v g) := rfl

end Inflation

variable (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
  (KL : OpenSubgroup (rationalPoints L)) (hKL : IsCompact (KL : Set (rationalPoints L)))
  (hPK : ∀ g : rationalPoints G, ∃ p : parabolic x, ∃ k : K, g = (p : rationalPoints G) * (k : rationalPoints G))
  (hPL : ∀ g : rationalPoints L, ∃ p : parabolic a, ∃ k : KL, g = (p : rationalPoints L) * (k : rationalPoints L))

local notation "CG" => CompactInductionPicture dG K A
local notation "CL" => CompactInductionPicture dL KL B
local notation "eLower[" z "]" => leviInflatedInductionEquivOfEquiv dL (radical_isClosed a) eTw[z]

include hL hKL hPL hpMap in
/-- The lower compact chart identifies the transported twist by the original
pointwise inducing equivalence before taking its compact restriction. -/
def realizedLowerCompactEquiv (z : X) : IL[z] ≃ₗ[ℂ] CL :=
  (eLower[z]).toLinearEquiv.trans (compactEquiv ξ hL KL hKL a hA hPL (pMap z) B)

local notation "Eg[" z "]" => compactEquiv χ hG K hK x hX hPK z A
local notation "El[" z "]" => realizedLowerCompactEquiv a hL χ ξ hA eM A B eB pMap hpMap KL hKL hPL z

set_option backward.isDefEq.respectTransparency.types false in
/-- Transport to the lower compact chart acts on each value by the same
linear inducing equivalence. -/
theorem realizedLowerCompactEquiv_eval (z : X) (f : IL[z]) (l : KL) :
    eval _ _ ((El[z]) f) l = eB (eval _ _ f l.val) :=
  (compactEquiv_eval ξ hL KL hKL a hA hPL (pMap z) B ((eLower[z]) f) l).trans
    (leviInflatedInductionEquivOfEquiv_eval dL (radical_isClosed a) eTw[z] f (l : rationalPoints L))

local notation "e" => RepresentedDynamicTransport.pointEquiv F (Dynamic.centralizer o) j hj hjc
variable (heM : ∀ l, (eM l : rationalPoints G) = (e (l : rationalPoints L) : rationalPoints G))
  (hKLK : ∀ k : KL, (e (k : rationalPoints L) : rationalPoints G) ∈ K)

include hx heM hKLK in
set_option backward.isDefEq.respectTransparency.types false in
/-- For these actual common-Levi charts there is a fixed surjective compact
restriction across the entire unramified parameter group. -/
theorem exists_realizedCommonLeviFixedCompactRestriction :
    ∃ R : CG →ₗ[ℂ] CL, Function.Surjective R ∧
      ∀ (z : X) (f : IG[z]), RealizedRestrictionFormula o j hj hjc x a dG dL Ag[z] eM f 1
        ((El[z]).symm (R ((Eg[z]) f))) :=
  exists_realizedFixedCompactRestriction o j hj hjc x a hx hG hL
    (congrArg (fun S : SubgroupFunctor G => S.carrier (Over.mk (𝟙 (Spec (CommRingCat.of F))))) hX)
    (congrArg (fun S : SubgroupFunctor L => S.carrier (Over.mk (𝟙 (Spec (CommRingCat.of F))))) hA)
    eM dG dL K KL heM hKLK (1 : X) A B (fun z => Ag[z])
    (fun _ => LinearEquiv.refl ℂ A) (fun _ => eB.toLinearEquiv)
    (fun z => Eg[z]) (fun z => El[z])
    (fun z f k => compactEquiv_eval χ hG K hK x hX hPK z A f k)
    (fun z f k => realizedLowerCompactEquiv_eval a hL χ ξ hA eM A B eB pMap hpMap KL hKL hPL z f k)
    (fun _ _ => rfl)

end Langlands.Plancherel.StandardIntertwining
