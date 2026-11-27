import Langlands.Representation.Plancherel.RealizedNestedStagesRestriction
import Langlands.Representation.Plancherel.CompactIntertwiningFamilies

/-! # The fixed compact restriction through a realized intermediate Levi -/

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
  {M : Subgroup (rationalPoints G)} {M' : Subgroup (rationalPoints L)}
  (hM : levi x = M) (hM' : levi a = M') (eM : M' ≃ₜ* M)
  (dG : IsSemidirectDecomposition (parabolic x) M (radical x))
  (dL : IsSemidirectDecomposition (parabolic a) M' (radical a))
  (K : OpenSubgroup (rationalPoints G)) (K' : OpenSubgroup (rationalPoints L))

local notation "e" => RepresentedDynamicTransport.pointEquiv F (Dynamic.centralizer o) j hj hjc
local notation "c" => HaarModulus.closedHalfCharacter (radical o) (radical_isClosed o)
  (levi o) (decomposition o).levi_le_normalizer

variable (heM : ∀ l, (eM l : rationalPoints G) = (e (l : rationalPoints L) : rationalPoints G))
  (hK' : ∀ k : K', (e (k : rationalPoints L) : rationalPoints G) ∈ K)
  {Z : Type uZ} (z₀ : Z)
  (A : SmoothRep.{0, u, uV} ℂ M) (B : SmoothRep.{0, u, uV} ℂ M')
  (Az : Z → SmoothRep.{0, u, uV} ℂ M)
  (va : ∀ z, Az z ≃ₗ[ℂ] A) (vb : ∀ z, SmoothRep.pullback eM (Az z) ≃ₗ[ℂ] B)

local notation "V" => CompactInductionPicture dG K A
local notation "W" => CompactInductionPicture dL K' B
local notation "I" z => (DynamicNormalization.leviTwistedInductionFunctor dG (radical_isClosed x)).obj (Az z)
local notation "Il" z => (DynamicNormalization.leviTwistedInductionFunctor dL (radical_isClosed a)).obj
  (SmoothRep.pullback eM (Az z))

variable (Eg : ∀ z : Z, (I z) ≃ₗ[ℂ] V)
  (El : ∀ z : Z, (Il z) ≃ₗ[ℂ] W)
  (hg : ∀ (z : Z) (f : I z) (k : K), eval _ _ (Eg z f) k = va z (eval _ _ f k.val))
  (hl : ∀ (z : Z) (f : Il z) (k : K'), eval _ _ (El z f) k = vb z (eval _ _ f k.val))
  (hval : ∀ (z : Z) (v : Az z), vb z v = vb z₀ ((va z₀).symm (va z v)))

include hx hG hL hM hM' heM hK' hg hl hval in
set_option backward.isDefEq.respectTransparency.types false in
/-- Pointwise restrictions in the compact pictures give one fixed surjective
linear map. The charts may present the actual twist on either the initial
or the transported inducing carrier. -/
theorem exists_realizedFixedCompactRestriction :
    ∃ R : V →ₗ[ℂ] W, Function.Surjective R ∧
      ∀ (z : Z) (f : I z), RealizedRestrictionFormula o j hj hjc x a dG dL (Az z) eM f 1
        ((El z).symm (R (Eg z f))) := by
  have hn (z : Z) := exists_realizedStagesRestriction_aligned o j hj hjc x a hx hG hL
    hM hM' (Az z) eM heM dG dL
  choose r hr hform using hn
  let Rc (z : Z) : V →ₗ[ℂ] W :=
    (El z).toLinearMap.comp ((r z).comp (Eg z).symm.toLinearMap)
  have hRc (z : Z) (v : V) (k : K') : eval _ _ (Rc z v) k =
      (↑(c (e (k : rationalPoints L)))⁻¹ : ℂ) • vb z₀ ((va z₀).symm
        (eval _ _ v (⟨(e (k : rationalPoints L) : rationalPoints G), hK' k⟩ : K))) := by
    let f := (Eg z).symm v
    let v₀ : K := ⟨(e (k : rationalPoints L) : rationalPoints G), hK' k⟩
    have hEval := hform z f (k : rationalPoints L)
    rw [mul_one] at hEval
    have hEv : va z (eval _ _ f (v₀ : rationalPoints G)) = eval _ _ v v₀ :=
      (hg z f v₀).symm.trans (congrArg (fun g : V => eval _ _ g v₀) ((Eg z).apply_symm_apply v))
    change eval _ _ (El z (r z f)) k = _
    exact (hl z (r z f) k).trans ((congrArg (vb z) hEval).trans
      ((map_smul (vb z) _ _).trans (congrArg (fun q => (↑(c (e (k : rationalPoints L)))⁻¹ : ℂ) • q)
        ((hval z _).trans (congrArg (fun q => vb z₀ ((va z₀).symm q)) hEv)))))
  have he (z : Z) : Rc z₀ = Rc z := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    apply Subtype.ext
    funext k
    exact (hRc z₀ v k).trans (hRc z v k).symm
  refine ⟨Rc z₀, (El z₀).surjective.comp ((hr z₀).comp (Eg z₀).symm.surjective), ?_⟩
  intro z f
  rw [he z]
  have hp : (El z).symm (Rc z (Eg z f)) = r z f :=
    ((El z).symm_apply_apply _).trans (congrArg (r z) ((Eg z).symm_apply_apply f))
  rw [hp]
  exact hform z f

end Langlands.Plancherel.StandardIntertwining
