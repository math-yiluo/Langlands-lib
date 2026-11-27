import Langlands.Representation.Plancherel.RationalUnitaryBoundTransport

/-! # Transfer of a compact factorization to all rational presentations -/

noncomputable section

set_option hygiene false
set_option quotPrecheck false

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Plancherel.UnramifiedOperatorFamily

universe u uV₁ uV₂ uW₁ uW₂ uE

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {H J : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine H.X.left] [IsAffine J.X.left] [LocallyOfFiniteType J.X.hom]

local instance compactFactorizationPointTopologyH : TopologicalSpace (rationalPoints H) := rationalPointTopology F H.X
local instance compactFactorizationPointTopologyJ : TopologicalSpace (rationalPoints J) := rationalPointTopology F J.X

local notation "ν[" G "]" => fun ψ => (rationalNormCharacters G ψ).toMul
local notation "X[" G "]" => unramifiedCharacters ν[G]
local notation "R[" G "]" => unramifiedRegularFunctions ν[G]

omit [LocallyOfFiniteType J.X.hom] in
/-- Pullback along a group-scheme isomorphism identifies the actual full
unramified parameter groups as topological spaces. -/
def rationalCharacterRestrictionHomeomorph (f : H ≅ J) : X[J] ≃ₜ X[H] where
  toFun := rationalUnramifiedCharacterRestrict f.hom
  invFun := rationalUnramifiedCharacterRestrict f.inv
  left_inv z := rationalUnramifiedCharacterRestrict_transport f.symm z
  right_inv z := rationalUnramifiedCharacterRestrict_transport f z
  continuous_toFun := (rationalUnramifiedCharacterRestrict f.hom).continuous
  continuous_invFun := (rationalUnramifiedCharacterRestrict f.inv).continuous

variable (hJ : IsConnectedReductive J) (f : H ≅ J)
  {V : Type uV₁} [AddCommGroup V] [Module ℂ V]
  {V' : Type uV₂} [AddCommGroup V'] [Module ℂ V']
  {W : Type uW₁} [NormedAddCommGroup W] [NormedSpace ℂ W]
  {W' : Type uW₂} [AddCommGroup W'] [Module ℂ W']
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
  (e : W' →ₗ[ℂ] E)
  {Ω O : Set X[J]} (hO : IsOpen O) (hne : O.Nonempty) (hOΩ : O ⊆ Ω)
  {A : Ω → V' →ₗ[ℂ] W'} (p : RationalOperatorContinuationData Ω A)
  (N : X[H] → V →ₗ[ℂ] W) (d : R[H]) (hd : d ≠ 0)
  (hN : IsPolynomialOperatorOn Set.univ (fun z => N z.val)) (hB : HasClearedUnitaryBound H N d)
  (P : X[J] → V' →ₗ[ℂ] V) (hP : IsPolynomialOperatorOn Set.univ (fun z => P z.val))
  (L : W →ₗ[ℂ] W')

local notation "τ" => rationalUnramifiedCharacterRestrict f.hom
local notation "D" => rationalUnramifiedRegularFunctionsMap f.hom d

include hJ hO hne hd hN hB hP in
/-- A bound on a compact model transfers to every presentation of the
family with which the model agrees after clearing on a nonempty open set. -/
theorem hasClearedUnitaryBound_of_compactFactorization
    (hA : ∀ z (hz : z ∈ O), (D).val z • A ⟨z, hOΩ hz⟩ = L.comp ((N ((τ) z)).comp (P z))) :
    HasClearedUnitaryBound J (fun z => e.comp (p.numerator z)) p.denominator := by
  let N' (z : X[J]) := (N ((τ) z)).comp (P z)
  have hN' : IsPolynomialOperatorOn Set.univ (fun z => N' z.val) :=
    (polynomialOperatorOn_restrict_univ H f.hom hN).comp hP
  have hB' : HasClearedUnitaryBound J N' D :=
    hasClearedUnitaryBound_precomp J (hasClearedUnitaryBound_restrict H f.hom hB) P hP
  have hd' : (D) ≠ 0 := fun h => hd ((rationalUnramifiedRegularFunctionsEquiv f).injective
    (h.trans (map_zero (rationalUnramifiedRegularFunctionsEquiv f)).symm))
  let L' := e.comp L
  have hB'' := hasClearedUnitaryBound_postcomp J hN' hB' L'
  apply hasClearedUnitaryBound_of_crossOn_open J hJ hd' (hN'.postcomp L') hB''
    p.denominator (fun z => e.comp (p.numerator z)) (p.polynomial.postcomp e) hO hne
  intro z hz
  apply LinearMap.ext
  intro v
  have hp := LinearMap.congr_fun (p.clears ⟨z, hOΩ hz⟩) v
  have hA' := LinearMap.congr_fun (hA z hz) v
  change p.numerator z v = p.denominator.val z • A ⟨z, hOΩ hz⟩ v at hp
  change (D).val z • A ⟨z, hOΩ hz⟩ v = L (N' z v) at hA'
  change (D).val z • e (p.numerator z v) = p.denominator.val z • e (L (N' z v))
  rw [hp, ← hA', map_smul, map_smul, smul_comm]

end Langlands.Plancherel.UnramifiedOperatorFamily
