import Langlands.Representation.Plancherel.ActualConjugateLeviRationalParameter
import Langlands.Representation.Plancherel.RationalOperatorPoleAlgebra

/-! # Transport of unitary pole presentations along scheme isomorphisms -/

noncomputable section

set_option quotPrecheck false

universe u uV uW

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.Plancherel

open UnramifiedOperatorFamily

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G H : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [IsAffine H.X.left] [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType H.X.hom]

local instance transportPointTopology (J : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine J.X.left] : TopologicalSpace (rationalPoints J) := rationalPointTopology F J.X

set_option hygiene false in
local notation "χ(" J ")" => unramifiedCharacters (fun a => (rationalNormCharacters J a).toMul)
set_option hygiene false in
local notation "𝓡(" J ")" => unramifiedRegularFunctions (fun a => (rationalNormCharacters J a).toMul)
local notation "Λ(" J ")" => Additive (rationalDiscreteValuationImage J)

/-- A scheme isomorphism gives a homeomorphism of the full unramified parameter spaces. -/
def rationalUnramifiedParameterHomeomorph (e : G ≅ H) : χ(G) ≃ₜ χ(H) where
  toFun := rationalUnramifiedCharacterTransport e
  invFun := rationalUnramifiedCharacterTransport e.symm
  left_inv := rationalUnramifiedCharacterRestrict_transport e
  right_inv := rationalUnramifiedCharacterRestrict_transport e.symm
  continuous_toFun := (rationalUnramifiedCharacterTransport e).continuous
  continuous_invFun := (rationalUnramifiedCharacterTransport e.symm).continuous

section PoleFactors

variable (e : G ≅ H)

omit [IsAffine G.X.left] [IsAffine H.X.left] [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType H.X.hom] in
private def valuationImageEquiv : rationalDiscreteValuationImage H ≃* rationalDiscreteValuationImage G where
  toFun := rationalValuationImageMap e.inv
  invFun := rationalValuationImageMap e.hom
  map_mul' := map_mul (rationalValuationImageMap e.inv)
  left_inv := by
    intro a
    obtain ⟨m, rfl⟩ := rationalValuationImageProjection_surjective H a
    rw [rationalValuationImageMap_projection, rationalValuationImageMap_projection]
    congr 1
    rw [rationalPoints.map_apply, rationalPoints.map_apply, Category.assoc,
      ← Grp.comp_hom_hom, e.inv_hom_id, Grp.id_hom_hom, Category.comp_id]
  right_inv := by
    intro a
    obtain ⟨m, rfl⟩ := rationalValuationImageProjection_surjective G a
    rw [rationalValuationImageMap_projection, rationalValuationImageMap_projection]
    congr 1
    rw [rationalPoints.map_apply, rationalPoints.map_apply, Category.assoc,
      ← Grp.comp_hom_hom, e.hom_inv_id, Grp.id_hom_hom, Category.comp_id]

private theorem root_eval (J : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine J.X.left] [LocallyOfFiniteType J.X.hom]
    {n : ℕ} (B : Module.Basis (Fin (n + 1)) ℤ Λ(J)) (s : ℂˣ)
    (m : rationalPoints J) (hm : rationalValuationImageProjection J m = (B 0).toMul) (z : χ(J)) :
    (rationalUnramifiedBasisCoordinateRoot J B s).val z = (z.val m : ℂ) - (s : ℂ) := by
  let c := rationalUnramifiedBasisUnitCoordinates J B z
  have h := rationalUnramifiedBasisLaurentEquiv_eval J B c (finiteLaurentCoordinateRoot n s)
  change (rationalUnramifiedBasisCoordinateRoot J B s).val
    ((rationalUnramifiedBasisUnitCoordinates J B).symm c) = _ at h
  rw [show (rationalUnramifiedBasisUnitCoordinates J B).symm c = z from
    (rationalUnramifiedBasisUnitCoordinates J B).symm_apply_apply z] at h
  rw [h, ← Fin.cons_self_tail c, finiteLaurentCoordinateRoot_eval_cons]
  change ((rationalCanonicalImageUnramifiedContinuousEquiv J).symm z (B 0).toMul : ℂ) - (s : ℂ) = _
  rw [← hm, rationalCanonicalImageUnramifiedContinuousEquiv_symm_projection]

local notation "pull" => (rationalUnramifiedRegularFunctionsEquiv e).symm

private def pullBasisPole (r : RationalUnitaryBasisPole H) : RationalUnitaryBasisPole G :=
  ⟨r.dimension, r.basis.map (valuationImageEquiv e).toAdditive.toIntLinearEquiv, r.value, r.multiplicity⟩

private theorem pullBasisPole_factor (r : RationalUnitaryBasisPole H) :
    (pullBasisPole e r).factor G = pull (r.factor H) := by
  obtain ⟨m, hm⟩ := rationalValuationImageProjection_surjective H (r.basis 0).toMul
  apply Subtype.ext
  funext z
  have hm' : rationalValuationImageProjection G (rationalPoints.map e.inv m) =
      ((pullBasisPole e r).basis 0).toMul := by
    rw [← rationalValuationImageMap_projection, hm]
    change rationalValuationImageMap e.inv (r.basis 0).toMul = ((r.basis.map (valuationImageEquiv e).toAdditive.toIntLinearEquiv) 0).toMul
    rw [Module.Basis.map_apply]
    rfl
  rw [rationalUnramifiedRegularFunctionsEquiv_symm_val]
  simp only [RationalUnitaryBasisPole.factor, Subalgebra.coe_pow, Pi.pow_apply,
    root_eval G _ _ _ hm', root_eval H _ _ _ hm]
  rfl

/-- Pull back each basis through the induced integral lattice isomorphism,
and pull back the remainder through the character homeomorphism. -/
def RationalUnitaryPoleFactorization.parameterPullback {b : 𝓡(H)}
    (f : RationalUnitaryPoleFactorization H b) : RationalUnitaryPoleFactorization G (pull b) where
  poles := f.poles.map (pullBasisPole e)
  remainder := pull f.remainder
  factorization := by
    rw [congrArg pull f.factorization, map_mul]
    congr 1
    simp only [rationalUnitaryPoleProduct, List.map_map, Function.comp_def,
      pullBasisPole_factor, map_list_prod]
  remainder_nonzero z := by
    have hz := f.remainder_nonzero (rationalUnitaryUnramifiedCharacterRestrict e.inv z)
    exact hz

end PoleFactors

variable (e : G ≅ H)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

local notation "param" => rationalUnramifiedCharacterTransport e
local notation "pull" => (rationalUnramifiedRegularFunctionsEquiv e).symm

/-- Character transport preserves the global cleared cross identity and the
finite expansions of the operator numerator. -/
def RationalOperatorPolePresentation.parameterPullback {a : 𝓡(H)} {N : χ(H) → V →ₗ[ℂ] W}
    (q : RationalOperatorPolePresentation H a N) :
    RationalOperatorPolePresentation G (pull a) (fun z => N (param z)) where
  denominator := pull q.denominator
  factors := q.factors.parameterPullback e
  numerator z := q.numerator (param z)
  polynomial v := by
    simpa only [Set.preimage_univ, Function.comp_def, Set.restrictPreimage, Set.MapsTo.restrict,
      Subtype.map] using (q.polynomial v).parameterPullback e
  cross z := q.cross (param z)

/-- Pull back the whole operator continuation to the actual preimage of its domain. -/
def UnramifiedOperatorFamily.RationalOperatorContinuationData.parameterPullback
    {D : Set χ(H)} {A : D → V →ₗ[ℂ] W} (p : RationalOperatorContinuationData D A) :
    RationalOperatorContinuationData (param ⁻¹' D)
      (fun z => A ⟨param z.val, z.property⟩) where
  denominator := pull p.denominator
  denominator_nonzero z := p.denominator_nonzero ⟨param z.val, z.property⟩
  numerator z := p.numerator (param z)
  polynomial v := by
    simpa only [Set.preimage_univ, Function.comp_def, Set.restrictPreimage, Set.MapsTo.restrict,
      Subtype.map] using (p.polynomial v).parameterPullback e
  clears z := p.clears ⟨param z.val, z.property⟩

end Langlands.Plancherel
