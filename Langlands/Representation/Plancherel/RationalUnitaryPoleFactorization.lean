import Langlands.Representation.Plancherel.ActualCommonLeviV3PoleCancellation
import Langlands.Representation.Plancherel.RationalUnramifiedLatticeFactors

/-! # Factoring monomial denominators for actual unitary pole cancellation -/

noncomputable section

set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open CategoryTheory AlgebraicGeometry Topology
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Plancherel

universe u uV uE

section Factorization

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

local instance poleFactorizationPointTopology : TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X

local notation "Λ" => Additive (rationalDiscreteValuationImage G)
set_option quotPrecheck false in
local notation "R" => unramifiedRegularFunctions (fun a => (rationalNormCharacters G a).toMul)

/-- A scalar denominator split into the factors used by unitary cancellation
and a remainder nonvanishing on the entire actual unitary subgroup. -/
structure RationalUnitaryPoleFactorization (b : R) where
  poles : List (RationalUnitaryBasisPole G)
  remainder : R
  factorization : b = rationalUnitaryPoleProduct G poles * remainder
  remainder_nonzero : ∀ z, remainder.val (unitaryToUnramified G z) ≠ 0

namespace RationalUnitaryPoleFactorization

/-- A denominator with no unitary zeros has an empty list of pole factors. -/
def ofNonvanishing (b : R) (hb : ∀ z, b.val (unitaryToUnramified G z) ≠ 0) :
    RationalUnitaryPoleFactorization G b where
  poles := []
  remainder := b
  factorization := by simp [rationalUnitaryPoleProduct]
  remainder_nonzero := hb

/-- Product denominators concatenate the two lists and multiply the remainders. -/
def mul {b c : R} (p : RationalUnitaryPoleFactorization G b)
    (q : RationalUnitaryPoleFactorization G c) :
    RationalUnitaryPoleFactorization G (b * c) where
  poles := p.poles ++ q.poles
  remainder := p.remainder * q.remainder
  factorization := by
    have h : rationalUnitaryPoleProduct G (p.poles ++ q.poles) =
        rationalUnitaryPoleProduct G p.poles * rationalUnitaryPoleProduct G q.poles := by
      simp only [rationalUnitaryPoleProduct, List.map_append, List.prod_append]
    calc
      b * c = (rationalUnitaryPoleProduct G p.poles * p.remainder) *
          (rationalUnitaryPoleProduct G q.poles * q.remainder) :=
        congrArg₂ (fun x y : R => x * y) p.factorization q.factorization
      _ = rationalUnitaryPoleProduct G (p.poles ++ q.poles) * (p.remainder * q.remainder) := by
        rw [h]
        ac_rfl
  remainder_nonzero z := mul_ne_zero (p.remainder_nonzero z) (q.remainder_nonzero z)

/-- A monomial binomial with nonzero exponent separates into basis-coordinate
roots on the unit circle or a factor nonvanishing there. -/
def ofMonomialDifference (hG : GroupScheme.IsConnectedReductive G)
    (v : Λ) (hv : v ≠ 0) (a : ℂ) :
    RationalUnitaryPoleFactorization G
      (rationalUnramifiedLatticeMonomial G v - algebraMap ℂ R a) := by
  classical
  by_cases ha : ‖a‖ = 1
  · let t : Circle := ⟨a, mem_sphere_zero_iff_norm.mpr ha⟩
    exact Classical.choice (by
      obtain ⟨n, B, roots, hf⟩ := rationalUnramifiedLatticeMonomial_sub_factorization G hG v hv t
      let rs := roots.map (fun r : Circle => (⟨n, B, r, 1⟩ : RationalUnitaryBasisPole G))
      refine ⟨⟨rs, 1, ?_, fun _ => one_ne_zero⟩⟩
      rw [mul_one]
      simpa only [rationalUnitaryPoleProduct, rs, List.map_map,
        Function.comp_def, RationalUnitaryBasisPole.factor, pow_one] using hf)
  · exact ofNonvanishing G _ (rationalUnramifiedLatticeMonomial_sub_nonvanishing G v a ha)

/-- Factor an entire monomial-binomial denominator in the form required by
the unitary pole cancellation theorem. The base factor is already
nonvanishing throughout the unitary subgroup. -/
def ofMonomialDifferences (hG : GroupScheme.IsConnectedReductive G)
    (factors : List (Λ × ℂ)) (hne : ∀ t ∈ factors, t.1 ≠ 0)
    (d : R) (hd : ∀ z, d.val (unitaryToUnramified G z) ≠ 0) :
    RationalUnitaryPoleFactorization G
      ((factors.map (fun t => rationalUnramifiedLatticeMonomial G t.1 -
        algebraMap ℂ R t.2)).prod * d) := by
  induction factors with
  | nil =>
    simpa only [List.map_nil, List.prod_nil, one_mul] using ofNonvanishing G d hd
  | cons t ts ih =>
    have hhead := hne t (List.mem_cons_self ..)
    have htail : ∀ w ∈ ts, w.1 ≠ 0 :=
      fun w hw => hne w (List.mem_cons_of_mem _ hw)
    simpa only [List.map_cons, List.prod_cons, mul_assoc] using
      mul G (ofMonomialDifference G hG t.1 hhead t.2) (ih htail)

end RationalUnitaryPoleFactorization
end Factorization

namespace ActualCommonLeviV3

open Aubert.General Induction StandardIntertwining DynamicOppositeStandardIntertwining
open DynamicCommonLeviComposition DynamicCommonLeviCompact DynamicCommonLeviContinuation
open ActualCommonLeviTensor ActualCommonLeviCompactTensor ActualCommonLeviRationalTensor
open UnramifiedOperatorFamily

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
  DynamicCommonLeviContinuation.radicalMeasurable
  DynamicCommonLeviContinuation.radicalBorel
  DynamicCommonLeviContinuation.intersectionMeasurable
  DynamicCommonLeviContinuation.intersectionBorel
  DynamicCommonLeviContinuation.quotientMeasurable
  DynamicCommonLeviContinuation.quotientBorel

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hG : IsConnectedReductive G)
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))
  (K : OpenSubgroup (RationalPoint F G.X))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))
  (ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hψ : Dynamic.centralizer ψ = Dynamic.centralizer χ)
  (hψK : ∀ g : RationalPoint F G.X, ∃ p : parabolic ψ, ∃ k : K,
    g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (ψ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hψ' : Dynamic.centralizer ψ' = Dynamic.centralizer χ)
  (hψ'K : ∀ g : RationalPoint F G.X, ∃ p : parabolic ψ', ∃ k : K,
    g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (p : ContinuedPair χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A)
  (q : ContinuedPair χ hG K hK ψ' hψ' hψ'K ψ hψ hψK A.contragredient)

local notation "X" => unramifiedCharacters (normCharacters χ)
local notation "Xu" => unitaryUnramifiedCharacters (normCharacters χ)
local notation "V₀" => compactFiber χ K ψ hψ A
local notation "V₁" => compactFiber χ K ψ' hψ' A
local notation "D" => genericLocus χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q
local notation "J" => compactComparison χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q

/-- A pole factorization of the original common denominator supplies the
existing actual regular germs from the cleared numerator and bound. -/
theorem exists_regularGermAt_of_poleFactorization
    (b : unramifiedRegularFunctions (normCharacters χ))
    (f : RationalUnitaryPoleFactorization (parameterScheme χ) b)
    (N : X → V₀ →ₗ[ℂ] V₁)
    (hN : IsPolynomialOperatorOn Set.univ (fun z => N z.val))
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E] (e : V₁ ≃ₗ[ℂ] E)
    (hbound : HasClearedUnitaryBound (parameterScheme χ) (fun z => e.toLinearMap.comp (N z)) b)
    (hden : ∀ z : D, b.val z.val ≠ 0)
    (hnum : ∀ z : D, N z.val = b.val z.val • J z)
    (z : Xu) :
    ∃ M : V₀ →ₗ[ℂ] V₁,
      RegularGermAt χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q (unitaryParameter χ z) M := by
  obtain ⟨rs, d, hb, hd⟩ := f
  subst b
  exact ⟨_, regularGermAt_of_unitary_pole_data χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K
    p q rs N hN e d hbound hden hnum hd z⟩

end ActualCommonLeviV3
end Langlands.Plancherel
