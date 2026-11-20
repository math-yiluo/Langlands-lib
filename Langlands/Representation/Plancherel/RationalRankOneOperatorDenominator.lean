import Langlands.Representation.Plancherel.RationalUnitaryCoordinateDenominator
import Langlands.Representation.Plancherel.RationalUnramifiedRestrictionKernel
import Langlands.Representation.Plancherel.DynamicOppositeMaximalLeviRegularity

/-! # Denominators for operators invariant under rank-one ambient restriction -/

noncomputable section

set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.Plancherel

open UnramifiedOperatorFamily

universe u uV uW

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (H : GroupScheme (Spec (CommRingCat.of F)))
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom]
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

local instance rankOneDenominatorSourceTopology : TopologicalSpace (rationalPoints H) :=
  rationalPointTopology F H.X

local instance rankOneDenominatorTargetTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X

set_option quotPrecheck false in
local notation "X" => unramifiedCharacters (fun a => (rationalNormCharacters H a).toMul)
set_option quotPrecheck false in
local notation "R" => unramifiedRegularFunctions (fun a => (rationalNormCharacters H a).toMul)

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- A second pair of polynomial numerator and denominator for the same
rational operator, with a unitary pole factorization and a global cross
identity with the original numerator and denominator. -/
structure RationalOperatorPolePresentation
    (b₀ : R) (N₀ : X → V →ₗ[ℂ] W) where
  denominator : R
  factors : RationalUnitaryPoleFactorization H denominator
  numerator : X → V →ₗ[ℂ] W
  polynomial : IsPolynomialOperatorOn Set.univ (fun z => numerator z.val)
  cross : ∀ z, b₀.val z • numerator z = denominator.val z • N₀ z

namespace RationalOperatorPolePresentation

private def successorLinearEquiv (n : ℕ) :
    ((Fin 1 → ℤ) × (Fin n → ℤ)) ≃ₗ[ℤ] (Fin (n + 1) → ℤ) :=
  ((LinearEquiv.funUnique (Fin 1) ℤ ℤ).prodCongr (LinearEquiv.refl ℤ _)).trans
    { toEquiv := Fin.consEquiv (fun _ : Fin (n + 1) => ℤ)
      map_add' := fun _ _ => by ext j; exact Fin.cases rfl (fun _ => rfl) j
      map_smul' := fun _ _ => by ext j; exact Fin.cases rfl (fun _ => rfl) j }

variable (i : H ⟶ G)

omit [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom]
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
private theorem exists_basis_spanning_valuation_kernel {n : ℕ}
    (e : Additive (rationalDiscreteValuationImage H) ≃ₗ[ℤ] (Fin 1 → ℤ) × (Fin n → ℤ))
    (he : ∀ x : Additive (rationalDiscreteValuationImage H),
      (e x).2 = 0 ↔ rationalValuationImageMap i x.toMul = 1) :
    ∃ B : Module.Basis (Fin (n + 1)) ℤ (Additive (rationalDiscreteValuationImage H)),
      ∀ a : (rationalValuationImageMap i).ker, ∃ k : ℤ, a.val = (B 0).toMul ^ k := by
  let coords := e.trans (successorLinearEquiv n)
  let B := Module.Basis.ofEquivFun coords
  refine ⟨B, fun a => ?_⟩
  let x := Additive.ofMul a.val
  let k := (e x).1 0
  refine ⟨k, ?_⟩
  change x.toMul = (k • B 0).toMul
  apply congrArg Additive.toMul
  apply coords.injective
  have ht : (e x).2 = 0 := (he x).mpr a.property
  have hB : coords (B 0) = Pi.single 0 1 := by
    simp [B]
  rw [map_smul, hB]
  change (Fin.cons k (e x).2 : Fin (n + 1) → ℤ) = _
  rw [ht]
  ext j
  refine Fin.cases ?_ (fun m => ?_) j
  · simp
  · simp

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
private theorem valuationKernelRestrict_eq_of_firstCoordinate {n : ℕ}
    (B : Module.Basis (Fin (n + 1)) ℤ (Additive (rationalDiscreteValuationImage H)))
    (hB : ∀ a : (rationalValuationImageMap i).ker, ∃ k : ℤ, a.val = (B 0).toMul ^ k)
    {z w : X}
    (he : rationalUnramifiedBasisUnitCoordinates H B z 0 =
      rationalUnramifiedBasisUnitCoordinates H B w 0) :
    rationalUnramifiedValuationKernelRestrict i z =
      rationalUnramifiedValuationKernelRestrict i w := by
  apply MonoidHom.ext
  intro a
  obtain ⟨k, hk⟩ := hB a
  change rationalImageUnramifiedDescend H z a.val = rationalImageUnramifiedDescend H w a.val
  rw [hk, map_zpow, map_zpow]
  exact congrArg (fun c : ℂˣ => c ^ k) he

variable {Ω : Set (unramifiedCharacters (fun a => (rationalNormCharacters H a).toMul))}
  {A : Ω → V →ₗ[ℂ] W}

/-- An operator invariant under actual ambient restriction acquires a
pole-factorable denominator when the adapted valuation kernel has rank
at most one. The starting region can be any nonempty open subset of its
original domain. -/
def ofAmbientInvariant (hH : IsConnectedReductive H)
    {r n : ℕ} (hr : r ≤ 1)
    (e : Additive (rationalDiscreteValuationImage H) ≃ₗ[ℤ] (Fin r → ℤ) × (Fin n → ℤ))
    (he : ∀ x : Additive (rationalDiscreteValuationImage H),
      (e x).2 = 0 ↔ rationalValuationImageMap i x.toMul = 1)
    {U : Set X} (hU : IsOpen U) (z₀ : U) (hsub : U ⊆ Ω)
    (p : RationalOperatorContinuationData Ω A)
    (hInv : ∀ (eta : unramifiedCharacters (fun a => (rationalNormCharacters G a).toMul))
      (z w : U), z.val = rationalUnramifiedCharacterRestrict i eta * w.val →
        A ⟨z.val, hsub z.property⟩ = A ⟨w.val, hsub w.property⟩) :
    RationalOperatorPolePresentation H p.denominator p.numerator :=
  Classical.choice (by
    have hA (z w : U) (heq : rationalUnramifiedValuationKernelRestrict i z.val =
        rationalUnramifiedValuationKernelRestrict i w.val) :
        A ⟨z.val, hsub z.property⟩ = A ⟨w.val, hsub w.property⟩ := by
      obtain ⟨eta, heta⟩ := (rationalUnramifiedValuationKernelRestrict_eq_iff i _ _).mp heq
      exact hInv eta z w heta
    rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl
    · let N : X → V →ₗ[ℂ] W := fun _ => A ⟨z₀.val, hsub z₀.property⟩
      have hN : IsPolynomialOperatorOn Set.univ (fun z => N z.val) :=
        isPolynomialOperatorOn_const _
      have ha (a : (rationalValuationImageMap i).ker) : a.val = 1 := by
        change (Additive.ofMul a.val).toMul = (0 : Additive (rationalDiscreteValuationImage H)).toMul
        apply congrArg Additive.toMul
        apply e.injective
        rw [map_zero]
        exact Prod.ext (Subsingleton.elim _ _) ((he _).mpr a.property)
      refine ⟨⟨1, RationalUnitaryPoleFactorization.ofNonvanishing H 1 (fun _ => one_ne_zero),
        N, hN, fun z => ?_⟩⟩
      apply LinearMap.ext
      intro v
      let f : ↥(Set.univ : Set X) → W := fun w =>
        p.denominator.val w.val • N w.val v - p.numerator w.val v
      have hf : IsPolynomialOn Set.univ f :=
        ((hN v).regular_smul p.denominator).sub (p.polynomial v)
      have hzero := rationalUnramifiedPolynomial_eq_zero_of_isOpen H
        (continuous_rationalValuationImageProjection H) hH hU ⟨z₀.val, z₀.property⟩
        (fun _ _ => Set.mem_univ _) f hf (by
          intro w hw
          let a : Ω := ⟨w, hsub hw⟩
          have hwz : A a = A ⟨z₀.val, hsub z₀.property⟩ :=
            hA ⟨w, hw⟩ z₀ (MonoidHom.ext fun x => by
              change rationalImageUnramifiedDescend H w x.val =
                rationalImageUnramifiedDescend H z₀.val x.val
              rw [ha x, map_one, map_one])
          change p.denominator.val w • N w v - p.numerator a.val v = 0
          rw [p.clears a, LinearMap.smul_apply, hwz]
          exact sub_self _)
      simpa only [LinearMap.smul_apply, Subalgebra.coe_one, Pi.one_apply, one_smul] using
        sub_eq_zero.mp (hzero ⟨z, Set.mem_univ _⟩)
    · obtain ⟨B, hB⟩ := exists_basis_spanning_valuation_kernel H i e he
      let pU : RationalOperatorContinuationData U (fun z => A ⟨z.val, hsub z.property⟩) :=
        ⟨p.denominator, fun z => p.denominator_nonzero ⟨z.val, hsub z.property⟩,
          p.numerator, p.polynomial, fun z => p.clears ⟨z.val, hsub z.property⟩⟩
      let c := Fin.tail (rationalUnramifiedBasisUnitCoordinates H B z₀.val)
      obtain ⟨hb, hN, hcross⟩ := continuation_cross_eq_coordinateSlice H B hH hU z₀ pU
        (fun z w heq => hA z w (valuationKernelRestrict_eq_of_firstCoordinate H i B hB heq))
      exact ⟨⟨_, RationalUnitaryPoleFactorization.ofSlice H B hH c p.denominator z₀.val hb,
        _, hN, fun z => (hcross z).symm⟩⟩)

end RationalOperatorPolePresentation
end Langlands.Plancherel

namespace Langlands.Plancherel.DynamicOppositeMaximalLeviRegularity

open Aubert.General DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar
open DynamicOppositeAmbientTwist

attribute [local instance]
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsAffine
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsTopologicalGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarLocallyCompactSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology2
  DynamicOppositeCanonicalScalar.centralizerClosedImmersion
  DynamicOppositeCanonicalScalar.centralizerAffine
  DynamicOppositeCanonicalScalar.centralizerFiniteType
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup2

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hG : IsConnectedReductive G)
  (hχ : IsMaximalProper χ hG)
  (hRefl : RelativeRootReflectionExistenceStatement.{u})
  (hCST : CentralSplitTorusCharacterStatement.{u})
  (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
  (hPK : ∀ g : rationalPoints G, ∃ p : parabolic χ, ∃ k : K,
    g = (p : rationalPoints G) * (k : rationalPoints G))
  (hOppK : ∀ g : rationalPoints G, ∃ p : oppositeParabolic χ, ∃ k : K,
    g = (p : rationalPoints G) * (k : rationalPoints G))
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))
  {U : Set (unramifiedCharacters (normCharacters χ))}
  (hU : IsOpen U) (z₀ : U)

/-- For the actual forward compact standard operator at a maximal proper
parabolic, ambient twist invariance supplies the pole presentation. -/
def forwardPolePresentation
    (p : ForwardContinuation χ hRefl hCST hG K hK hPK hOppK A)
    (hsub : U ⊆ forwardFullDomainRegion χ K hK A) :
    RationalOperatorPolePresentation (parameterScheme χ) p.denominator p.numerator :=
  Classical.choice (by
    obtain ⟨r, n, hr, e, he⟩ := exists_kernel_coordinates χ hG hχ
    refine ⟨RationalOperatorPolePresentation.ofAmbientInvariant (parameterScheme χ)
      (Dynamic.Affine.centralizerHom χ) (parameterScheme_isConnectedReductive χ hG)
      hr e he hU z₀ hsub p ?_⟩
    intro eta z w hzw
    have heq : (⟨z.val, hsub z.property⟩ : forwardFullDomainRegion χ K hK A) =
        ⟨restrictedAmbientParameter χ eta * w.val, hzw ▸ hsub z.property⟩ :=
      Subtype.ext hzw
    rw [heq]
    exact conditionalForwardCompactFamily_ambient_mul χ hG eta K hK A hRefl hCST hPK hOppK
      w.val (hsub w.property) _)

/-- The reverse compact standard operator at the same maximal proper
parabolic has the corresponding pole presentation. -/
def reversePolePresentation
    (p : ReverseContinuation χ hRefl hCST hG K hK hPK hOppK A)
    (hsub : U ⊆ reverseFullDomainRegion χ K hK A) :
    RationalOperatorPolePresentation (parameterScheme χ) p.denominator p.numerator :=
  Classical.choice (by
    obtain ⟨r, n, hr, e, he⟩ := exists_kernel_coordinates χ hG hχ
    refine ⟨RationalOperatorPolePresentation.ofAmbientInvariant (parameterScheme χ)
      (Dynamic.Affine.centralizerHom χ) (parameterScheme_isConnectedReductive χ hG)
      hr e he hU z₀ hsub p ?_⟩
    intro eta z w hzw
    have heq : (⟨z.val, hsub z.property⟩ : reverseFullDomainRegion χ K hK A) =
        ⟨restrictedAmbientParameter χ eta * w.val, hzw ▸ hsub z.property⟩ :=
      Subtype.ext hzw
    rw [heq]
    exact conditionalReverseCompactFamily_ambient_mul χ hG eta K hK A hRefl hCST hPK hOppK
      w.val (hsub w.property) _)

end Langlands.Plancherel.DynamicOppositeMaximalLeviRegularity
