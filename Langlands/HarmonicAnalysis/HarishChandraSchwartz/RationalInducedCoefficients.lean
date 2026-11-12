import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalTemperedInduction
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.InducedCoefficientTwistXi
import Langlands.Representation.Aubert.General.RationalLeviNormTopology

/-! # The coefficient map `E_P^G` on actual rational points and Lemma VI.2.2

For a connected reductive group `G` over a nonarchimedean local field, a maximal split torus, a
generic cocharacter and an actual standard parabolic `P_I = M_I U_I ⊇ P₀` (`I` a finite set of
simple roots), this module instantiates Worker 200's coefficient map on the product-induced space
`L(ω, P) = I_{P×P}^{G×G}(ω ⊗ ω^∨)` (Waldspurger V.1) on actual rational points
(`rationalInducedCoefficientMap`), and proves Waldspurger's Lemma VI.2.2 for it: if the
coefficients of an admissible representation of `M_I(F)` are bounded by multiples of `Ξ^{M_I}`,
then the coefficients `E_P^G(F)` are bounded by multiples of `Ξ`, uniformly over the unitary
unramified twists in the compact picture.
-/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel


namespace Langlands.HarishChandraSchwartz

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

local instance rationalInducedSecondCountable : SecondCountableTopology (rationalPoints G) :=
  rationalPoint_secondCountableTopology F G
local instance rationalInducedT2 : T2Space (rationalPoints G) := rationalPoint_t2Space F G
local instance rationalInducedNonarchimedean : NonarchimedeanGroup (rationalPoints G) :=
  Plancherel.rationalPoints_nonarchimedeanGroup G

variable {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}


section Coefficients

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (I : Finset (RationalPointFamily.SimpleRoot i ν))

omit [LocallyOfFiniteType G.X.hom] in
include hG hi hν in
/-- The actual standard parabolic `P_I(F)` is closed. -/
theorem isClosed_standardParabolicPoints_rootSet :
    IsClosed (standardParabolicPoints i ν (RationalPointFamily.rootSet i ν I) :
      Set (rationalPoints G)) := by
  have := hi.isSplitSubtorus.mono
  exact RationalPointFamily.isClosed_standard_parabolic i ν standardCocharacter hG hi hν I

include hG hi hν in
/-- The actual standard parabolic `P_I(F)` is locally compact. -/
theorem locallyCompactSpace_standardParabolicPoints_rootSet :
    LocallyCompactSpace (standardParabolicPoints i ν (RationalPointFamily.rootSet i ν I)) :=
  (isClosed_standardParabolicPoints_rootSet hG hi hν I).locallyCompactSpace

variable {K : OpenSubgroup (rationalPoints G)}

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
include hG hi hν in
/-- `G(F) = P₀(F) K` gives `G(F) = P_I(F) K`. -/
theorem exists_standardParabolicPoints_rootSet_mul
    (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) (K : Subgroup (rationalPoints G)))
    (g : rationalPoints G) :
    ∃ q ∈ standardParabolicPoints i ν (RationalPointFamily.rootSet i ν I), ∃ k ∈ K, g = q * k := by
  obtain ⟨p, hp, k, hk, e⟩ := hPK g
  exact ⟨p, standardParabolicPoints_empty_le hG hi hν (RationalPointFamily.rootSet_subset i ν I)
    hp, k, hk, e⟩

variable (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) (K : Subgroup (rationalPoints G)))

/-- **Waldspurger's coefficient map `E_P^G` on actual rational points** (V.1, printed p. 288):
for the actual standard parabolic `P = P_I(F) = M_I(F) ⋉ U_I(F)`, a compact open subgroup `K`
with `G(F) = P₀(F) K` and an admissible smooth representation `A` of `M_I(F)`, the linear map
from the product-induced space `L(A, P) = I_{P×P}^{G×G}(A ⊗ A^∨)` to locally constant functions
on `G(F)` whose value at `Φ` and `g` is `∫_K ⟨Φ(k g, k)⟩ dk` for the Haar probability measure of
`K` (`rationalInducedCoefficientMap_integral`); on the image of `f ⊗ f^∨` this is
`∫_K ⟨f^∨(k), f(k g)⟩ dk` (the Library's `CompactInduction.coefficientMap_tmul`), Waldspurger's
`⟨π(g) f, f^∨⟩`. It is the Library's `CompactInduction.coefficientMap` with the actual decomposition
`isSemidirectDecomposition_standard`, the unimodularity of `G(F)`
(`rationalReductiveUnimodularity`) and the modular character of `P_I(F)`
(`modularCharacter_standardParabolicPoints`). -/
def rationalInducedCoefficientMap
    (A : SmoothRep.{0, u, uV} ℂ
      (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)))
    (hA : A.IsAdmissible) :=
  haveI := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I
  CompactInduction.coefficientMap (G := rationalPoints G)
    (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
    (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I)) A K hKc
    (isClosed_standardParabolicPoints_rootSet hG hi hν I)
    (continuous_projection_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I) _)
    (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK)
    (fun g => RationalPointFamily.rationalReductiveUnimodularity F G hG standardCocharacter g)
    (modularCharacter_standardParabolicPoints hG hi hν I rfl
      (RationalPointFamily.rootSet_subset i ν I)) hA


variable (A : SmoothRep.{0, u, uV} ℂ
  (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I))) (hA : A.IsAdmissible)

/-- `rationalInducedCoefficientMap` unfolded to the Library's `CompactInduction.coefficientMap`
with its explicit actual arguments. -/
theorem rationalInducedCoefficientMap_eq_coefficientMap :
    rationalInducedCoefficientMap hG hi hν I hKc hPK A hA =
      (haveI := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I
      CompactInduction.coefficientMap (G := rationalPoints G)
        (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
        (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I)) A K hKc
        (isClosed_standardParabolicPoints_rootSet hG hi hν I)
        (continuous_projection_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I) _)
        (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK)
        (fun g => RationalPointFamily.rationalReductiveUnimodularity F G hG standardCocharacter g)
        (modularCharacter_standardParabolicPoints hG hi hν I rfl
          (RationalPointFamily.rootSet_subset i ν I)) hA) :=
  rfl

/-- The coefficient `E_P^G(F)(g)` is the integral over `K`, for its Haar probability measure,
of the diagonal contraction `k ↦ ⟨Φ(k g, k)⟩` (`CompactInduction.integrand`). -/
theorem rationalInducedCoefficientMap_integral
    (Φ : productInducedCoefficientObject (G := rationalPoints G)
      (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
      (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I)) A)
    (g : rationalPoints G) :
    rationalInducedCoefficientMap hG hi hν I hKc hPK A hA Φ g =
      ∫ k : K, CompactInduction.integrand
        (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
        (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I)) A K g Φ k
        ∂CompactInduction.measure K hKc := by
  have := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I
  have h := CompactInduction.coefficientMap_integral (G := rationalPoints G)
    (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
    (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I)) A K hKc
    (isClosed_standardParabolicPoints_rootSet hG hi hν I)
    (continuous_projection_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I) _)
    (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK)
    (fun g => RationalPointFamily.rationalReductiveUnimodularity F G hG standardCocharacter g)
    (modularCharacter_standardParabolicPoints hG hi hν I rfl
      (RationalPointFamily.rootSet_subset i ν I)) hA Φ g
  rw [rationalInducedCoefficientMap_eq_coefficientMap hG hi hν I hKc hPK A hA]
  convert h using 2

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
include hG hi hν hKc hPK in
/-- `P_I(F) \ G(F)` is compact, being the image of the compact `K`. -/
theorem compactSpace_leftQuotient_standardParabolicPoints_rootSet :
    CompactSpace (Induction.LeftQuotient
      (standardParabolicPoints i ν (RationalPointFamily.rootSet i ν I))) :=
  Induction.compactSpace_leftQuotient_of_compact_representatives _ hKc
    (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK)

/-- `E_P^G` intertwines the action of `G(F) × G(F)` on `L(A, P)` with the translation
`φ ↦ (g ↦ φ(x₂⁻¹ g x₁))`. -/
theorem rationalInducedCoefficientMap_action (x : rationalPoints G × rationalPoints G)
    (Φ : productInducedCoefficientObject (G := rationalPoints G)
      (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
      (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I)) A)
    (g : rationalPoints G) :
    rationalInducedCoefficientMap hG hi hν I hKc hPK A hA
        ((productInducedCoefficientObject (G := rationalPoints G)
          (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
          (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I))
          A).representation x Φ) g =
      rationalInducedCoefficientMap hG hi hν I hKc hPK A hA Φ (x.2⁻¹ * g * x.1) := by
  have := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I
  have h := CompactInduction.coefficientMap_action (G := rationalPoints G)
    (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
    (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I)) A K hKc
    (isClosed_standardParabolicPoints_rootSet hG hi hν I)
    (continuous_projection_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I) _)
    (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK)
    (fun g => RationalPointFamily.rationalReductiveUnimodularity F G hG standardCocharacter g)
    (modularCharacter_standardParabolicPoints hG hi hν I rfl
      (RationalPointFamily.rootSet_subset i ν I)) hA x Φ g
  rw [rationalInducedCoefficientMap_eq_coefficientMap hG hi hν I hKc hPK A hA]
  exact h

/-- Every coefficient `E_P^G(F)` is bi-invariant under one open subgroup of `G(F)`. -/
theorem rationalInducedCoefficientMap_biInvariant
    (Φ : productInducedCoefficientObject (G := rationalPoints G)
      (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
      (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I)) A) :
    ∃ L : OpenSubgroup (rationalPoints G), ∀ (k l : L) (g : rationalPoints G),
      rationalInducedCoefficientMap hG hi hν I hKc hPK A hA Φ
          ((k : rationalPoints G) * g * (l : rationalPoints G)) =
        rationalInducedCoefficientMap hG hi hν I hKc hPK A hA Φ g := by
  have := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I
  have h := CompactInduction.coefficientMap_biInvariant (G := rationalPoints G)
    (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
    (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I)) A K hKc
    (isClosed_standardParabolicPoints_rootSet hG hi hν I)
    (continuous_projection_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I) _)
    (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK)
    (fun g => RationalPointFamily.rationalReductiveUnimodularity F G hG standardCocharacter g)
    (modularCharacter_standardParabolicPoints hG hi hν I rfl
      (RationalPointFamily.rootSet_subset i ν I)) hA Φ
  rw [rationalInducedCoefficientMap_eq_coefficientMap hG hi hν I hKc hPK A hA]
  exact h

/-- The image of `E_P^G` is exactly the space of matrix coefficients of the normalized
induced representation `I_P^G A` (`normalizedCoefficientMap`). -/
theorem range_rationalInducedCoefficientMap :
    LinearMap.range (rationalInducedCoefficientMap hG hi hν I hKc hPK A hA) =
      LinearMap.range (normalizedCoefficientMap (G := rationalPoints G)
        (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
        (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I)) A) := by
  have := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I
  have h := CompactInduction.range_coefficientMap (G := rationalPoints G)
    (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
    (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I)) A K hKc
    (isClosed_standardParabolicPoints_rootSet hG hi hν I)
    (continuous_projection_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I) _)
    (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK)
    (fun g => RationalPointFamily.rationalReductiveUnimodularity F G hG standardCocharacter g)
    (modularCharacter_standardParabolicPoints hG hi hν I rfl
      (RationalPointFamily.rootSet_subset i ν I)) hA
  rw [rationalInducedCoefficientMap_eq_coefficientMap hG hi hν I hKc hPK A hA]
  exact h

variable (hM : IsIwasawaPair
  ((standardParabolicPoints i ν ∅).subgroupOf
    (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)))
  ((K : Subgroup (rationalPoints G)).subgroupOf
    (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I))))

/-- **Waldspurger's Lemma VI.2.2 on actual rational points**, for one representation: if every
coefficient of the admissible representation `A` of `M_I(F)` is bounded by a multiple of
`Ξ^{M_I}` (the conclusion of Corollary III.1.2 for `M_I`, hypothesis `hcoeff`), then every
coefficient `E_P^G(F)` of `I_{P_I}^G A` satisfies `|E_P^G(F)(g)| ≤ C Ξ(g)` on `G(F)`. -/
theorem norm_rationalInducedCoefficientMap_le_rationalXi
    (hcoeff : ∀ (v : A) (ℓ : SmoothDual A.representation),
      ∃ C : ℝ, 0 < C ∧ ∀ m, ‖ℓ.val (A.representation m v)‖ ≤ C * rationalLeviXi hKc hM m)
    (Φ : productInducedCoefficientObject (G := rationalPoints G)
      (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
      (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I)) A) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : rationalPoints G,
      ‖rationalInducedCoefficientMap hG hi hν I hKc hPK A hA Φ g‖ ≤ C * rationalXi hKc hPK g := by
  have : CompactSpace (K : Subgroup (rationalPoints G)) := isCompact_iff_compactSpace.mp hKc
  have := compactSpace_subgroupOf_standardLevi (i := i) (ν := ν)
    (J := RationalPointFamily.rootSet i ν I) hKc
  have := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I
  have h := norm_coefficientMap_le_xi (G := rationalPoints G)
    (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
    (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I)) A K hKc
    (isClosed_standardParabolicPoints_rootSet hG hi hν I)
    (continuous_projection_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I) _)
    (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK)
    (fun g => RationalPointFamily.rationalReductiveUnimodularity F G hG standardCocharacter g)
    (modularCharacter_standardParabolicPoints hG hi hν I rfl
      (RationalPointFamily.rootSet_subset i ν I)) hA
    (isUnimodularModulus_standardUnipotentPoints hG hi hν I rfl)
    (rationalLeviData hG hi hν (RationalPointFamily.rootSet_subset i ν I) K.isOpen hKc) hPK hM
    (fun p hp => rationalMinimalModulus_eq_one i ν K.isOpen hKc p hp) hcoeff Φ
  obtain ⟨C, hC, hb⟩ := h
  refine ⟨C, hC, fun g => ?_⟩
  have hx : xi (G := rationalPoints G) hPK (rationalMinimalModulus i ν) g =
      rationalXi hKc hPK g := rfl
  rewrite [rationalInducedCoefficientMap_eq_coefficientMap hG hi hν I hKc hPK A hA, ← hx]
  with_reducible_and_instances exact hb g

/-- Waldspurger's `v_χ` (proof of Lemma VI.2.2) on actual points: for a unitary unramified
character `χ ∈ Im X(M_I)` (an element of `unramifiedCharacters` for the norms `|χ'|_F` of the
rational characters `χ'` of the Levi scheme, `leviRationalNormCharacters`) and a section `F₀` of
the compact picture of `L(A, P)`, the element of `L(A ⊗ χ, P)` whose restriction to `K × K` is
`F₀`. -/
def rationalTwistedSection
    (χ : unramifiedCharacters (G := {x : rationalPoints G //
        @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
          (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)) x})
      (RationalPointFamily.leviRationalNormCharacters i ν I))
    (F₀ : ProductInducedCompactPicture (G := rationalPoints G)
      (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
      K A) :
    productInducedCoefficientObject (G := rationalPoints G)
      (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
      (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I))
      (SmoothRep.twist (G := {x : rationalPoints G //
          @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
            (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)) x})
        χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker _ χ) A) :=
  twistedSection (G := rationalPoints G)
    (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
    (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I)) A K
    (RationalPointFamily.leviRationalNormCharacters i ν I)
    (isClosed_standardParabolicPoints_rootSet hG hi hν I) hKc
    (RationalPointFamily.continuous_leviRationalNormCharacters i ν I)
    (continuous_projection_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I) _)
    (factorization_subtype (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK)) χ F₀

/-- `rationalTwistedSection` unfolded to the Library's `twistedSection`. -/
theorem rationalTwistedSection_eq_twistedSection
    (χ : unramifiedCharacters (G := {x : rationalPoints G //
        @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
          (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)) x})
      (RationalPointFamily.leviRationalNormCharacters i ν I))
    (F₀ : ProductInducedCompactPicture (G := rationalPoints G)
      (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
      K A) :
    rationalTwistedSection hG hi hν I hKc hPK A χ F₀ =
      twistedSection (G := rationalPoints G)
        (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
        (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I)) A K
        (RationalPointFamily.leviRationalNormCharacters i ν I)
        (isClosed_standardParabolicPoints_rootSet hG hi hν I) hKc
        (RationalPointFamily.continuous_leviRationalNormCharacters i ν I)
        (continuous_projection_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I) _)
        (factorization_subtype (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK)) χ F₀ :=
  rfl

/-- **Waldspurger's Lemma VI.2.2 on actual rational points, uniform over `Im X(M_I)`**: under
the hypothesis `hcoeff` of `norm_rationalInducedCoefficientMap_le_rationalXi`, for every fixed
section `F₀` of the compact picture there is one `C > 0` with
`|E_P^G(v_χ)(g)| ≤ C Ξ(g)` for every unitary unramified character `χ` of `M_I(F)` and every
`g ∈ G(F)`, where `v_χ = rationalTwistedSection χ F₀ ∈ L(A ⊗ χ, P)`. -/
theorem norm_rationalInducedCoefficientMap_twist_le_rationalXi
    (hcoeff : ∀ (v : A) (ℓ : SmoothDual A.representation),
      ∃ C : ℝ, 0 < C ∧ ∀ m, ‖ℓ.val (A.representation m v)‖ ≤ C * rationalLeviXi hKc hM m)
    (F₀ : ProductInducedCompactPicture (G := rationalPoints G)
      (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
      K A) :
    ∃ C : ℝ, 0 < C ∧
      ∀ χ : unramifiedCharacters (G := {x : rationalPoints G //
            @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
              (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)) x})
          (RationalPointFamily.leviRationalNormCharacters i ν I),
        (∀ m, ‖(χ.val m : ℂ)‖ = 1) → ∀ g : rationalPoints G,
        ‖rationalInducedCoefficientMap hG hi hν I hKc hPK
            (SmoothRep.twist (G := {x : rationalPoints G //
                @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
                  (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)) x})
              χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker _ χ) A)
            ((SmoothRep.isAdmissible_twist_iff (G := {x : rationalPoints G //
                @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
                  (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)) x}) _ _ A).mpr hA)
            (rationalTwistedSection hG hi hν I hKc hPK A χ F₀) g‖ ≤
          C * rationalXi hKc hPK g := by
  have : CompactSpace (K : Subgroup (rationalPoints G)) := isCompact_iff_compactSpace.mp hKc
  have := compactSpace_subgroupOf_standardLevi (i := i) (ν := ν)
    (J := RationalPointFamily.rootSet i ν I) hKc
  have := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I
  have h := norm_twist_coefficientMap_le_xi (G := rationalPoints G)
    (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
    (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I)) A K hKc
    (RationalPointFamily.leviRationalNormCharacters i ν I)
    (RationalPointFamily.continuous_leviRationalNormCharacters i ν I)
    (isClosed_standardParabolicPoints_rootSet hG hi hν I)
    (continuous_projection_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I) _)
    (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK)
    (fun g => RationalPointFamily.rationalReductiveUnimodularity F G hG standardCocharacter g)
    (modularCharacter_standardParabolicPoints hG hi hν I rfl
      (RationalPointFamily.rootSet_subset i ν I)) hA
    (isUnimodularModulus_standardUnipotentPoints hG hi hν I rfl)
    (rationalLeviData hG hi hν (RationalPointFamily.rootSet_subset i ν I) K.isOpen hKc) hPK hM
    (fun p hp => rationalMinimalModulus_eq_one i ν K.isOpen hKc p hp) hcoeff F₀
  obtain ⟨C, hC, hb⟩ := h
  refine ⟨C, hC, fun χ hχ g => ?_⟩
  have hx : xi (G := rationalPoints G) hPK (rationalMinimalModulus i ν) g =
      rationalXi hKc hPK g := rfl
  rewrite [rationalTwistedSection_eq_twistedSection hG hi hν I hKc hPK A χ F₀,
    rationalInducedCoefficientMap_eq_coefficientMap hG hi hν I hKc hPK, ← hx]
  with_reducible_and_instances exact hb χ hχ g

end Coefficients

end Langlands.HarishChandraSchwartz
