import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalInducedOrbitWavePacket
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.OrbitWavePacketDecay
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalValuationCoordinates
import Langlands.Representation.CuspidalSupport.RationalCuspidalBlockVisibility

/-! # The first bound of Proposition VI.3.1 for actual standard parabolic subgroups

For a connected reductive group `G` over a nonarchimedean local field, a maximal split torus, a
generic cocharacter and an actual standard parabolic `P = P_I(F) = M_I(F) ⋉ U_I(F) ⊇ P₀(F)`, this
module proves on actual rational points the first bound in Waldspurger's proof of Proposition
VI.3.1 for the wave packets `f_ψ` of `RationalInducedOrbitWavePacket`:
`|f_ψ(g)| ≤ c Ξ(g) (1 + ‖n_G(g)‖)^{-r}`, where `n_G(g) ∈ ℤ^r` are the lattice coordinates of the
valuation image of `g` (Waldspurger's `H_G(g)` in a basis of its image lattice).

It supplies the data that the Library's abstract `exists_norm_inducedOrbitWavePacket_le_xi_rpow`
leaves as hypotheses:

* `n_G` as a homomorphism (`rationalValuationCoordinatesHom`), surjective with kernel the common
  norm kernel `G(F)¹`;
* `n_G` is trivial on the compact open `K` and on `U_I(F)`;
* the restriction `Im X(G) → Im X(M_I)` in circle coordinates is the integer monomial map of the
  matrix `leviValuationRestrictionMatrix`, obtained from a general factorization lemma for
  lattice-valued homomorphisms (`latticeFactorMatrix`).
-/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel
open Langlands.HarmonicAnalysis.TorusFourier

namespace Langlands.HarishChandraSchwartz

section LatticeFactor

variable {H : Type*} [Group H] {J L : Type*} [Fintype J] [DecidableEq J] [Fintype L]

/-- The torus character `∏ⱼ zⱼ^{mⱼ}` as the image in `ℂ` of a product in `Circle`. -/
theorem torusCharacter_eq_coe_prod {K : Type*} [Fintype K] (m : K → ℤ) (y : K → Circle) :
    torusCharacter m y = ((∏ k, y k ^ m k : Circle) : ℂ) := by
  rw [torusCharacter]
  change _ = Circle.coeHom (∏ k, y k ^ m k)
  rw [map_prod]
  rfl

/-- `∏ⱼ (∏ₗ z_l^{a_{jl}})^{n_j} = ∏ₗ z_l^{Σⱼ n_j a_{jl}}`. -/
theorem torusCharacter_finiteTorusMonomial (a : J → L → ℤ) (n : J → ℤ) (z : L → Circle) :
    torusCharacter n (finiteTorusMonomial a z) = torusCharacter (∑ j, n j • a j) z := by
  rw [torusCharacter_eq_coe_prod, torusCharacter_eq_coe_prod]
  congr 1
  simp only [finiteTorusMonomial, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [← Finset.prod_zpow, ← zpow_mul]
  rw [Finset.prod_comm]
  have hzs : ∀ (y : Circle) (s : Finset J) (f : J → ℤ), ∏ x ∈ s, y ^ f x = y ^ ∑ x ∈ s, f x := by
    intro y s f
    induction s using Finset.induction_on with
    | empty => simp
    | insert x s hx ih => rw [Finset.prod_insert hx, Finset.sum_insert hx, ih, zpow_add]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [hzs]
  congr 1
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

variable (nH : H →* Multiplicative (J → ℤ)) (hs : Function.Surjective nH)
  (φ : H →* Multiplicative (L → ℤ)) (hk : nH.ker ≤ φ.ker)

/-- The integer matrix of the factorization of `φ` through a surjective `nH` with smaller
kernel: row `j` is the image of the `j`-th basis vector. -/
def latticeFactorMatrix : J → L → ℤ := fun j =>
  AddMonoidHom.toMultiplicative.symm
    (nH.liftOfRightInverse (Function.surjInv hs) (Function.rightInverse_surjInv hs) ⟨φ, hk⟩)
    (fun i => if j = i then 1 else 0)

omit [Fintype L] in
/-- `φ(h) = Σⱼ nH(h)_j a_j` for the rows `a_j` of `latticeFactorMatrix`. -/
theorem toAdd_eq_sum_latticeFactorMatrix (h : H) :
    Multiplicative.toAdd (φ h) =
      ∑ j, Multiplicative.toAdd (nH h) j • latticeFactorMatrix nH hs φ hk j := by
  set θ := nH.liftOfRightInverse (Function.surjInv hs) (Function.rightInverse_surjInv hs) ⟨φ, hk⟩
  have hθ : θ (nH h) = φ h :=
    MonoidHom.liftOfRightInverse_comp_apply nH (Function.surjInv hs)
      (Function.rightInverse_surjInv hs) ⟨φ, hk⟩ h
  rw [← hθ]
  exact (AddMonoidHom.toMultiplicative.symm θ).toIntLinearMap.pi_apply_eq_sum_univ
    (Multiplicative.toAdd (nH h))

/-- In torus coordinates: the character `z ↦ z^{φ(h)}` is the character `y ↦ y^{nH(h)}`
evaluated at the monomial image `y = finiteTorusMonomial a z`. -/
theorem torusCharacter_latticeFactorMatrix (h : H) (z : L → Circle) :
    torusCharacter (Multiplicative.toAdd (nH h))
        (finiteTorusMonomial (latticeFactorMatrix nH hs φ hk) z) =
      torusCharacter (Multiplicative.toAdd (φ h)) z := by
  rw [torusCharacter_finiteTorusMonomial, toAdd_eq_sum_latticeFactorMatrix nH hs φ hk h]

end LatticeFactor

section ValuationHom

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)

/-- The lattice coordinates `n_G(g) ∈ ℤ^r` of the valuation image (Waldspurger's `H_G` in a
basis of its image lattice), as a homomorphism `G(F) → ℤ^r`. -/
def rationalValuationCoordinatesHom :
    rationalPoints G →* Multiplicative (Fin (rationalImageRank G) → ℤ) where
  toFun g := Multiplicative.ofAdd (rationalValuationCoordinates G hG g)
  map_one' := by
    rw [rationalValuationCoordinates_one]
    rfl
  map_mul' g h := by
    rw [rationalValuationCoordinates_mul]
    rfl

@[simp]
theorem toAdd_rationalValuationCoordinatesHom (g : rationalPoints G) :
    Multiplicative.toAdd (rationalValuationCoordinatesHom G hG g) =
      rationalValuationCoordinates G hG g := rfl

theorem surjective_rationalValuationCoordinatesHom :
    Function.Surjective (rationalValuationCoordinatesHom G hG) := by
  intro x
  obtain ⟨g, hg⟩ := rationalValuationImageProjection_surjective G
    (Additive.toMul ((rationalValuationLatticeEquiv G hG).symm (Multiplicative.toAdd x)))
  refine ⟨g, ?_⟩
  change Multiplicative.ofAdd (rationalValuationLatticeEquiv G hG
    (Additive.ofMul (rationalValuationImageProjection G g))) = x
  rw [hg]
  simp

theorem ker_rationalValuationCoordinatesHom :
    (rationalValuationCoordinatesHom G hG).ker = rationalCommonNormKernel G := by
  rw [← rationalValuationImageProjection_ker]
  ext g
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
  change Multiplicative.ofAdd (rationalValuationLatticeEquiv G hG
    (Additive.ofMul (rationalValuationImageProjection G g))) = 1 ↔ _
  constructor
  · intro h
    have h' : rationalValuationLatticeEquiv G hG
        (Additive.ofMul (rationalValuationImageProjection G g)) = 0 := h
    rw [AddEquiv.map_eq_zero_iff] at h'
    exact h'
  · intro h
    change Multiplicative.ofAdd (rationalValuationLatticeEquiv G hG
      (Additive.ofMul (rationalValuationImageProjection G g))) = Multiplicative.ofAdd 0
    rw [h]
    simp

end ValuationHom

section Levi

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}

local instance instRationalInducedOrbitWavePacketDecay1 : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance instRationalInducedOrbitWavePacketDecay2
    (I : Finset (RationalPointFamily.SimpleRoot i ν)) :
    IsClosedImmersion (Standard.leviHom i ν (RationalPointFamily.rootSet i ν I)).hom.hom.left :=
  Standard.isClosedSubgroup_leviHom i ν (RationalPointFamily.rootSet i ν I)
local instance instRationalInducedOrbitWavePacketDecay3
    (I : Finset (RationalPointFamily.SimpleRoot i ν)) :
    IsAffine (Standard.leviScheme i ν (RationalPointFamily.rootSet i ν I)).X.left :=
  isAffine_of_isAffineHom (Standard.leviHom i ν (RationalPointFamily.rootSet i ν I)).hom.hom.left
local instance instRationalInducedOrbitWavePacketDecay4 : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology
local instance instRationalInducedOrbitWavePacketDecay5
    (I : Finset (RationalPointFamily.SimpleRoot i ν)) :
    TopologicalSpace
      (rationalPoints (Standard.leviScheme i ν (RationalPointFamily.rootSet i ν I))) :=
  rationalPointTopology F (Standard.leviScheme i ν (RationalPointFamily.rootSet i ν I)).X

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (I : Finset (RationalPointFamily.SimpleRoot i ν))

/-- The kernel of `n_{M_I}` (the common norm kernel `M_I(F)¹`) lies in the kernel of
`n_G ∘ j`, `j : M_I → G` the Levi inclusion. -/
theorem ker_rationalValuationCoordinatesHom_levi_le :
    (rationalValuationCoordinatesHom (Standard.leviScheme i ν (RationalPointFamily.rootSet i ν I))
        (isConnectedReductive_leviScheme_rootSet hG hi hν I)).ker ≤
      ((rationalValuationCoordinatesHom G hG).comp
        (rationalPoints.map (Standard.leviHom i ν (RationalPointFamily.rootSet i ν I)))).ker := by
  rw [ker_rationalValuationCoordinatesHom, ← MonoidHom.comap_ker,
    ker_rationalValuationCoordinatesHom]
  exact rationalCommonNormKernel_le_comap _

/-- **The restriction `Im X(G) → Im X(M_I)` in coordinates**: the integer matrix `a` with
`n_G(j(m)) = Σⱼ n_{M_I}(m)_j a_j` for `m ∈ M_I(F)`, so that the restriction to `M_I(F)` of the
character of `G(F)` with circle coordinates `z` has the coordinates `finiteTorusMonomial a z`. -/
def leviValuationRestrictionMatrix :
    Fin (rationalImageRank (Standard.leviScheme i ν (RationalPointFamily.rootSet i ν I))) →
      Fin (rationalImageRank G) → ℤ :=
  latticeFactorMatrix
    (rationalValuationCoordinatesHom (Standard.leviScheme i ν (RationalPointFamily.rootSet i ν I))
      (isConnectedReductive_leviScheme_rootSet hG hi hν I))
    (surjective_rationalValuationCoordinatesHom _ _)
    ((rationalValuationCoordinatesHom G hG).comp
      (rationalPoints.map (Standard.leviHom i ν (RationalPointFamily.rootSet i ν I))))
    (ker_rationalValuationCoordinatesHom_levi_le hG hi hν I)

-- `M_I(F)` as a subtype of `G(F) = rationalPoints G`, with the membership of `Subgroup G(F)`.
set_option hygiene false in
local notation "𝐌" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)) x}

/-- The restriction to `M_I(F)` of the unitary unramified character of `G(F)` with circle
coordinates `z` is the character of `M_I(F)` with coordinates
`finiteTorusMonomial (leviValuationRestrictionMatrix …) z`: at `m ∈ M_I(F)` both equal
`∏ₗ z_l^{n_G(m)_l}`. -/
theorem leviRationalUnitaryCoordinates_symm_finiteTorusMonomial_apply (m : 𝐌)
    (z : Fin (rationalImageRank G) → Circle) :
    (((leviRationalUnitaryCoordinates hG hi hν I).toMulEquiv.symm
        (finiteTorusMonomial (leviValuationRestrictionMatrix hG hi hν I) z)).val m : ℂ) =
      torusCharacter (Multiplicative.toAdd (rationalValuationCoordinatesHom G hG m)) z := by
  set pt := RationalPointFamily.leviRationalPointHomeomorph i ν I
  set hL := isConnectedReductive_leviScheme_rootSet hG hi hν I
  have h2 : (rationalPoints.map (Standard.leviHom i ν (RationalPointFamily.rootSet i ν I))
      (pt.symm m) : rationalPoints G) = (m : rationalPoints G) := by
    rw [← RationalPointFamily.leviRationalPointHomeomorph_apply_coe,
      ContinuousMulEquiv.apply_symm_apply]
  have h1 : (((leviRationalUnitaryCoordinates hG hi hν I).toMulEquiv.symm
        (finiteTorusMonomial (leviValuationRestrictionMatrix hG hi hν I) z)).val m : ℂ) =
      ((((rationalCanonicalUnitaryUnramifiedCharacterCoordinates _ hL).symm
        (finiteTorusMonomial (leviValuationRestrictionMatrix hG hi hν I) z)).val
          (pt.symm m) : ℂˣ) : ℂ) := rfl
  rw [h1, rationalUnitaryUnramifiedCharacter_apply]
  have h3 := torusCharacter_latticeFactorMatrix
    (rationalValuationCoordinatesHom (Standard.leviScheme i ν (RationalPointFamily.rootSet i ν I))
      hL)
    (surjective_rationalValuationCoordinatesHom _ _)
    ((rationalValuationCoordinatesHom G hG).comp
      (rationalPoints.map (Standard.leviHom i ν (RationalPointFamily.rootSet i ν I))))
    (ker_rationalValuationCoordinatesHom_levi_le hG hi hν I) (pt.symm m) z
  rw [MonoidHom.comp_apply, h2] at h3
  exact h3

include hi hν in
/-- `n_G` is trivial on the unipotent radical `U_I(F)`. -/
theorem rationalValuationCoordinatesHom_eq_one_of_mem_standardUnipotent
    {u : rationalPoints G}
    (hu : u ∈ standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I)) :
    rationalValuationCoordinatesHom G hG u = 1 := by
  have h := CuspidalSupport.standardUnipotent_le_rationalCommonNormKernel G i ν
    standardCocharacter hG hi hν I hu
  rw [← ker_rationalValuationCoordinatesHom G hG] at h
  exact h

end Levi

section WavePacket

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

variable {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (I : Finset (RationalPointFamily.SimpleRoot i ν))
  {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) (K : Subgroup (rationalPoints G)))

omit [LocallyOfFiniteType G.X.hom] in
include hKc in
/-- `n_G` is trivial on the compact open subgroup `K`. -/
theorem rationalValuationCoordinatesHom_eq_one_of_mem_compact {k : rationalPoints G}
    (hk : k ∈ K) : rationalValuationCoordinatesHom G hG k = 1 := by
  have h := compactSubgroup_le_rationalCommonNormKernel G (K : Subgroup (rationalPoints G)) hKc hk
  rw [← ker_rationalValuationCoordinatesHom G hG] at h
  exact h

-- `M_I(F)` as a subtype of `G(F) = rationalPoints G`, with the membership of `Subgroup G(F)`.
set_option hygiene false in
local notation "𝐌" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)) x}

variable (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
  (C : Subgroup 𝐌) [C.Normal] (hC : C ≤ Subgroup.center 𝐌)
  [MeasurableSpace (𝐌 ⧸ C)] (mu : Measure (𝐌 ⧸ C)) [mu.IsHaarMeasure]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation mu)
  (hM : IsIwasawaPair
    ((standardParabolicPoints i ν ∅).subgroupOf
      (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)))
    ((K : Subgroup (rationalPoints G)).subgroupOf
      (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I))))
  [Finite (discreteSeriesStabilizer C hC mu
    (RationalPointFamily.leviRationalNormCharacters i ν I) (discreteSeriesClass C hC mu π hsq))]
  (ρ : Measure (unitaryUnramifiedCharacters
    (RationalPointFamily.leviRationalNormCharacters i ν I)))
  (w : discreteSeriesOrbit C hC mu (RationalPointFamily.leviRationalNormCharacters i ν I)
      (discreteSeriesClass C hC mu π hsq) → ℂ)

/-- **The first bound in the proof of Proposition VI.3.1 on actual rational points**
(Waldspurger, printed p. 303): for a finite left invariant measure `ρ` on `Im X(M_I)`, a weight
`w` smooth in the circle coordinates of `Im X(M_I)`, the coefficient bound `hcoeff` on `π`, a
section `ψ = q ∈ C^∞(O, P)` and every real `r`, there is `c > 0` with
`|f_ψ(g)| ≤ c Ξ(g) (1 + ‖n_G(g)‖)^{-r}` for all `g ∈ G(F)`, where `n_G(g) ∈ ℤ^r` are the lattice
coordinates of the valuation image of `g` (`rationalValuationCoordinates`). -/
theorem exists_norm_rationalInducedOrbitWavePacket_le_rationalXi_rpow
    [IsFiniteMeasure ρ] [ρ.IsMulLeftInvariant]
    (hws : IsSmoothFiniteTorusFunction fun y =>
      w (discreteSeriesOrbitMap C hC mu (RationalPointFamily.leviRationalNormCharacters i ν I)
        (discreteSeriesClass C hC mu π hsq)
        ((leviRationalUnitaryCoordinates hG hi hν I).toMulEquiv.symm y)))
    (hcoeff : ∀ (v : π.obj) (ℓ : SmoothDual π.obj.representation),
      ∃ c : ℝ, 0 < c ∧ ∀ m, ‖ℓ.val (π.obj.representation m v)‖ ≤ c * rationalLeviXi hKc hM m)
    (q : rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π) (r : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∀ g : rationalPoints G,
      ‖rationalInducedOrbitWavePacket hG hi hν I hKc hPK π C hC mu hsq ρ w q g‖ ≤
        c * rationalXi hKc hPK g * (1 + ‖rationalValuationCoordinates G hG g‖) ^ (-r) := by
  have : CompactSpace (K : Subgroup (rationalPoints G)) := isCompact_iff_compactSpace.mp hKc
  have := compactSpace_subgroupOf_standardLevi (i := i) (ν := ν)
    (J := RationalPointFamily.rootSet i ν I) hKc
  have := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I
  obtain ⟨c, hc, hb⟩ := exists_norm_inducedOrbitWavePacket_le_xi_rpow (G := rationalPoints G)
    (M := standardLeviPoints i ν (RationalPointFamily.rootSet i ν I))
    (isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I))
    (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I))
    (isClosed_standardParabolicPoints_rootSet hG hi hν I) K hKc
    (factorization_subtype (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK))
    (fun g => RationalPointFamily.rationalReductiveUnimodularity F G hG standardCocharacter g)
    (modularCharacter_standardParabolicPoints hG hi hν I rfl
      (RationalPointFamily.rootSet_subset i ν I))
    (RationalPointFamily.leviRationalNormCharacters i ν I) π
    (RationalPointFamily.continuous_leviRationalNormCharacters i ν I)
    (continuous_projection_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I) _)
    (leviRationalUnitaryCoordinates hG hi hν I).toMulEquiv C hC mu hsq ρ w
    (leviRationalUnitaryCoordinates_hasLaurent hG hi hν I)
    (leviRationalUnitaryCoordinates hG hi hν I).continuous hws
    (rationalValuationCoordinatesHom G hG) (leviValuationRestrictionMatrix hG hi hν I)
    (fun k hk => rationalValuationCoordinatesHom_eq_one_of_mem_compact hG hKc hk)
    (fun u hu => rationalValuationCoordinatesHom_eq_one_of_mem_standardUnipotent hG hi hν I hu)
    (fun m z => leviRationalUnitaryCoordinates_symm_finiteTorusMonomial_apply hG hi hν I m z)
    (isUnimodularModulus_standardUnipotentPoints hG hi hν I rfl)
    (rationalLeviData hG hi hν (RationalPointFamily.rootSet_subset i ν I) K.isOpen hKc) hPK hM
    (fun p hp => rationalMinimalModulus_eq_one i ν K.isOpen hKc p hp) hcoeff q r
  refine ⟨c, hc, fun g => ?_⟩
  have hx : xi (G := rationalPoints G) hPK (rationalMinimalModulus i ν) g =
      rationalXi hKc hPK g := rfl
  have hn : Multiplicative.toAdd (rationalValuationCoordinatesHom G hG g) =
      rationalValuationCoordinates G hG g := rfl
  unfold rationalInducedOrbitWavePacket
  rewrite [← hx, ← hn]
  with_reducible_and_instances exact hb g

end WavePacket

end Langlands.HarishChandraSchwartz
