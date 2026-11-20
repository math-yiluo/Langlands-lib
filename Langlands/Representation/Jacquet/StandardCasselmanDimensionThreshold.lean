import Langlands.Representation.Jacquet.StablePairingDimensionThreshold
import Langlands.Representation.Jacquet.StandardCasselmanUniformAsymptotics

/-! # A representation-independent threshold for Proposition I.4.3 on the dominant lattice

For the actual standard parabolic `P_J = M_J U_J` of a connected reductive group with Renard's
simultaneous basis data, a basis member `K` and a natural number `d`, there is one threshold `T`
such that for **every** admissible representation `ρ` whose `K`-fixed vectors have dimension at
most `d`, every stable pairing `b` of the I.4.1 data of `P_J` for `ρ`, and all `K`-fixed `v` and
`ℓ`, the identity `ℓ(ρ(ϖ^λ) v) = b(ǰ(ℓ), j(ρ(ϖ^λ) v))` holds for every dominant `λ` with
`⟨α, λ⟩ > T` for the simple roots `α ∉ J`. The threshold is `d Σ_α |⟨α, z⟩|`, where `ϖ^z` is the
strict element of the split component used by the pairing data.

The commutation and factorization hypotheses of `IsStablePairing.asymptotics_of_finrank_le`
concern the compressions of the particular `ρ`. Here they are derived from group-level facts
(the Iwahori factorization of `K` relative to `P_∅`, the contraction properties of dominant
lattice points, and `ϖ^λ = ϖ^{λ - d z} g^d`) through `compressedAction_commute_of_factor` and
`compressedAction_mul_of_factor`, so they hold for every admissible `ρ` with `dim V^K ≤ d` at once.
-/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.BruhatTits.SpecialCompact

section DimensionThreshold

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] standardCasselmanIsAffine standardCasselmanTopology
  standardCasselmanTopologicalGroup

variable (hG : IsConnectedReductive G) {i : S.toGrp ⟶ G} (hi : IsMaximalSplitTorus i)
  {ν : cocharacterLattice S} (hν : IsGenericCocharacter i ν)
  {K0 : Subgroup (rationalPoints G)} {B : Set (Subgroup (rationalPoints G))}
  (hB : CompactOpenNormalBasis K0 B)
  (A : Set (characterLattice S) → CommGroupScheme (Spec (CommRingCat.of F)))
  (q : ∀ J, (A J).toGrp ⟶ S.toGrp)
  (hA : ∀ J, J ⊆ simpleRelativeRoots i ν →
    IsCompatibleStandardSplitComponent i ν J (A J) (q J))
  (hmem : ∀ J, J ⊆ simpleRelativeRoots i ν → ∀ K ∈ B,
    StandardParabolicBasisMember i ν J (q J) K)
  (ζ : Set (characterLattice S) → cocharacterLattice S)
  (hζ : ∀ J, J ⊆ simpleRelativeRoots i ν → IsStandardCocharacter i ν J (ζ J))

include hG hi hν hB hA hmem hζ in
open Langlands.Jacquet in
/-- **Proposition I.4.3 on the dominant lattice with a threshold depending only on `K` and `d`.**
For a face `J ⊆ Δ`, a basis member `K` and `d : ℕ` there is `T` such that for every admissible
`ρ` (carrier in the universe `uV`) whose `K`-fixed vectors have dimension at most `d`, every stable
pairing `b` of the I.4.1 data `standardCasselmanPairingData` of `P_J` for `ρ`, all `K`-fixed `v`,
`ℓ`, and every dominant `λ` with `⟨α, λ⟩ > T` for all simple roots `α ∉ J`,
`ℓ(ρ(ϖ^λ) v) = b(ǰ(ℓ), j(ρ(ϖ^λ) v))`. -/
theorem exists_dimension_threshold_standardCasselmanPairing {J : Set (characterLattice S)}
    (hJ : J ⊆ simpleRelativeRoots i ν) {K : Subgroup (rationalPoints G)} (hK : K ∈ B) (d : ℕ) :
    ∃ T : ℝ, ∀ {V : Type uV} [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (rationalPoints G) V) (hρ : IsAdmissible ρ)
      (b : Coinvariants (smoothContragredient ρ) (standardOppositeUnipotentPoints i ν J) →ₗ[ℂ]
        Coinvariants ρ (standardUnipotentPoints i ν J) →ₗ[ℂ] ℂ),
      (standardCasselmanPairingData hG hi hν (hζ J hJ) hB (hA J hJ) (hmem J hJ)).IsStablePairing
        ρ hρ.1 b →
      Module.finrank ℂ (fixedVectors ρ K) ≤ d →
      ∀ v ∈ fixedVectors ρ K, ∀ ℓ ∈ fixedVectors (smoothContragredient ρ) K,
      ∀ lam : cocharacterLattice S,
        (∀ α ∈ simpleRelativeRoots i ν, 0 ≤ latticePairing S α lam) →
        (∀ α ∈ simpleRelativeRoots i ν, α ∉ J → T < latticePairing S α lam) →
          smoothDualPairing ρ ℓ (ρ (Aubert.General.uniformizerPowers i (.ofAdd lam)) v) =
            b (Jacquet.mk (smoothContragredient ρ) (standardOppositeUnipotentPoints i ν J) ℓ)
              (Jacquet.mk ρ (standardUnipotentPoints i ν J)
                (ρ (Aubert.General.uniformizerPowers i (.ofAdd lam)) v)) := by
  classical
  have hfinite := hi.isSplitSubtorus.1.finite_simpleRelativeRoots i ν
  set g := (hA J hJ).strictElement i ν hi (hζ J hJ) with hg_def
  obtain ⟨-, -, hgplus, -⟩ := (hA J hJ).strictElement_spec i ν hi (hζ J hJ)
  obtain ⟨z, hgz, hz0, hznn⟩ := (hA J hJ).exists_eq_uniformizerPowers hJ hgplus
  have hgz' : g = Aubert.General.uniformizerPowers i (.ofAdd z) := hgz
  set C : ℤ := ∑ α ∈ hfinite.toFinset, |latticePairing S α z| with hC
  refine ⟨(d : ℝ) * C, ?_⟩
  intro V _ _ ρ hρ b hb hd v hv ℓ hℓ lam hlam hdeep
  let D := standardCasselmanPairingData hG hi hν (hζ J hJ) hB (hA J hJ) (hmem J hJ)
  have hAd : D.Admits ρ hρ.1 :=
    standardCasselmanPairingData_admits hG hi hν (hζ J hJ) hB (hA J hJ) (hmem J hJ) ρ hρ
  set K' := basisOpenSubgroup hB hK with hK'
  have hKgood : D.Good K' := good_of_mem hG hi hν (hζ J hJ) hB (hA J hJ) (hmem J hJ) hK
  have : FiniteDimensional ℂ (fixedVectors ρ K'.toSubgroup) := hρ.2 K'
  set a := Aubert.General.uniformizerPowers i (.ofAdd lam) with ha_def
  -- the dominant remainder `lam - d z`
  set lr := lam - d • z with hlr_def
  have hlr : ∀ α ∈ simpleRelativeRoots i ν, 0 ≤ latticePairing S α lr := by
    intro α hα
    have hlin : latticePairing S α lr = latticePairing S α lam - d * latticePairing S α z := by
      rw [hlr_def, map_sub, map_nsmul, nsmul_eq_mul]
    by_cases hαJ : α ∈ J
    · rw [hlin, hz0 α hαJ, mul_zero, sub_zero]
      exact hlam α hα
    · have hle : latticePairing S α z ≤ C :=
        (le_abs_self _).trans (Finset.single_le_sum (f := fun α => |latticePairing S α z|)
          (fun _ _ => abs_nonneg _) (hfinite.mem_toFinset.mpr hα))
      have hd' : (d : ℤ) * C < latticePairing S α lam := by
        have := hdeep α hα hαJ
        exact_mod_cast this
      have hm : (d : ℤ) * latticePairing S α z ≤ d * C :=
        mul_le_mul_of_nonneg_left hle (by positivity)
      rw [hlin]
      linarith
  have hnz : ∀ n : ℕ, ∀ α ∈ simpleRelativeRoots i ν, 0 ≤ latticePairing S α (n • z) := by
    intro n α hα
    rw [map_nsmul, nsmul_eq_mul]
    exact mul_nonneg (by positivity) (hznn α hα)
  have hgpow : ∀ n : ℕ, g ^ n = Aubert.General.uniformizerPowers i (.ofAdd (n • z)) := by
    intro n
    rw [hgz', ← map_pow, ← ofAdd_nsmul]
  obtain ⟨hfac₀, hcon₀⟩ := hmem ∅ (Set.empty_subset _) K hK
  have hfactor : ∀ k ∈ K',
      ∃ l ∈ K'.toSubgroup ⊓ standardOppositeUnipotentPoints i ν ∅,
      ∃ m ∈ K'.toSubgroup ⊓ standardLeviPoints i ν ∅,
      ∃ u ∈ K'.toSubgroup ⊓ standardUnipotentPoints i ν ∅, k = l * m * u := by
    intro k hk
    obtain ⟨⟨l, m, n⟩, heq⟩ := hfac₀.2 ⟨k, hk⟩
    exact ⟨l, l.property, m, m.property, n, n.property, (congrArg Subtype.val heq).symm⟩
  have hup : ∀ c ∈ standardComponentCAplus i ν ∅ (q ∅),
      ∀ u ∈ K'.toSubgroup ⊓ standardUnipotentPoints i ν ∅, c * u * c⁻¹ ∈ K' :=
    fun c hc u hu => ((hcon₀.2.1 c hc).1 ⟨u, hu, rfl⟩).1
  have hlow : ∀ c ∈ standardComponentCAplus i ν ∅ (q ∅),
      ∀ l ∈ K'.toSubgroup ⊓ standardOppositeUnipotentPoints i ν ∅,
        c⁻¹ * l * c ∈ K' := fun c hc l hl => by
    have h := (hcon₀.2.1 c hc).2 ⟨l, hl, rfl⟩
    simp only [inv_inv, SetLike.mem_coe] at h
    exact h.1
  have hmid : ∀ c ∈ (standardComponentCA i (q ∅) : Set (rationalPoints G)),
      ∀ m ∈ K'.toSubgroup ⊓ standardLeviPoints i ν ∅, c⁻¹ * m * c ∈ K' := fun c hc m hm => by
    have hm' : m ∈ ambientConjugate c ((K ⊓ standardLeviPoints i ν ∅ :
        Subgroup (rationalPoints G)) : Set (rationalPoints G)) := by
      rw [hcon₀.1 c hc]
      exact hm
    obtain ⟨y, hy, heq⟩ := hm'
    have h : c⁻¹ * m * c = y := by
      rw [← heq]
      group
    rw [h]
    exact hy.1
  obtain ⟨haCA, haplus⟩ := uniformizerPowers_mem_emptyChambers hi A q hA ζ hζ lam hlam
  obtain ⟨hrCA, hrplus⟩ := uniformizerPowers_mem_emptyChambers hi A q hA ζ hζ lr hlr
  have hpowCA : ∀ n : ℕ, g ^ n ∈ standardComponentCA i (q ∅) ∧
      g ^ n ∈ standardComponentCAplus i ν ∅ (q ∅) := by
    intro n
    rw [hgpow n]
    exact uniformizerPowers_mem_emptyChambers hi A q hA ζ hζ _ (hnz n)
  have hg1 : g ∈ standardComponentCA i (q ∅) ∧ g ∈ standardComponentCAplus i ν ∅ (q ∅) := by
    simpa using hpowCA 1
  have hDg : D.g⁻¹ = g := inv_inv g
  -- compression is multiplicative on the dominant lattice
  have hCpow : ∀ n : ℕ, compressedAction ρ hρ.1 K' (D.isCompact K' hKgood) (g ^ n) =
      compressedAction ρ hρ.1 K' (D.isCompact K' hKgood) g ^ n := by
    intro n
    induction n with
    | zero => rw [pow_zero, pow_zero, compressedAction_one]; rfl
    | succ n ih =>
      rw [pow_succ', compressedAction_mul_of_factor ρ hρ.1 K' _ (standardUnipotentPoints i ν ∅)
        (standardLeviPoints i ν ∅) (standardOppositeUnipotentPoints i ν ∅) hfactor g (g ^ n)
        (hup g hg1.2)
        (hlow (g ^ n) (hpowCA n).2) (hmid (g ^ n) (hpowCA n).1), ih, pow_succ']
  have hsplit : a = Aubert.General.uniformizerPowers i (.ofAdd lr) * g ^ d := by
    rw [hgpow d, ha_def, ← map_mul, ← ofAdd_add, hlr_def, sub_add_cancel]
  have hX : compressedAction ρ hρ.1 K' (D.isCompact K' hKgood) a =
      compressedAction ρ hρ.1 K' (D.isCompact K' hKgood)
          (Aubert.General.uniformizerPowers i (.ofAdd lr)) *
        compressedAction ρ hρ.1 K' (D.isCompact K' hKgood) D.g⁻¹ ^ d := by
    rw [hsplit, compressedAction_mul_of_factor ρ hρ.1 K' _ (standardUnipotentPoints i ν ∅)
      (standardLeviPoints i ν ∅) (standardOppositeUnipotentPoints i ν ∅) hfactor _ (g ^ d)
      (hup _ hrplus) (hlow (g ^ d) (hpowCA d).2) (hmid (g ^ d) (hpowCA d).1), hCpow, hDg]
  have hac : a * g = g * a := by
    rw [hgz', ha_def, ← map_mul, ← map_mul (Aubert.General.uniformizerPowers i),
      mul_comm (Multiplicative.ofAdd lam)]
  have h1 : ∀ u ∈ K', u ∈ D.N → a⁻¹ * u * a ∈ K' :=
    fun u hu huN => hlow a haplus u
      ⟨hu, standardOppositeUnipotentPoints_le_empty hG hi hν (hζ J hJ) huN⟩
  have h2 : Commute (compressedAction ρ hρ.1 K' (D.isCompact K' hKgood) a)
      (compressedAction ρ hρ.1 K' (D.isCompact K' hKgood) D.g⁻¹) := by
    rw [hDg]
    exact compressedAction_commute_of_factor ρ hρ.1 K' _ (standardUnipotentPoints i ν ∅)
      (standardLeviPoints i ν ∅) (standardOppositeUnipotentPoints i ν ∅) hfactor hac
      (hup a haplus) (hlow a haplus) (hmid a haCA)
      (hup g hg1.2)
      (hlow g hg1.2) (hmid g hg1.1)
  exact hb.asymptotics_of_finrank_le hAd K' hKgood hd hv hℓ a h1 h2 _ hX

end DimensionThreshold

end Langlands.BruhatTits.SpecialCompact
