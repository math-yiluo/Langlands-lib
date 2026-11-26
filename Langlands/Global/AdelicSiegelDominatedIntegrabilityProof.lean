import Langlands.Global.AdelicWavePacketRapidDecaySiegelReduction
import Langlands.Global.AdelicFiniteVolumeProof
import Langlands.Global.AdelicPrincipalQuotientProduct
import Langlands.Global.AdelicCentralPositiveHeightProof
import Langlands.Global.AdelicHaarUnimodularityProof
import Langlands.Global.LeftCosetUnfoldingBound
import Langlands.Analysis.Local.SiegelSetIntegral

/-! # Integrability of Siegel-dominated functions on `G(F) \ G(𝔸)`

This module proves `Langlands.Global.SiegelDominatedIntegrabilityStatement`
(`siegelDominatedIntegrability`). The Siegel data are those of the Library's finite-volume
construction: an algebraic Siegel setup, compact factors whose compact subgroup lies in an open
subgroup `H₁ ⊆ P(𝔸) K`, a threshold `t` and a finite set `W ⊆ G(𝔸)¹` with
`G(𝔸)¹ = G(F) S W` for the weak Siegel product `S`. With `Ω = W` and `d = 2 n`, `n` the number
of coordinates of `A_G × A_{T₀}`, the proof

* bounds the integral over `[G]` by the integral over `A_G S W` (`G(𝔸) = A_G G(𝔸)¹`, unfolding);
* splits off the finitely many right translates by `W` (unimodularity of `G(𝔸)`);
* bounds the integral over `A_G S` piece by piece in dyadic coordinates of `A_G × A_{T₀}`
  (`SiegelSetMeasure.exists_lintegral_chamber_le`): the Haar volume of each dyadic piece is
  bounded above by a constant times the inverse modulus `δ(a₀)⁻¹` at a representative `a₀` of
  the piece, which cancels the modulus factor `δ(a)` of the pointwise bound;
* bounds the dyadic coordinates by `A σ + B` at Siegel points, using that `rho` is a closed
  embedding (character norms are polynomial in the height), and sums `σ^{-d}`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal ENNReal Pointwise

set_option autoImplicit false

namespace Langlands.Global.AdelicSiegelFactors

open Langlands.GroupScheme AdelicGroupPoints

section Finprod

/-- An injective monoid homomorphism commutes with `finprod`, with no finiteness assumption:
both sides are `1` when the support is infinite. -/
theorem map_finprod_of_injective {α M N : Type*} [CommMonoid M] [CommMonoid N] (g : M →* N)
    (hg : Function.Injective g) (f : α → M) : g (∏ᶠ i, f i) = ∏ᶠ i, g (f i) := by
  by_cases hf : (Function.mulSupport f).Finite
  · exact g.map_finprod hf
  · have hsupp : Function.mulSupport (fun i => g (f i)) = Function.mulSupport f := by
      ext i
      simp only [Function.mem_mulSupport, ne_eq]
      rw [← map_one g, hg.eq_iff]
    have hf' : ¬ (Function.mulSupport (fun i => g (f i))).Finite := by rwa [hsupp]
    rw [finprod_of_infinite_mulSupport hf, finprod_of_infinite_mulSupport hf', map_one]

/-- The coercion `ℝ≥0 → ℝ` commutes with `finprod`. -/
theorem coe_finprod_nnreal {α : Type*} (f : α → ℝ≥0) : ((∏ᶠ i, f i : ℝ≥0) : ℝ) = ∏ᶠ i, (f i : ℝ) :=
  map_finprod_of_injective (NNReal.toRealHom : ℝ≥0 →* ℝ) NNReal.coe_injective f

end Finprod

section Structure

variable {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G}
  {ν : cocharacterLattice T} {T₀ : CommGroupScheme (Spec (CommRingCat.of F))} {j : T₀ ⟶ T}

/-- The adelic Levi decomposition `P(𝔸) = M(𝔸) ⋉ N(𝔸)` inside `G(𝔸)`, with continuous
Levi projection. -/
theorem exists_semidirect_standard (hsetup : IsSiegelAlgebraicSetup F G T i ν T₀ j) :
    ∃ h : Aubert.General.IsSemidirectDecomposition (standardParabolicImage F G T i ν)
      (standardLeviImage F G T i ν) (standardUnipotentImage F G T i ν),
      (haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom; Continuous h.projection) := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨f, hfc, hfM, hfid, hfker⟩ := exists_standardLeviPart F G T i ν T₀ j hsetup
  exact ⟨_, Aubert.General.IsSemidirectDecomposition.continuous_of_retraction_projection
    (standardLeviImage_le_parabolic F G T i ν) (standardUnipotentImage_le_parabolic F G T i ν)
    f hfM hfid hfker hfc⟩

/-- Under `standardLevi = torusCentralizer`, the image of every positive torus mapping to `T`
commutes with `M(𝔸)`. -/
theorem positiveMap_commute_of_mem_standardLevi (hlevi : standardLevi i ν ∅ = torusCentralizer i)
    {T₁ : CommGroupScheme (Spec (CommRingCat.of F))} (j₁ : T₁ ⟶ T)
    (x : PositiveRealTorus.intrinsicSubgroup F T₁) {m : AdelicGroupPoints F G}
    (hm : m ∈ standardLeviImage F G T i ν) : Commute (positiveMap F G T i T₁ j₁ x) m := by
  have hm' : m ∈ (torusCentralizer i).carrier
      ((algSpec (CommRingCat.of F)).obj (Opposite.op (CommAlgCat.of F (Adeles F)))) := by
    rw [← hlevi, ← standardLeviImage_eq]
    exact hm
  have hm'' : ∀ (V : Over (Spec (CommRingCat.of F)))
      (b : V ⟶ (algSpec (CommRingCat.of F)).obj (Opposite.op (CommAlgCat.of F (Adeles F))))
      (s : V ⟶ T.X), Commute (b ≫ m) (s ≫ i.hom.hom) := hm'
  have h' : Commute m (positiveMap F G T i T₁ j₁ x) := by
    have h := hm'' _ (𝟙 _) (x.val ≫ (CommGroupScheme.groupHom j₁).hom.hom)
    rw [Category.id_comp] at h
    convert h using 1
    change x.val ≫ (CommGroupScheme.groupHom j₁ ≫ i).hom.hom = _
    simp only [Grp.comp_hom_hom, Category.assoc]
  exact h'.symm

end Structure

section Measure

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {i : T.toGrp ⟶ G} {ν : cocharacterLattice T} {T₀ : CommGroupScheme (Spec (CommRingCat.of F))}
  {j : T₀ ⟶ T} {Z₀ : CommGroupScheme (Spec (CommRingCat.of F))} (zc : Z₀ ⟶ T)
  (hzc : IsCentral (CommGroupScheme.groupHom zc ≫ i))

/-- The positive torus `A_{Z₀} × A_{T₀}` of a split central torus `Z₀ → T` and of `T₀ → T`,
mapped into `G(𝔸)` by `(z, x) ↦ z x`. -/
def siegelTorusMap :
    PositiveRealTorus.intrinsicSubgroup F Z₀ × PositiveRealTorus.intrinsicSubgroup F T₀ →*
      AdelicGroupPoints F G :=
  MonoidHom.noncommCoprod (positiveMap F G T i Z₀ zc).toMonoidHom
    (positiveMap F G T i T₀ j).toMonoidHom
    (fun z _ => PositiveRealTorus.positivePointMap_commute F G Z₀ _ hzc z _)

omit [IsAffine G.X.left] [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
theorem siegelTorusMap_apply (p : PositiveRealTorus.intrinsicSubgroup F Z₀ ×
    PositiveRealTorus.intrinsicSubgroup F T₀) :
    siegelTorusMap (j := j) zc hzc p = positiveMap F G T i Z₀ zc p.1 * positiveMap F G T i T₀ j p.2 :=
  rfl

omit [IsAffine G.X.left] [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
include hzc in
theorem positiveMap_central (z : PositiveRealTorus.intrinsicSubgroup F Z₀)
    (g : AdelicGroupPoints F G) : Commute (positiveMap F G T i Z₀ zc z) g :=
  PositiveRealTorus.positivePointMap_commute F G Z₀ _ hzc z g

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
theorem continuous_siegelTorusMap : Continuous (siegelTorusMap (j := j) zc hzc) :=
  ((positiveMap F G T i Z₀ zc).continuous.comp continuous_fst).mul
    ((positiveMap F G T i T₀ j).continuous.comp continuous_snd)

/-- The Siegel set `Ω_N Ω_M a(A_{Z₀} × A_{T₀}(t)) K` of `G(𝔸)`. -/
def centralSiegelSet
    (C : CompactFactors F G (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅))
    (t : ℝ≥0ˣ) : Set (AdelicGroupPoints F G) :=
  (map F (Standard.unipotentScheme i ν ∅) G (Standard.unipotentHom i ν ∅) '' C.omegaN) *
    ((fun m : normOneSubgroup F (Standard.leviScheme i ν ∅) =>
      map F (Standard.leviScheme i ν ∅) G (Standard.leviHom i ν ∅) m) '' C.omegaM) *
    (siegelTorusMap (j := j) zc hzc ''
      (Set.univ ×ˢ PositiveRealTorus.weakSimpleRootChamber F T₀ T j G i ν t)) *
    (C.compactSubgroup : Set (AdelicGroupPoints F G))

/-- The `ℝ≥0`-valued modulus `∏_{β > 0} |β(x)|^{m_β}`. -/
def siegelModulusNN (x : PositiveRealTorus.intrinsicSubgroup F T₀) : ℝ≥0 :=
  ∏ᶠ (β : characterLattice T) (_ : β ∈ positiveRelativeRoots i ν),
    (PositiveRealTorus.normCharacter F T₀ (j ≫ β) x : ℝ≥0) ^ Module.finrank F (weightSpace i β)

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
theorem coe_siegelModulusNN (x : PositiveRealTorus.intrinsicSubgroup F T₀) :
    ((siegelModulusNN (i := i) (ν := ν) (j := j) x : ℝ≥0) : ℝ) =
      siegelModulus F G T i ν T₀ j x := by
  classical
  unfold siegelModulusNN siegelModulus
  rw [coe_finprod_nnreal]
  refine finprod_congr fun β => ?_
  rw [finprod_eq_if, finprod_eq_if]
  split_ifs <;> simp

/-- **Weighted Siegel bound in `G(𝔸)`.** For an algebraic Siegel setup, compact factors whose
compact subgroup `K` lies in an open subgroup `H₁ ⊆ P(𝔸) K` and is compatible with the positive
torus, a central split torus `Z₀ → T`, and characters `λ` of `A_{Z₀} × A_{T₀}` with compact
dyadic box and `δ ≤ ∏ λ^e`, there is `D < ∞` such that every measurable `f ≥ 0` with
`f(n m a(z, x) k) ≤ δ(x) Φ(κ(z, x))` on the Siegel set has integral at most `D ∑ Φ`. -/
theorem exists_lintegral_centralSiegelSet_le
    (hG : IsConnectedReductive G) (hsetup : IsSiegelAlgebraicSetup F G T i ν T₀ j)
    (C : CompactFactors F G (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅))
    (t : ℝ≥0ˣ) (H₁ : Subgroup (AdelicGroupPoints F G)) (hH₁ : IsOpen (H₁ : Set (AdelicGroupPoints F G)))
    (hKH₁ : C.compactSubgroup ≤ H₁)
    (hH₁P : (H₁ : Set (AdelicGroupPoints F G)) ⊆
      Set.range (map F (Standard.parabolicScheme i ν ∅) G (Standard.parabolicHom i ν ∅)) *
        (C.compactSubgroup : Set (AdelicGroupPoints F G)))
    (hcompat : IsPositiveTorusCompatible F G T i ν T₀ j C.compactSubgroup)
    {J : Type} [Fintype J]
    (lam : J → PositiveRealTorus.intrinsicSubgroup F Z₀ × PositiveRealTorus.intrinsicSubgroup F T₀ →*
      ℝ≥0ˣ) (hbox : IsCompact (SiegelSetMeasure.dyadicBox lam)) (e : J → ℕ)
    (hδ : ∀ p, siegelModulusNN (i := i) (ν := ν) (j := j) p.2 ≤ ∏ k, (lam k p : ℝ≥0) ^ e k) :
    ∃ D : ℝ≥0∞, D ≠ ∞ ∧ ∀ f : AdelicGroupPoints F G → ℝ≥0∞, Measurable f →
      ∀ Φ : (J → ℤ) → ℝ≥0∞,
      (∀ p : PositiveRealTorus.intrinsicSubgroup F Z₀ × PositiveRealTorus.intrinsicSubgroup F T₀,
        p.2 ∈ PositiveRealTorus.weakSimpleRootChamber F T₀ T j G i ν t →
        ∀ n ∈ C.omegaN, ∀ m ∈ C.omegaM, ∀ k ∈ C.compactSubgroup,
          f (map F (Standard.unipotentScheme i ν ∅) G (Standard.unipotentHom i ν ∅) n *
            map F (Standard.leviScheme i ν ∅) G (Standard.leviHom i ν ∅) m *
              siegelTorusMap (j := j) zc hzc p * k) ≤
            (siegelModulusNN (i := i) (ν := ν) (j := j) p.2 : ℝ≥0∞) *
              Φ (SiegelSetMeasure.zIndex lam p)) →
      ∫⁻ y in centralSiegelSet (j := j) zc hzc C t, f y ∂Measure.haar ≤ D * ∑' κ, Φ κ := by
  classical
  obtain ⟨-, -, -, -, -, hlevi, -⟩ := id hsetup
  obtain ⟨hsd, hp⟩ := exists_semidirect_standard hsetup
  set Q := standardParabolicImage F G T i ν
  set M := standardLeviImage F G T i ν
  set U := standardUnipotentImage F G T i ν
  set K := C.compactSubgroup
  have hQ : IsClosed (Q : Set (AdelicGroupPoints F G)) := isClosed_standardParabolicImage F G T i ν
  have hM : IsClosed (M : Set (AdelicGroupPoints F G)) := isClosed_standardLeviImage F G T i ν
  have hU : IsClosed (U : Set (AdelicGroupPoints F G)) := isClosed_standardUnipotentImage F G T i ν
  have hK : IsCompact (K : Set (AdelicGroupPoints F G)) := C.compact_compactSubgroup
  have : LocallyCompactSpace Q := hQ.locallyCompactSpace
  let μQ : Measure Q := Measure.haar
  have hfac : ∀ g ∈ H₁, ∃ q ∈ Q, ∃ k ∈ K, g = q * k := by
    intro g hg
    obtain ⟨_, ⟨y, rfl⟩, k, hk, hyk⟩ := hH₁P hg
    exact ⟨_, ⟨y, rfl⟩, k, hk, hyk.symm⟩
  obtain ⟨c, hc⟩ := CompactFactorization.exists_measure_inter_mul_eq_of_isOpen
    (Measure.haar : Measure (AdelicGroupPoints F G)) Q hQ K hK H₁ hH₁ hKH₁ hfac μQ
  let μr : Measure (AdelicGroupPoints F G) :=
    (Measure.haar : Measure (AdelicGroupPoints F G)).restrict ((Q : Set _) * (H₁ : Set _))
  have hcμ : ∀ S : Set (AdelicGroupPoints F G), MeasurableSet S →
      (∀ s ∈ S, ∀ k ∈ K, s * k ∈ S) → μr S ≤ c * μQ (Subtype.val ⁻¹' S) := by
    intro S hS hsat
    rw [Measure.restrict_apply hS, hc S hS hsat]
  set a := siegelTorusMap (j := j) zc hzc
  have haM : ∀ p, a p ∈ M := fun p =>
    M.mul_mem (positiveMap_mem_standardLeviImage F G T i ν Z₀ zc p.1)
      (positiveMap_mem_standardLeviImage F G T i ν T₀ j p.2)
  have hacent : ∀ p, ∀ m ∈ M, Commute (a p) m := fun p m hm =>
    (positiveMap_commute_of_mem_standardLevi hlevi zc p.1 hm).mul_left
      (positiveMap_commute_of_mem_standardLevi hlevi j p.2 hm)
  have haK : ∀ k ∈ K, k ∈ Q → ∀ p, Commute k (a p) := fun k hk hkQ p =>
    ((positiveMap_central zc hzc p.1 k).symm).mul_right (hcompat k hk hkQ p.2)
  have hδeq : ∀ p, (HaarModulus.closedNormalizerCharacter U hU
      ⟨a p, hsd.levi_le_normalizer (haM p)⟩ : ℝ≥0) = siegelModulusNN (i := i) (ν := ν) (j := j) p.2 := by
    intro p
    have hn1 : positiveMap F G T i Z₀ zc p.1 ∈ Subgroup.normalizer (U : Set (AdelicGroupPoints F G)) :=
      hsd.levi_le_normalizer (positiveMap_mem_standardLeviImage F G T i ν Z₀ zc p.1)
    have hn2 : positiveMap F G T i T₀ j p.2 ∈ Subgroup.normalizer (U : Set (AdelicGroupPoints F G)) :=
      hsd.levi_le_normalizer (positiveMap_mem_standardLeviImage F G T i ν T₀ j p.2)
    have hsplit : (⟨a p, hsd.levi_le_normalizer (haM p)⟩ :
        Subgroup.normalizer (U : Set (AdelicGroupPoints F G))) = ⟨_, hn1⟩ * ⟨_, hn2⟩ := rfl
    have h1 : HaarModulus.closedNormalizerCharacter U hU ⟨_, hn1⟩ = 1 :=
      SiegelSetMeasure.closedNormalizerCharacter_eq_one_of_commute hU ⟨_, hn1⟩
        (fun m _ => positiveMap_central zc hzc p.1 m)
    have h2 : (HaarModulus.closedNormalizerCharacter U hU ⟨_, hn2⟩ : ℝ≥0) =
        siegelModulusNN (i := i) (ν := ν) (j := j) p.2 :=
      positiveTorusUnipotentModulus_of_coordinates positiveTorusTriangularCoordinates F G hG T i ν
        T₀ j hsetup p.2
    rw [hsplit, map_mul, h1, one_mul, h2]
  have hδ' : ∀ p, (HaarModulus.closedNormalizerCharacter U hU
      ⟨a p, hsd.levi_le_normalizer (haM p)⟩ : ℝ≥0) ≤ ∏ k, (lam k p : ℝ≥0) ^ e k := fun p => by
    rw [hδeq p]
    exact hδ p
  have hΩU : IsCompact (map F (Standard.unipotentScheme i ν ∅) G (Standard.unipotentHom i ν ∅) ''
      C.omegaN) := C.compact_omegaN.image (map F _ G (Standard.unipotentHom i ν ∅)).continuous
  have hΩUU : map F (Standard.unipotentScheme i ν ∅) G (Standard.unipotentHom i ν ∅) '' C.omegaN ⊆
      U := by rintro g ⟨n, -, hn⟩; exact ⟨n, hn⟩
  have hΩM : IsCompact ((fun m : normOneSubgroup F (Standard.leviScheme i ν ∅) =>
      map F (Standard.leviScheme i ν ∅) G (Standard.leviHom i ν ∅) m) '' C.omegaM) :=
    C.compact_omegaM.image
      ((map F _ G (Standard.leviHom i ν ∅)).continuous.comp continuous_subtype_val)
  have hΩMM : (fun m : normOneSubgroup F (Standard.leviScheme i ν ∅) =>
      map F (Standard.leviScheme i ν ∅) G (Standard.leviHom i ν ∅) m) '' C.omegaM ⊆ M := by
    rintro g ⟨m, -, hm⟩
    exact ⟨(m : AdelicGroupPoints F (Standard.leviScheme i ν ∅)), hm⟩
  obtain ⟨D, hD, hbound⟩ := SiegelSetMeasure.exists_lintegral_chamber_le μr hQ hM hU hK hsd hp μQ c
    hcμ hΩU hΩUU hΩM hΩMM a (continuous_siegelTorusMap zc hzc) haM hacent haK lam hbox e hδ'
  refine ⟨D, hD, fun f hf Φ hf' => ?_⟩
  have key := hbound (Set.univ ×ˢ PositiveRealTorus.weakSimpleRootChamber F T₀ T j G i ν t)
    f hf Φ (by
      rintro p ⟨-, hp2⟩ _ ⟨n, hn, rfl⟩ _ ⟨m, hm, rfl⟩ k hk
      rw [hδeq p]
      exact hf' p hp2 n hn m hm k hk)
  have hsub : centralSiegelSet (j := j) zc hzc C t ⊆ (Q : Set _) * (H₁ : Set _) := by
    rintro _ ⟨_, ⟨_, ⟨u, hu, m, hm, rfl⟩, _, ⟨p, -, rfl⟩, rfl⟩, k, hk, rfl⟩
    exact ⟨u * m * a p, Q.mul_mem (Q.mul_mem (hsd.unipotent_le (hΩUU hu))
      (hsd.levi_le (hΩMM hm))) (hsd.levi_le (haM p)), k, hKH₁ hk, rfl⟩
  calc ∫⁻ y in centralSiegelSet (j := j) zc hzc C t, f y ∂Measure.haar
      = ∫⁻ y in centralSiegelSet (j := j) zc hzc C t, f y ∂μr := by
        rw [Measure.restrict_restrict_of_subset hsub]
    _ ≤ D * ∑' κ, Φ κ := key

end Measure

section Coordinates

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {i : T.toGrp ⟶ G} {ν : cocharacterLattice T} {T₀ : CommGroupScheme (Spec (CommRingCat.of F))}
  {j : T₀ ⟶ T} {Z₀ : CommGroupScheme (Spec (CommRingCat.of F))} (zc : Z₀ ⟶ T)

/-- The coordinates of `A_{Z₀} × A_{T₀}`: the norms `|χ_k(z)|` of finitely many rational
characters of `G` on the central factor, and the simple-root norms `|α(x)|` on `A_{T₀}`. -/
def siegelCoordinates {J₀ : Type} (χ : J₀ → rationalCharacters G) :
    J₀ ⊕ simpleRelativeRoots i ν →
      PositiveRealTorus.intrinsicSubgroup F Z₀ × PositiveRealTorus.intrinsicSubgroup F T₀ →* ℝ≥0ˣ
  | Sum.inl k => ((characterNorm F G (χ k).toMul).toMonoidHom.comp
      (positiveMap F G T i Z₀ zc).toMonoidHom).comp (MonoidHom.fst _ _)
  | Sum.inr α => ((PositiveRealTorus.normCharacter F T₀ (j ≫ (α : characterLattice T))).toMonoidHom.comp
      (PositiveRealTorus.intrinsicSubgroup F T₀).subtype).comp (MonoidHom.snd _ _)

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
@[simp] theorem siegelCoordinates_inl {J₀ : Type} (χ : J₀ → rationalCharacters G) (k : J₀)
    (p : PositiveRealTorus.intrinsicSubgroup F Z₀ × PositiveRealTorus.intrinsicSubgroup F T₀) :
    siegelCoordinates (i := i) (ν := ν) (j := j) zc χ (Sum.inl k) p =
      characterNorm F G (χ k).toMul (positiveMap F G T i Z₀ zc p.1) := rfl

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
@[simp] theorem siegelCoordinates_inr {J₀ : Type} (χ : J₀ → rationalCharacters G)
    (α : simpleRelativeRoots i ν)
    (p : PositiveRealTorus.intrinsicSubgroup F Z₀ × PositiveRealTorus.intrinsicSubgroup F T₀) :
    siegelCoordinates (i := i) (ν := ν) (j := j) zc χ (Sum.inr α) p =
      PositiveRealTorus.normCharacter F T₀ (j ≫ (α : characterLattice T)) p.2 := rfl

omit [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
/-- **Compact central boxes.** For a coordinate splitting of a torus `Z₀ → G` and rational
characters `χ_k` of `G` with `|χ_k(z(x))| = x_k ^ n` on positive points, `n > 0`, the box
`1/2 ≤ |χ_k(z)| ≤ 2` in `A_{Z₀}` is compact. -/
theorem isCompact_characterNormBox (zi : Z₀.toGrp ⟶ G) {I : Type} [Fintype I]
    (e : Z₀.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (χ : I → rationalCharacters G)
    {n : ℕ} (hn : 0 < n)
    (hχ : ∀ (k : I) (x : I → ℝ≥0ˣ), characterNorm F G (χ k).toMul
      (map F Z₀.toGrp G zi (PositiveRealTorus.full F I Z₀ e x)) = x k ^ n) :
    IsCompact {z : PositiveRealTorus.intrinsicSubgroup F Z₀ | ∀ k,
      (2 : ℝ≥0)⁻¹ ≤ (characterNorm F G (χ k).toMul (map F Z₀.toGrp G zi z.val) : ℝ≥0) ∧
        (characterNorm F G (χ k).toMul (map F Z₀.toGrp G zi z.val) : ℝ≥0) ≤ 2} := by
  set box := {z : PositiveRealTorus.intrinsicSubgroup F Z₀ | ∀ k,
      (2 : ℝ≥0)⁻¹ ≤ (characterNorm F G (χ k).toMul (map F Z₀.toGrp G zi z.val) : ℝ≥0) ∧
        (characterNorm F G (χ k).toMul (map F Z₀.toGrp G zi z.val) : ℝ≥0) ≤ 2}
  let R : Set (I → ℝ≥0ˣ) := Set.pi Set.univ fun _ =>
    {u | (2 : ℝ)⁻¹ ≤ ((u : ℝ≥0) : ℝ) ∧ ((u : ℝ≥0) : ℝ) ≤ 2}
  have hRc : IsCompact R := isCompact_univ_pi fun _ =>
    PositiveRealTorus.isCompact_unitsBox _ _ (by norm_num)
  have hΦc : Continuous (PositiveRealTorus.fullIntrinsic F Z₀ I e) :=
    (PositiveRealTorus.isClosedEmbedding_full F I Z₀ e).continuous.subtype_mk _
  have hfc : ∀ k, Continuous fun z : PositiveRealTorus.intrinsicSubgroup F Z₀ =>
      (characterNorm F G (χ k).toMul (map F Z₀.toGrp G zi z.val) : ℝ≥0) := fun k =>
    Units.continuous_val.comp ((characterNorm F G (χ k).toMul).continuous.comp
      ((map F Z₀.toGrp G zi).continuous.comp continuous_subtype_val))
  have hboxc : IsClosed box := by
    have h : box = ⋂ k, ({z | (2 : ℝ≥0)⁻¹ ≤ (characterNorm F G (χ k).toMul
        (map F Z₀.toGrp G zi z.val) : ℝ≥0)} ∩
        {z | (characterNorm F G (χ k).toMul (map F Z₀.toGrp G zi z.val) : ℝ≥0) ≤ 2}) := by
      ext z
      simp [box]
    rw [h]
    exact isClosed_iInter fun k =>
      (isClosed_le continuous_const (hfc k)).inter (isClosed_le (hfc k) continuous_const)
  have hpre : PositiveRealTorus.fullIntrinsic F Z₀ I e ⁻¹' box ⊆ R := by
    intro x hx k _
    have hk := hx k
    change (2 : ℝ≥0)⁻¹ ≤ (characterNorm F G (χ k).toMul
        (map F Z₀.toGrp G zi (PositiveRealTorus.full F I Z₀ e x)) : ℝ≥0) ∧
      (characterNorm F G (χ k).toMul
        (map F Z₀.toGrp G zi (PositiveRealTorus.full F I Z₀ e x)) : ℝ≥0) ≤ 2 at hk
    rw [hχ k x, Units.val_pow_eq_pow_val] at hk
    set u : ℝ≥0 := (x k : ℝ≥0)
    have hn0 : n ≠ 0 := hn.ne'
    have hu1 : (2 : ℝ≥0)⁻¹ ≤ u := by
      rcases le_total u 1 with h | h
      · exact hk.1.trans (pow_le_of_le_one (by positivity) h hn0)
      · exact (by norm_num : (2 : ℝ≥0)⁻¹ ≤ 1).trans h
    have hu2 : u ≤ 2 := by
      rcases le_total u 1 with h | h
      · exact h.trans (by norm_num)
      · exact (le_self_pow₀ h hn0).trans hk.2
    constructor
    · have := NNReal.coe_le_coe.mpr hu1
      simpa using this
    · have := NNReal.coe_le_coe.mpr hu2
      simpa using this
  have hcpt : IsCompact (PositiveRealTorus.fullIntrinsic F Z₀ I e ⁻¹' box) :=
    hRc.of_isClosed_subset (hboxc.preimage hΦc) hpre
  have himage : PositiveRealTorus.fullIntrinsic F Z₀ I e ''
      (PositiveRealTorus.fullIntrinsic F Z₀ I e ⁻¹' box) = box :=
    Set.image_preimage_eq _ (PositiveRealTorus.fullIntrinsic_surjective F Z₀ I e)
  rw [← himage]
  exact hcpt.image hΦc

omit [IsAffine G.X.left] in
/-- The compact dyadic box of the Siegel coordinates. -/
theorem isCompact_dyadicBox_siegelCoordinates (hG : IsConnectedReductive G)
    (hsetup : IsSiegelAlgebraicSetup F G T i ν T₀ j) {I : Type} [Fintype I]
    (e : Z₀.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (χ : I → rationalCharacters G)
    {n : ℕ} (hn : 0 < n)
    (hχ : ∀ (k : I) (x : I → ℝ≥0ˣ), characterNorm F G (χ k).toMul
      (map F Z₀.toGrp G (CommGroupScheme.groupHom zc ≫ i) (PositiveRealTorus.full F I Z₀ e x)) =
        x k ^ n) :
    IsCompact (SiegelSetMeasure.dyadicBox (siegelCoordinates (i := i) (ν := ν) (j := j) zc χ)) := by
  have h1 := isCompact_characterNormBox (CommGroupScheme.groupHom zc ≫ i) e χ hn hχ
  have h2 := simpleRootBoxCompactStatement_of_rootComplement relativeRootNegation
    relativeCharacterRootComplement F G hG T i ν T₀ j hsetup 2
  convert h1.prod h2 using 1
  ext ⟨z, x⟩
  simp only [SiegelSetMeasure.dyadicBox, Set.mem_ofPred_eq, Sum.forall, siegelCoordinates_inl,
    siegelCoordinates_inr, Set.mem_prod, Subtype.forall]
  rfl

omit [IsAffine G.X.left] in
/-- The modulus is a product of powers of the simple-root coordinates. -/
theorem exists_siegelModulusNN_le (hsetup : IsSiegelAlgebraicSetup F G T i ν T₀ j)
    [Fintype (simpleRelativeRoots i ν)] {I : Type} [Fintype I] (χ : I → rationalCharacters G) :
    ∃ e : I ⊕ simpleRelativeRoots i ν → ℕ, ∀ p : PositiveRealTorus.intrinsicSubgroup F Z₀ ×
        PositiveRealTorus.intrinsicSubgroup F T₀,
      siegelModulusNN (i := i) (ν := ν) (j := j) p.2 ≤
        ∏ c, (siegelCoordinates (i := i) (ν := ν) (j := j) zc χ c p : ℝ≥0) ^ e c := by
  obtain ⟨hTmax, -⟩ := hsetup
  obtain ⟨e₀, -, hexp⟩ := exists_simpleRoot_exponents (G := G) i ν j hTmax.1.1
  refine ⟨Sum.elim (fun _ => 0) e₀, fun p => le_of_eq ?_⟩
  rw [Fintype.prod_sum_type]
  simp only [Sum.elim_inl, pow_zero, Finset.prod_const_one, one_mul, Sum.elim_inr,
    siegelCoordinates_inr]
  exact hexp p.2.val

end Coordinates

section Height

/-- `|⌊log₂ r⌋| ≤ |log r| / log 2 + 1` for `r > 0`. -/
theorem abs_intLog_two_le {r : ℝ≥0} (hr : 0 < r) :
    |(Int.log 2 r : ℝ)| ≤ |Real.log r| / Real.log 2 + 1 := by
  set k := Int.log 2 r
  have h1 : (2 : ℝ≥0) ^ k ≤ r := by
    have := Int.zpow_log_le_self (b := 2) (by norm_num) hr
    exact_mod_cast this
  have h2 : r < (2 : ℝ≥0) ^ (k + 1) := by
    have := Int.lt_zpow_succ_log_self (b := 2) (by norm_num) r
    exact_mod_cast this
  have hr' : (0 : ℝ) < r := hr
  have h1' : (2 : ℝ) ^ k ≤ (r : ℝ) := by exact_mod_cast h1
  have h2' : (r : ℝ) < (2 : ℝ) ^ (k + 1) := by exact_mod_cast h2
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl1 : (k : ℝ) * Real.log 2 ≤ Real.log r := by
    rw [← Real.log_zpow]
    exact Real.log_le_log (zpow_pos (by norm_num) _) h1'
  have hl2 : Real.log r < ((k : ℝ) + 1) * Real.log 2 := by
    have := Real.log_lt_log hr' h2'
    rw [Real.log_zpow] at this
    exact_mod_cast this
  have ha : (k : ℝ) ≤ Real.log r / Real.log 2 := by rw [le_div_iff₀ hL]; exact hl1
  have hb : Real.log r / Real.log 2 - 1 < k := by
    rw [sub_lt_iff_lt_add, div_lt_iff₀ hL]
    linarith
  have hc : |Real.log r / Real.log 2| = |Real.log r| / Real.log 2 := by
    rw [abs_div, abs_of_pos hL]
  rw [abs_le]
  constructor <;> linarith [le_abs_self (Real.log r / Real.log 2),
    neg_abs_le (Real.log r / Real.log 2)]

/-- A positive number `r` with `r ≤ C h^e` and `r⁻¹ ≤ C h^e`, `C, h ≥ 1`, has
`|log r| ≤ log C + e log h`. -/
theorem abs_log_le_of_le_of_inv_le {r C h : ℝ} (hr : 0 < r) (hC : 1 ≤ C) (hh : 1 ≤ h) (e : ℕ)
    (h1 : r ≤ C * h ^ e) (h2 : r⁻¹ ≤ C * h ^ e) :
    |Real.log r| ≤ Real.log C + e * Real.log h := by
  have hCh : 0 < C * h ^ e := by positivity
  have hlog : Real.log (C * h ^ e) = Real.log C + e * Real.log h := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
  have l1 := Real.log_le_log hr h1
  have l2 := Real.log_le_log (inv_pos.mpr hr) h2
  rw [Real.log_inv] at l2
  rw [hlog] at l1 l2
  exact abs_le.mpr ⟨by linarith, l1⟩

/-- A number `r` with `t ≤ r ≤ C h^e`, `t > 0`, `C, h ≥ 1`, has
`|log r| ≤ |log t| + log C + e log h`. -/
theorem abs_log_le_of_mem_Icc {r t C h : ℝ} (ht : 0 < t) (htr : t ≤ r) (hC : 1 ≤ C) (hh : 1 ≤ h)
    (e : ℕ) (h1 : r ≤ C * h ^ e) :
    |Real.log r| ≤ |Real.log t| + Real.log C + e * Real.log h := by
  have hr : 0 < r := ht.trans_le htr
  have hlog : Real.log (C * h ^ e) = Real.log C + e * Real.log h := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
  have l1 := Real.log_le_log hr h1
  rw [hlog] at l1
  have l2 := Real.log_le_log ht htr
  have hC0 : 0 ≤ Real.log C := Real.log_nonneg hC
  have hh0 : 0 ≤ (e : ℝ) * Real.log h := mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg hh)
  rw [abs_le]
  constructor <;> linarith [neg_abs_le (Real.log t), le_abs_self (Real.log t)]

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}

/-- `log ‖x‖ ≤ log N^{[F:ℚ]} + σ(x)` for the full height and the logarithmic height. -/
theorem log_adelicHeight_le {N : ℕ} (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N)
    (x : AdelicGroupPoints F G) :
    Real.log (RepresentationGrowth.adelicHeight F G rho x) ≤
      Real.log ((N : ℝ) ^ (∑ v : NumberField.InfinitePlace F, v.mult)) +
        adelicLogHeight F G rho x := by
  have hs := RepresentationGrowth.adelicSourceNorm_pos F G rho hN x
  have hNs : (0 : ℝ) < (N : ℝ) ^ (∑ v : NumberField.InfinitePlace F, v.mult) := by
    have : (0 : ℝ) < N := by exact_mod_cast hN
    positivity
  rw [RepresentationGrowth.adelicHeight_eq_scalar_mul_sourceNorm, Real.log_mul hNs.ne' hs.ne']
  unfold adelicLogHeight
  have : Real.log (RepresentationGrowth.adelicSourceNorm F G rho x) ≤
      Real.log (max 1 (RepresentationGrowth.adelicSourceNorm F G rho x)) :=
    Real.log_le_log hs (le_max_right _ _)
  linarith

end Height

section SiegelHeight

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {i : T.toGrp ⟶ G} {ν : cocharacterLattice T} {T₀ : CommGroupScheme (Spec (CommRingCat.of F))}
  {j : T₀ ⟶ T} {Z₀ : CommGroupScheme (Spec (CommRingCat.of F))} (zc : Z₀ ⟶ T)
  (hzc : IsCentral (CommGroupScheme.groupHom zc ≫ i))

omit [IsAffine G.X.left] in
/-- The normalized adelic absolute values `|χ(·)|` of the rational characters `χ` of `G` agree
at a point `n m a(z, x) k w` of the Siegel set and at its central factor `z`, because every other
factor has norm one. -/
theorem characterNorm_siegelPoint (hsetup : IsSiegelAlgebraicSetup F G T i ν T₀ j)
    (C : CompactFactors F G (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅))
    {W : Set (AdelicGroupPoints F G)} (hW1 : W ⊆ normOneSubgroup F G)
    (χ : rationalCharacters G)
    (p : PositiveRealTorus.intrinsicSubgroup F Z₀ × PositiveRealTorus.intrinsicSubgroup F T₀)
    (n : AdelicGroupPoints F (Standard.unipotentScheme i ν ∅))
    (m : normOneSubgroup F (Standard.leviScheme i ν ∅))
    {k : AdelicGroupPoints F G} (hk : k ∈ C.compactSubgroup) {w : AdelicGroupPoints F G}
    (hw : w ∈ W) :
    characterNorm F G χ.toMul
        (map F (Standard.unipotentScheme i ν ∅) G (Standard.unipotentHom i ν ∅) n *
          map F (Standard.leviScheme i ν ∅) G (Standard.leviHom i ν ∅) m *
            siegelTorusMap (j := j) zc hzc p * k * w) =
      characterNorm F G χ.toMul (positiveMap F G T i Z₀ zc p.1) := by
  obtain ⟨-, -, -, -, -, -, -, ⟨D, d, t₀, hd, -, ht₀⟩, -⟩ := id hsetup
  have hT : SubgroupFunctor.range (CommGroupScheme.groupHom j ≫ i) ≤ derivedSubgroup G := by
    rw [← ht₀, ← hd.2]
    intro V x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    exact SubgroupFunctor.mem_range.mpr ⟨y ≫ t₀.hom.hom, by
      simp only [Grp.comp_hom_hom, Category.assoc]⟩
  have h1 : characterNorm F G χ.toMul
      (map F (Standard.unipotentScheme i ν ∅) G (Standard.unipotentHom i ν ∅) n) = 1 :=
    (mem_normOneSubgroup F G _).mp (standardUnipotentImage_le_normOne F G T i ν T₀ j
      hsetup unipotentRationalQuotientCompact ⟨n, rfl⟩) χ.toMul
  have h2 : characterNorm F G χ.toMul
      (map F (Standard.leviScheme i ν ∅) G (Standard.leviHom i ν ∅) m) = 1 :=
    (mem_normOneSubgroup F G _).mp (map_normOneSubgroup_le F _ G
      (Standard.leviHom i ν ∅) ⟨m.1, m.2, rfl⟩) χ.toMul
  have h3 := (mem_normOneSubgroup F G _).mp
    (positiveMap_mem_normOne_of_range_le_derived F G T i T₀ j hT p.2) χ.toMul
  have h4 := (mem_normOneSubgroup F G _).mp
    (compactSubgroup_le_normOneSubgroup F G _ C.compact_compactSubgroup hk) χ.toMul
  have h5 := (mem_normOneSubgroup F G _).mp (hW1 hw) χ.toMul
  rw [siegelTorusMap_apply]
  simp only [map_mul, h1, h2, h3, h4, h5, one_mul, mul_one]

/-- An elementary estimate for products of five nonnegative reals. -/
theorem mul_five_le {a₁ a₂ a₃ a₄ a₅ b₁ b₂ b₄ b₅ : ℝ} (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂)
    (h₄ : a₄ ≤ b₄) (h₅ : a₅ ≤ b₅) (h₀₁ : 0 ≤ a₁) (h₀₂ : 0 ≤ a₂) (h₀₃ : 0 ≤ a₃) (h₀₄ : 0 ≤ a₄)
    (h₀₅ : 0 ≤ a₅) : a₁ * a₂ * a₃ * a₄ * a₅ ≤ b₁ * b₂ * b₄ * b₅ * a₃ := by
  have hb₁ : 0 ≤ b₁ := h₀₁.trans h₁
  have hb₂ : 0 ≤ b₂ := h₀₂.trans h₂
  have hb₄ : 0 ≤ b₄ := h₀₄.trans h₄
  have : a₁ * a₂ * a₃ * a₄ * a₅ ≤ b₁ * b₂ * a₃ * b₄ * b₅ := by gcongr
  linarith [this, show b₁ * b₂ * a₃ * b₄ * b₅ = b₁ * b₂ * b₄ * b₅ * a₃ by ring]

omit [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
/-- Submultiplicativity of the height for `g = m⁻¹ n⁻¹ X w⁻¹ k⁻¹`. -/
theorem adelicHeight_le_of_eq_mul {N : ℕ} (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N)
    {g nG mG X k w : AdelicGroupPoints F G} (hX : X = nG * mG * g * k * w) :
    RepresentationGrowth.adelicHeight F G rho g ≤
      RepresentationGrowth.adelicHeight F G rho mG⁻¹ *
        RepresentationGrowth.adelicHeight F G rho nG⁻¹ *
          RepresentationGrowth.adelicHeight F G rho X *
            RepresentationGrowth.adelicHeight F G rho w⁻¹ *
              RepresentationGrowth.adelicHeight F G rho k⁻¹ := by
  have heq : g = mG⁻¹ * nG⁻¹ * X * w⁻¹ * k⁻¹ := by
    rw [hX]
    group
  have h0 : ∀ g, 0 ≤ RepresentationGrowth.adelicHeight F G rho g := fun g =>
    zero_le_one.trans (RepresentationGrowth.one_le_adelicHeight F G rho hN g)
  have hmul := RepresentationGrowth.adelicHeight_mul_le F G rho hN
  rw [heq]
  refine (hmul _ _).trans (mul_le_mul_of_nonneg_right ((hmul _ _).trans
    (mul_le_mul_of_nonneg_right ((hmul _ _).trans
      (mul_le_mul_of_nonneg_right (hmul _ _) (h0 _))) (h0 _))) (h0 _))

omit [LocallyOfFiniteType G.X.hom] in
/-- The height of the torus factor `a(z, x)` of a point `n m a(z, x) k w` of the Siegel set is
bounded by a constant times the height of the point. -/
theorem exists_adelicHeight_siegelTorusMap_le {N : ℕ} (rho : MatrixRepresentation G (Fin N))
    (hN : 0 < N)
    (C : CompactFactors F G (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅))
    {W : Set (AdelicGroupPoints F G)} (hW : W.Finite) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (p : PositiveRealTorus.intrinsicSubgroup F Z₀ ×
        PositiveRealTorus.intrinsicSubgroup F T₀),
      ∀ n ∈ C.omegaN, ∀ m ∈ C.omegaM, ∀ k ∈ C.compactSubgroup, ∀ w ∈ W,
        RepresentationGrowth.adelicHeight F G rho (siegelTorusMap (j := j) zc hzc p) ≤
          B * RepresentationGrowth.adelicHeight F G rho
            (map F (Standard.unipotentScheme i ν ∅) G (Standard.unipotentHom i ν ∅) n *
              map F (Standard.leviScheme i ν ∅) G (Standard.leviHom i ν ∅) m *
                siegelTorusMap (j := j) zc hzc p * k * w) := by
  have hc : Continuous (RepresentationGrowth.adelicHeight F G rho) :=
    RepresentationGrowth.continuous_adelicHeight F G rho hN
  have h0 : ∀ g, 0 ≤ RepresentationGrowth.adelicHeight F G rho g := fun g =>
    zero_le_one.trans (RepresentationGrowth.one_le_adelicHeight F G rho hN g)
  obtain ⟨BN, hBN⟩ := (C.compact_omegaN.image (hc.comp
    (map F _ G (Standard.unipotentHom i ν ∅)).continuous.inv)).bddAbove
  obtain ⟨BM, hBM⟩ := (C.compact_omegaM.image (hc.comp
    ((map F _ G (Standard.leviHom i ν ∅)).continuous.comp continuous_subtype_val).inv)).bddAbove
  obtain ⟨BK, hBK⟩ := (C.compact_compactSubgroup.image (hc.comp continuous_inv)).bddAbove
  obtain ⟨BW, hBW⟩ := (hW.image (fun w => RepresentationGrowth.adelicHeight F G rho w⁻¹)).bddAbove
  refine ⟨max BM 1 * max BN 1 * max BW 1 * max BK 1, ?_, ?_⟩
  · have := le_max_right BM 1
    have := le_max_right BN 1
    have := le_max_right BW 1
    have := le_max_right BK 1
    calc (1 : ℝ) = 1 * 1 * 1 * 1 := by ring
      _ ≤ _ := by gcongr
  intro p n hn m hm k hk w hw
  have hN' : RepresentationGrowth.adelicHeight F G rho
      (map F (Standard.unipotentScheme i ν ∅) G (Standard.unipotentHom i ν ∅) n)⁻¹ ≤ max BN 1 :=
    (hBN ⟨n, hn, rfl⟩).trans (le_max_left _ _)
  have hM' : RepresentationGrowth.adelicHeight F G rho
      (map F (Standard.leviScheme i ν ∅) G (Standard.leviHom i ν ∅) m)⁻¹ ≤ max BM 1 :=
    (hBM ⟨m, hm, rfl⟩).trans (le_max_left _ _)
  have hK' : RepresentationGrowth.adelicHeight F G rho k⁻¹ ≤ max BK 1 :=
    (hBK ⟨k, hk, rfl⟩).trans (le_max_left _ _)
  have hW' : RepresentationGrowth.adelicHeight F G rho w⁻¹ ≤ max BW 1 :=
    (hBW ⟨w, hw, rfl⟩).trans (le_max_left _ _)
  exact (adelicHeight_le_of_eq_mul rho hN
    (nG := map F (Standard.unipotentScheme i ν ∅) G (Standard.unipotentHom i ν ∅) n)
    (mG := map F (Standard.leviScheme i ν ∅) G (Standard.leviHom i ν ∅) m) (k := k) (w := w)
    rfl).trans (mul_five_le hM' hN' hW' hK' (h0 _) (h0 _) (h0 _) (h0 _) (h0 _))

omit [IsAffine G.X.left] in
/-- **Root norms are polynomially bounded by the height.** For a relative root `α`, the norm
`|α(x)|` of the torus coordinate is at most `C ‖a(z, x)‖^e`. This uses that `rho` restricted to
the closed subtorus `T` is a closed embedding, and that roots are trivial on the central split
torus `Z₀`. -/
theorem exists_rootNorm_le {N : ℕ} (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N)
    (hrho : IsClosedSubgroup rho) (hsetup : IsSiegelAlgebraicSetup F G T i ν T₀ j)
    (hZ : IsSplitTorus Z₀.toGrp) {α : characterLattice T} (hα : α ∈ relativeRoots i) :
    ∃ Cα : ℝ, 1 ≤ Cα ∧ ∃ e : ℕ, ∀ (p : PositiveRealTorus.intrinsicSubgroup F Z₀ ×
        PositiveRealTorus.intrinsicSubgroup F T₀),
      ((PositiveRealTorus.normCharacter F T₀ (j ≫ α) p.2 : ℝ≥0) : ℝ) ≤
        Cα * RepresentationGrowth.adelicHeight F G rho (siegelTorusMap (j := j) zc hzc p) ^ e := by
  obtain ⟨hTmax, -⟩ := hsetup
  have hiC : IsClosedSubgroup i := hTmax.1.2
  obtain ⟨Cα, hCα, eα, hb⟩ := RepresentationGrowth.exists_characterNorm_le F (i ≫ rho) hN
    (IsClosedSubgroup.comp hiC hrho) α
  refine ⟨Cα, hCα, eα, fun p => ?_⟩
  set tT : AdelicGroupPoints F T.toGrp :=
    map F Z₀.toGrp T.toGrp (CommGroupScheme.groupHom zc) p.1.val *
      map F T₀.toGrp T.toGrp (CommGroupScheme.groupHom j) p.2.val
  have hcomp : ∀ {H : GroupScheme (Spec (CommRingCat.of F))} (f : H ⟶ T.toGrp)
      (y : AdelicGroupPoints F H), map F H G (f ≫ i) y = map F T.toGrp G i (map F H T.toGrp f y) := by
    intro H f y
    simp only [map_apply, GroupScheme.affinePointsTarget_apply, Grp.comp_hom_hom, Category.assoc]
  have hmapT : map F T.toGrp G i tT = siegelTorusMap (j := j) zc hzc p := by
    rw [map_mul, siegelTorusMap_apply]
    exact congrArg₂ (· * ·) (hcomp _ _).symm (hcomp _ _).symm
  have h0 : zc ≫ α = 0 := root_restrict_eq_zero_of_isCentral i zc hZ hzc hα
  have hz : characterNorm F T.toGrp α.toMul
      (map F Z₀.toGrp T.toGrp (CommGroupScheme.groupHom zc) p.1.val) = 1 := by
    rw [← characterNorm_comp]
    have h0' : CommGroupScheme.groupHom zc ≫ α.toMul =
        (0 : rationalCharacters Z₀.toGrp).toMul := by
      change (zc ≫ α).toMul = _
      rw [h0]
    rw [h0']
    exact characterNorm_zero F Z₀.toGrp _
  have hj : characterNorm F T.toGrp α.toMul
      (map F T₀.toGrp T.toGrp (CommGroupScheme.groupHom j) p.2.val) =
        PositiveRealTorus.normCharacter F T₀ (j ≫ α) p.2 := by
    rw [← characterNorm_comp]
    rfl
  have hnorm : characterNorm F T.toGrp α.toMul tT =
      PositiveRealTorus.normCharacter F T₀ (j ≫ α) p.2 := by
    rw [map_mul, hz, hj, one_mul]
  have hheight : RepresentationGrowth.adelicHeight F T.toGrp (i ≫ rho) tT =
      RepresentationGrowth.adelicHeight F G rho (siegelTorusMap (j := j) zc hzc p) := by
    unfold RepresentationGrowth.adelicHeight
    rw [← RepresentationGrowth.adelicMatrix_map, hmapT]
  rw [← hnorm, ← hheight]
  exact (hb tT).1

/-- **Lower bound of the logarithmic height at Siegel points.** Every integer dyadic coordinate
of the torus factor of a point `X = n m a(z, x) k w` of the Siegel set is bounded by
`A σ(X) + B`. -/
theorem exists_abs_zIndex_le (hsetup : IsSiegelAlgebraicSetup F G T i ν T₀ j) {N : ℕ}
    (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N) (hrho : IsClosedSubgroup rho)
    (hZ : IsSplitTorus Z₀.toGrp)
    (C : CompactFactors F G (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅))
    (t : ℝ≥0ˣ) {W : Set (AdelicGroupPoints F G)} (hW : W.Finite)
    (hW1 : W ⊆ normOneSubgroup F G) {J₀ : Type} [Fintype J₀] (χ : J₀ → rationalCharacters G)
    [Fintype (simpleRelativeRoots i ν)] :
    ∃ A B : ℝ, 0 ≤ A ∧ ∀ (p : PositiveRealTorus.intrinsicSubgroup F Z₀ ×
        PositiveRealTorus.intrinsicSubgroup F T₀),
      p.2 ∈ PositiveRealTorus.weakSimpleRootChamber F T₀ T j G i ν t →
      ∀ n ∈ C.omegaN, ∀ m ∈ C.omegaM, ∀ k ∈ C.compactSubgroup, ∀ w ∈ W, ∀ c,
        |(SiegelSetMeasure.zIndex (siegelCoordinates (i := i) (ν := ν) (j := j) zc χ) p c : ℝ)| ≤
          A * adelicLogHeight F G rho
            (map F (Standard.unipotentScheme i ν ∅) G (Standard.unipotentHom i ν ∅) n *
              map F (Standard.leviScheme i ν ∅) G (Standard.leviHom i ν ∅) m *
                siegelTorusMap (j := j) zc hzc p * k * w) + B := by
  classical
  set Lsc := Real.log ((N : ℝ) ^ (∑ v : NumberField.InfinitePlace F, v.mult))
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨Bh, hBh1, hBh⟩ := exists_adelicHeight_siegelTorusMap_le zc hzc rho hN C hW
  have hcoord : ∀ c, ∃ A B : ℝ, 0 ≤ A ∧ ∀ (p : PositiveRealTorus.intrinsicSubgroup F Z₀ ×
        PositiveRealTorus.intrinsicSubgroup F T₀),
      p.2 ∈ PositiveRealTorus.weakSimpleRootChamber F T₀ T j G i ν t →
      ∀ n ∈ C.omegaN, ∀ m ∈ C.omegaM, ∀ k ∈ C.compactSubgroup, ∀ w ∈ W,
        |(SiegelSetMeasure.zIndex (siegelCoordinates (i := i) (ν := ν) (j := j) zc χ) p c : ℝ)| ≤
          A * adelicLogHeight F G rho
            (map F (Standard.unipotentScheme i ν ∅) G (Standard.unipotentHom i ν ∅) n *
              map F (Standard.leviScheme i ν ∅) G (Standard.leviHom i ν ∅) m *
                siegelTorusMap (j := j) zc hzc p * k * w) + B := by
    intro c
    cases c with
    | inl k₀ =>
      obtain ⟨Cχ, hCχ, eχ, hb⟩ := RepresentationGrowth.exists_characterNorm_le F rho hN hrho (χ k₀)
      refine ⟨eχ / Real.log 2, (Real.log Cχ + eχ * Lsc) / Real.log 2 + 1, by positivity, ?_⟩
      intro p hp n hn m hm k hk w hw
      have hnorm := characterNorm_siegelPoint zc hzc hsetup C hW1 (χ k₀) p n m hk hw
      set X := map F (Standard.unipotentScheme i ν ∅) G (Standard.unipotentHom i ν ∅) n *
        map F (Standard.leviScheme i ν ∅) G (Standard.leviHom i ν ∅) m *
          siegelTorusMap (j := j) zc hzc p * k * w with hX
      have hr : (siegelCoordinates (i := i) (ν := ν) (j := j) zc χ (Sum.inl k₀) p : ℝ≥0) =
          (characterNorm F G (χ k₀).toMul X : ℝ≥0) := by
        rw [siegelCoordinates_inl, hnorm]
      have hpos : 0 < (characterNorm F G (χ k₀).toMul X : ℝ≥0) :=
        pos_iff_ne_zero.mpr (Units.ne_zero _)
      have h1 := (hb X).1
      have h2 : ((characterNorm F G (χ k₀).toMul X : ℝ≥0) : ℝ)⁻¹ ≤
          Cχ * RepresentationGrowth.adelicHeight F G rho X ^ eχ := by
        simpa only [Units.val_inv_eq_inv_val, NNReal.coe_inv] using (hb X).2
      have hlog := abs_log_le_of_le_of_inv_le (NNReal.coe_pos.mpr hpos) hCχ
        (RepresentationGrowth.one_le_adelicHeight F G rho hN X) eχ h1 h2
      have hσ := log_adelicHeight_le rho hN X
      have hIL := abs_intLog_two_le hpos
      change |(Int.log 2 (siegelCoordinates (i := i) (ν := ν) (j := j) zc χ (Sum.inl k₀) p : ℝ≥0) :
        ℝ)| ≤ _
      rw [hr]
      have h3 : |Real.log ((characterNorm F G (χ k₀).toMul X : ℝ≥0) : ℝ)| / Real.log 2 ≤
          (Real.log Cχ + eχ * (Lsc + adelicLogHeight F G rho X)) / Real.log 2 := by
        apply div_le_div_of_nonneg_right _ hL.le
        refine hlog.trans ?_
        have : (eχ : ℝ) * Real.log (RepresentationGrowth.adelicHeight F G rho X) ≤
            eχ * (Lsc + adelicLogHeight F G rho X) :=
          mul_le_mul_of_nonneg_left hσ (Nat.cast_nonneg _)
        linarith
      have key : (Real.log Cχ + eχ * (Lsc + adelicLogHeight F G rho X)) / Real.log 2 =
          eχ / Real.log 2 * adelicLogHeight F G rho X + (Real.log Cχ + eχ * Lsc) / Real.log 2 := by
        ring
      linarith
    | inr α =>
      have hα : (α : characterLattice T) ∈ relativeRoots i :=
        positiveRelativeRoots_subset_relativeRoots i ν (simpleRelativeRoots_subset_positive i ν α.2)
      obtain ⟨Cα, hCα, eα, hb⟩ := exists_rootNorm_le zc hzc rho hN hrho hsetup hZ hα
      set C' := Cα * Bh ^ eα
      have hC' : 1 ≤ C' := one_le_mul_of_one_le_of_one_le hCα (one_le_pow₀ hBh1)
      refine ⟨eα / Real.log 2, (|Real.log ((t : ℝ≥0) : ℝ)| + Real.log C' + eα * Lsc) /
        Real.log 2 + 1, by positivity, ?_⟩
      intro p hp n hn m hm k hk w hw
      set X := map F (Standard.unipotentScheme i ν ∅) G (Standard.unipotentHom i ν ∅) n *
        map F (Standard.leviScheme i ν ∅) G (Standard.leviHom i ν ∅) m *
          siegelTorusMap (j := j) zc hzc p * k * w with hX
      set r : ℝ≥0 := (PositiveRealTorus.normCharacter F T₀ (j ≫ (α : characterLattice T)) p.2 : ℝ≥0)
      have hpos : 0 < r := pos_iff_ne_zero.mpr (Units.ne_zero _)
      have htr : ((t : ℝ≥0) : ℝ) ≤ (r : ℝ) :=
        NNReal.coe_le_coe.mpr (Units.val_le_val.mpr (hp (α : characterLattice T) α.2))
      have ht0 : (0 : ℝ) < ((t : ℝ≥0) : ℝ) :=
        NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero _))
      have hhX := RepresentationGrowth.one_le_adelicHeight F G rho hN X
      have hra : (r : ℝ) ≤ C' * RepresentationGrowth.adelicHeight F G rho X ^ eα := by
        have h1 := hb p
        have h2 := hBh p n hn m hm k hk w hw
        have h0a : 0 ≤ RepresentationGrowth.adelicHeight F G rho (siegelTorusMap (j := j) zc hzc p) :=
          zero_le_one.trans (RepresentationGrowth.one_le_adelicHeight F G rho hN _)
        calc (r : ℝ) ≤ Cα * RepresentationGrowth.adelicHeight F G rho
              (siegelTorusMap (j := j) zc hzc p) ^ eα := h1
          _ ≤ Cα * (Bh * RepresentationGrowth.adelicHeight F G rho X) ^ eα := by
              gcongr
          _ = C' * RepresentationGrowth.adelicHeight F G rho X ^ eα := by
              rw [mul_pow]
              ring
      have hlog := abs_log_le_of_mem_Icc ht0 htr hC' hhX eα hra
      have hσ := log_adelicHeight_le rho hN X
      have hIL := abs_intLog_two_le hpos
      change |(Int.log 2 r : ℝ)| ≤ _
      have h3 : |Real.log (r : ℝ)| / Real.log 2 ≤
          (|Real.log ((t : ℝ≥0) : ℝ)| + Real.log C' + eα * (Lsc + adelicLogHeight F G rho X)) /
            Real.log 2 := by
        apply div_le_div_of_nonneg_right _ hL.le
        refine hlog.trans ?_
        have : (eα : ℝ) * Real.log (RepresentationGrowth.adelicHeight F G rho X) ≤
            eα * (Lsc + adelicLogHeight F G rho X) :=
          mul_le_mul_of_nonneg_left hσ (Nat.cast_nonneg _)
        linarith
      have key : (|Real.log ((t : ℝ≥0) : ℝ)| + Real.log C' +
          eα * (Lsc + adelicLogHeight F G rho X)) / Real.log 2 =
          eα / Real.log 2 * adelicLogHeight F G rho X +
            (|Real.log ((t : ℝ≥0) : ℝ)| + Real.log C' + eα * Lsc) / Real.log 2 := by
        ring
      linarith
  choose A B hA hB using hcoord
  refine ⟨∑ c, A c, ∑ c, |B c|, Finset.sum_nonneg fun c _ => hA c,
    fun p hp n hn m hm k hk w hw c => ?_⟩
  have hσ0 : 0 ≤ adelicLogHeight F G rho
      (map F (Standard.unipotentScheme i ν ∅) G (Standard.unipotentHom i ν ∅) n *
        map F (Standard.leviScheme i ν ∅) G (Standard.leviHom i ν ∅) m *
          siegelTorusMap (j := j) zc hzc p * k * w) :=
    zero_le_one.trans (one_le_adelicLogHeight rho _)
  refine (hB c p hp n hn m hm k hk w hw).trans (add_le_add
    (mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun c _ => hA c) (Finset.mem_univ c)) hσ0)
    ((le_abs_self _).trans (Finset.single_le_sum (fun c _ => abs_nonneg (B c))
      (Finset.mem_univ c))))

end SiegelHeight

section Main

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {i : T.toGrp ⟶ G} {ν : cocharacterLattice T} {T₀ : CommGroupScheme (Spec (CommRingCat.of F))}
  {j : T₀ ⟶ T} {Z₀ : CommGroupScheme (Spec (CommRingCat.of F))} (zc : Z₀ ⟶ T)
  (hzc : IsCentral (CommGroupScheme.groupHom zc ≫ i))

/-- A point `n m a(z, x) k w` of the Siegel set, with `x` in the chamber, is a Siegel point in
the sense of `IsSiegelPoint`, with central factor `z` and torus coordinate `x`. -/
theorem isSiegelPoint_of_mem (hzsplit : IsSplitComponent (CommGroupScheme.groupHom zc ≫ i))
    (C : CompactFactors F G (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅))
    (t : ℝ≥0ˣ) (W : Set (AdelicGroupPoints F G))
    (p : PositiveRealTorus.intrinsicSubgroup F Z₀ × PositiveRealTorus.intrinsicSubgroup F T₀)
    (hp : p.2 ∈ PositiveRealTorus.weakSimpleRootChamber F T₀ T j G i ν t)
    {n : AdelicGroupPoints F (Standard.unipotentScheme i ν ∅)} (hn : n ∈ C.omegaN)
    {m : normOneSubgroup F (Standard.leviScheme i ν ∅)} (hm : m ∈ C.omegaM)
    {k : AdelicGroupPoints F G} (hk : k ∈ C.compactSubgroup) {w : AdelicGroupPoints F G}
    (hw : w ∈ W) :
    IsSiegelPoint F G T i ν T₀ j C t W p.2
      (map F (Standard.unipotentScheme i ν ∅) G (Standard.unipotentHom i ν ∅) n *
        map F (Standard.leviScheme i ν ∅) G (Standard.leviHom i ν ∅) m *
          siegelTorusMap (j := j) zc hzc p * k * w) := by
  have hz : positiveMap F G T i Z₀ zc p.1 ∈ RestrictionSplitCentre.canonicalSubgroup F G := by
    rw [← RestrictionSplitCentre.imageSubgroup_eq_canonicalSubgroup hzsplit]
    exact ⟨p.1.val, p.1.property, rfl⟩
  refine ⟨_, hz, n, hn, m, hm, hp, k, hk, w, hw, ?_⟩
  have hc := (positiveMap_central zc hzc p.1
    (map F (Standard.unipotentScheme i ν ∅) G (Standard.unipotentHom i ν ∅) n *
      map F (Standard.leviScheme i ν ∅) G (Standard.leviHom i ν ∅) m)).eq
  rw [siegelTorusMap_apply]
  calc _ = map F (Standard.unipotentScheme i ν ∅) G (Standard.unipotentHom i ν ∅) n *
          map F (Standard.leviScheme i ν ∅) G (Standard.leviHom i ν ∅) m *
            positiveMap F G T i Z₀ zc p.1 * positiveMap F G T i T₀ j p.2 * k * w := by
        simp only [mul_assoc]
    _ = _ := by
        rw [← hc]
        simp only [mul_assoc]

/-- **Siegel cover of `G(𝔸)`.** If every norm-one point has a rational left translate in
`S W` for the weak Siegel product `S`, then every point of `G(𝔸)` has a rational left translate
in `A_G S W`, written as the Siegel set `Ω_N Ω_M a(A_{Z₀} × A_{T₀}(t)) K` times `W`. -/
theorem exists_rational_mul_mem_centralSiegelSet_mul (hG : IsConnectedReductive G)
    (hzsplit : IsSplitComponent (CommGroupScheme.groupHom zc ≫ i))
    (C : CompactFactors F G (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅))
    (t : ℝ≥0ˣ) (W : Set (AdelicGroupPoints F G))
    (hcover : ∀ g : normOneSubgroup F G, ∃ q : RationalGroupPoints F G,
      rational F G q * (g : AdelicGroupPoints F G) ∈
        weakSiegelProduct F G T i ν (canonicalStandardFactors F G T i ν) C T₀ j t * W)
    (g : AdelicGroupPoints F G) :
    ∃ r ∈ rationalSubgroup F G, r * g ∈ centralSiegelSet (j := j) zc hzc C t * W := by
  obtain ⟨⟨a₀, n₀⟩, rfl⟩ := (RestrictionSplitCentre.intrinsicNormOneDecomposition F G hG).surjective g
  rw [RestrictionSplitCentre.intrinsicNormOneDecomposition_apply]
  have hz : PositiveRealTorus.positivePointMap F G (RestrictionSplitCentre.canonicalTorus F G)
      (RestrictionSplitCentre.canonicalComponent F G) a₀ ∈
        RestrictionSplitCentre.canonicalSubgroup F G := by
    rw [RestrictionSplitCentre.canonicalSubgroup_eq_imageSubgroup F G]
    exact ⟨a₀.val, a₀.property, rfl⟩
  rw [← RestrictionSplitCentre.imageSubgroup_eq_canonicalSubgroup hzsplit] at hz
  obtain ⟨z', hz', hzeq⟩ := hz
  obtain ⟨q, s, hs, w, hw, hsw⟩ := hcover n₀
  obtain ⟨n, hn, m', hm, x, hx, k, hk, hseq⟩ :=
    (mem_productSet_iff F G T i ν (canonicalStandardFactors F G T i ν) C T₀ j _ s).mp hs
  let m : normOneSubgroup F (Standard.leviScheme i ν ∅) := m'
  let pz : PositiveRealTorus.intrinsicSubgroup F Z₀ := ⟨z', hz'⟩
  have hpz : positiveMap F G T i Z₀ zc pz = PositiveRealTorus.positivePointMap F G
      (RestrictionSplitCentre.canonicalTorus F G) (RestrictionSplitCentre.canonicalComponent F G)
        a₀ := hzeq
  refine ⟨rational F G q, ⟨q, rfl⟩, ?_⟩
  refine ⟨map F (Standard.unipotentScheme i ν ∅) G (Standard.unipotentHom i ν ∅) n *
      map F (Standard.leviScheme i ν ∅) G (Standard.leviHom i ν ∅) m *
        siegelTorusMap (j := j) zc hzc (pz, x) * k,
    Set.mul_mem_mul (Set.mul_mem_mul (Set.mul_mem_mul ⟨n, hn, rfl⟩ ⟨m, hm, rfl⟩)
      ⟨(pz, x), ⟨Set.mem_univ _, hx⟩, rfl⟩) hk, w, hw, ?_⟩
  have hc1 := (positiveMap_central zc hzc pz (rational F G q)).eq
  have hc2 := (positiveMap_central zc hzc pz
    (map F (Standard.unipotentScheme i ν ∅) G (Standard.unipotentHom i ν ∅) n *
      map F (Standard.leviScheme i ν ∅) G (Standard.leviHom i ν ∅) m)).eq
  rw [← hpz]
  calc _ = map F (Standard.unipotentScheme i ν ∅) G (Standard.unipotentHom i ν ∅) n *
          map F (Standard.leviScheme i ν ∅) G (Standard.leviHom i ν ∅) m *
            positiveMap F G T i Z₀ zc pz * positiveMap F G T i T₀ j x * k * w := by
        rw [siegelTorusMap_apply]
        simp only [mul_assoc]
    _ = positiveMap F G T i Z₀ zc pz *
          (map F (Standard.unipotentScheme i ν ∅) G (Standard.unipotentHom i ν ∅) n *
            map F (Standard.leviScheme i ν ∅) G (Standard.leviHom i ν ∅) m *
              positiveMap F G T i T₀ j x * k * w) := by
        rw [← hc2]
        simp only [mul_assoc]
    _ = positiveMap F G T i Z₀ zc pz * (rational F G q * n₀.val) := by
        rw [← hsw, ← hseq]
        rfl
    _ = rational F G q * (positiveMap F G T i Z₀ zc pz * n₀.val) := by
        rw [← mul_assoc, hc1, mul_assoc]

/-- The real estimate turning coordinatewise bounds `|κ_c| ≤ A σ + B` into
`max(1, c₀ ∑ |κ_c| - C₀) ≤ σ`. -/
theorem max_le_of_sum_le {σ A B S : ℝ} {n : ℕ} (hA : 0 ≤ A) (hσ1 : 1 ≤ σ)
    (hS : S ≤ n * (A * σ + |B|)) :
    max 1 (1 / ((n + 1) * (A + 1)) * S - |B| / (A + 1)) ≤ σ := by
  have hA1 : 0 < A + 1 := by linarith
  have hn1 : (n : ℝ) / (n + 1) ≤ 1 := div_le_one_of_le₀ (by linarith) (by positivity)
  set X := (A * σ + |B|) / (A + 1)
  have hX : 0 ≤ X := by positivity
  have key : 1 / ((n + 1) * (A + 1)) * (n * (A * σ + |B|)) = (n / (n + 1)) * X := by
    simp only [X]
    field_simp
  have h2 : X ≤ σ + |B| / (A + 1) := by
    simp only [X]
    rw [div_le_iff₀ hA1, add_mul, div_mul_cancel₀ _ hA1.ne']
    nlinarith
  have hc0 : 0 ≤ 1 / (((n : ℝ) + 1) * (A + 1)) := by positivity
  refine max_le hσ1 ?_
  calc 1 / ((n + 1) * (A + 1)) * S - |B| / (A + 1)
      ≤ 1 / ((n + 1) * (A + 1)) * (n * (A * σ + |B|)) - |B| / (A + 1) := by gcongr
    _ = (n / (n + 1)) * X - |B| / (A + 1) := by rw [key]
    _ ≤ X - |B| / (A + 1) := by nlinarith
    _ ≤ σ := by linarith

/-- **Main case, `N > 0`.** -/
theorem siegelDominatedIntegrability_of_pos (hG : IsConnectedReductive G) {N : ℕ}
    (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N) (hrho : IsClosedSubgroup rho) :
    ∃ (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
      (ν : cocharacterLattice T) (T₀ : CommGroupScheme (Spec (CommRingCat.of F)))
      (j : T₀ ⟶ T), IsSiegelAlgebraicSetup F G T i ν T₀ j ∧
    ∃ (C : CompactFactors F G (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅))
      (t : ℝ≥0ˣ) (Ω : Set (AdelicGroupPoints F G)) (d : ℕ), IsCompact Ω ∧
      ∀ f : AdelicGroupPoints F G → ℝ≥0∞, Measurable f →
        (∀ q ∈ rationalSubgroup F G, ∀ g : AdelicGroupPoints F G, f (q * g) = f g) →
        (∀ (a : PositiveRealTorus.intrinsicSubgroup F T₀) (x : AdelicGroupPoints F G),
          IsSiegelPoint F G T i ν T₀ j C t Ω a x →
            f x ≤ ENNReal.ofReal
              (siegelModulus F G T i ν T₀ j a / adelicLogHeight F G rho x ^ d)) →
        ∫⁻ y : RationalQuotient F G, f y.out ∂(LeftCosetSpace.discreteQuotientMeasure
          (rationalSubgroup F G) (isDiscrete_rationalSubgroup F G) Measure.haar) < ∞ := by
  classical
  obtain ⟨T, i, ν, T₀, j, hS⟩ := siegelAlgebraicSetupExistence_of_structural
    genericMinimalParabolic derivedMaximalSplitTorus derivedCentralSplitTorusProduct F G hG
  obtain ⟨K, H₁, W, hKc, hH₁, hKH₁, hH₁P, hcompat, hW, hW1, hcov⟩ :=
    exists_compact_openSubgroup_finite_cover F G hG T i ν T₀ j hS
  obtain ⟨C, t, rfl, hcover⟩ :=
    exists_rational_mul_mem_weakSiegelProduct_mul F G hG T i ν T₀ j hS K hKc W hW hW1 hcov
  obtain ⟨hTmax, -, -, -, -, -, -, -, Z₀, zc, hzsplit, -⟩ := id hS
  have hzc : IsCentral (CommGroupScheme.groupHom zc ≫ i) := hzsplit.1.2
  have hZ : IsSplitTorus Z₀.toGrp := hzsplit.1.1.1
  obtain ⟨I, hI, ⟨e⟩⟩ := id hZ
  have : Fintype I := Fintype.ofFinite I
  have : (characterRestrict (CommGroupScheme.groupHom zc ≫ i)).range.FiniteIndex :=
    characterRestrictionFiniteIndexStatement F G hG Z₀ _ hzsplit
  obtain ⟨m₀, hm₀, hχ⟩ := RepresentationGrowth.exists_characterNorm_full F Z₀
    (CommGroupScheme.groupHom zc ≫ i) e
  choose χ hχ using hχ
  have : Fintype (simpleRelativeRoots i ν) := (hTmax.1.1.finite_simpleRelativeRoots i ν).fintype
  have hbox := isCompact_dyadicBox_siegelCoordinates zc hG hS e χ
    (Nat.mul_pos hm₀ Module.finrank_pos) hχ
  obtain ⟨eδ, heδ⟩ := exists_siegelModulusNN_le zc hS χ
  obtain ⟨D, hD, hDb⟩ := exists_lintegral_centralSiegelSet_le zc hzc hG hS C t H₁ hH₁ hKH₁ hH₁P
    hcompat _ hbox eδ heδ
  obtain ⟨A, B, hA, hAB⟩ := exists_abs_zIndex_le zc hzc hS rho hN hrho hZ C t hW hW1 χ
  set nι := Fintype.card (I ⊕ simpleRelativeRoots i ν)
  set c₀ : ℝ := 1 / ((nι + 1) * (A + 1))
  set C₀ : ℝ := |B| / (A + 1)
  have hc₀ : 0 < c₀ := by positivity
  let Φ : (I ⊕ simpleRelativeRoots i ν → ℤ) → ℝ≥0∞ := fun κ =>
    ENNReal.ofReal ((max 1 (c₀ * ∑ c, |(κ c : ℝ)| - C₀))⁻¹ ^ (2 * nι))
  have hΦ : ∑' κ, Φ κ ≠ ∞ := SiegelSetMeasure.tsum_decay_ne_top hc₀ C₀
  refine ⟨T, i, ν, T₀, j, hS, C, t, W, 2 * nι, hW.isCompact, ?_⟩
  intro f hf hinv hbound
  -- the pointwise estimate on each right translate of the Siegel set
  have hwb : ∀ w ∈ W, ∫⁻ y in centralSiegelSet (j := j) zc hzc C t, f (y * w) ∂Measure.haar ≤
      D * ∑' κ, Φ κ := by
    intro w hw
    refine hDb (fun y => f (y * w)) (hf.comp (continuous_id.mul continuous_const).measurable) Φ ?_
    intro p hp n hn m hm k hk
    have hsp := isSiegelPoint_of_mem zc hzc hzsplit C t W p hp hn hm hk hw
    have hfx := hbound p.2 _ hsp
    set X := map F (Standard.unipotentScheme i ν ∅) G (Standard.unipotentHom i ν ∅) n *
      map F (Standard.leviScheme i ν ∅) G (Standard.leviHom i ν ∅) m *
        siegelTorusMap (j := j) zc hzc p * k * w with hX
    have hσ1 : 1 ≤ adelicLogHeight F G rho X := one_le_adelicLogHeight rho X
    have hsum : ∑ c, |(SiegelSetMeasure.zIndex (siegelCoordinates (i := i) (ν := ν) (j := j) zc χ)
        p c : ℝ)| ≤ nι * (A * adelicLogHeight F G rho X + |B|) := by
      calc ∑ c, |(SiegelSetMeasure.zIndex (siegelCoordinates (i := i) (ν := ν) (j := j) zc χ)
            p c : ℝ)| ≤ ∑ _c : I ⊕ simpleRelativeRoots i ν,
              (A * adelicLogHeight F G rho X + |B|) :=
            Finset.sum_le_sum fun c _ => (hAB p hp n hn m hm k hk w hw c).trans
              (by linarith [le_abs_self B])
        _ = nι * (A * adelicLogHeight F G rho X + |B|) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hmax := max_le_of_sum_le hA hσ1 hsum
    have hmpos : 0 < max 1 (c₀ * ∑ c, |(SiegelSetMeasure.zIndex
        (siegelCoordinates (i := i) (ν := ν) (j := j) zc χ) p c : ℝ)| - C₀) :=
      lt_of_lt_of_le one_pos (le_max_left _ _)
    have hsm : 0 ≤ siegelModulus F G T i ν T₀ j p.2 := by
      rw [← coe_siegelModulusNN]
      exact NNReal.coe_nonneg _
    calc f (X) ≤ ENNReal.ofReal (siegelModulus F G T i ν T₀ j p.2 /
          adelicLogHeight F G rho X ^ (2 * nι)) := hfx
      _ = ENNReal.ofReal (siegelModulus F G T i ν T₀ j p.2) *
          ENNReal.ofReal ((adelicLogHeight F G rho X ^ (2 * nι))⁻¹) := by
          rw [div_eq_mul_inv, ENNReal.ofReal_mul hsm]
      _ ≤ (siegelModulusNN (i := i) (ν := ν) (j := j) p.2 : ℝ≥0∞) *
          Φ (SiegelSetMeasure.zIndex (siegelCoordinates (i := i) (ν := ν) (j := j) zc χ) p) := by
          rw [← coe_siegelModulusNN, ENNReal.ofReal_coe_nnreal]
          gcongr
          apply ENNReal.ofReal_le_ofReal
          rw [← inv_pow]
          exact pow_le_pow_left₀ (inv_nonneg.mpr (zero_le_one.trans hσ1))
            (inv_anti₀ hmpos hmax) _
  -- unfolding and the finitely many right translates
  have hcov' := exists_rational_mul_mem_centralSiegelSet_mul zc hzc hG hzsplit C t W hcover
  have : (Measure.haar : Measure (AdelicGroupPoints F G)).IsMulRightInvariant :=
    adelicHaarUnimodularity.2 F G hG
  have : Finite W := hW.to_subtype
  calc ∫⁻ y : RationalQuotient F G, f y.out ∂(LeftCosetSpace.discreteQuotientMeasure
        (rationalSubgroup F G) (isDiscrete_rationalSubgroup F G) Measure.haar)
      ≤ ∫⁻ x in centralSiegelSet (j := j) zc hzc C t * W, f x ∂Measure.haar :=
        LeftCosetSpace.lintegral_comp_out_le_setLIntegral _ _ _ hf hinv hcov'
    _ ≤ ∑' w : W, ∫⁻ x in (fun x => x * (w : AdelicGroupPoints F G)⁻¹) ⁻¹'
          centralSiegelSet (j := j) zc hzc C t, f x ∂Measure.haar := by
        refine (lintegral_mono_set ?_).trans (lintegral_iUnion_le _ _)
        rintro _ ⟨s, hs, w, hw, rfl⟩
        refine Set.mem_iUnion.mpr ⟨⟨w, hw⟩, ?_⟩
        simpa only [Set.mem_preimage, mul_inv_cancel_right] using hs
    _ = ∑' w : W, ∫⁻ y in centralSiegelSet (j := j) zc hzc C t,
          f (y * (w : AdelicGroupPoints F G)) ∂Measure.haar := by
        refine tsum_congr fun w => ?_
        have hmp := measurePreserving_mul_right (Measure.haar : Measure (AdelicGroupPoints F G))
          (w : AdelicGroupPoints F G)⁻¹
        have key := hmp.setLIntegral_comp_preimage_emb
          (MeasurableEquiv.mulRight (w : AdelicGroupPoints F G)⁻¹).measurableEmbedding
          (fun y => f (y * (w : AdelicGroupPoints F G))) (centralSiegelSet (j := j) zc hzc C t)
        simp only [inv_mul_cancel_right] at key
        exact key
    _ ≤ ∑' _w : W, D * ∑' κ, Φ κ := ENNReal.tsum_le_tsum fun w => hwb w w.2
    _ < ∞ := by
        have : Fintype W := Fintype.ofFinite W
        rw [tsum_fintype]
        exact ENNReal.sum_lt_top.mpr fun w _ => ENNReal.mul_lt_top hD.lt_top hΦ.lt_top

/-- **Degenerate case, `N = 0`.** A closed embedding into `GL_0` forces `G(𝔸)` to be trivial;
then `[G]` is a point of finite measure. -/
theorem siegelDominatedIntegrability_of_zero (hG : IsConnectedReductive G)
    (rho : MatrixRepresentation G (Fin 0)) (hrho : IsClosedSubgroup rho) :
    ∃ (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
      (ν : cocharacterLattice T) (T₀ : CommGroupScheme (Spec (CommRingCat.of F)))
      (j : T₀ ⟶ T), IsSiegelAlgebraicSetup F G T i ν T₀ j ∧
    ∃ (C : CompactFactors F G (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅))
      (t : ℝ≥0ˣ) (Ω : Set (AdelicGroupPoints F G)) (d : ℕ), IsCompact Ω ∧
      ∀ f : AdelicGroupPoints F G → ℝ≥0∞, Measurable f →
        (∀ q ∈ rationalSubgroup F G, ∀ g : AdelicGroupPoints F G, f (q * g) = f g) →
        (∀ (a : PositiveRealTorus.intrinsicSubgroup F T₀) (x : AdelicGroupPoints F G),
          IsSiegelPoint F G T i ν T₀ j C t Ω a x →
            f x ≤ ENNReal.ofReal
              (siegelModulus F G T i ν T₀ j a / adelicLogHeight F G rho x ^ d)) →
        ∫⁻ y : RationalQuotient F G, f y.out ∂(LeftCosetSpace.discreteQuotientMeasure
          (rationalSubgroup F G) (isDiscrete_rationalSubgroup F G) Measure.haar) < ∞ := by
  classical
  have : Subsingleton (AdelicGL F 0) :=
    ⟨fun a b => Units.ext (Subsingleton.elim _ _)⟩
  have hsub : Subsingleton (AdelicGroupPoints F G) :=
    (RepresentationGrowth.isClosedEmbedding_adelicMatrix F G rho hrho).injective.subsingleton
  obtain ⟨T, i, ν, T₀, j, hS⟩ := siegelAlgebraicSetupExistence_of_structural
    genericMinimalParabolic derivedMaximalSplitTorus derivedCentralSplitTorusProduct F G hG
  let C : CompactFactors F G (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅) :=
    ⟨{1}, {1}, isCompact_singleton, isCompact_singleton, ⊥, by
      rw [Subgroup.coe_bot]
      exact isCompact_singleton⟩
  refine ⟨T, i, ν, T₀, j, hS, C, 1, {1}, 0, isCompact_singleton, ?_⟩
  intro f hf hinv hbound
  have hchamber : (1 : PositiveRealTorus.intrinsicSubgroup F T₀) ∈
      PositiveRealTorus.weakSimpleRootChamber F T₀ T j G i ν 1 := by
    intro χ _
    change (1 : ℝ≥0ˣ) ≤ PositiveRealTorus.normCharacter F T₀ (j ≫ χ)
      ((1 : PositiveRealTorus.intrinsicSubgroup F T₀) : Lie.AffinePoints T₀.toGrp (Adeles F))
    rw [OneMemClass.coe_one, map_one]
  have h1 := hbound 1 1 ⟨1, Subgroup.one_mem _, 1, Set.mem_singleton _, 1, Set.mem_singleton _,
    hchamber, 1, Subgroup.one_mem _, 1, Set.mem_singleton _, Subsingleton.elim _ _⟩
  have hfin : f 1 < ∞ := h1.trans_lt ENNReal.ofReal_lt_top
  have heq : ∀ y : RationalQuotient F G, f y.out = f 1 := fun y =>
    congrArg f (Subsingleton.elim _ _)
  simp_rw [heq]
  rw [lintegral_const]
  refine ENNReal.mul_lt_top hfin ?_
  rw [LeftCosetSpace.discreteQuotientMeasure, LeftCosetSpace.quotientMeasure,
    Measure.map_apply (LeftCosetSpace.measurable_mk _) MeasurableSet.univ, Set.preimage_univ,
    Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  have : CompactSpace (AdelicGroupPoints F G) := Finite.compactSpace
  exact (measure_mono (Set.subset_univ _)).trans_lt isCompact_univ.measure_lt_top

end Main

end Langlands.Global.AdelicSiegelFactors

namespace Langlands.Global

/-- **Integrability of Siegel-dominated functions on `[G]`** (derived from Lapid 2013, §2, and
Delorme 2023, (2.5)). -/
theorem siegelDominatedIntegrability : SiegelDominatedIntegrabilityStatement := by
  intro F _ _ G _ _ _ hG N rho hrho
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    exact AdelicSiegelFactors.siegelDominatedIntegrability_of_zero hG rho hrho
  · exact AdelicSiegelFactors.siegelDominatedIntegrability_of_pos hG rho hN hrho

end Langlands.Global
