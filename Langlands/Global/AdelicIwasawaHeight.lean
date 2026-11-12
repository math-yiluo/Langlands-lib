import Langlands.Global.AdelicCharacterLog
import Langlands.Global.AdelicPositiveImageClosed
import Langlands.Global.AdelicIwasawaStatement
import Langlands.GroupScheme.Rational.CharacterLine

/-! # The Iwasawa height `H_P` on actual adelic points

For a closed subgroup `p : P → G` and a compact subgroup `K` of `G(𝔸_F)` with
`P(𝔸_F) K = G(𝔸_F)`, every `g` factors as `g = p(q) k`, and `H_P(g) = log_P(q)` does not
depend on the factorization. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.Global.AdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]
variable {G P : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [IsAffine P.X.left]
variable (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left]

/-- A point of `P(𝔸_F)` whose image lies in a compact subgroup of `G(𝔸_F)` has zero
logarithmic functional. -/
theorem characterLog_eq_zero_of_map_mem {K : Subgroup (AdelicGroupPoints F G)}
    (hK : IsCompact (K : Set (AdelicGroupPoints F G))) {q : AdelicGroupPoints F P}
    (hq : map F P G p q ∈ K) : characterLog F P q = 0 := by
  have hc : IsCompact ((K.comap (map F P G p).toMonoidHom : Subgroup (AdelicGroupPoints F P)) :
      Set (AdelicGroupPoints F P)) :=
    (isClosedEmbedding_map F P G p).isCompact_preimage hK
  exact characterLog_eq_zero_on_compactSubgroup F P _ hc hq

variable {F p}

/-- `K` is an Iwasawa subgroup for `p : P → G`: it is compact and `P(𝔸_F) K = G(𝔸_F)`, with the
parabolic factor on the left. No maximality is required. -/
structure IsIwasawaCompact (p : P ⟶ G) (K : Subgroup (AdelicGroupPoints F G)) : Prop where
  isCompact : IsCompact (K : Set (AdelicGroupPoints F G))
  range_mul : Set.range (map F P G p) * (K : Set (AdelicGroupPoints F G)) = Set.univ

omit [IsAffine G.X.left] [IsAffine P.X.left] [IsClosedImmersion p.hom.hom.left] in
/-- A maximal compact Iwasawa subgroup in the sense of the published
`IsParabolicIwasawaCompact` is an Iwasawa subgroup. -/
theorem IsParabolicIwasawaCompact.isIwasawaCompact {K : Subgroup (AdelicGroupPoints F G)}
    (hK : IsParabolicIwasawaCompact F G P p K) : IsIwasawaCompact p K :=
  ⟨hK.1.1, hK.2⟩

variable {K : Subgroup (AdelicGroupPoints F G)}

omit [IsAffine G.X.left] [IsAffine P.X.left] [IsClosedImmersion p.hom.hom.left] in
theorem IsIwasawaCompact.exists_eq (hK : IsIwasawaCompact p K) (g : AdelicGroupPoints F G) :
    ∃ q : AdelicGroupPoints F P, ∃ k ∈ K, map F P G p q * k = g := by
  have hg : g ∈ Set.range (map F P G p) * (K : Set (AdelicGroupPoints F G)) := by
    rw [hK.range_mul]
    exact Set.mem_univ g
  obtain ⟨_, ⟨q, rfl⟩, k, hk, hqk⟩ := hg
  exact ⟨q, k, hk, hqk⟩

/-- Two factorizations of the same point have the same logarithmic functional. -/
theorem IsIwasawaCompact.characterLog_eq (hK : IsIwasawaCompact p K)
    {q q' : AdelicGroupPoints F P} {k k' : AdelicGroupPoints F G} (hk : k ∈ K) (hk' : k' ∈ K)
    (h : map F P G p q * k = map F P G p q' * k') :
    characterLog F P q = characterLog F P q' := by
  have hmem : map F P G p (q'⁻¹ * q) ∈ K := by
    have : map F P G p (q'⁻¹ * q) = k' * k⁻¹ := by
      rw [map_mul, map_inv]
      calc (map F P G p q')⁻¹ * map F P G p q
          = (map F P G p q')⁻¹ * (map F P G p q * k) * k⁻¹ := by group
        _ = (map F P G p q')⁻¹ * (map F P G p q' * k') * k⁻¹ := by rw [h]
        _ = k' * k⁻¹ := by group
    rw [this]
    exact K.mul_mem hk' (K.inv_mem hk)
  have h0 := characterLog_eq_zero_of_map_mem F p hK.isCompact hmem
  have hsplit : q = q' * (q'⁻¹ * q) := by group
  rw [hsplit, characterLog_mul, h0, add_zero]

/-- The Iwasawa height `H_P : G(𝔸_F) → Hom(Rat(P), ℝ)`: for `g = p(q) k` with `k ∈ K`, it is
`log_P(q)`. -/
def IsIwasawaCompact.height (hK : IsIwasawaCompact p K) (g : AdelicGroupPoints F G) :
    RealCharacterDual F P :=
  characterLog F P (hK.exists_eq g).choose

/-- The height is computed by any factorization. -/
theorem IsIwasawaCompact.height_eq (hK : IsIwasawaCompact p K) {g : AdelicGroupPoints F G}
    {q : AdelicGroupPoints F P} {k : AdelicGroupPoints F G} (hk : k ∈ K)
    (hg : map F P G p q * k = g) : hK.height g = characterLog F P q := by
  obtain ⟨k₀, hk₀, h₀⟩ := (hK.exists_eq g).choose_spec
  exact hK.characterLog_eq hk₀ hk (h₀.trans hg.symm)

/-- The height is right `K`-invariant. -/
theorem IsIwasawaCompact.height_mul_right (hK : IsIwasawaCompact p K) (g : AdelicGroupPoints F G)
    {k : AdelicGroupPoints F G} (hk : k ∈ K) : hK.height (g * k) = hK.height g := by
  obtain ⟨q, k₀, hk₀, rfl⟩ := hK.exists_eq g
  rw [hK.height_eq (K.mul_mem hk₀ hk) (mul_assoc _ _ _).symm, hK.height_eq hk₀ rfl]

/-- Left translation by `P(𝔸_F)` adds its logarithmic functional. -/
theorem IsIwasawaCompact.height_map_mul (hK : IsIwasawaCompact p K) (q : AdelicGroupPoints F P)
    (g : AdelicGroupPoints F G) :
    hK.height (map F P G p q * g) = characterLog F P q + hK.height g := by
  obtain ⟨q₀, k₀, hk₀, rfl⟩ := hK.exists_eq g
  rw [hK.height_eq hk₀ (by rw [map_mul, mul_assoc]), hK.height_eq hk₀ rfl, characterLog_mul]

/-- The height of the image of a point of `P(𝔸_F)` is its logarithmic functional. -/
theorem IsIwasawaCompact.height_map (hK : IsIwasawaCompact p K) (q : AdelicGroupPoints F P) :
    hK.height (map F P G p q) = characterLog F P q :=
  hK.height_eq K.one_mem (mul_one _)

/-- The height is invariant under left translation by principal points of `P`. -/
theorem IsIwasawaCompact.height_rational_mul (hK : IsIwasawaCompact p K)
    (γ : RationalGroupPoints F P) (g : AdelicGroupPoints F G) :
    hK.height (map F P G p (rational F P γ) * g) = hK.height g := by
  rw [hK.height_map_mul, characterLog_rational, zero_add]

/-- The height vanishes on `K`. -/
theorem IsIwasawaCompact.height_of_mem (hK : IsIwasawaCompact p K) {k : AdelicGroupPoints F G}
    (hk : k ∈ K) : hK.height k = 0 := by
  rw [hK.height_eq hk (by rw [map_one, one_mul] : map F P G p 1 * k = k), characterLog_one]

omit [IsAffine G.X.left] [IsAffine P.X.left] in
/-- A unipotent group has zero logarithmic functional, since it has no nonzero rational
character. -/
theorem characterLog_eq_zero_of_isUnipotent {U : GroupScheme (Spec (CommRingCat.of F))}
    (hU : GroupScheme.IsUnipotent U) (x : AdelicGroupPoints F U) : characterLog F U x = 0 := by
  apply AddMonoidHom.ext
  intro χ
  rw [hU.rationalCharacter_eq_zero χ]
  change Real.log ((characterNorm F U (0 : GroupScheme.rationalCharacters U).toMul x : NNReal) :
    ℝ) = 0
  rw [characterNorm_zero]
  exact Real.log_one

/-- Left translation by points of a unipotent subgroup of `P` does not change the height. -/
theorem IsIwasawaCompact.height_unipotent_mul (hK : IsIwasawaCompact p K)
    {U : GroupScheme (Spec (CommRingCat.of F))} (hU : GroupScheme.IsUnipotent U) (iU : U ⟶ P)
    (x : AdelicGroupPoints F U) (g : AdelicGroupPoints F G) :
    hK.height (map F P G p (map F U P iU x) * g) = hK.height g := by
  rw [hK.height_map_mul, characterLog_map, characterLog_eq_zero_of_isUnipotent hU, map_zero,
    zero_add]

/-- The Mœglin–Waldspurger form of the height: for `g = p(ι(u) l(m)) k` with `u` in a unipotent
subgroup `iU : U → P`, `m` in a subgroup `l : M → P` and `k ∈ K`, the height is the image of
`log_M(m)` under the map `Hom(Rat(M), ℝ) → Hom(Rat(P), ℝ)` induced by `l`. -/
theorem IsIwasawaCompact.height_eq_levi (hK : IsIwasawaCompact p K)
    {U M : GroupScheme (Spec (CommRingCat.of F))} (hU : GroupScheme.IsUnipotent U)
    (iU : U ⟶ P) (l : M ⟶ P) (u : AdelicGroupPoints F U) (m : AdelicGroupPoints F M)
    {k : AdelicGroupPoints F G} (hk : k ∈ K) :
    hK.height (map F P G p (map F U P iU u * map F M P l m) * k) =
      realCharacterDualMap F M P l (characterLog F M m) := by
  rw [map_mul, mul_assoc, hK.height_unipotent_mul hU, ← characterLog_map, hK.height_eq hk rfl]

omit [IsAffine G.X.left] [IsAffine P.X.left] [IsClosedImmersion p.hom.hom.left] in
/-- The adelic-point map of a composite is the composite of the adelic-point maps. -/
theorem map_comp_apply_of_hom {P₀ : GroupScheme (Spec (CommRingCat.of F))} (f : P₀ ⟶ P)
    (x : AdelicGroupPoints F P₀) : map F P₀ G (f ≫ p) x = map F P G p (map F P₀ P f x) := by
  simp only [map_apply, GroupScheme.affinePointsTarget_apply, Grp.comp_hom_hom, Category.assoc]

omit [IsAffine G.X.left] [IsAffine P.X.left] [IsClosedImmersion p.hom.hom.left] in
/-- An Iwasawa subgroup for a subgroup `P₀` of `P` is an Iwasawa subgroup for `P`. For instance a
`K` with `P₀(𝔸_F) K = G(𝔸_F)` for the minimal parabolic serves every standard parabolic. -/
theorem IsIwasawaCompact.of_comp {P₀ : GroupScheme (Spec (CommRingCat.of F))} (f : P₀ ⟶ P)
    (hK : IsIwasawaCompact (f ≫ p) K) : IsIwasawaCompact p K := by
  refine ⟨hK.isCompact, Set.eq_univ_of_univ_subset ?_⟩
  rw [← hK.range_mul]
  apply Set.mul_subset_mul_right
  rintro _ ⟨x, rfl⟩
  exact ⟨map F P₀ P f x, (map_comp_apply_of_hom f x).symm⟩

section Levi

variable {A B C : GroupScheme (Spec (CommRingCat.of F))}

omit [NumberField F] [IsAffine G.X.left] [IsAffine P.X.left]
  [IsClosedImmersion p.hom.hom.left] in
/-- The covariant maps of real character duals compose. -/
theorem realCharacterDualMap_comp_apply (f : A ⟶ B) (g : B ⟶ C) (ℓ : RealCharacterDual F A) :
    realCharacterDualMap F B C g (realCharacterDualMap F A B f ℓ) =
      realCharacterDualMap F A C (f ≫ g) ℓ := by
  apply AddMonoidHom.ext
  intro χ
  change ℓ (GroupScheme.characterRestrict f (GroupScheme.characterRestrict g χ)) =
    ℓ (GroupScheme.characterRestrict (f ≫ g) χ)
  rw [GroupScheme.characterRestrict_comp]
  rfl

omit [NumberField F] [IsAffine G.X.left] [IsAffine P.X.left]
  [IsClosedImmersion p.hom.hom.left] in
/-- The covariant map of the identity is the identity. -/
theorem realCharacterDualMap_id_apply (ℓ : RealCharacterDual F A) :
    realCharacterDualMap F A A (𝟙 A) ℓ = ℓ := by
  apply AddMonoidHom.ext
  intro χ
  change ℓ (GroupScheme.characterRestrict (𝟙 A) χ) = ℓ χ
  rw [GroupScheme.characterRestrict_id]
  rfl

/-- With a Levi projection `q : P → M` (`l ≫ q = 𝟙`), the height of `p(iU(u) l(m)) k` maps to
`log_M(m) ∈ Hom(Rat(M), ℝ)`: Mœglin–Waldspurger's `log_M(m_P(g))`. -/
theorem IsIwasawaCompact.realCharacterDualMap_height_eq (hK : IsIwasawaCompact p K)
    {U M : GroupScheme (Spec (CommRingCat.of F))} (hU : GroupScheme.IsUnipotent U)
    (iU : U ⟶ P) (l : M ⟶ P) (q : P ⟶ M) (hq : l ≫ q = 𝟙 M) (u : AdelicGroupPoints F U)
    (m : AdelicGroupPoints F M) {k : AdelicGroupPoints F G} (hk : k ∈ K) :
    realCharacterDualMap F P M q
        (hK.height (map F P G p (map F U P iU u * map F M P l m) * k)) =
      characterLog F M m := by
  rw [hK.height_eq_levi hU iU l u m hk, realCharacterDualMap_comp_apply, hq,
    realCharacterDualMap_id_apply]

end Levi

end Langlands.Global.AdelicGroupPoints
