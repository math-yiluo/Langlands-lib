import Langlands.Representation.Smooth.FixedVectors.NormalizedJacquetBridgeProof
import Langlands.Representation.Jacquet.StandardCentralContraction
import Langlands.BruhatTits.SpecialCompact.StrictChamberPowerBasis
import Langlands.BruhatTits.SpecialCompact.CompatibleComponent
import Langlands.Representation.Plancherel.RationalTwistStabilizer

/-! # Nonvanishing form of Jacquet's lemma, without admissibility -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.Jacquet

universe uG uV uF

section Abstract

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- For a `K`-fixed vector `y` of the unnormalized coinvariants, some power of `g` moves
`y` into the image of the `K`-fixed vectors. -/
theorem exists_fixedVector_mk_eq_of_contraction
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (N M Nbar : Subgroup G)
    (hMN : M ≤ Subgroup.normalizer N)
    (hfactor : ∀ k ∈ K, ∃ l ∈ K.toSubgroup ⊓ Nbar, ∃ m ∈ K.toSubgroup ⊓ M,
      ∃ u ∈ K.toSubgroup ⊓ N, k = l * m * u)
    (g : M) (hlevi : ∀ m ∈ K.toSubgroup ⊓ M, (g : G)⁻¹ * m * g ∈ K.toSubgroup ⊓ M)
    (hcontract : ∀ L : OpenSubgroup G, ∃ s : ℕ,
      ∀ l ∈ K.toSubgroup ⊓ Nbar, ((g : G) ^ s)⁻¹ * l * (g : G) ^ s ∈ L)
    (y : fixedVectors (action ρ N M hMN) (K.toSubgroup.comap M.subtype)) :
    ∃ (s : ℕ) (v : V), v ∈ fixedVectors ρ K.toSubgroup ∧
      mk ρ N v = action ρ N M hMN (g ^ s) (y : Coinvariants ρ N) := by
  obtain ⟨v, hv⟩ := mk_surjective ρ N (y : Coinvariants ρ N)
  obtain ⟨U, hU⟩ := hρ v
  obtain ⟨s, hs⟩ := hcontract U
  have hgs : ((g ^ s : M) : G) = (g : G) ^ s := by simp
  have hlow : ∀ l ∈ K.toSubgroup ⊓ Nbar,
      ρ l (ρ ((g : G) ^ s) v) = ρ ((g : G) ^ s) v := by
    intro l hl
    calc
      ρ l (ρ ((g : G) ^ s) v) =
          ρ ((g : G) ^ s) (ρ (((g : G) ^ s)⁻¹ * l * (g : G) ^ s) v) := by
        simp only [← Module.End.mul_apply, ← map_mul ρ]
        congr 1
        group
      _ = ρ ((g : G) ^ s) v := congrArg _ (hU ⟨_, hs l hl⟩)
  have hlevi_pow : ∀ r : ℕ, ∀ m ∈ K.toSubgroup ⊓ M,
      ((g : G) ^ r)⁻¹ * m * (g : G) ^ r ∈ K.toSubgroup ⊓ M := by
    intro r
    induction r with
    | zero => intro m hm; simpa using hm
    | succ r ih =>
      intro m hm
      have e : ((g : G) ^ (r + 1))⁻¹ * m * (g : G) ^ (r + 1) =
          (g : G)⁻¹ * (((g : G) ^ r)⁻¹ * m * (g : G) ^ r) * g := by
        group
      rw [e]
      exact hlevi _ (ih m hm)
  have hlevi' : ∀ m ∈ K.toSubgroup ⊓ M,
      mk ρ N (ρ m (ρ ((g : G) ^ s) v)) =
        action ρ N M hMN (g ^ s) (y : Coinvariants ρ N) := by
    intro m hm
    have hm' := hlevi_pow s m hm
    have hyfix := y.property ⟨⟨_, hm'.2⟩, hm'.1⟩
    calc
      mk ρ N (ρ m (ρ ((g : G) ^ s) v)) =
          mk ρ N (ρ ((g ^ s : M) : G) (ρ (((g : G) ^ s)⁻¹ * m * (g : G) ^ s) v)) := by
        rw [hgs]
        simp only [← Module.End.mul_apply, ← map_mul ρ]
        congr 2
        group
      _ = action ρ N M hMN (g ^ s)
            (action ρ N M hMN ⟨_, hm'.2⟩ (mk ρ N v)) := by
        rw [action_mk, action_mk]
      _ = _ := by
        rw [hv]
        exact congrArg _ hyfix
  have hconst : ∀ k : K,
      mk ρ N (ρ k.val (ρ ((g : G) ^ s) v)) =
        action ρ N M hMN (g ^ s) (y : Coinvariants ρ N) := by
    intro k
    obtain ⟨l, hl, m, hm, u, hu, hprod⟩ := hfactor k.val⁻¹ (K.inv_mem k.property)
    have heq : k.val = u⁻¹ * (m⁻¹ * l⁻¹) := by
      rw [← inv_inv k.val, hprod]
      group
    rw [heq, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
      hlow _ ((K.toSubgroup ⊓ Nbar).inv_mem hl)]
    rw [mk_apply_subgroup ρ N ⟨u⁻¹, N.inv_mem hu.2⟩]
    exact hlevi' _ ((K.toSubgroup ⊓ M).inv_mem hm)
  exact ⟨s, Compact.averageMap ρ hρ K hK (ρ ((g : G) ^ s) v),
    Compact.averageMap_mem_fixedVectors ρ hρ K hK _,
    map_averageMap_of_forall_eq ρ hρ K hK (mk ρ N) _ _ hconst⟩

/-- Nonvanishing form of Jacquet's lemma: a nonzero `K ∩ M`-fixed vector of the
unnormalized coinvariants gives a nonzero `K`-fixed vector. No admissibility is used. -/
theorem nontrivial_fixedVectors_of_contraction
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (N M Nbar : Subgroup G)
    (hMN : M ≤ Subgroup.normalizer N)
    (hfactor : ∀ k ∈ K, ∃ l ∈ K.toSubgroup ⊓ Nbar, ∃ m ∈ K.toSubgroup ⊓ M,
      ∃ u ∈ K.toSubgroup ⊓ N, k = l * m * u)
    (g : M) (hlevi : ∀ m ∈ K.toSubgroup ⊓ M, (g : G)⁻¹ * m * g ∈ K.toSubgroup ⊓ M)
    (hcontract : ∀ L : OpenSubgroup G, ∃ s : ℕ,
      ∀ l ∈ K.toSubgroup ⊓ Nbar, ((g : G) ^ s)⁻¹ * l * (g : G) ^ s ∈ L)
    (h : Nontrivial (fixedVectors (action ρ N M hMN) (K.toSubgroup.comap M.subtype))) :
    Nontrivial (fixedVectors ρ K.toSubgroup) := by
  obtain ⟨y, hy⟩ := exists_ne (0 : fixedVectors (action ρ N M hMN)
    (K.toSubgroup.comap M.subtype))
  obtain ⟨s, v, hvK, hv⟩ := exists_fixedVector_mk_eq_of_contraction ρ hρ K hK N M Nbar hMN
    hfactor g hlevi hcontract y
  refine ⟨⟨⟨v, hvK⟩, 0, fun h0 => hy ?_⟩⟩
  have hv0 : v = 0 := congrArg Subtype.val h0
  apply Subtype.ext
  apply (Representation.apply_bijective (action ρ N M hMN) (g ^ s)).injective
  rw [← hv, hv0, map_zero, ZeroMemClass.coe_zero, map_zero]

omit [IsTopologicalGroup G] in
/-- A power neighbourhood basis of `Nbar` for `g⁻¹` gives the uniform contraction of
`K ∩ Nbar` by the inverse powers of `g` into every open subgroup. -/
theorem contract_of_conjugatePowerNeighborhoodBasis
    {K Nbar : Subgroup G} {g : G}
    (hbasis : BruhatTits.SpecialCompact.ConjugatePowerNeighborhoodBasis K Nbar g⁻¹)
    (L : OpenSubgroup G) :
    ∃ s : ℕ, ∀ l ∈ K ⊓ Nbar, (g ^ s)⁻¹ * l * g ^ s ∈ L := by
  let Lbar : OpenSubgroup Nbar := L.comap Nbar.subtype continuous_subtype_val
  obtain ⟨s, _, hs⟩ := hbasis.2.mem_iff.mp Lbar.mem_nhds_one
  refine ⟨s, ?_⟩
  intro l hl
  have hU : (g ^ s)⁻¹ * l * g ^ s ∈ Nbar := by
    have himage : (g⁻¹) ^ s * l * ((g⁻¹) ^ s)⁻¹ ∈
        BruhatTits.SpecialCompact.ambientConjugate ((g⁻¹) ^ s)
          ((K ⊓ Nbar : Subgroup G) : Set G) :=
      ⟨l, hl, rfl⟩
    simpa only [inv_pow, inv_inv, SetLike.mem_coe] using hbasis.1 s himage
  apply hs (show (⟨(g ^ s)⁻¹ * l * g ^ s, hU⟩ : Nbar) ∈
    {x : Nbar | ∃ y : Nbar, y ∈ Subgroup.comap Nbar.subtype K ∧
      (x : G) = (g⁻¹) ^ s * (y : G) * ((g⁻¹) ^ s)⁻¹} from ?_)
  exact ⟨⟨l, hl.2⟩, hl.1, by simp only [inv_pow, inv_inv]⟩

end Abstract

section Normalized

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]

/-- A nonzero `K ∩ M`-fixed vector of the normalized Jacquet module gives a nonzero
`K ∩ M`-fixed vector of the unnormalized coinvariants: the normalizing character is
trivial on the compact group `K ∩ M`. -/
theorem nontrivial_jacquetAction_fixedVectors_of_normalized
    (N M : Subgroup G) (hN : IsClosed (N : Set G)) (hMN : M ≤ Subgroup.normalizer N)
    (hM : IsClosed (M : Set G)) (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (D : SmoothRep.{0, uG, uV} ℂ G)
    (h : Nontrivial (fixedVectors
      ((Aubert.General.normalizedJacquetFunctor N M hN hMN).obj D).representation
      (K.toSubgroup.comap M.subtype))) :
    Nontrivial (fixedVectors (action D.representation N M hMN)
      (K.toSubgroup.comap M.subtype)) := by
  let χ := HaarModulus.closedInverseHalfCharacter N hN M hMN
  let ρD := Jacquet.Localization.action D.representation N 1 M hMN
    (Jacquet.Localization.isInvariant_one N M hMN)
  let KM := K.toSubgroup.comap M.subtype
  have hχ : KM ≤ χ.ker := NormalizedJacquetBridge.character_trivial N M hN hMN hM K hK
  obtain ⟨⟨w, hw⟩, hw0⟩ := exists_ne (0 : fixedVectors
      ((Aubert.General.normalizedJacquetFunctor N M hN hMN).obj D).representation KM)
  have hwLoc : w ∈ fixedVectors ρD KM := by
    change w ∈ fixedVectors (twist χ ρD) KM at hw
    rwa [fixedVectors_twist_eq_of_le_ker χ ρD KM hχ] at hw
  let e := Jacquet.Localization.trivialEquiv D.representation N M hMN
  have hew : e w ∈ fixedVectors (action D.representation N M hMN) KM :=
    map_mem_fixedVectors e.toIntertwiningMap hwLoc
  refine ⟨⟨⟨e w, hew⟩, 0, fun hz => hw0 ?_⟩⟩
  have hz' : e w = 0 := congrArg Subtype.val hz
  apply Subtype.ext
  exact e.injective (hz'.trans (map_zero e).symm)

end Normalized

section Standard

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)

local instance iwahoriJacquetNonvanishingAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance iwahoriJacquetNonvanishingTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X

/-- Nonvanishing form of Jacquet's lemma for a standard parabolic: if `K` is a compact
open subgroup with an Iwahori decomposition along the standard parabolic `P_J = M_J N_J`,
then a nonzero `K ∩ M_J`-fixed vector of the unnormalized `N_J`-coinvariants of a smooth
representation gives a nonzero `K`-fixed vector. -/
theorem nontrivial_fixedVectors_of_standardJacquet
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) {J : Set (characterLattice S)}
    (hJ : J ⊆ simpleRelativeRoots i ν)
    (hstd : ∃ zeta, IsStandardCocharacter i ν J zeta)
    (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
    (hIwahori : HasIwahoriIntersectionDecomposition K.toSubgroup (standardLeviPoints i ν J)
      (standardUnipotentPoints i ν J) (standardOppositeUnipotentPoints i ν J))
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (rationalPoints G) V) (hρ : IsSmooth ρ)
    (hMN : standardLeviPoints i ν J ≤ Subgroup.normalizer (standardUnipotentPoints i ν J))
    (h : Nontrivial (fixedVectors
      (action ρ (standardUnipotentPoints i ν J) (standardLeviPoints i ν J) hMN)
      (K.toSubgroup.comap (standardLeviPoints i ν J).subtype))) :
    Nontrivial (fixedVectors ρ K.toSubgroup) := by
  let : Smooth G.X.hom := hG.smooth
  let : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  obtain ⟨zeta, hzeta⟩ := hstd
  obtain ⟨A, q, hA⟩ := exists_compatibleStandardSplitComponent hG i hi ν hν J hJ
  let g : standardLeviPoints i ν J :=
    (hA.centralStrictElement i ν hi hzeta : standardLeviPoints i ν J)
  have hcentral := (hA.centralStrictElement i ν hi hzeta).property
  have hgstrict := (hA.strictElement_spec i ν hi hzeta).2.2.2
  have hbases := (hA.strictChamber_power_basis_and_exhaustion i ν hG hi hν hJ K.toSubgroup
    K.isOpen hK).2 _ hgstrict
  refine nontrivial_fixedVectors_of_contraction ρ hρ K hK (standardUnipotentPoints i ν J)
    (standardLeviPoints i ν J) (standardOppositeUnipotentPoints i ν J) hMN ?_ g ?_ ?_ h
  · intro k hk
    obtain ⟨⟨l, m, n⟩, heq⟩ := hIwahori.2 ⟨k, hk⟩
    exact ⟨l, l.property, m, m.property, n, n.property,
      (congrArg Subtype.val heq).symm⟩
  · intro m hm
    have hcomm := congrArg Subtype.val (Subgroup.mem_center_iff.mp hcentral ⟨m, hm.2⟩)
    have hgm : (g : rationalPoints G)⁻¹ * m * g = m := by
      change m * (g : rationalPoints G) = (g : rationalPoints G) * m at hcomm
      rw [mul_assoc, hcomm, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [hgm]
    exact hm
  · exact contract_of_conjugatePowerNeighborhoodBasis hbases.2

/-- Normalized form: a nonzero `K ∩ M_J`-fixed vector of the normalized Jacquet module of a
smooth representation `D` along the standard parabolic `P_J` gives a nonzero `K`-fixed
vector of `D`. -/
theorem nontrivial_fixedVectors_of_standardNormalizedJacquet
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) {J : Set (characterLattice S)}
    (hJ : J ⊆ simpleRelativeRoots i ν)
    (hstd : ∃ zeta, IsStandardCocharacter i ν J zeta)
    (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
    (hIwahori : HasIwahoriIntersectionDecomposition K.toSubgroup (standardLeviPoints i ν J)
      (standardUnipotentPoints i ν J) (standardOppositeUnipotentPoints i ν J))
    (hN : IsClosed (standardUnipotentPoints i ν J : Set (rationalPoints G)))
    (hM : IsClosed (standardLeviPoints i ν J : Set (rationalPoints G)))
    (hMN : standardLeviPoints i ν J ≤ Subgroup.normalizer (standardUnipotentPoints i ν J))
    [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
    (D : SmoothRep.{0, uF, uV} ℂ (rationalPoints G))
    (h : Nontrivial (fixedVectors
      ((Aubert.General.normalizedJacquetFunctor (standardUnipotentPoints i ν J)
        (standardLeviPoints i ν J) hN hMN).obj D).representation
      (K.toSubgroup.comap (standardLeviPoints i ν J).subtype))) :
    Nontrivial (fixedVectors D.representation K.toSubgroup) := by
  exact nontrivial_fixedVectors_of_standardJacquet i ν hG hi hν hJ hstd K hK hIwahori
    D.representation D.isSmooth hMN
    (nontrivial_jacquetAction_fixedVectors_of_normalized _ _ hN hMN hM K hK D h)

end Standard

end Langlands.Jacquet
