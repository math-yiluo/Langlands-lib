import Langlands.GroupScheme.Reductive.RootPairNoncommutation
import Langlands.GroupScheme.Reductive.RootDatumOrbitPartners
import Langlands.GroupScheme.Rational.RootDoubleCommutatorRationalPoints
import Langlands.GroupScheme.Rational.RootFiberTransitivity
import Langlands.GroupScheme.Rational.RootSubgroupBaseChange
import Langlands.GroupScheme.Rational.CrossTorusRootTransport
import Langlands.GroupScheme.Rational.TorusSplitPartTransfer
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.Torus.RootSupportBaseChange
import Langlands.GroupScheme.Torus.MaximalSelfCentralizing
import Langlands.GroupScheme.Lie.RootOrbitRelativeWeights
import Langlands.GroupScheme.Reductive.AlgebraicExtensionAscent

/-! # Noncommuting points of a multipliable relative root group

Let `S → T → G` be a maximal split torus inside its centralizer torus `T`, split by a finite
Galois extension `L/k`, and let `a` be a relative root with `2 • a` a relative root and no
`n • a`, `n ≥ 3`, a relative root. Over `L` there are absolute roots `β, β'` restricting to `a`
with `⟨β, β'^∨⟩ = -1`. Their root subgroups do not commute over `Spec L`, and they lie in the
base change of the relative root group of `a`. Hence the points of the relative root group of
`a` over `Spec L` do not all commute.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace MultipliableRootNoncommutation

/-- A nontrivial field automorphism moves some element other than `0` and `-1`. -/
theorem exists_ne_zero_add_ne_zero (k L : Type u) [Field k] [Field L] [Algebra k L]
    {σ : L ≃ₐ[k] L} (hσ : σ ≠ 1) : ∃ x : L, x ≠ 0 ∧ 1 + x ≠ 0 := by
  obtain ⟨x, hx⟩ : ∃ x, σ x ≠ x := by
    by_contra! h
    exact hσ (AlgEquiv.ext fun x => by rw [h x, AlgEquiv.one_apply])
  refine ⟨x, fun h0 => hx (by rw [h0, map_zero]), fun h1 => hx ?_⟩
  have hx1 : x = -1 := eq_neg_of_add_eq_zero_right h1
  rw [hx1, map_neg, map_one]

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {S : CommGroupScheme (Spec (CommRingCat.of k))} (f : S ⟶ T)
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (j : T.toGrp ⟶ G)

local notation "b" => algebraBaseMap k L
local notation "T_L" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T
local notation "S_L" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) S
local notation "f_L" => CategoryTheory.Functor.map (CommGroupScheme.baseChange b) f
local notation "j_L" => CategoryTheory.Functor.map (GroupScheme.baseChange b) j
local notation "G_L" => CategoryTheory.Functor.obj (GroupScheme.baseChange b) G

local instance : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

attribute [local instance] rootsGaloisAction

omit [IsAffineHom G.X.hom] in
/-- Two absolute roots `P.root r` and `P.root r'` of `T_L` form an obtuse pair over the
character `a` of `S`: both restrict to `a` on `S_L`, `⟨P.root r, (P.root r')^∨⟩ = -1`, and
`P.root r + P.root r'` is a root. -/
def IsObtusePair {J : Type*} (P : RootDatum J (characterLattice T_L) (cocharacterLattice T_L))
    (a : characterLattice S) (r r' : J) : Prop :=
  f_L ≫ P.root r = characterLattice.baseChange b S a ∧
    f_L ≫ P.root r' = characterLattice.baseChange b S a ∧ P.pairing r r' = -1 ∧
      P.root r + P.root r' ∈ Set.range P.root

/-- **No higher absolute roots.** If no `n • a` with `n ≥ 3` is a relative root, no absolute
root over `L` restricts to `n • a` with `n ≥ 3`. -/
theorem restrict_ne_nsmul [LocallyOfFiniteType G.X.hom]
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus (T_L).toGrp)
    {a : characterLattice S}
    (hhigh : ∀ n : ℕ, 3 ≤ n → n • a ∉ relativeRoots (CommGroupScheme.groupHom f ≫ j))
    {χ : characterLattice T_L} (hχ : χ ∈ roots (T := T_L) (G := G_L) j_L)
    (hzero : f_L ≫ χ ≠ 0) (n : ℕ) (hn : 3 ≤ n) :
    f_L ≫ χ ≠ n • characterLattice.baseChange b S a := by
  intro h
  have hSL : IsSplitTorus (S_L).toGrp := hS.baseChange b
  let : LocallyOfFiniteType (G_L).X.hom :=
    MorphismProperty.baseChange_obj (P := @LocallyOfFiniteType) b G.X inferInstance
  have hne : n • characterLattice.baseChange b S a ≠ 0 := by
    rw [← h]
    exact hzero
  have hmem : n • characterLattice.baseChange b S a ∈
      roots (T := S_L) ((GroupScheme.baseChange b).map (CommGroupScheme.groupHom f ≫ j)) := by
    rw [Functor.map_comp]
    change _ ∈ roots (T := S_L) (CommGroupScheme.groupHom f_L ≫ j_L)
    refine ⟨hne, ?_⟩
    rw [weightSpace_comp_eq_iSup_roots hT hSL f_L j_L _ hne]
    intro hbot
    apply hχ.2
    rw [eq_bot_iff, ← hbot]
    exact le_iSup_of_le ⟨⟨χ, hχ⟩, h⟩ le_rfl
  rw [← map_nsmul] at hmem
  exact hhigh n hn ((mem_roots_baseChange_iff G S hS _ (n • a)).mp hmem)

/-- **Existence of an obtuse partner pair.** If `a` and `2 • a` are relative roots, there are
absolute roots `β = P.root r` and `β' = P.root r'` forming an obtuse pair over `a`, and a
nontrivial Galois automorphism `σ` with `σ β = β'`. -/
theorem exists_partner [FiniteDimensional k L] [IsGalois k L] [LocallyOfFiniteType G.X.hom]
    [IsAffineHom T.toGrp.X.hom] [LocallyOfFiniteType T.toGrp.X.hom]
    (hS : IsSplitTorus S.toGrp) (hf : IsLargestSplitSubtorus (CommGroupScheme.groupHom f))
    (hT : IsSplitTorus (T_L).toGrp) (hj : IsClosedImmersion (j_L).hom.hom.left)
    {J : Type*} [Finite J]
    {P : RootDatum J (characterLattice T_L) (cocharacterLattice T_L)}
    (hP : IsRootDatumOf (T := T_L) j_L P)
    (hzero : ∀ β : roots (T := T_L) (G := G_L) j_L, f_L ≫ β.val ≠ 0)
    (hred : ∀ r : J, P.root r + P.root r ∉ Set.range P.root)
    {a : characterLattice S} (ha : a ∈ relativeRoots (CommGroupScheme.groupHom f ≫ j))
    (h2a : 2 • a ∈ relativeRoots (CommGroupScheme.groupHom f ≫ j)) :
    ∃ (r r' : J) (σ : L ≃ₐ[k] L), IsObtusePair k L f P a r r' ∧
      characterLattice.galoisRepresentation k L T σ (P.root r) = P.root r' ∧ σ ≠ 1 := by
  classical
  have : Fintype (L ≃ₐ[k] L) := Fintype.ofFinite _
  have hTt : IsTorus T.toGrp := ⟨L, inferInstance, inferInstance, hT⟩
  let ρ := IsRootDatumOf.galoisRootDatumActionOfClosedSplitTorus k L j hT hj hP
  have hroot : ∀ m : J, P.root m ∈ roots (T := T_L) (G := G_L) j_L := fun m => by
    rw [← hP.2.1]
    exact ⟨m, rfl⟩
  have hsum : ∀ m : J, RootPairing.OrbitPartner.orbitSum P ρ m =
      CharacterAveraging.galoisOrbitSum k L T (P.root m) := by
    intro m
    unfold RootPairing.OrbitPartner.orbitSum CharacterAveraging.galoisOrbitSum
      CocharacterAveraging.orbitSum
    exact Finset.sum_congr rfl fun σ _ => IsRootDatumOf.galoisRootIndexEquiv_root k L j hP σ m
  have hne : ∀ m : J, RootPairing.OrbitPartner.orbitSum P ρ m ≠ 0 := fun m => by
    rw [hsum]
    exact galoisOrbitSum_ne_zero_of_restrict_ne_zero k L f hS (hzero ⟨P.root m, hroot m⟩)
  have hrestrict : ∀ (σ : L ≃ₐ[k] L) (m : J),
      f_L ≫ P.root m = characterLattice.baseChange b S a →
        f_L ≫ P.root (ρ σ • m) = characterLattice.baseChange b S a := by
    intro σ m hm
    have h := rootsGaloisAction_mem_restrictionFiber k L j f a σ (β := ⟨P.root m, hroot m⟩) hm
    have hs : P.root (ρ σ • m) = characterLattice.galoisRepresentation k L T σ (P.root m) :=
      IsRootDatumOf.galoisRootIndexEquiv_root k L j hP σ m
    rw [hs]
    exact h
  obtain ⟨β, hβ⟩ := rootRestrictionFiber_nonempty k L j f hS hT ⟨a, ha⟩
  obtain ⟨β₂, hβ₂⟩ := rootRestrictionFiber_nonempty k L j f hS hT ⟨2 • a, h2a⟩
  obtain ⟨p, hp⟩ : β.val ∈ Set.range P.root := by
    rw [hP.2.1]
    exact β.property
  obtain ⟨m, hm⟩ : β₂.val ∈ Set.range P.root := by
    rw [hP.2.1]
    exact β₂.property
  have hpa : f_L ≫ P.root p = characterLattice.baseChange b S a := by
    rw [hp]
    exact hβ
  have hma : f_L ≫ P.root m = characterLattice.baseChange b S (2 • a) := by
    rw [hm]
    exact hβ₂
  have horbit : RootPairing.OrbitPartner.orbitSum P ρ m =
      2 • RootPairing.OrbitPartner.orbitSum P ρ p := by
    rw [hsum, hsum]
    have h1 : CharacterAveraging.galoisOrbitSum k L T (P.root m) =
        CharacterAveraging.galoisOrbitSum k L T (2 • P.root p) :=
      IsLargestSplitSubtorus.galoisOrbitSum_eq_of_restrict_eq k L f hf hTt
        (by rw [hma, Preadditive.comp_nsmul, hpa, map_nsmul])
    rw [h1]
    simp only [CharacterAveraging.galoisOrbitSum, CocharacterAveraging.orbitSum, map_nsmul,
      Finset.smul_sum]
  obtain ⟨g, q, hmq, hq⟩ :=
    RootPairing.OrbitPartner.exists_root_eq_add_of_orbitSum_eq_two_nsmul hne horbit
  have hqr : P.rootOrbitSum ρ q = P.rootOrbitSum ρ (ρ g • p) := by
    change RootPairing.OrbitPartner.orbitSum P ρ q =
      RootPairing.OrbitPartner.orbitSum P ρ (ρ g • p)
    rw [hq, RootPairing.OrbitPartner.orbitSum_smul]
  obtain ⟨σ, hσ⟩ := P.exists_smul_eq_of_rootOrbitSum_eq ρ hqr hne
  have hpartner : RootPairing.OrbitPartner.IsOrbitPartner P ρ (ρ g • p) q :=
    RootPairing.OrbitPartner.isOrbitPartner_of_root_eq_add hred ⟨σ, hσ⟩ hmq
  refine ⟨ρ g • p, q, σ,
    ⟨hrestrict g p hpa, ?_, hpartner.pairing_eq_neg_one hne, m, hmq⟩, ?_, ?_⟩
  · rw [← hσ]
    exact hrestrict σ _ (hrestrict g p hpa)
  · rw [← hσ]
    exact (IsRootDatumOf.galoisRootIndexEquiv_root k L j hP σ _).symm
  · rintro rfl
    apply hpartner.2.1
    rw [← hσ, map_one, one_smul]

/-- **Noncommuting points of a multipliable root group.** Let `f ≫ j` be a maximal split torus
of a connected reductive group `G` whose full centralizer is the closed torus `j : T ⟶ G`, split
by a finite Galois extension `L/k` with a root datum `P` of `T_L`. Let `a` and `2 • a` be relative
roots with no `n • a`, `n ≥ 3`, a relative root. Then two points of the relative root subgroup of
`a` over `Spec L` do not commute. -/
theorem notCommuteOver [FiniteDimensional k L] [IsGalois k L]
    [IsAffineHom T.toGrp.X.hom] [LocallyOfFiniteType T.toGrp.X.hom]
    (hG : IsConnectedReductive G) (hjc : IsClosedSubgroup j)
    (hf : IsMaximalSplitTorus (CommGroupScheme.groupHom f ≫ j))
    (hcent : (torusCentralizer (CommGroupScheme.groupHom f ≫ j)).IsRepresentedBy j)
    (hT : IsSplitTorus (T_L).toGrp)
    {J : Type u} [Finite J]
    {P : RootDatum J (characterLattice T_L) (cocharacterLattice T_L)}
    (hP : IsRootDatumOf (T := T_L) j_L P)
    {a : characterLattice S} (ha : a ∈ relativeRoots (CommGroupScheme.groupHom f ≫ j))
    (h2a : 2 • a ∈ relativeRoots (CommGroupScheme.groupHom f ≫ j))
    (hhigh : ∀ n : ℕ, 3 ≤ n → n • a ∉ relativeRoots (CommGroupScheme.groupHom f ≫ j)) :
    RootPairNoncommutation.NotCommuteOver
      (RelativeRoot.subgroup (CommGroupScheme.groupHom f ≫ j) a)
      (RelativeRoot.subgroup (CommGroupScheme.groupHom f ≫ j) a)
      ((Over.map b).obj (Over.mk (𝟙 (Spec (CommRingCat.of L))))) := by
  let : Smooth G.X.hom := hG.smooth
  have hS : IsSplitTorus S.toGrp := hf.1.1
  have hzero := root_restrict_ne_zero_of_torusCentralizer k L f j hS hT hcent
  have hTt : IsTorus T.toGrp := ⟨L, inferInstance, inferInstance, hT⟩
  let : IsAffine T.X.left := isAffine_of_isAffineHom T.toGrp.X.hom
  have hself : torusCentralizer j = SubgroupFunctor.range j :=
    le_antisymm ((torusCentralizer_le_of_factor j (CommGroupScheme.groupHom f ≫ j)
      (CommGroupScheme.groupHom f) rfl).trans hcent.2.symm.le) (range_le_torusCentralizer j)
  have hjL : IsMaximalTorus (T := T_L) j_L :=
    isMaximalTorus_baseChange_of_torusCentralizer_eq L hTt hjc hself
  have : Algebra.IsAlgebraic k L := Algebra.IsAlgebraic.of_finite k L
  have hGL : IsConnectedReductive G_L := hG.baseChange_of_algebraicExtension (K := L)
  have hroot : ∀ m : J, P.root m ∈ roots (T := T_L) (G := G_L) j_L := fun m => by
    rw [← hP.2.1]
    exact ⟨m, rfl⟩
  have hred : ∀ r : J, P.root r + P.root r ∉ Set.range P.root := by
    intro r h
    apply RootPairNoncommutation.hasNoHigherRoots hGL hT hjL hP r 2 le_rfl
    rw [two_nsmul, relativeRoots_eq_roots, ← hP.2.1]
    exact h
  obtain ⟨r, r', σ, ⟨hr, hr', hpair, -⟩, -, hσ⟩ := exists_partner k L f j hS
    (hf.of_comp hjc).isLargestSplitSubtorus hT (IsClosedSubgroup.baseChange b hjc) hP hzero hred
    ha h2a
  let res : characterLattice T_L →+ characterLattice S_L :=
    AddMonoidHom.mk' (fun χ => f_L ≫ χ) fun χ ψ => Preadditive.comp_add _ _ _ _ _ _
  have hstrict : ∀ n m : ℕ, 0 < n → 0 < m →
      n • P.root r + m • (-P.root r') ≠ 0 ∧
        n • P.root r + m • (-P.root r') ∉ roots (T := T_L) (G := G_L) j_L := by
    intro n m hn hm
    have h := RootPairNoncommutation.strict_combination_not_root P res
      (characterLattice.baseChange b S a) hr hr' hpair
      (fun s n hn => restrict_ne_nsmul k L f j hS hT hhigh (hroot s)
        (hzero ⟨P.root s, hroot s⟩) n hn) n m hn hm
    rw [← hP.2.1]
    exact h
  obtain ⟨x, hx0, hx1⟩ := exists_ne_zero_add_ne_zero k L hσ
  let Z : Over (Spec (CommRingCat.of L)) := Over.mk (𝟙 (Spec (CommRingCat.of L)))
  let c : Γ(Z.left, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of L)).inv.hom x
  have hc : c ≠ 0 := by
    intro h
    apply hx0
    have := congrArg (Scheme.ΓSpecIso (CommRingCat.of L)).hom.hom h
    simpa [c] using this
  have hu : IsUnit (1 + c) := by
    have h : 1 + c = (Scheme.ΓSpecIso (CommRingCat.of L)).inv.hom (1 + x) := by
      simp [c]
    rw [h]
    exact (Ne.isUnit hx1).map _
  obtain ⟨x', hx', y', hy', hxy⟩ :=
    RootPairNoncommutation.exists_not_commute hGL hT hjL hP hpair hstrict (Z := Z) c hc hu
  have hx'' : x' ∈ (RelativeRoot.subgroup (S := S_L)
      ((GroupScheme.baseChange b).map (CommGroupScheme.groupHom f ≫ j))
      (characterLattice.baseChange b S a)).carrier Z := by
    have h := RelativeRoot.mem_subgroup_precomp_torus_hom (S := T_L) j_L (P.root r) f_L hx'
    rw [hr] at h
    rw [Functor.map_comp]
    exact h
  have hy'' : y' ∈ (RelativeRoot.subgroup (S := S_L)
      ((GroupScheme.baseChange b).map (CommGroupScheme.groupHom f ≫ j))
      (characterLattice.baseChange b S a)).carrier Z := by
    have h := RelativeRoot.mem_subgroup_precomp_torus_hom (S := T_L) j_L (P.root r') f_L hy'
    rw [hr'] at h
    rw [Functor.map_comp]
    exact h
  let e := RelativeRoot.subgroupPointsBaseChangeEquiv b (CommGroupScheme.groupHom f ≫ j) a Z
  refine ⟨(e ⟨x', hx''⟩).val, (e ⟨x', hx''⟩).property, (e ⟨y', hy''⟩).val,
    (e ⟨y', hy''⟩).property, fun hcomm => hxy ?_⟩
  have h1 : Commute (e ⟨x', hx''⟩) (e ⟨y', hy''⟩) := Subtype.ext hcomm
  have h2 := h1.map e.symm
  simp only [MulEquiv.symm_apply_apply] at h2
  exact congrArg Subtype.val h2.eq

/-- **The root group of a multipliable relative root is not commutative.** Under the hypotheses
of `notCommuteOver`, a group scheme representing the relative root subgroup of `a` has two
points over `Spec L` that do not commute. -/
theorem not_pointsCommute [FiniteDimensional k L] [IsGalois k L]
    [IsAffineHom T.toGrp.X.hom] [LocallyOfFiniteType T.toGrp.X.hom]
    (hG : IsConnectedReductive G) (hjc : IsClosedSubgroup j)
    (hf : IsMaximalSplitTorus (CommGroupScheme.groupHom f ≫ j))
    (hcent : (torusCentralizer (CommGroupScheme.groupHom f ≫ j)).IsRepresentedBy j)
    (hT : IsSplitTorus (T_L).toGrp)
    {J : Type u} [Finite J]
    {P : RootDatum J (characterLattice T_L) (cocharacterLattice T_L)}
    (hP : IsRootDatumOf (T := T_L) j_L P)
    {a : characterLattice S} (ha : a ∈ relativeRoots (CommGroupScheme.groupHom f ≫ j))
    (h2a : 2 • a ∈ relativeRoots (CommGroupScheme.groupHom f ≫ j))
    (hhigh : ∀ n : ℕ, 3 ≤ n → n • a ∉ relativeRoots (CommGroupScheme.groupHom f ≫ j))
    {U : GroupScheme (Spec (CommRingCat.of k))} {jU : U ⟶ G}
    (hU : (RelativeRoot.subgroup (CommGroupScheme.groupHom f ≫ j) a).IsRepresentedBy jU) :
    ¬ RelativeRoot.PointsCommute U := by
  intro hc
  obtain ⟨x, hx, y, hy, hxy⟩ :=
    notCommuteOver k L f j hG hjc hf hcent hT hP ha h2a hhigh
  rw [← hU.2] at hx hy
  obtain ⟨x₀, rfl⟩ := hx
  obtain ⟨y₀, rfl⟩ := hy
  apply hxy
  change (x₀ ≫ jU.hom.hom) * (y₀ ≫ jU.hom.hom) = (y₀ ≫ jU.hom.hom) * (x₀ ≫ jU.hom.hom)
  rw [← MonObj.mul_comp, ← MonObj.mul_comp, (hc _ x₀ y₀).eq]

end MultipliableRootNoncommutation

end Langlands.GroupScheme
