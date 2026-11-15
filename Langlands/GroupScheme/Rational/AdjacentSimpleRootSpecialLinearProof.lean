import Langlands.GroupScheme.SpecialLinearTernaryWeakRelations
import Langlands.GroupScheme.Rational.AdjacentSimpleRootSpecialLinearStatement
import Langlands.GroupScheme.Rational.OrthogonalOrbitWeylNormalizer
import Langlands.GroupScheme.Rational.OrthogonalOrbitRootCoordinates
import Langlands.GroupScheme.Rational.OrthogonalOrbitCorootWords
import Langlands.GroupScheme.Rational.PieceTorusCharacter
import Langlands.GroupScheme.Rational.StandardLeviRootTransport
import Langlands.GroupScheme.Rational.AdjacentSimpleRootCommutator
import Langlands.GroupScheme.Rational.AdjacentSimpleRootNoncommutation
import Langlands.GroupScheme.Rational.RootSubgroupSeparation
import Langlands.GroupScheme.Rational.RootSubgroupConjugation

/-! # Ternary special linear homomorphisms at adjacent simple roots: proof -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SplitPinning

open SpecialLinear.BinaryPresentation SpecialLinear.TernaryPresentation RealTorusSpace

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] {p : SplitPinning G}

local instance adjacentSpecialLinearMono : Mono p.inclusion.hom.hom.left :=
  p.isMaximalTorus.2.1.mono

section RootDatum

/-- If `⟨b, a^∨⟩ = -1`, the reflection in `a` sends `b` to `a + b`. -/
theorem reflection_root_of_pairing_eq_neg_one (a b : p.base.support)
    (hba : p.rootDatum.pairing b a = -1) :
    p.rootDatum.reflection a (p.rootDatum.root b) = p.rootDatum.root a + p.rootDatum.root b := by
  rw [RootPairing.reflection_apply_root, hba, neg_one_smul, sub_neg_eq_add, add_comm]

/-- The integral pairing of a pinned root and a pinned coroot is the root datum pairing. -/
theorem latticePairing_root_coroot (a b : p.rootIndex) :
    latticePairing p.torus (p.rootDatum.root b) (p.rootDatum.coroot a) =
      p.rootDatum.pairing b a := by
  rw [← p.isRootDatum.1, p.rootDatum.root_coroot_eq_pairing]

end RootDatum

variable (x : p.NormalizedSimpleRootParametrizations)

section Points

theorem rootSL2_upper_eq_xpPoint (a : p.base.support) (t : k) :
    rootSL2 x a (upper t) = (x a).linked.xpPoint t := by
  rw [rootSL2_upper]
  rfl

theorem rootSL2_upper_eq_rationalPoint (a : p.base.support) (t : k) :
    rootSL2 x a (upper t) = (x a).toRootParametrization.rationalPoint t := by
  rw [rootSL2_upper, rankData_xp]

theorem rootSL2_lower_eq_negPoint (a : p.base.support) (t : k) :
    rootSL2 x a (lower t) = (x a).negPoint t := by
  rw [rootSL2_lower, rankData_xm]

theorem rootSL2_lower_eq_xmPoint (a : p.base.support) (t : k) :
    rootSL2 x a (lower t) = (x a).linked.xmPoint t := by
  rw [rootSL2_lower]
  rfl

theorem rootSL2_diag_eq_map (a : p.base.support) (u : kˣ) :
    rootSL2 x a (diag u) =
      rationalPoints.map p.inclusion (p.torusCocharacterPoint (p.rootDatum.coroot a) u) := by
  rw [rootSL2_diag, rankData_h]
  rfl

theorem rootSL2_upper_mem (a : p.base.support) (t : k) :
    rootSL2 x a (upper t) ∈
      (RelativeRoot.subgroup p.inclusion (p.rootDatum.root a)).carrier (Over.mk (𝟙 _)) := by
  rw [rootSL2_upper_eq_rationalPoint]
  exact (x a).toRootParametrization.rationalPoint_mem t

theorem rootSL2_lower_mem (a : p.base.support) (t : k) :
    rootSL2 x a (lower t) ∈
      (RelativeRoot.subgroup p.inclusion (-p.rootDatum.root a)).carrier (Over.mk (𝟙 _)) := by
  rw [rootSL2_lower_eq_negPoint]
  exact (x a).negPoint_mem t

end Points

section Weyl

/-- The Weyl element `rootSL2 x a w` of a simple root, as a point of the normalizer of the
pinned torus. -/
def rootWeyl (a : p.base.support) : normalizerPoints p.inclusion :=
  ⟨rootSL2 x a SpecialLinear.BinaryUpper.weylMatrix, rootSL2_weylMatrix_mem x a⟩

theorem coe_rootWeyl (a : p.base.support) :
    ((rootWeyl x a : normalizerPoints p.inclusion) : rationalPoints G) =
      rootSL2 x a SpecialLinear.BinaryUpper.weylMatrix := rfl

theorem rootSL2_weylMatrix_inv (a : p.base.support) :
    (rootSL2 x a SpecialLinear.BinaryUpper.weylMatrix)⁻¹ =
      (x a).negPoint (-1) * (x a).unitPoint * (x a).negPoint (-1) := by
  rw [← map_inv, weylMatrix_inv_eq, map_mul, map_mul, rootSL2_lower, rootSL2_upper]
  change (x a).negPoint (-1) * (x a).linked.xpPoint 1 * (x a).negPoint (-1) = _
  rw [(x a).xpPoint_linked]
  rfl

/-- The Weyl element of a simple root `a` acts on characters by the reflection in `a`. -/
theorem weylAction_rootWeyl (a : p.base.support) :
    weylAction p.inclusion (rootWeyl x a) = p.rootDatum.reflection a := by
  have hpair := (x a).eq_oppositeFactorPair (x a).isOppositeFactorPair_unitPoint
  have hpt : (((rootWeyl x a)⁻¹ : normalizerPoints p.inclusion) : rationalPoints G) =
      (x a).reflectionRepresentative.point := by
    rw [Subgroup.coe_inv, coe_rootWeyl, rootSL2_weylMatrix_inv,
      (x a).reflectionRepresentative_point, ← hpair]
  have hn : IsNormalizingPoint p.inclusion
      (((rootWeyl x a)⁻¹ : normalizerPoints p.inclusion) : rationalPoints G)
      (x a).reflectionRepresentative.torusAut := by
    rw [hpt]
    exact (x a).reflectionRepresentative.normalizes
  have hinv : weylAction p.inclusion (rootWeyl x a)⁻¹ = p.rootDatum.reflection a := by
    apply LinearEquiv.ext
    intro χ
    rw [weylAction_eq p.inclusion hn, ← characterAut_apply,
      (x a).reflectionRepresentative.characterAut_eq]
  rw [← inv_inv (rootWeyl x a), map_inv, hinv, RootPairing.reflection_inv]

/-- The Weyl element of a simple root `a` acts on cocharacters by the coreflection in `a`. -/
theorem cocharacterAut_rootWeyl (a : p.base.support) (ζ : cocharacterLattice p.torus) :
    cocharacterAut (normalizingAut p.inclusion (rootWeyl x a)) ζ =
      p.rootDatum.coreflection a ζ := by
  set σ := normalizingAut p.inclusion (rootWeyl x a)
  have hσ : characterAut σ = p.rootDatum.reflection a := weylAction_rootWeyl x a
  apply p.rootDatum.flip.toPerfPair.injective
  apply LinearMap.ext
  intro χ
  change p.rootDatum.toLinearMap χ (cocharacterAut σ ζ) =
    p.rootDatum.toLinearMap χ (p.rootDatum.coreflection a ζ)
  have h := latticePairing_characterAut_cocharacterAut σ (p.rootDatum.reflection a χ) ζ
  rw [hσ, p.rootDatum.reflection_same, ← p.isRootDatum.1] at h
  rw [h]
  have e := LinearMap.congr_fun (LinearMap.congr_fun
    (p.rootDatum.reflection_dualMap_eq_coreflection a) ζ) χ
  simpa using e

/-- `ν_a h_b(u) ν_a⁻¹ = h_a(u) h_b(u)` when `⟨a, b^∨⟩ = -1`. -/
theorem rootSL2_weyl_conj_diag (a b : p.base.support) (hab : p.rootDatum.pairing a b = -1)
    (u : kˣ) :
    rootSL2 x a SpecialLinear.BinaryUpper.weylMatrix * rootSL2 x b (diag u) *
        (rootSL2 x a SpecialLinear.BinaryUpper.weylMatrix)⁻¹ =
      rootSL2 x a (diag u) * rootSL2 x b (diag u) := by
  have h := p.conj_map_inclusion (rootWeyl x a)
    (p.torusCocharacterPoint (p.rootDatum.coroot b) u)
  rw [coe_rootWeyl] at h
  rw [rootSL2_diag_eq_map, rootSL2_diag_eq_map, h, ← map_mul]
  congr 1
  have hc : p.rootDatum.coroot b ≫ (normalizingAut p.inclusion (rootWeyl x a)).hom =
      p.rootDatum.coroot a + p.rootDatum.coroot b := by
    change cocharacterAut _ _ = _
    rw [cocharacterAut_rootWeyl, RootPairing.coreflection_apply_coroot, hab, neg_one_smul,
      sub_neg_eq_add, add_comm]
  simp only [torusCocharacterPoint, CocharacterUniformizer.cocharacterPoints,
    MonoidHom.coe_comp, Function.comp_apply, rationalPoints.map_apply]
  rw [← comp_groupHom_comp, hc, comp_groupHom_add]

end Weyl

section Torus

/-- `h_a(u) x_b(t) h_a(u)⁻¹ = x_b(u⁻¹ t)` when `⟨b, a^∨⟩ = -1`. -/
theorem rootSL2_conj_diag_upper (a b : p.base.support) (hba : p.rootDatum.pairing b a = -1)
    (u : kˣ) (t : k) :
    rootSL2 x a (diag u) * rootSL2 x b (upper t) * (rootSL2 x a (diag u))⁻¹ =
      rootSL2 x b (upper ((u : k)⁻¹ * t)) := by
  rw [rootSL2_diag_eq_map, rootSL2_upper_eq_xpPoint, rootSL2_upper_eq_xpPoint,
    (x b).linked.conj_xpPoint]
  congr 2
  change ((p.charEval (p.rootDatum.root b)
    (p.torusCocharacterPoint (p.rootDatum.coroot a) u) : kˣ) : k) = _
  rw [charEval_torusCocharacterPoint, latticePairing_root_coroot, hba, zpow_neg_one,
    Units.val_inv_eq_inv_val]

/-- `h_a(u) y_b(t) h_a(u)⁻¹ = y_b(u t)` when `⟨b, a^∨⟩ = -1`. -/
theorem rootSL2_conj_diag_lower (a b : p.base.support) (hba : p.rootDatum.pairing b a = -1)
    (u : kˣ) (t : k) :
    rootSL2 x a (diag u) * rootSL2 x b (lower t) * (rootSL2 x a (diag u))⁻¹ =
      rootSL2 x b (lower ((u : k) * t)) := by
  rw [rootSL2_diag_eq_map, rootSL2_lower_eq_xmPoint, rootSL2_lower_eq_xmPoint,
    (x b).linked.conj_xmPoint]
  congr 2
  change ((p.charEval (-p.rootDatum.root b)
    (p.torusCocharacterPoint (p.rootDatum.coroot a) u) : kˣ) : k) = _
  rw [charEval_torusCocharacterPoint, map_neg, LinearMap.neg_apply, latticePairing_root_coroot,
    hba, neg_neg, zpow_one]

end Torus

section Corner

/-- The corner point `ν_a x_b(-t) ν_a⁻¹` lies in the root group of `a + b`. -/
theorem cornerPoint_mem (a b : p.base.support) (hba : p.rootDatum.pairing b a = -1) (t : k) :
    cornerPoint (rootSL2 x a) (rootSL2 x b) t ∈
      (RelativeRoot.subgroup p.inclusion (p.rootDatum.root a + p.rootDatum.root b)).carrier
        (Over.mk (𝟙 _)) := by
  have h := RelativeRoot.normalizer_conj_mem p.inclusion (p.rootDatum.root b) (rootWeyl x a)
    (rootSL2_upper_mem x b (-t))
  rw [constantPoint_self, weylAction_rootWeyl, reflection_root_of_pairing_eq_neg_one a b hba,
    coe_rootWeyl] at h
  exact h

/-- Every rational point of the root group of `a + b` is a corner point. -/
theorem exists_cornerPoint_eq (a b : p.base.support) (hba : p.rootDatum.pairing b a = -1)
    {g : rationalPoints G}
    (hg : g ∈ (RelativeRoot.subgroup p.inclusion
      (p.rootDatum.root a + p.rootDatum.root b)).carrier (Over.mk (𝟙 _))) :
    ∃ t : k, cornerPoint (rootSL2 x a) (rootSL2 x b) t = g := by
  have h := RelativeRoot.normalizer_conj_mem p.inclusion
    (p.rootDatum.root a + p.rootDatum.root b) (rootWeyl x a)⁻¹ hg
  rw [constantPoint_self, map_inv, weylAction_rootWeyl, RootPairing.reflection_inv,
    ← reflection_root_of_pairing_eq_neg_one a b hba, RootPairing.reflection_same] at h
  obtain ⟨r, hr⟩ := (x b).toRootParametrization.exists_rationalPoint_eq h
  refine ⟨-r, ?_⟩
  rw [cornerPoint, neg_neg, rootSL2_upper_eq_rationalPoint, hr, Subgroup.coe_inv, coe_rootWeyl]
  group

end Corner

section Commutation

/-- Points of the root groups of `b` and `a + b` commute, for adjacent simple roots. -/
theorem commute_of_mem_root_of_mem_sum (a b : p.base.support) (hab : a ≠ b)
    (hab' : p.rootDatum.pairing a b = -1) (hba : p.rootDatum.pairing b a = -1)
    {g h : rationalPoints G}
    (hg : g ∈ (RelativeRoot.subgroup p.inclusion (p.rootDatum.root b)).carrier
      (Over.mk (𝟙 _)))
    (hh : h ∈ (RelativeRoot.subgroup p.inclusion
      (p.rootDatum.root a + p.rootDatum.root b)).carrier (Over.mk (𝟙 _))) :
    Commute g h := by
  have hsum : p.rootDatum.root a + p.rootDatum.root b ≠ 0 := by
    simpa using p.simple_add_ne_zero a b hab 1 1 one_pos
  apply p.commute_of_no_strict_root_combinations _ _ (p.rootDatum.ne_zero b) hsum _ hg hh
  intro n m hn hm
  have e : n • p.rootDatum.root b + m • (p.rootDatum.root a + p.rootDatum.root b) =
      m • p.rootDatum.root a + (n + m) • p.rootDatum.root b := by
    rw [smul_add, add_smul]
    abel
  rw [e]
  refine ⟨p.simple_add_ne_zero a b hab m (n + m) hm, fun hr => ?_⟩
  have := p.adjacent_root_combination a b hab hab' hba m (n + m) hm (by omega) hr
  omega

/-- `x_a(s) x_b(c) x_a(s)⁻¹ = x_b(c) x₃(f)` for some `f`. -/
theorem rootSL2_weak_commutator (a b : p.base.support) (hab : a ≠ b)
    (hab' : p.rootDatum.pairing a b = -1) (hba : p.rootDatum.pairing b a = -1) (s c : k) :
    ∃ f : k, rootSL2 x a (upper s) * rootSL2 x b (upper c) * (rootSL2 x a (upper s))⁻¹ =
      rootSL2 x b (upper c) * cornerPoint (rootSL2 x a) (rootSL2 x b) f := by
  have hα : p.rootDatum.root (p.rootDatum.reflectionPerm a b) =
      p.rootDatum.root a + p.rootDatum.root b := by
    rw [RootPairing.root_reflectionPerm, reflection_root_of_pairing_eq_neg_one a b hba]
  have hmem := p.adjacent_commutator_mem b a hab.symm hba hab'
    (by rw [hα, add_comm])
    (Subgroup.inv_mem _ (rootSL2_upper_mem x b c)) (rootSL2_upper_mem x a s)
  rw [hα] at hmem
  obtain ⟨f, hf⟩ := exists_cornerPoint_eq x a b hba hmem
  refine ⟨f, ?_⟩
  rw [hf]
  group

/-- Root group separation: `x_b(e) = x₃(d)` forces `x_b(e) = 1`. -/
theorem rootSL2_separation (a b : p.base.support) (hba : p.rootDatum.pairing b a = -1)
    (e d : k) (h : rootSL2 x b (upper e) = cornerPoint (rootSL2 x a) (rootSL2 x b) d) :
    rootSL2 x b (upper e) = 1 := by
  have hc := cornerPoint_mem x a b hba d
  rw [← h] at hc
  have hpos : 0 < latticePairing p.torus (p.rootDatum.root b) (-p.rootDatum.coroot a) := by
    rw [map_neg, latticePairing_root_coroot, hba]
    norm_num
  have hpos' : 0 < latticePairing p.torus (p.rootDatum.root a + p.rootDatum.root b)
      (p.rootDatum.coroot a) := by
    rw [map_add, LinearMap.add_apply, latticePairing_root_coroot, latticePairing_root_coroot,
      RootPairing.pairing_same, hba]
    norm_num
  apply RelativeRoot.eq_one_of_mem_subgroup_of_mem_negative_parabolic p.inclusion
    (-p.rootDatum.coroot a) hpos (rootSL2_upper_mem x b e)
  rw [neg_neg]
  exact Dynamic.unipotent_le_parabolic _ _
    (RelativeRoot.subgroup_le_dynamicUnipotent p.inclusion (p.rootDatum.coroot a) hpos' _ hc)

end Commutation

section Lower

/-- If `ν_a ν_b` conjugates `x_a(t)` to `x_b(t)` for all `t`, it conjugates `y_a(t)` to
`y_b(t)`: conjugation carries the unique opposite pair of `x_a(c)` to an opposite pair of
`x_b(c)`. -/
theorem rootSL2_weyl_mul_weyl_conj_lower (a b : p.base.support)
    (hab' : p.rootDatum.pairing a b = -1) (hba : p.rootDatum.pairing b a = -1)
    (hupper : ∀ t : k, (rootSL2 x a SpecialLinear.BinaryUpper.weylMatrix *
        rootSL2 x b SpecialLinear.BinaryUpper.weylMatrix) * rootSL2 x a (upper t) *
        (rootSL2 x a SpecialLinear.BinaryUpper.weylMatrix *
          rootSL2 x b SpecialLinear.BinaryUpper.weylMatrix)⁻¹ = rootSL2 x b (upper t))
    (t : k) :
    (rootSL2 x a SpecialLinear.BinaryUpper.weylMatrix *
        rootSL2 x b SpecialLinear.BinaryUpper.weylMatrix) * rootSL2 x a (lower t) *
        (rootSL2 x a SpecialLinear.BinaryUpper.weylMatrix *
          rootSL2 x b SpecialLinear.BinaryUpper.weylMatrix)⁻¹ = rootSL2 x b (lower t) := by
  rw [rootSL2_lower_eq_negPoint, rootSL2_lower_eq_negPoint]
  by_cases ht : t = 0
  · subst ht
    rw [(x a).negPoint_zero, (x b).negPoint_zero]
    group
  set m : normalizerPoints p.inclusion := rootWeyl x a * rootWeyl x b with hm
  have hM : ((m : normalizerPoints p.inclusion) : rationalPoints G) =
      rootSL2 x a SpecialLinear.BinaryUpper.weylMatrix *
        rootSL2 x b SpecialLinear.BinaryUpper.weylMatrix := rfl
  rw [← hM]
  rw [← hM] at hupper
  have hact : weylAction p.inclusion m (-p.rootDatum.root a) = -p.rootDatum.root b := by
    rw [hm, map_mul, LinearEquiv.mul_apply, weylAction_rootWeyl, weylAction_rootWeyl, map_neg,
      map_neg, reflection_root_of_pairing_eq_neg_one b a hab', map_add,
      reflection_root_of_pairing_eq_neg_one a b hba, RootPairing.reflection_apply_self]
    abel
  set c : kˣ := Units.mk0 (-t⁻¹) (by simpa using ht) with hc
  have hct : -((c : k))⁻¹ = t := by
    rw [hc, Units.val_mk0, inv_neg, inv_inv, neg_neg]
  have hpair := (x a).isOppositeFactorPair_rationalPoint c
  rw [hct] at hpair
  have hy : (m : rationalPoints G) * (x a).negPoint t * (m : rationalPoints G)⁻¹ ∈
      (RelativeRoot.subgroup p.inclusion (-p.rootDatum.root b)).carrier (Over.mk (𝟙 _)) := by
    have h := RelativeRoot.normalizer_conj_mem p.inclusion (-p.rootDatum.root a) m hpair.1
    rwa [constantPoint_self, hact] at h
  have hxc : (m : rationalPoints G) * (x a).toRootParametrization.rationalPoint c *
      (m : rationalPoints G)⁻¹ = (x b).toRootParametrization.rationalPoint c := by
    rw [← rootSL2_upper_eq_rationalPoint, ← rootSL2_upper_eq_rationalPoint, hupper]
  have hq : RelativeRoot.IsOppositeFactorPair p.inclusion (p.rootDatum.root b)
      ((x b).toRootParametrization.rationalPoint c)
      ((m : rationalPoints G) * (x a).negPoint t * (m : rationalPoints G)⁻¹,
        (m : rationalPoints G) * (x a).negPoint t * (m : rationalPoints G)⁻¹) := by
    refine ⟨hy, hy, ?_⟩
    have e : (m : rationalPoints G) * (x a).negPoint t * (m : rationalPoints G)⁻¹ *
        (x b).toRootParametrization.rationalPoint c *
        ((m : rationalPoints G) * (x a).negPoint t * (m : rationalPoints G)⁻¹) =
        (m : rationalPoints G) * ((x a).negPoint t * (x a).toRootParametrization.rationalPoint c *
          (x a).negPoint t) * (m : rationalPoints G)⁻¹ := by
      rw [← hxc]
      group
    change _ ∈ normalizerPoints p.inclusion
    rw [e]
    exact (normalizerPoints p.inclusion).mul_mem
      ((normalizerPoints p.inclusion).mul_mem m.2 hpair.2.2)
      ((normalizerPoints p.inclusion).inv_mem m.2)
  have hq' := (x b).eq_negPoint_of_isOppositeFactorPair c hq
  rw [hct] at hq'
  exact congrArg Prod.fst hq'

end Lower

section Assembly

/-- The weak ternary relations hold for the rank-one homomorphisms of two adjacent simple
roots. -/
theorem weakTernaryRelations_rootSL2 (a b : p.base.support) (hab : a ≠ b)
    (hab' : p.rootDatum.pairing a b = -1) (hba : p.rootDatum.pairing b a = -1) :
    WeakTernaryRelations (rootSL2 x a) (rootSL2 x b) where
  torus_upper := rootSL2_conj_diag_upper x a b hba
  torus_lower := rootSL2_conj_diag_lower x a b hba
  torus_upper' := rootSL2_conj_diag_upper x b a hab'
  weyl_torus := rootSL2_weyl_conj_diag x a b hab'
  commute_lower_upper r c :=
    (p.commute_simple_neg_simple a b hab (rootSL2_upper_mem x a c)
      (rootSL2_lower_mem x b r)).symm
  commute_lower_upper' r c :=
    (p.commute_simple_neg_simple b a hab.symm (rootSL2_upper_mem x b c)
      (rootSL2_lower_mem x a r)).symm
  commute_upper_corner c t :=
    commute_of_mem_root_of_mem_sum a b hab hab' hba (rootSL2_upper_mem x b c)
      (cornerPoint_mem x a b hba t)
  commute_upper_corner' c t :=
    commute_of_mem_root_of_mem_sum b a hab.symm hba hab' (rootSL2_upper_mem x a c)
      (cornerPoint_mem x b a hab' t)
  commute_corner s t :=
    commute_of_mem_root_of_mem_sum b a hab.symm hba hab' (rootSL2_upper_mem x a s)
      (by rw [add_comm]; exact cornerPoint_mem x a b hba t)
  weak_commutator := rootSL2_weak_commutator x a b hab hab' hba
  weak_commutator' := rootSL2_weak_commutator x b a hab.symm hba hab'
  separation := rootSL2_separation x a b hba
  separation' := rootSL2_separation x b a hab'

end Assembly

end SplitPinning

/-- **Ternary `SL` at an `A₂` pair of simple roots.** For adjacent simple roots `a`, `b` of a
split pinning with `⟨a, b^∨⟩ = ⟨b, a^∨⟩ = -1`, the rank-one homomorphisms `rootSL2 x a` and
`rootSL2 x b` are the restrictions of one homomorphism `SL₃(k) →* G(k)` to the two block
copies of `SL₂(k)`. -/
theorem adjacentSimpleRootSpecialLinear : AdjacentSimpleRootSpecialLinearStatement.{u} := by
  intro k _ G _ p x a b hab' hba
  have hab : a ≠ b := by
    rintro rfl
    rw [RootPairing.pairing_same] at hab'
    norm_num at hab'
  have R := SplitPinning.weakTernaryRelations_rootSL2 x a b hab hab' hba
  exact R.exists_lift
    (SplitPinning.rootSL2_weyl_mul_weyl_conj_lower x a b hab' hba R.weyl_mul_weyl_conj_upper)

end Langlands.GroupScheme
