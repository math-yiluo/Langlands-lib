import Langlands.GroupScheme.Rational.QuasiSplitCompatiblePinning
import Langlands.GroupScheme.Rational.RootFiberTransitivity
import Langlands.GroupScheme.Reductive.RootDatumTorusTransport
import Langlands.GroupScheme.Torus.SplitLatticeBaseChange
import Langlands.GroupScheme.Torus.RootSupportBaseChange
import Langlands.GroupScheme.Torus.WeilRestrictionNormOneCharacters
import Langlands.GroupScheme.Rational.RootFactorizationFromExistence
import Langlands.Geometry.Building.QuasiSplitMultipliablePieces

/-! # Restriction of pinned roots to a maximal split torus

For Galois-compatible pinning data `D` of `G` over a finite Galois extension `K/k` and a
maximal split torus `S ⟶ D.torus ⟶ G`, the roots of the pinning restrict to relative roots,
restriction is invariant under the Galois action on simple roots, and each restriction fibre
of a simple root is its Galois orbit. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace GaloisCompatiblePinningData

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (D : GaloisCompatiblePinningData k K G)
  {S : CommGroupScheme (Spec (CommRingCat.of k))} (t : S ⟶ D.torus)

local notation "bK" => algebraBaseMap k K
local notation "S_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange bK) S
local notation "t_K" => CategoryTheory.Functor.map (CommGroupScheme.baseChange bK) t

/-- The restriction map from the base-changed split torus to the pinned torus. -/
def restrictMap : S_K ⟶ D.pinning.torus :=
  t_K ≫ D.torusIso.inv

/-- The pinned inclusion restricted along `restrictMap` is the base change of
`groupHom t ≫ D.inclusion`. -/
theorem groupHom_restrictMap_comp_inclusion :
    CommGroupScheme.groupHom (D.restrictMap t) ≫ D.pinning.inclusion =
      (GroupScheme.baseChange bK).map (CommGroupScheme.groupHom t ≫ D.inclusion) := by
  rw [D.inclusion_eq, Functor.map_comp]
  change CommGroupScheme.groupHom (t_K ≫ D.torusIso.inv ≫ D.torusIso.hom) ≫ _ = _
  rw [D.torusIso.inv_hom_id, Category.comp_id]
  rfl

/-- The root datum of the pinning transported to the base-changed descended torus. -/
def transportedRootDatum :=
  torusTransportRootDatum D.torusIso D.pinning.rootDatum

theorem transportedRootDatum_root (r : D.pinning.rootIndex) :
    D.transportedRootDatum.root r =
      characterLattice.congr D.torusIso (D.pinning.rootDatum.root r) := by
  simp [transportedRootDatum, torusTransportRootDatum_root]

theorem restrictMap_comp_root (r : D.pinning.rootIndex) :
    D.restrictMap t ≫ D.pinning.rootDatum.root r = t_K ≫ D.transportedRootDatum.root r := by
  rw [D.transportedRootDatum_root]
  rfl

theorem transportedRootDatum_isRootDatum :
    IsRootDatumOf ((GroupScheme.baseChange bK).map D.inclusion) D.transportedRootDatum := by
  have hs : D.pinning.inclusion ≫ (Iso.refl _).hom =
      CommGroupScheme.groupHom D.torusIso.hom ≫
        (GroupScheme.baseChange bK).map D.inclusion := by
    simpa only [Iso.refl_hom, Category.comp_id] using D.inclusion_eq
  exact D.pinning.isRootDatum.torusTransport D.torusIso (Iso.refl _) hs

theorem transportedRootDatum_action_root (σ : K ≃ₐ[k] K) (a : D.pinning.base.support) :
    D.transportedRootDatum.root (D.action σ a : D.pinning.rootIndex) =
      characterLattice.galoisRepresentation k K D.torus σ
        (D.transportedRootDatum.root (a : D.pinning.rootIndex)) := by
  rw [D.transportedRootDatum_root, D.transportedRootDatum_root]
  exact D.action_root σ a

/-- Restriction to the split torus is invariant under the Galois action on simple roots. -/
theorem restrictMap_comp_root_action (hS : IsSplitTorus S.toGrp) (σ : K ≃ₐ[k] K)
    (a : D.pinning.base.support) :
    D.restrictMap t ≫ D.pinning.rootDatum.root (D.action σ a : D.pinning.rootIndex) =
      D.restrictMap t ≫ D.pinning.rootDatum.root (a : D.pinning.rootIndex) := by
  rw [D.restrictMap_comp_root, D.restrictMap_comp_root, D.transportedRootDatum_action_root]
  obtain ⟨c, hc⟩ := (characterLattice.baseChangeEquiv bK S hS).surjective
    (t_K ≫ D.transportedRootDatum.root (a : D.pinning.rootIndex))
  rw [characterLattice.baseChangeEquiv_apply] at hc
  rw [← characterLattice.galoisRepresentation_precompose, ← hc,
    characterLattice.galoisRepresentation_baseChange]

section Fibre

local notation "j_K" => CategoryTheory.Functor.map (GroupScheme.baseChange bK) D.inclusion
local notation "T_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange bK) D.torus

theorem transportedRoot_mem_roots (r : D.pinning.rootIndex) :
    D.transportedRootDatum.root r ∈ roots (T := T_K) j_K := by
  rw [← D.transportedRootDatum_isRootDatum.2.1]
  exact Set.mem_range_self r

variable [LocallyOfFiniteType G.X.hom] [IsAffineHom D.torus.toGrp.X.hom]
  [LocallyOfFiniteType D.torus.toGrp.X.hom]

attribute [local instance] rootsGaloisAction

/-- Every root of the pinning restricts to a relative root of the maximal split torus. -/
theorem exists_relativeRoot_restrict (hS : IsSplitTorus S.toGrp)
    (hT : IsSplitTorus (T_K).toGrp)
    (hcent : (torusCentralizer (CommGroupScheme.groupHom t ≫ D.inclusion)).IsRepresentedBy
      D.inclusion)
    (r : D.pinning.rootIndex) :
    ∃ a : characterLattice S, a ∈ relativeRoots (CommGroupScheme.groupHom t ≫ D.inclusion) ∧
      D.restrictMap t ≫ D.pinning.rootDatum.root r = characterLattice.baseChange bK S a := by
  obtain ⟨a, ha⟩ := (characterLattice.baseChangeEquiv bK S hS).surjective
    (t_K ≫ D.transportedRootDatum.root r)
  rw [characterLattice.baseChangeEquiv_apply] at ha
  refine ⟨a, ?_, by rw [D.restrictMap_comp_root, ha]⟩
  have hSK : IsSplitTorus (S_K).toGrp := hS.baseChange bK
  have : LocallyOfFiniteType ((GroupScheme.baseChange bK).obj G).X.hom := by
    change LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd G.X.hom bK)
    infer_instance
  have hne := root_restrict_ne_zero_of_torusCentralizer k K t D.inclusion hS hT hcent
    ⟨_, D.transportedRoot_mem_roots r⟩
  have hK : characterLattice.baseChange bK S a ∈
      roots (T := S_K) ((GroupScheme.baseChange bK).map (CommGroupScheme.groupHom t ≫
        D.inclusion)) := by
    rw [Functor.map_comp]
    refine (mem_roots_comp_iff (T := T_K) (T' := S_K) hT hSK t_K j_K _).mpr
      ⟨by rw [ha]; exact hne, _, D.transportedRoot_mem_roots r, ha.symm⟩
  exact (mem_roots_baseChange_iff (K := K) G S hS _ a).mp hK

variable [FiniteDimensional k K] [IsGalois k K]

/-- **Restriction fibres are Galois orbits.** Two roots of the pinning with the same
restriction to the split torus are Galois conjugate as characters of the descended torus. -/
theorem exists_galois_of_restrict_eq (hS : IsSplitTorus S.toGrp)
    (hT : IsSplitTorus (T_K).toGrp)
    (hf : IsMaximalSplitTorus (CommGroupScheme.groupHom t ≫ D.inclusion))
    (hjc : IsClosedSubgroup D.inclusion)
    (hcent : (torusCentralizer (CommGroupScheme.groupHom t ≫ D.inclusion)).IsRepresentedBy
      D.inclusion)
    {r r₀ : D.pinning.rootIndex}
    (h : D.restrictMap t ≫ D.pinning.rootDatum.root r =
      D.restrictMap t ≫ D.pinning.rootDatum.root r₀) :
    ∃ σ : K ≃ₐ[k] K, D.transportedRootDatum.root r =
      characterLattice.galoisRepresentation k K D.torus σ (D.transportedRootDatum.root r₀) := by
  obtain ⟨a, -, ha⟩ := D.exists_relativeRoot_restrict t hS hT hcent r₀
  have hβ : (⟨_, D.transportedRoot_mem_roots r₀⟩ : roots (T := T_K) j_K) ∈
      rootRestrictionFiber k K D.inclusion t a := by
    change t_K ≫ D.transportedRootDatum.root r₀ = _
    rw [← D.restrictMap_comp_root, ha]
  have hβ' : (⟨_, D.transportedRoot_mem_roots r⟩ : roots (T := T_K) j_K) ∈
      rootRestrictionFiber k K D.inclusion t a := by
    change t_K ≫ D.transportedRootDatum.root r = _
    rw [← D.restrictMap_comp_root, h, ha]
  have horb := rootOrbit_eq_restrictionFiber_of_torusCentralizer k K t D.inclusion hf hjc hcent
    hT D.transportedRootDatum_isRootDatum a hβ
  rw [← horb] at hβ'
  obtain ⟨σ, hσ⟩ := MulAction.mem_orbit_iff.mp hβ'
  exact ⟨σ, (congrArg Subtype.val hσ).symm⟩

/-- A root with the restriction of a simple root is a Galois conjugate of it. -/
theorem exists_action_eq_of_restrict_eq (hS : IsSplitTorus S.toGrp)
    (hT : IsSplitTorus (T_K).toGrp)
    (hf : IsMaximalSplitTorus (CommGroupScheme.groupHom t ≫ D.inclusion))
    (hjc : IsClosedSubgroup D.inclusion)
    (hcent : (torusCentralizer (CommGroupScheme.groupHom t ≫ D.inclusion)).IsRepresentedBy
      D.inclusion)
    {r : D.pinning.rootIndex} {a₀ : D.pinning.base.support}
    (h : D.restrictMap t ≫ D.pinning.rootDatum.root r =
      D.restrictMap t ≫ D.pinning.rootDatum.root (a₀ : D.pinning.rootIndex)) :
    ∃ σ : K ≃ₐ[k] K, r = (D.action σ a₀ : D.pinning.rootIndex) := by
  obtain ⟨σ, hσ⟩ := D.exists_galois_of_restrict_eq t hS hT hf hjc hcent h
  refine ⟨σ, D.transportedRootDatum.root.injective ?_⟩
  rw [hσ, D.transportedRootDatum_action_root]

omit [FiniteDimensional k K] [IsGalois k K] in
/-- **Restrictions lie on multipliable lines.** If the maximal split torus has opposite factor
pairs, every root of the pinning restricting to an integer multiple `n • a_K` of a character
`a` of `S` has `n ∈ {±1, ±2}`. -/
theorem restrictsToMultipliableLine [Smooth G.X.hom]
    [Mono (CommGroupScheme.groupHom t ≫ D.inclusion).hom.hom.left] (hS : IsSplitTorus S.toGrp)
    (hT : IsSplitTorus (T_K).toGrp)
    (hcent : (torusCentralizer (CommGroupScheme.groupHom t ≫ D.inclusion)).IsRepresentedBy
      D.inclusion)
    (hE : RelativeRoot.HasOppositeFactorPairs (CommGroupScheme.groupHom t ≫ D.inclusion))
    (a : characterLattice S) :
    Langlands.Geometry.Building.RestrictsToMultipliableLine (D.restrictMap t)
      D.pinning.rootDatum (characterLattice.baseChange bK S a) := by
  intro l n hl
  have hSK : IsSplitTorus (S_K).toGrp := hS.baseChange bK
  have : LocallyOfFiniteType ((GroupScheme.baseChange bK).obj G).X.hom := by
    change LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd G.X.hom bK)
    infer_instance
  have hne := root_restrict_ne_zero_of_torusCentralizer k K t D.inclusion hS hT hcent
    ⟨_, D.transportedRoot_mem_roots l⟩
  rw [D.restrictMap_comp_root] at hl
  have hK : n • characterLattice.baseChange bK S a ∈
      roots (T := S_K) ((GroupScheme.baseChange bK).map (CommGroupScheme.groupHom t ≫
        D.inclusion)) := by
    rw [Functor.map_comp]
    refine (mem_roots_comp_iff (T := T_K) (T' := S_K) hT hSK t_K j_K _).mpr
      ⟨by rw [← hl]; exact hne, _, D.transportedRoot_mem_roots l, hl⟩
  rw [← map_zsmul] at hK
  have hroot := (mem_roots_baseChange_iff (K := K) G S hS _ (n • a)).mp hK
  rcases le_or_gt 0 n with hn | hn
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [natCast_zsmul] at hroot
    have := hE.eq_one_or_two_of_nsmul_mem _ hS hroot
    omega
  · obtain ⟨m, rfl⟩ := Int.exists_eq_neg_ofNat hn.le
    rw [neg_smul, natCast_zsmul, ← smul_neg] at hroot
    have := hE.eq_one_or_two_of_nsmul_mem _ hS hroot
    omega

end Fibre

end GaloisCompatiblePinningData

end Langlands.GroupScheme
