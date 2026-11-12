import Langlands.BruhatTits.SpecialCompact.Properties
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Langlands.GroupScheme.Rational.StandardRepresentability
import Langlands.GroupScheme.Dynamic.SchemeDecomposition
import Langlands.AlgebraicGeometry.PointTopology.RepresentedSubgroup

/-! # Compact parabolic factorization from maximal compact Levi intersections -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.BruhatTits.SpecialCompact

section Groups

variable {G P M : Type*} [Group G] [Group P] [Group M]
  [TopologicalSpace G] [TopologicalSpace P] [TopologicalSpace M]

/-- A continuous retraction maps a compact preimage onto the maximal compact
preimage in its section. -/
theorem compact_preimage_map_retraction
    (p : P →* G) (m : M →* G) (r : P →* M) (s : M →* P)
    (hp : IsClosedEmbedding p) (hr : Continuous r)
    (hs : ∀ z, r (s z) = z) (hsm : ∀ z, p (s z) = m z)
    (K : Subgroup G) (hK : IsCompact (K : Set G))
    (hM : Maximal (fun L : Subgroup M => IsCompact (L : Set M)) (K.comap m)) :
    (K.comap p).map r = K.comap m := by
  have hcompact : IsCompact (((K.comap p).map r : Subgroup M) : Set M) :=
    (hp.isCompact_preimage hK).image hr
  have hle : K.comap m ≤ (K.comap p).map r := by
    intro z hz
    refine Subgroup.mem_map.mpr ⟨s z, ?_, hs z⟩
    change p (s z) ∈ K
    rw [hsm]
    exact hz
  exact le_antisymm (hM.2 hcompact hle) hle

end Groups

section Schemes

variable {F : Type u} [Field F] [TopologicalSpace F] [T2Space F]
  {G P M : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffineHom P.X.hom] [IsAffineHom M.X.hom]
  {χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G}
  {iP : P ⟶ G} {iM : M ⟶ G}

local instance parabolicCompactFactorizationInstance1 : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance parabolicCompactFactorizationInstance2 : IsAffine P.X.left := isAffine_of_isAffineHom P.X.hom
local instance parabolicCompactFactorizationInstance3 : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
local instance parabolicCompactFactorizationInstance4 : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
local instance parabolicCompactFactorizationInstance5 : TopologicalSpace (rationalPoints P) := rationalPointTopology F P.X
local instance parabolicCompactFactorizationInstance6 : TopologicalSpace (rationalPoints M) := rationalPointTopology F M.X

/-- Maximality of the literal Levi preimage forces the algebraic limit map to
preserve a compact subgroup. -/
theorem dynamic_limit_mem_of_maximal_compact_preimage
    (hP : (Dynamic.parabolic χ).IsRepresentedBy iP)
    (hM : (Dynamic.centralizer χ).IsRepresentedBy iM)
    (hcP : IsClosedSubgroup iP)
    (K : Subgroup (rationalPoints G))
    (hK : IsCompact (K : Set (rationalPoints G)))
    (hmax : Maximal (fun L : Subgroup (rationalPoints M) =>
      IsCompact (L : Set (rationalPoints M))) (K.comap (rationalPoints.map iM)))
    (p : rationalPoints P) (hp : rationalPoints.map iP p ∈ K) :
    rationalPoints.map iM (rationalPoints.map (Dynamic.limitGroupHom hP hM) p) ∈ K := by
  have : IsClosedImmersion iP.hom.hom.left := hcP
  have hsec : ∀ z : rationalPoints M,
      rationalPoints.map (Dynamic.limitGroupHom hP hM)
        (rationalPoints.map (Dynamic.centralizerToParabolic hP hM) z) = z := by
    intro z
    change (z ≫ (Dynamic.centralizerToParabolic hP hM).hom.hom) ≫
      (Dynamic.limitGroupHom hP hM).hom.hom = z
    rw [Category.assoc]
    change z ≫ (Dynamic.centralizerToParabolic hP hM ≫
      Dynamic.limitGroupHom hP hM).hom.hom = z
    rw [Dynamic.centralizerToParabolic_comp_limitGroupHom]
    simp
  have hinc : ∀ z : rationalPoints M,
      rationalPoints.map iP
        (rationalPoints.map (Dynamic.centralizerToParabolic hP hM) z) =
        rationalPoints.map iM z := by
    intro z
    change (z ≫ (Dynamic.centralizerToParabolic hP hM).hom.hom) ≫ iP.hom.hom =
      z ≫ iM.hom.hom
    rw [Category.assoc]
    change z ≫ (Dynamic.centralizerToParabolic hP hM ≫ iP).hom.hom = _
    rw [Dynamic.centralizerToParabolic_comp]
  have heq := compact_preimage_map_retraction (rationalPoints.map iP)
    (rationalPoints.map iM) (rationalPoints.map (Dynamic.limitGroupHom hP hM))
    (rationalPoints.map (Dynamic.centralizerToParabolic hP hM))
    (isClosedEmbedding_rationalPointMap F iP.hom.hom)
    (continuous_rationalPointMap F (Dynamic.limitGroupHom hP hM).hom.hom)
    hsec hinc K hK hmax
  have hmem : rationalPoints.map (Dynamic.limitGroupHom hP hM) p ∈
      (K.comap (rationalPoints.map iP)).map
        (rationalPoints.map (Dynamic.limitGroupHom hP hM)) :=
    Subgroup.mem_map.mpr ⟨p, hp, rfl⟩
  rwa [heq] at hmem

/-- The algebraic limit homomorphism restricted to the literal compact
preimages in the represented parabolic and Levi. -/
def dynamicCompactLeviRetraction
    (hP : (Dynamic.parabolic χ).IsRepresentedBy iP)
    (hM : (Dynamic.centralizer χ).IsRepresentedBy iM)
    (hcP : IsClosedSubgroup iP)
    (K : Subgroup (rationalPoints G))
    (hK : IsCompact (K : Set (rationalPoints G)))
    (hmax : Maximal (fun L : Subgroup (rationalPoints M) =>
      IsCompact (L : Set (rationalPoints M))) (K.comap (rationalPoints.map iM))) :
    K.comap (rationalPoints.map iP) →* K.comap (rationalPoints.map iM) where
  toFun p := ⟨rationalPoints.map (Dynamic.limitGroupHom hP hM) (p : rationalPoints P),
    dynamic_limit_mem_of_maximal_compact_preimage hP hM hcP K hK hmax p p.property⟩
  map_one' := Subtype.ext (rationalPoints.map (Dynamic.limitGroupHom hP hM)).map_one
  map_mul' p q := Subtype.ext
    ((rationalPoints.map (Dynamic.limitGroupHom hP hM)).map_mul
      (p : rationalPoints P) (q : rationalPoints P))

/-- A compact subgroup factors on a dynamic parabolic whenever its literal
Levi preimage is maximal compact. -/
theorem dynamic_compact_parabolic_factorization
    (hP : (Dynamic.parabolic χ).IsRepresentedBy iP)
    (hM : (Dynamic.centralizer χ).IsRepresentedBy iM)
    (hcP : IsClosedSubgroup iP)
    (K : Subgroup (rationalPoints G))
    (hK : IsCompact (K : Set (rationalPoints G)))
    (hmax : Maximal (fun L : Subgroup (rationalPoints M) =>
      IsCompact (L : Set (rationalPoints M))) (K.comap (rationalPoints.map iM))) :
    ((K ⊓ (Dynamic.parabolic χ).carrier (Over.mk (𝟙 _)) :
        Subgroup (rationalPoints G)) : Set (rationalPoints G)) =
      ((K ⊓ (Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)) :
        Subgroup (rationalPoints G)) : Set (rationalPoints G)) *
      ((K ⊓ (Dynamic.unipotent χ).carrier (Over.mk (𝟙 _)) :
        Subgroup (rationalPoints G)) : Set (rationalPoints G)) := by
  ext g
  constructor
  · rintro ⟨hgK, hgP⟩
    let p := (hP.pointsEquiv (Over.mk (𝟙 _))).symm ⟨g, hgP⟩
    have hp : rationalPoints.map iP p = g :=
      SubgroupFunctor.IsRepresentedBy.pointsEquiv_symm_comp hP _
    have hlim : rationalPoints.map iM
        (rationalPoints.map (Dynamic.limitGroupHom hP hM) p) =
        Dynamic.limit χ ⟨g, hgP⟩ := by
      change (p ≫ (Dynamic.limitGroupHom hP hM).hom.hom) ≫ iM.hom.hom = _
      rw [Dynamic.limitGroupHom_comp]
      congr 1
      exact Subtype.ext hp
    have hlimK : Dynamic.limit χ ⟨g, hgP⟩ ∈ K := by
      rw [← hlim]
      exact dynamic_limit_mem_of_maximal_compact_preimage hP hM hcP K hK hmax p
        (hp.symm ▸ hgK)
    have hz := Dynamic.limit_mem_centralizer χ ⟨g, hgP⟩
    have hu : (Dynamic.limit χ ⟨g, hgP⟩)⁻¹ * g ∈
        (Dynamic.unipotent χ).carrier (Over.mk (𝟙 _)) := by
      have h := (Dynamic.hasLimit_of_mem_centralizer χ hz).inv.mul χ
        (Dynamic.hasLimit_limit χ ⟨g, hgP⟩)
      rwa [inv_mul_cancel] at h
    exact Set.mem_mul.mpr ⟨_, ⟨hlimK, hz⟩, _,
      ⟨K.mul_mem (K.inv_mem hlimK) hgK, hu⟩, mul_inv_cancel_left _ _⟩
  · rintro ⟨m, ⟨hmK, hmM⟩, u, ⟨huK, huU⟩, rfl⟩
    exact ⟨K.mul_mem hmK huK,
      mul_mem (Dynamic.centralizer_le_parabolic χ _ hmM)
        (Dynamic.unipotent_le_parabolic χ _ huU)⟩

end Schemes

section Standard

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}

local instance parabolicCompactFactorizationInstance7 : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance parabolicCompactFactorizationInstance8 : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X

/-- Compactness of `K` and maximal compactness of all its literal standard-Levi
preimages imply every required standard-parabolic intersection factorization. -/
theorem hasParabolicFactorization_of_maximal_compact_levis
    (hG : IsConnectedReductive G) (i : S.toGrp ⟶ G) (hi : IsMaximalSplitTorus i)
    (ν : cocharacterLattice S) (hν : IsGenericCocharacter i ν)
    (K : Subgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
    (hmax : ∀ J ⊆ simpleRelativeRoots i ν,
      haveI : IsAffineHom (Standard.leviScheme i ν J).X.hom :=
        (Standard.isClosedSubgroup_leviHom i ν J).isAffineHom
      IsCompactOpenMaximal F (K.comap (rationalPoints.map (Standard.leviHom i ν J)))) :
    HasParabolicFactorization i ν K := by
  letI : T2Space F := Langlands.BruhatTits.localField_t2Space F
  intro J hJ
  letI : IsAffineHom (Standard.parabolicScheme i ν J).X.hom :=
    (Standard.isClosedSubgroup_parabolicHom i ν J).isAffineHom
  letI : IsAffineHom (Standard.leviScheme i ν J).X.hom :=
    (Standard.isClosedSubgroup_leviHom i ν J).isAffineHom
  obtain ⟨⟨ζ, hζ⟩, hcompare⟩ := standardCocharacter F G hG S i hi ν hν J hJ
  have hcomp := hcompare ζ hζ
  have hP : (Dynamic.parabolic (CommGroupScheme.groupHom ζ ≫ i)).IsRepresentedBy
      (Standard.parabolicHom i ν J) := by
    rw [← hcomp.1]
    exact Standard.isRepresentedBy_parabolicHom i ν J
  have hM : (Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i)).IsRepresentedBy
      (Standard.leviHom i ν J) := by
    rw [← hcomp.2.1]
    exact Standard.isRepresentedBy_leviHom i ν J
  have hfac := dynamic_compact_parabolic_factorization hP hM
    (Standard.isClosedSubgroup_parabolicHom i ν J) K hK (hmax J hJ).2.2
  simpa only [← hcomp.1, ← hcomp.2.1, ← hcomp.2.2] using hfac

end Standard

end Langlands.BruhatTits.SpecialCompact
