import Langlands.GroupScheme.Rational.SimpleRootFiberUnitary
import Langlands.Geometry.Building.AlgebraicSL2RootCoordinatesConstruction
import Langlands.Geometry.Building.SplitRelativeRootGroupProductProof

/-! # Construction of algebraic SU3 rank-one coordinates at multipliable roots -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.GroupScheme.SimpleRootFiber

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  [IsAffineHom T.toGrp.X.hom] [LocallyOfFiniteType T.toGrp.X.hom]
  (f : S ⟶ T) (j : T.toGrp ⟶ G)

local notation "bK" => algebraBaseMap k K
local notation "T_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange bK) T
local notation "G_K" => CategoryTheory.Functor.obj (GroupScheme.baseChange bK) G
local notation "f_K" => CategoryTheory.Functor.map (CommGroupScheme.baseChange bK) f

local instance algebraicSU3ConstructionIsAffineHom : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom bK)
  infer_instance

attribute [local instance] rootsGaloisAction

variable {J : Type u} [Finite J]
  {P : RootDatum J
    (characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))
    (cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))}
  (hP : IsRootDatumOf (T := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
    ((GroupScheme.baseChange (algebraBaseMap k K)).map j) P)
  (hf : IsMaximalSplitTorus (CommGroupScheme.groupHom f ≫ j))
  (hcent : (torusCentralizer (CommGroupScheme.groupHom f ≫ j)).IsRepresentedBy j)
  (hT : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T).toGrp)
  [P.IsReduced]
  (ν : cocharacterLattice S)
  (hν : IsGenericCocharacter (CommGroupScheme.groupHom f ≫ j) ν)
  [FiniteDimensional k K]
  (hGK : IsConnectedReductive ((GroupScheme.baseChange (algebraBaseMap k K)).obj G))
  (hi : IsMaximalTorus (T := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
    ((GroupScheme.baseChange (algebraBaseMap k K)).map j))
  [IsGalois k K] (hjc : IsClosedSubgroup j) [Smooth G.X.hom]
  {a : characterLattice S} (ha : a ∈ simpleRelativeRoots (CommGroupScheme.groupHom f ≫ j) ν)
  (h2a : 2 • a ∈ relativeRoots (CommGroupScheme.groupHom f ≫ j))
  [Mono (CommGroupScheme.groupHom f ≫ j).hom.hom.left]
  (hR : HasRelativeRootSystem (CommGroupScheme.groupHom f ≫ j))
  [Fintype (fiberSet k K f j hP hf hcent hT ν hν hGK hi a)]
  (hProd : Langlands.Geometry.Building.SplitRelativeRootGroupProductStatement.{u})
  (hAdj : AdjacentSimpleRootSpecialLinearStatement.{u})

local notation "Dₚ" => fiberPinning k K f j hP hf hcent hT ν hν hGK hi
local notation "Oₐ" => fiberSet k K f j hP hf hcent hT ν hν hGK hi a
local notation "L₀" => fiberField k K f j hP hf hcent hT ν hν hGK hi ha
local notation "E₀" => pairField k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a
local notation "Dπ" => fiberPartnerData k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a
local notation "τₐ" => fiberEmbedding k K f j hP hf hcent hT ν hν hGK hi hjc ha
local notation "β₀" => baseRoot k K f j hP hf hcent hT ν hν hGK hi ha
local notation "p₀" => basePoint k K f j hP hf hcent hT ν hν hGK hi ha
local notation "π" => partner k K f j hP hf hcent hT ν hν hGK hi

/-- The descended special unitary homomorphism of the fiber. -/
def fiberUnitaryRho :
    SU3Root.specialUnitarySubgroup (SU3Root.fieldInvolution E₀ L₀) →* rationalPoints G :=
  SplitPinning.unitaryRho k K j hAdj (Dₚ).pinning (Dₚ).torusIso (Dₚ).inclusion_eq (Dₚ).rootMaps
      (Dₚ).rootMaps_compatible (Dₚ).action_root
      (fiberPinning_pairing_action k K f j hP hf hcent hT ν hν hGK hi) (Dπ)
      (fiberSet_galois k K f j hP hf hcent hT ν hν hGK hi a)
      (fun σ _ ht => partner_action k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a σ ht) τₐ
      (fun σ t ht => fiberEmbedding_galois k K f j hP hf hcent hT ν hν hGK hi hjc ha σ t ht)
      (SU3Root.fieldInvolution E₀ L₀)
      (fun _ ht y => fiberEmbedding_partner k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a ht y)

/-- Unitary coordinates on the root group of `a`: the upper parameters of the descended
`SU₃(L₀/E₀)`, with the root-orbit character of the base root. -/
def fiberPositiveUnitary :
    Langlands.Geometry.Building.RootUnitaryCoordinatesOn (CommGroupScheme.groupHom f ≫ j) j
      (CommGroupScheme.groupHom f) a E₀ L₀ where
  equiv := SplitPinning.upperUnitaryEquiv k K j hAdj (Dₚ).pinning (Dₚ).torusIso (Dₚ).inclusion_eq (Dₚ).rootMaps
      (Dₚ).rootMaps_compatible (Dₚ).action_root
      (fiberPinning_pairing_action k K f j hP hf hcent hT ν hν hGK hi) (Dπ)
      (fiberSet_galois k K f j hP hf hcent hT ν hν hGK hi a)
      (fun σ _ ht => partner_action k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a σ ht) τₐ
      (fun σ t ht => fiberEmbedding_galois k K f j hP hf hcent hT ν hν hGK hi hjc ha σ t ht)
      (SU3Root.fieldInvolution E₀ L₀)
      (fun _ ht y => fiberEmbedding_partner k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a ht y)
    (CommGroupScheme.groupHom f ≫ j) a hf.1.1 ha.1.1.1
    (fiber_hmem_upper k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a hR hProd hAdj) (fiber_hprod_upper k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a hR hProd hAdj)
    (fiber_huniq_upper k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a hR hProd hAdj)
    (fun c hc => exists_eq_fiberEmbedding k K f j hP hf hcent hT ν hν hGK hi hjc ha c hc)
    (basePoint_mem k K f j hP hf hcent hT ν hν hGK hi ha)
  double g := SplitPinning.mem_double_iff_upper k K j hAdj (Dₚ).pinning (Dₚ).torusIso (Dₚ).inclusion_eq (Dₚ).rootMaps
      (Dₚ).rootMaps_compatible (Dₚ).action_root
      (fiberPinning_pairing_action k K f j hP hf hcent hT ν hν hGK hi) (Dπ)
      (fiberSet_galois k K f j hP hf hcent hT ν hν hGK hi a)
      (fun σ _ ht => partner_action k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a σ ht) τₐ
      (fun σ t ht => fiberEmbedding_galois k K f j hP hf hcent hT ν hν hGK hi hjc ha σ t ht)
      (SU3Root.fieldInvolution E₀ L₀)
      (fun _ ht y => fiberEmbedding_partner k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a ht y)
    (CommGroupScheme.groupHom f ≫ j) a hf.1.1 (fiber_huniq_upper k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a hR hProd hAdj)
    (fun c hc => exists_eq_fiberEmbedding k K f j hP hf hcent hT ν hν hGK hi hjc ha c hc)
    (basePoint_mem k K f j hP hf hcent hT ν hν hGK hi ha) h2a.1
    (fiber_hmem2_upper k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a hR hProd hAdj) (fiber_hprod2_upper k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a hR hProd hAdj) g
  character := rootOrbitCharacter k K j β₀
  restriction := by
    have : IsAffine T.toGrp.X.left := isAffine_of_isAffineHom T.toGrp.X.hom
    have : IsAffineHom S.toGrp.X.hom := hf.1.1.isAffineHom
    have : IsAffine S.toGrp.X.left := isAffine_of_isAffineHom S.toGrp.X.hom
    exact characterRestrict_rootOrbitCharacter k K j f a
      (rootOf_mem_restrictionFiber k K f j hP hf hcent hT ν hν hGK hi _
        (basePoint_mem k K f j hP hf hcent hT ν hν hGK hi ha))
  conjugation z q := by
    rw [SplitPinning.upperUnitaryEquiv_apply, SplitPinning.upperUnitaryEquiv_apply]
    refine SplitPinning.conj_unitaryRho_upper k K j hAdj (Dₚ).pinning (Dₚ).torusIso (Dₚ).inclusion_eq (Dₚ).rootMaps
      (Dₚ).rootMaps_compatible (Dₚ).action_root
      (fiberPinning_pairing_action k K f j hP hf hcent hT ν hν hGK hi) (Dπ)
      (fiberSet_galois k K f j hP hf hcent hT ν hν hGK hi a)
      (fun σ _ ht => partner_action k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a σ ht) τₐ
      (fun σ t ht => fiberEmbedding_galois k K f j hP hf hcent hT ν hν hGK hi hjc ha σ t ht)
      (SU3Root.fieldInvolution E₀ L₀)
      (fun _ ht y => fiberEmbedding_partner k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a ht y)
      (fun z => ((rationalCharacterEval (rootOrbitCharacter k K j β₀)
        (GaloisPointComparison.rationalExtend k L₀ T.toGrp z) : L₀ˣ) : L₀)) ?_ z q
    intro z b hb
    refine (fiberEmbedding_rootOrbitCharacter k K f j hP hf hcent hT ν hν hGK hi hjc ha b hb
      z).trans ?_
    exact congrArg (fun y => ((rationalCharacterEval
      ((rationalCharacters.equivCharacterLattice (T_K)).symm (P.root b.1)) y : Kˣ) : K))
      (fiber_torusIso_inv k K f j hP hf hcent hT ν hν hGK hi _).symm

/-- Unitary coordinates on the root group of `-a`: the lower parameters of the descended
`SU₃(L₀/E₀)`, with the inverse of the descended root of the partner of the base point. -/
def fiberNegativeUnitary :
    Langlands.Geometry.Building.RootUnitaryCoordinatesOn (CommGroupScheme.groupHom f ≫ j) j
      (CommGroupScheme.groupHom f) (-a) E₀ L₀ where
  equiv := SplitPinning.lowerUnitaryEquiv k K j hAdj (Dₚ).pinning (Dₚ).torusIso (Dₚ).inclusion_eq (Dₚ).rootMaps
      (Dₚ).rootMaps_compatible (Dₚ).action_root
      (fiberPinning_pairing_action k K f j hP hf hcent hT ν hν hGK hi) (Dπ)
      (fiberSet_galois k K f j hP hf hcent hT ν hν hGK hi a)
      (fun σ _ ht => partner_action k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a σ ht) τₐ
      (fun σ t ht => fiberEmbedding_galois k K f j hP hf hcent hT ν hν hGK hi hjc ha σ t ht)
      (SU3Root.fieldInvolution E₀ L₀)
      (fun _ ht y => fiberEmbedding_partner k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a ht y)
    (CommGroupScheme.groupHom f ≫ j) a hf.1.1 ha.1.1.1
    (fiber_hmem_lower k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a hR hProd hAdj) (fiber_hprod_lower k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a hR hProd hAdj)
    (fiber_huniq_lower k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a hR hProd hAdj)
    (fun c hc => exists_eq_fiberEmbedding k K f j hP hf hcent hT ν hν hGK hi hjc ha c hc)
    (basePoint_mem k K f j hP hf hcent hT ν hν hGK hi ha)
  double g := SplitPinning.mem_double_iff_lower k K j hAdj (Dₚ).pinning (Dₚ).torusIso (Dₚ).inclusion_eq (Dₚ).rootMaps
      (Dₚ).rootMaps_compatible (Dₚ).action_root
      (fiberPinning_pairing_action k K f j hP hf hcent hT ν hν hGK hi) (Dπ)
      (fiberSet_galois k K f j hP hf hcent hT ν hν hGK hi a)
      (fun σ _ ht => partner_action k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a σ ht) τₐ
      (fun σ t ht => fiberEmbedding_galois k K f j hP hf hcent hT ν hν hGK hi hjc ha σ t ht)
      (SU3Root.fieldInvolution E₀ L₀)
      (fun _ ht y => fiberEmbedding_partner k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a ht y)
    (CommGroupScheme.groupHom f ≫ j) a hf.1.1 (fiber_huniq_lower k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a hR hProd hAdj)
    (fun c hc => exists_eq_fiberEmbedding k K f j hP hf hcent hT ν hν hGK hi hjc ha c hc)
    (basePoint_mem k K f j hP hf hcent hT ν hν hGK hi ha)
    (by rw [smul_neg, neg_ne_zero]; exact h2a.1)
    (fiber_hmem2_lower k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a hR hProd hAdj) (fiber_hprod2_lower k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a hR hProd hAdj) g
  character := -partnerCharacter k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a
  restriction := by
    have : IsAffine T.toGrp.X.left := isAffine_of_isAffineHom T.toGrp.X.hom
    have : IsAffineHom S.toGrp.X.hom := hf.1.1.isAffineHom
    have : IsAffine S.toGrp.X.left := isAffine_of_isAffineHom S.toGrp.X.hom
    have hpos : characterRestrict ((GroupScheme.baseChange
        (GaloisPointComparison.baseMap k L₀)).map (CommGroupScheme.groupHom f))
        (partnerCharacter k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a) =
        rationalCharacters.baseChange (GaloisPointComparison.baseMap k L₀)
          ((rationalCharacters.equivCharacterLattice S).symm a) := by
      apply AffineCharacterTowerDescent.characterRestrict_fixedDescend
      exact congrArg (fun φ => Additive.ofMul (CommGroupScheme.groupHom φ))
        (rootOf_mem_restrictionFiber k K f j hP hf hcent hT ν hν hGK hi _
          (partner_mem k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a (basePoint_mem k K f j hP hf hcent hT ν hν hGK hi ha)))
    rw [map_neg, hpos, AddEquiv.map_neg, map_neg]
  conjugation z q := by
    rw [SplitPinning.lowerUnitaryEquiv_apply, SplitPinning.lowerUnitaryEquiv_apply]
    refine SplitPinning.conj_unitaryRho_lower k K j hAdj (Dₚ).pinning (Dₚ).torusIso (Dₚ).inclusion_eq (Dₚ).rootMaps
      (Dₚ).rootMaps_compatible (Dₚ).action_root
      (fiberPinning_pairing_action k K f j hP hf hcent hT ν hν hGK hi) (Dπ)
      (fiberSet_galois k K f j hP hf hcent hT ν hν hGK hi a)
      (fun σ _ ht => partner_action k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a σ ht) τₐ
      (fun σ t ht => fiberEmbedding_galois k K f j hP hf hcent hT ν hν hGK hi hjc ha σ t ht)
      (SU3Root.fieldInvolution E₀ L₀)
      (fun _ ht y => fiberEmbedding_partner k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a ht y)
      (fun z => ((rationalCharacterEval (-partnerCharacter k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a)
        (GaloisPointComparison.rationalExtend k L₀ T.toGrp z) : L₀ˣ) : L₀)) ?_ z q
    intro z b hb
    refine (fiberEmbedding_neg_partnerCharacter k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a hb z).trans ?_
    exact congrArg (fun y => (((rationalCharacterEval
      ((rationalCharacters.equivCharacterLattice (T_K)).symm (P.root (π b).1)) y)⁻¹ : Kˣ) : K))
      (fiber_torusIso_inv k K f j hP hf hcent hT ν hν hGK hi _).symm

/-- Algebraic `SU₃` coordinates at a simple relative root `a` with `2 • a` a relative root,
built over the fiber field and the pair field from the fiber pinning. -/
def fiberSU3Coordinates :
    Langlands.Geometry.Building.AlgebraicSU3RootCoordinates (CommGroupScheme.groupHom f ≫ j) j
      (CommGroupScheme.groupHom f) a where
  base := E₀
  extension := L₀
  positive := fiberPositiveUnitary k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a hR hProd hAdj
  negative := fiberNegativeUnitary k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a hR hProd hAdj
  rho := SplitPinning.unitaryRho k K j hAdj (Dₚ).pinning (Dₚ).torusIso (Dₚ).inclusion_eq (Dₚ).rootMaps
      (Dₚ).rootMaps_compatible (Dₚ).action_root
      (fiberPinning_pairing_action k K f j hP hf hcent hT ν hν hGK hi) (Dπ)
      (fiberSet_galois k K f j hP hf hcent hT ν hν hGK hi a)
      (fun σ _ ht => partner_action k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a σ ht) τₐ
      (fun σ t ht => fiberEmbedding_galois k K f j hP hf hcent hT ν hν hGK hi hjc ha σ t ht)
      (SU3Root.fieldInvolution E₀ L₀)
      (fun _ ht y => fiberEmbedding_partner k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a ht y)
  rho_upper _ := rfl
  rho_lower _ := rfl
  coroot := CommGroupScheme.groupHom (fiberCoroot k K f j hP hf hcent hT ν hν hGK hi hjc ha)
  coroot_points t := by
    have hid : ∀ z : rationalPoints (T_K).toGrp,
        rationalPoints.map (CommGroupScheme.groupHom (Dₚ).torusIso.inv) z = z := fun z => by
      rw [rationalPoints.map_apply]
      exact Category.comp_id z
    apply SplitPinning.rationalExtend_injective_of_isAffineHom k K
    rw [SplitPinning.rationalExtend_unitaryRho_diagonal k K j hAdj (Dₚ).pinning (Dₚ).torusIso (Dₚ).inclusion_eq (Dₚ).rootMaps
      (Dₚ).rootMaps_compatible (Dₚ).action_root
      (fiberPinning_pairing_action k K f j hP hf hcent hT ν hν hGK hi) (Dπ)
      (fiberSet_galois k K f j hP hf hcent hT ν hν hGK hi a)
      (fun σ _ ht => partner_action k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a σ ht) τₐ
      (fun σ t ht => fiberEmbedding_galois k K f j hP hf hcent hT ν hν hGK hi hjc ha σ t ht)
      (SU3Root.fieldInvolution E₀ L₀)
      (fun _ ht y => fiberEmbedding_partner k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a ht y),
      GaloisPointComparison.rationalExtend_map, GaloisPointComparison.rationalExtend_map,
      map_baseChange_map_fiber k K f j hP hf hcent hT ν hν hGK hi, hid]
    exact congrArg (rationalPoints.map (Dₚ).pinning.inclusion)
      (fiberCoroot_extendedUnitPoint k K f j hP hf hcent hT ν hν hGK hi hjc ha t)

include hjc in
/-- The antidiagonal Weyl element of the constructed coordinates normalizes the maximal split
torus. -/
theorem fiberSU3Coordinates_weyl :
    (fiberSU3Coordinates k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a hR hProd hAdj).rho ⟨SU3Root.weylElement,
      SU3Root.weylElement_mem_specialUnitarySubgroup (SU3Root.fieldInvolution
        (fiberSU3Coordinates k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a hR hProd hAdj).base
        (fiberSU3Coordinates k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a hR hProd hAdj).extension)⟩ ∈
      normalizerPoints (CommGroupScheme.groupHom f ≫ j) := by
  have : IsClosedImmersion j.hom.hom.left := hjc
  apply IsMaximalSplitTorus.mem_normalizerPoints_of_mem_normalizerPoints _ j hf
  exact SplitPinning.unitaryRho_weylElement_mem k K j hAdj (Dₚ).pinning (Dₚ).torusIso (Dₚ).inclusion_eq (Dₚ).rootMaps
      (Dₚ).rootMaps_compatible (Dₚ).action_root
      (fiberPinning_pairing_action k K f j hP hf hcent hT ν hν hGK hi) (Dπ)
      (fiberSet_galois k K f j hP hf hcent hT ν hν hGK hi a)
      (fun σ _ ht => partner_action k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a σ ht) τₐ
      (fun σ t ht => fiberEmbedding_galois k K f j hP hf hcent hT ν hν hGK hi hjc ha σ t ht)
      (SU3Root.fieldInvolution E₀ L₀)
      (fun _ ht y => fiberEmbedding_partner k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a ht y)

end Langlands.GroupScheme.SimpleRootFiber

namespace Langlands.Geometry.Building

/-- **The SU3 clause, given the split product statement and the adjacent-root statement.**
Under the hypotheses of `AlgebraicSU3RootCoordinatesExistenceStatement`, every indivisible
relative root `b` with `2 • b` a relative root has algebraic `SU₃` coordinates whose
antidiagonal Weyl element normalizes the maximal split torus. -/
theorem exists_algebraicSU3RootCoordinates_of_product_of_adjacent
    (hProd : SplitRelativeRootGroupProductStatement.{u})
    (hAdj : AdjacentSimpleRootSpecialLinearStatement.{u})
    (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) [IsAffineHom G.X.hom]
    (S Z : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : S.toGrp ⟶ G) (j : Z.toGrp ⟶ G) (s : S.toGrp ⟶ Z.toGrp)
    (hi : IsMaximalSplitTorus i) (hZ : IsTorus Z.toGrp)
    (hj : (torusCentralizer i).IsRepresentedBy j) (hs : s ≫ j = i)
    (b : characterLattice S) (hb : b ∈ RelativeRoot.indivisibleRoots i)
    (h2 : 2 • b ∈ relativeRoots i) :
    ∃ C : AlgebraicSU3RootCoordinates i j s b,
      C.rho ⟨SU3Root.weylElement,
        SU3Root.weylElement_mem_specialUnitarySubgroup
          (SU3Root.fieldInvolution C.base C.extension)⟩ ∈ normalizerPoints i := by
  subst hs
  let : Smooth G.X.hom := hG.smooth
  let : LocallyOfFiniteType G.X.hom := inferInstance
  have hjc : IsClosedSubgroup j := IsSplitTorus.isClosedSubgroup_torusCentralizer hi.1.1 _ hj
  let : IsAffineHom Z.toGrp.X.hom := hjc.isAffineHom
  let : LocallyOfFiniteType Z.toGrp.X.hom := hjc.locallyOfFiniteType
  let f : S ⟶ Z := Additive.ofMul s
  have hself : torusCentralizer j = SubgroupFunctor.range j :=
    le_antisymm ((torusCentralizer_le_of_factor j (s ≫ j) s rfl).trans hj.2.symm.le)
      (range_le_torusCentralizer j)
  obtain ⟨K, _, _, _, _, hK⟩ := torusFiniteGaloisSplitting k Z.toGrp hZ
  have : Algebra.IsAlgebraic k K := Algebra.IsAlgebraic.of_finite k K
  have hGK : IsConnectedReductive ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) :=
    hG.baseChange_of_algebraicExtension (K := K)
  have hiK : IsMaximalTorus (T := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj Z)
      ((GroupScheme.baseChange (algebraBaseMap k K)).map j) :=
    isMaximalTorus_baseChange_of_torusCentralizer_eq K hZ hjc hself
  obtain ⟨J, hJ, P, hP, hred⟩ := rootDatumExistence K
    ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) hGK
    ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj Z) hK
    ((GroupScheme.baseChange (algebraBaseMap k K)).map j) hiK
  let : Finite J := hJ
  let : P.IsReduced := hred
  let : Mono (s ≫ j).hom.hom.left := hi.isSplitSubtorus.mono
  let : Mono (CommGroupScheme.groupHom f ≫ j).hom.hom.left := hi.isSplitSubtorus.mono
  have hR : HasRelativeRootSystem (s ≫ j) := relativeRootSystem k G hG S (s ≫ j) hi
  obtain ⟨ν, hν, hbν⟩ :=
    RelativeRoot.exists_isGenericCocharacter_mem_simpleRelativeRoots (s ≫ j) hR hi.1.1 hb
  let : Fintype (SimpleRootFiber.fiberSet k K f j hP hi hj hK ν hν hGK hiK b) :=
    Fintype.ofFinite _
  exact ⟨SimpleRootFiber.fiberSU3Coordinates k K f j hP hi hj hK ν hν hGK hiK hjc hbν h2 hR
      hProd hAdj,
    SimpleRootFiber.fiberSU3Coordinates_weyl k K f j hP hi hj hK ν hν hGK hiK hjc hbν h2 hR
      hProd hAdj⟩

/-- **The SU3 clause from the adjacent-root statement.** -/
theorem algebraicSU3RootCoordinatesExistence_of_product_of_adjacent
    (hProd : SplitRelativeRootGroupProductStatement.{u})
    (hAdj : AdjacentSimpleRootSpecialLinearStatement.{u}) :
    AlgebraicSU3RootCoordinatesExistenceStatement.{u} := by
  intro k _ G hG S Z i j s hi hZ hj hs b hb h2
  have : IsAffineHom G.X.hom := hG.isAffineHom
  exact exists_algebraicSU3RootCoordinates_of_product_of_adjacent hProd hAdj k G hG S Z i j s hi
    hZ hj hs b hb h2

/-- **Reduction of the rank-one coordinate existence to the adjacent-root statement.** With the
published proof `splitRelativeRootGroupProduct` of the split product statement, both clauses
of `AlgebraicRankOneCoordinatesExistenceStatement` follow from
`AdjacentSimpleRootSpecialLinearStatement`. -/
theorem algebraicRankOneCoordinatesExistence_of_adjacent
    (hAdj : AdjacentSimpleRootSpecialLinearStatement.{u}) :
    AlgebraicRankOneCoordinatesExistenceStatement.{u} :=
  algebraicRankOneCoordinatesExistence_of_product_of_su3 splitRelativeRootGroupProduct
    (algebraicSU3RootCoordinatesExistence_of_product_of_adjacent splitRelativeRootGroupProduct
      hAdj)

end Langlands.Geometry.Building
