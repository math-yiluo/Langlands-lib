import Langlands.Global.AdelicRelativeParabolicQuotientMeasure

/-! # Fibres of the relative parabolic quotient coordinates -/

noncomputable section

open CategoryTheory AlgebraicGeometry Set Topology
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.AdelicGroupPoints.ParabolicIwasawaMeasure

open GroupScheme PositiveRealTorus
open LeftCosetSpace (mk rightTranslate)

variable {F : Type} [Field F] [NumberField F]
  {G P M U : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]
  [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
  (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
  [IsIso (subgroupMultiplication l iU)] (hU : LeviSubgroup.IsGeometricUnipotentRadical iU)
  {K : Subgroup (AdelicGroupPoints F G)}

local notation "KP" => K.comap (ContinuousMonoidHom.toMonoidHom (map F P G p))
local notation "KM" => K.comap (ContinuousMonoidHom.toMonoidHom (map F M G (l ≫ p)))
set_option quotPrecheck false in
local notation "ret" => leviRetraction l iU hU.1.isNormal
local notation "pr" => map F P M ret

omit [IsAffine M.X.left] [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType P.X.hom]
  [LocallyOfFiniteType M.X.hom] in
/-- The Levi retraction of the compact subgroup in the parabolic equals the subgroup induced
on the Levi when the latter is maximal compact. -/
theorem map_parabolicCompact_retraction (hKc : IsCompact (K : Set (AdelicGroupPoints F G)))
    (hKM : IsMaximalCompactSubgroup F M KM) :
    (KP).map (pr).toMonoidHom = KM := by
  have hP : IsCompact (KP : Set (AdelicGroupPoints F P)) :=
    (isClosedEmbedding_map F P G p).isCompact_preimage hKc
  refine hKM.2 _ (hP.image (pr).continuous) ?_
  intro m hm
  refine ⟨map F M P l m, ?_, ?_⟩
  · change map F P G p (map F M P l m) ∈ K
    rw [← map_comp_apply_of_hom]
    exact hm
  · change pr (map F M P l m) = m
    rw [← map_comp_apply_of_hom, levi_comp_leviRetraction]
    rfl

variable {A : CommGroupScheme (Spec (CommRingCat.of F))} [IsAffineHom M.X.hom] [IsAffine U.X.left]
  [IsClosedImmersion (iU ≫ p).hom.hom.left]
  (a : A.toGrp ⟶ M) (hM : IsConnectedReductive M) (ha : IsSplitComponent a)
  (hKc : IsCompact (K : Set (AdelicGroupPoints F G)))

local notation "G₁" => normOneSubgroup F G
local notation "M₁" => normOneSubgroup F M
local notation "L" => ambientNormOneLevi (l ≫ p)
local notation "B" => relativePositiveSubgroup (l ≫ p) a
local notation "N" => AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iU ≫ p))
local notation "ΓP" => parabolicRationalNormOneSubgroup p
local notation "ΓM" => rationalNormOneSubgroup F M
local notation "EL" => relativeLeviDecomposition (l ≫ p) a hM ha
local notation "X" => (N × (B × M₁)) × K
local notation "coord" => normOneRelativeParabolicQuotientCoordinates p iU l hU a hM ha hKc

private theorem eq_splitParts_of_eq {S T H : Type*} [Group S] [Group T] [Group H]
    (e : S × T ≃* H) (b b' : S) (m m' k d : T)
    (h : e (b', m') * e (1, k) = e (1, d) * e (b, m)) :
    b' = b ∧ m' * k = d * m := by
  rw [← map_mul, ← map_mul] at h
  have hPair := e.injective h
  exact ⟨by simpa only [Prod.fst_mul, mul_one, one_mul] using congrArg Prod.fst hPair,
    congrArg Prod.snd hPair⟩

set_option maxHeartbeats 1000000 in
/-- Equal coordinate images have the same relative split coordinate, and their intrinsic
Levi classes differ by right multiplication by an element of the induced compact subgroup. -/
theorem relativeParabolicCoordinates_fibre (hKM : IsMaximalCompactSubgroup F M KM)
    {x y : X} (hxy : coord x = coord y) :
    ∃ k : M₁, k.val ∈ KM ∧ y.1.2.1 = x.1.2.1 ∧
      rightTranslate ΓM k (mk ΓM y.1.2.2) = mk ΓM x.1.2.2 := by
  let E := normOneParabolicCoordinates p iU l hU
  let u (z : X) : ambientNormOneLevi p := E (z.1.1, EL z.1.2)
  let v (z : X) : G₁ := (normOneParabolicImageEquiv p (u z)).val * compactToNormOne K hKc z.2
  have hu (z : X) : pr (u z).val = (EL z.1.2).val :=
    proj_coordinates p iU l hU (z.1.1, (EL z.1.2).val)
  have hv (z : X) : (v z).val = map F P G p (u z).val * z.2.val := rfl
  change mk ΓP (v x) = mk ΓP (v y) at hxy
  obtain ⟨s, ⟨d, hd⟩, hs⟩ := (LeftCosetSpace.mk_eq_mk_iff ΓP _ _).mp hxy
  have hmul : mapNormOne F P G p (rationalNormOne F P d) * v x = v y := by
    change rationalNormOne F P d = s at hd
    rw [hd, show mapNormOne F P G p s = v y * (v x)⁻¹ from hs]
    exact inv_mul_cancel_right _ _
  have hG : map F P G p (rational F P d) * (map F P G p (u x).val * x.2.val) =
      map F P G p (u y).val * y.2.val := by
    have h := congrArg (Subtype.val : G₁ → AdelicGroupPoints F G) hmul
    change map F P G p (rational F P d) * (v x).val = (v y).val at h
    simpa only [hv] using h
  let c : AdelicGroupPoints F P := (u y).val⁻¹ * rational F P d * (u x).val
  have hc : map F P G p c ∈ K := by
    have hck : map F P G p c = y.2.val * x.2.val⁻¹ := by
      change map F P G p ((u y).val⁻¹ * rational F P d * (u x).val) = _
      rw [map_mul, map_mul, map_inv]
      calc
        _ = (map F P G p (u y).val)⁻¹ *
            (map F P G p (rational F P d) * (map F P G p (u x).val * x.2.val)) *
            x.2.val⁻¹ := by group
        _ = _ := by rw [hG]; group
    rw [hck]
    exact K.mul_mem y.2.property (K.inv_mem x.2.property)
  have hcM : pr c ∈ KM := by
    rw [← map_parabolicCompact_retraction p iU l hU hKc hKM]
    exact ⟨c, hc, rfl⟩
  let k : M₁ := ⟨pr c, compactSubgroup_le_normOneSubgroup F M (KM) hKM.1 hcM⟩
  let m : M₁ := rationalNormOne F M (P.affinePointsTarget (ret) _ d)
  have hdM : pr (rational F P d) = m.val := map_rational (ret) d
  have hck : (u y).val * c = rational F P d * (u x).val := by
    change (u y).val * ((u y).val⁻¹ * rational F P d * (u x).val) = _
    group
  have hEL (z : M₁) : (EL (1, z)).val = z.val := by
    rw [relativeLeviDecomposition_apply]
    change positivePointMap F M A a 1 * z.val = z.val
    rw [map_one, one_mul]
  have hLevi : EL y.1.2 * EL (1, k) = EL (1, m) * EL x.1.2 := by
    apply Subtype.ext
    change (EL y.1.2).val * (EL (1, k)).val = (EL (1, m)).val * (EL x.1.2).val
    rw [hEL, hEL, ← hu y, ← hu x]
    change pr (u y).val * pr c = m.val * pr (u x).val
    rw [← hdM, ← map_mul, ← map_mul, hck]
  have hparts := eq_splitParts_of_eq (EL).toMulEquiv x.1.2.1 y.1.2.1
    x.1.2.2 y.1.2.2 k m hLevi
  refine ⟨k, hcM, hparts.1, ?_⟩
  rw [LeftCosetSpace.rightTranslate_mk, hparts.2]
  exact LeftCosetSpace.mk_subgroup_mul ΓM ⟨m, ⟨_, rfl⟩⟩ x.1.2.2

/-- A product condition on relative height and the intrinsic Levi class pulls back unchanged
from its image in the rational parabolic quotient, if the Levi condition is right invariant
under the induced compact subgroup. -/
def RelativeParabolicCoordinateSaturationStatement : Prop :=
  IsMaximalCompactSubgroup F M KM →
    ∀ (A₀ : Set B) (D : Set (NormOneRationalQuotient F M)),
      (∀ k : M₁, k.val ∈ KM → ∀ q, rightTranslate ΓM k q ∈ D → q ∈ D) →
        let S : Set X := {x | x.1.2.1 ∈ A₀ ∧ mk ΓM x.1.2.2 ∈ D}
        coord ⁻¹' (coord '' S) = S

/-- The coordinate fibre relation preserves the split set and the compact-invariant Levi
condition. The other inclusion holds for every map into its image. -/
theorem relativeParabolicCoordinateSaturation :
    RelativeParabolicCoordinateSaturationStatement p iU l hU a hM ha hKc := by
  intro hKM A₀ D hD S
  ext y
  constructor
  · rintro ⟨x, hx, hxy⟩
    obtain ⟨k, hk, hb, he⟩ := relativeParabolicCoordinates_fibre p iU l hU a hM ha hKc hKM hxy
    exact ⟨hb ▸ hx.1, hD k hk _ (he.symm ▸ hx.2)⟩
  · intro hy
    exact ⟨y, hy, rfl⟩

end Langlands.Global.AdelicGroupPoints.ParabolicIwasawaMeasure
