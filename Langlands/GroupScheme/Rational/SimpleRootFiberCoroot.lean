import Langlands.GroupScheme.Rational.SimpleRootFiberPinning
import Langlands.GroupScheme.Rational.OrthogonalOrbitSpecialLinear
import Langlands.GroupScheme.Rational.SimpleCorootGaloisTransport
import Langlands.GroupScheme.Rational.SimpleOrbitCorootGeneration
import Langlands.GroupScheme.Torus.WeilRestrictionRationalCharacters
import Langlands.GroupScheme.Torus.WeilRestrictionEmbeddingLattices
import Langlands.GroupScheme.Torus.WeilRestrictionNormCoordinates
import Langlands.GroupScheme.Torus.FiniteGaloisCharacterDescent
import Langlands.Algebra.SeparableTensorProof
import Langlands.GroupScheme.Absolute.CocharacterAveraging
import Langlands.GroupScheme.Rational.ClassFunctionsTorusSeparationReduction

/-! # The coroot of a simple relative root fiber as a morphism from a Weil restriction -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SplitPinning

section CorootPoints

variable {K : Type u} [Field K] {H : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom H.X.hom]
  (p : SplitPinning H)

/-- A character takes the value `t ^ ⟨χ, α^∨⟩` at the simple-coroot point `α^∨(t)`. -/
theorem rationalCharacterEval_simpleCorootPoint (χ : characterLattice p.torus)
    (b : p.base.support) (t : Kˣ) :
    rationalCharacterEval ((rationalCharacters.equivCharacterLattice p.torus).symm χ)
        (p.simpleCorootPoint b t) =
      t ^ latticePairing p.torus χ (p.rootDatum.coroot b) := by
  unfold simpleCorootPoint
  simp only [MonoidHom.comp_apply, rationalPoints.map_apply, MulEquiv.coe_toMonoidHom]
  rw [rationalCharacterEval_apply]
  change Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of K)))
    (((Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of K)))).symm t ≫
      (CommGroupScheme.groupHom (p.rootDatum.coroot b)).hom.hom) ≫
      (CommGroupScheme.groupHom χ).hom.hom) = _
  rw [Category.assoc]
  change Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of K)))
    ((Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of K)))).symm t ≫
      (CommGroupScheme.groupHom (p.rootDatum.coroot b ≫ χ)).hom.hom) = _
  conv_lhs => rw [← (gmEndEquiv K).symm_apply_apply (p.rootDatum.coroot b ≫ χ)]
  rw [gmEndEquiv_symm_comp, map_zpow, MulEquiv.apply_symm_apply, latticePairing_apply]

end CorootPoints

end SplitPinning

/-- Rational points of a split torus are determined by their character values. -/
theorem IsSplitTorus.rationalPoint_ext {K : Type u} [Field K]
    {A : CommGroupScheme (Spec (CommRingCat.of K))} (hA : IsSplitTorus A.toGrp)
    {y y' : rationalPoints A.toGrp}
    (h : ∀ χ : characterLattice A,
      rationalCharacterEval ((rationalCharacters.equivCharacterLattice A).symm χ) y =
        rationalCharacterEval ((rationalCharacters.equivCharacterLattice A).symm χ) y') :
    y = y' := by
  apply IsSplitTorus.point_ext_characters hA
  intro χ
  have hχ := h χ
  rw [rationalCharacterEval_apply, rationalCharacterEval_apply] at hχ
  exact (Gm.affinePointsEquiv (𝟙 _)).injective hχ

namespace SimpleRootFiber

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  [IsAffineHom T.toGrp.X.hom] [LocallyOfFiniteType T.toGrp.X.hom]
  (f : S ⟶ T) (j : T.toGrp ⟶ G)

local notation "bK" => algebraBaseMap k K
local notation "T_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange bK) T
local notation "G_K" => CategoryTheory.Functor.obj (GroupScheme.baseChange bK) G
local notation "j_K" => CategoryTheory.Functor.map (GroupScheme.baseChange bK) j

local instance simpleRootFiberCorootIsAffineHom : IsAffineHom (G_K).X.hom := by
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
  [IsGalois k K] (hjc : IsClosedSubgroup j)
  {a : characterLattice S} (ha : a ∈ simpleRelativeRoots (CommGroupScheme.groupHom f ≫ j) ν)

local notation "Dₚ" => fiberPinning k K f j hP hf hcent hT ν hν hGK hi
local notation "Oₐ" => fiberSet k K f j hP hf hcent hT ν hν hGK hi a
local notation "Eₐ" => fiberField k K f j hP hf hcent hT ν hν hGK hi ha
local notation "τₐ" => fiberEmbedding k K f j hP hf hcent hT ν hν hGK hi hjc ha
local notation "β₀" => baseRoot k K f j hP hf hcent hT ν hν hGK hi ha
local notation "Φₐ" => rootRestrictionFiberEmbeddingEquiv k K f j a β₀
  (baseRoot_orbit k K f j hP hf hcent hT ν hν hGK hi hjc ha)

section Members

/-- Every embedding of the fiber field is attached to some member of the fiber. -/
theorem exists_member (σ : Eₐ →ₐ[k] K) :
    ∃ t ∈ Oₐ, rootOf k K j hP t.1 = ((Φₐ).symm σ).val := by
  obtain ⟨r, hr⟩ : (((Φₐ).symm σ).val.val) ∈ Set.range P.root := by
    rw [hP.2.1]
    exact ((Φₐ).symm σ).val.property
  have hra : restrictCharacter k K f hf.1.1 (P.root r) = a := by
    rw [restrictCharacter_eq_iff, hr]
    exact ((Φₐ).symm σ).property
  obtain ⟨t, ht, htr⟩ := exists_mem_fiberSet k K f j hP hf hcent hT ν hν hGK hi ha r hra
  refine ⟨t, ht, Subtype.ext ?_⟩
  change P.root t.1 = _
  rw [htr, hr]

/-- The member of the fiber whose embedding of the fiber field is `σ`. -/
def memberOf (σ : Eₐ →ₐ[k] K) : (Dₚ).pinning.base.support :=
  (exists_member k K f j hP hf hcent hT ν hν hGK hi hjc ha σ).choose

/-- The chosen member lies in the fiber. -/
theorem memberOf_mem (σ : Eₐ →ₐ[k] K) :
    memberOf k K f j hP hf hcent hT ν hν hGK hi hjc ha σ ∈ Oₐ :=
  (exists_member k K f j hP hf hcent hT ν hν hGK hi hjc ha σ).choose_spec.1

/-- The root of the chosen member is the root attached to the embedding. -/
theorem rootOf_memberOf (σ : Eₐ →ₐ[k] K) :
    rootOf k K j hP (memberOf k K f j hP hf hcent hT ν hν hGK hi hjc ha σ).1 =
      ((Φₐ).symm σ).val :=
  (exists_member k K f j hP hf hcent hT ν hν hGK hi hjc ha σ).choose_spec.2

/-- The embedding of the chosen member is the given embedding. -/
theorem fiberEmbedding_memberOf (σ : Eₐ →ₐ[k] K) :
    τₐ (memberOf k K f j hP hf hcent hT ν hν hGK hi hjc ha σ) = σ := by
  apply (Φₐ).symm.injective
  apply Subtype.ext
  rw [fiberEmbedding_symm k K f j hP hf hcent hT ν hν hGK hi hjc ha _
    (memberOf_mem k K f j hP hf hcent hT ν hν hGK hi hjc ha σ), rootOf_memberOf]

/-- Each member of the fiber is the chosen member of its own embedding. -/
theorem memberOf_fiberEmbedding (t : (Dₚ).pinning.base.support) (ht : t ∈ Oₐ) :
    memberOf k K f j hP hf hcent hT ν hν hGK hi hjc ha (τₐ t) = t := by
  apply Subtype.ext
  apply P.root.injective
  have h1 := rootOf_memberOf k K f j hP hf hcent hT ν hν hGK hi hjc ha (τₐ t)
  rw [fiberEmbedding_symm k K f j hP hf hcent hT ν hν hGK hi hjc ha t ht] at h1
  exact congrArg Subtype.val h1

/-- The fiber is in bijection with the embeddings of the fiber field. -/
def memberEquiv : Oₐ ≃ (Eₐ →ₐ[k] K) where
  toFun t := τₐ t.1
  invFun σ := ⟨memberOf k K f j hP hf hcent hT ν hν hGK hi hjc ha σ,
    memberOf_mem k K f j hP hf hcent hT ν hν hGK hi hjc ha σ⟩
  left_inv t := Subtype.ext (memberOf_fiberEmbedding k K f j hP hf hcent hT ν hν hGK hi hjc ha
    t.1 t.2)
  right_inv σ := fiberEmbedding_memberOf k K f j hP hf hcent hT ν hν hGK hi hjc ha σ

/-- Galois transport of embeddings moves members by the Galois action on simple roots. -/
theorem memberOf_comp (σ : K ≃ₐ[k] K) (φ : Eₐ →ₐ[k] K) :
    memberOf k K f j hP hf hcent hT ν hν hGK hi hjc ha (σ.toAlgHom.comp φ) =
      (Dₚ).action σ (memberOf k K f j hP hf hcent hT ν hν hGK hi hjc ha φ) := by
  have hm := memberOf_mem k K f j hP hf hcent hT ν hν hGK hi hjc ha φ
  have hσm := (fiberSet_galois k K f j hP hf hcent hT ν hν hGK hi a σ _).mp hm
  conv_lhs => rw [← fiberEmbedding_memberOf k K f j hP hf hcent hT ν hν hGK hi hjc ha φ,
    ← fiberEmbedding_galois k K f j hP hf hcent hT ν hν hGK hi hjc ha σ _ hm]
  exact memberOf_fiberEmbedding k K f j hP hf hcent hT ν hν hGK hi hjc ha _ hσm

end Members

section Coroot

local notation "Wₐ" => WeilGm.commGroupScheme (CommRingCat.of k) Eₐ
local notation "W_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange bK)
  (WeilGm.commGroupScheme (CommRingCat.of k) Eₐ)

/-- The fiber field is separable over `k`, as a subfield of the Galois extension `K`. -/
instance fiberField_isSeparable : Algebra.IsSeparable k Eₐ :=
  Algebra.isSeparable_tower_bot_of_isSeparable k Eₐ K

/-- The tensor algebra of the fiber field over `K` splits along its embeddings. -/
theorem fiberField_embeddingEvaluation_bijective :
    Function.Bijective (Langlands.Algebra.SeparableTensor.embeddingEvaluation k Eₐ K) :=
  Langlands.Algebra.SeparableTensor.embeddingEvaluationStatement k Eₐ K
    (WeilGm.intermediate_minpoly_splits k K Eₐ)

/-- The coroot index attached to an embedding of the fiber field. -/
def memberIndex (σ : Eₐ →ₐ[k] K) : J :=
  (memberOf k K f j hP hf hcent hT ν hν hGK hi hjc ha σ).1

/-- Characters of `T_K` pulled back along the coroot: the embedding `σ` gets the pairing with
the coroot of its member. -/
def corootCharacterMap : characterLattice T_K →+ characterLattice W_K :=
  (WeilGm.embeddingCharacterEquiv k Eₐ K
      (fiberField_embeddingEvaluation_bijective k K f j hP hf hcent hT ν hν hGK hi ha)).symm.toAddMonoidHom.comp
    { toFun := fun χ σ => latticePairing T_K χ
        (P.coroot (memberIndex k K f j hP hf hcent hT ν hν hGK hi hjc ha σ))
      map_zero' := by
        funext σ
        simp
      map_add' := by
        intro χ ψ
        funext σ
        simp }

/-- The coroot character map in embedding coordinates. -/
theorem corootCharacterMap_eq (χ : characterLattice T_K) :
    corootCharacterMap k K f j hP hf hcent hT ν hν hGK hi hjc ha χ =
      (WeilGm.embeddingCharacterEquiv k Eₐ K
        (fiberField_embeddingEvaluation_bijective k K f j hP hf hcent hT ν hν hGK hi ha)).symm
        (fun σ => latticePairing T_K χ
          (P.coroot (memberIndex k K f j hP hf hcent hT ν hν hGK hi hjc ha σ))) := rfl

/-- The embedding coordinates of the coroot character map. -/
theorem corootCharacterMap_apply (χ : characterLattice T_K) :
    WeilGm.embeddingCharacterEquiv k Eₐ K
        (fiberField_embeddingEvaluation_bijective k K f j hP hf hcent hT ν hν hGK hi ha)
        (corootCharacterMap k K f j hP hf hcent hT ν hν hGK hi hjc ha χ) =
      fun σ => latticePairing T_K χ
        (P.coroot (memberIndex k K f j hP hf hcent hT ν hν hGK hi hjc ha σ)) := by
  rw [corootCharacterMap_eq, AddEquiv.apply_symm_apply]

omit [IsGalois k K] in
/-- Galois transport of simple coroots of the fiber. -/
theorem coroot_action (σ : K ≃ₐ[k] K) (t : (Dₚ).pinning.base.support) :
    P.coroot (show J from ((Dₚ).action σ t).1) =
      cocharacterLattice.galoisRepresentation k K T σ (P.coroot (show J from t.1)) := by
  have h := GaloisCompatiblePinningData.action_coroot (Dₚ) σ t
  rw [cocharacterLattice.congr_apply, cocharacterLattice.congr_apply] at h
  change P.coroot (show J from ((Dₚ).action σ t).1) ≫ 𝟙 _ =
    cocharacterLattice.galoisRepresentation k K T σ (P.coroot (show J from t.1) ≫ 𝟙 _) at h
  simpa only [Category.comp_id] using h

/-- The coroot character map is Galois equivariant. -/
theorem corootCharacterMap_equivariant (σ : K ≃ₐ[k] K) (χ : characterLattice T_K) :
    corootCharacterMap k K f j hP hf hcent hT ν hν hGK hi hjc ha
        (characterLattice.galoisRepresentation k K T σ χ) =
      characterLattice.galoisRepresentation k K Wₐ σ
        (corootCharacterMap k K f j hP hf hcent hT ν hν hGK hi hjc ha χ) := by
  have hfun : (fun φ => latticePairing T_K (characterLattice.galoisRepresentation k K T σ χ)
      (P.coroot (memberIndex k K f j hP hf hcent hT ν hν hGK hi hjc ha φ))) =
      Langlands.Algebra.SeparableTensor.embeddingPermutationRepresentation k Eₐ K σ
        (fun φ => latticePairing T_K χ
          (P.coroot (memberIndex k K f j hP hf hcent hT ν hν hGK hi hjc ha φ))) := by
    funext φ
    change _ = latticePairing T_K χ (P.coroot (memberIndex k K f j hP hf hcent hT ν hν hGK hi
      hjc ha ((Langlands.Algebra.SeparableTensor.embeddingPermutation k Eₐ K σ).symm φ)))
    rw [Langlands.Algebra.SeparableTensor.embeddingPermutation_symm,
      Langlands.Algebra.SeparableTensor.embeddingPermutation_apply]
    unfold memberIndex
    rw [show σ.symm = σ⁻¹ from rfl, memberOf_comp, coroot_action,
      latticePairing_galoisRepresentation_right, inv_inv]
  rw [corootCharacterMap_eq, corootCharacterMap_eq,
    WeilGm.galoisRepresentation_embeddingCharacterEquiv_symm, hfun]

/-- The coroot of the fiber: the unique morphism from the Weil restriction of `𝔾ₘ` along the
fiber field whose character pullback is `corootCharacterMap`. -/
theorem existsUnique_coroot :
    ∃! c : Wₐ ⟶ T, ∀ χ : characterLattice T_K,
      (CommGroupScheme.baseChange bK).map c ≫ χ =
        corootCharacterMap k K f j hP hf hcent hT ν hν hGK hi hjc ha χ :=
  hT.existsUnique_hom_of_equivariant_characterMap _
    (fun σ χ => corootCharacterMap_equivariant k K f j hP hf hcent hT ν hν hGK hi hjc ha σ χ)

/-- The coroot morphism. -/
def fiberCoroot : Wₐ ⟶ T :=
  (existsUnique_coroot k K f j hP hf hcent hT ν hν hGK hi hjc ha).exists.choose

/-- The coroot pulls characters back by the coroot character map. -/
theorem fiberCoroot_comp (χ : characterLattice T_K) :
    (CommGroupScheme.baseChange bK).map
        (fiberCoroot k K f j hP hf hcent hT ν hν hGK hi hjc ha) ≫ χ =
      corootCharacterMap k K f j hP hf hcent hT ν hν hGK hi hjc ha χ :=
  (existsUnique_coroot k K f j hP hf hcent hT ν hν hGK hi hjc ha).exists.choose_spec χ

end Coroot

section Points

variable [Fintype (fiberSet k K f j hP hf hcent hT ν hν hGK hi a)]

omit [IsGalois k K] in
/-- The orbit coroot product over the fiber is the image of the product of the simple-coroot
points of its members. -/
theorem orbitCoroot_eq_map_prod (hO : ∀ t ∈ Oₐ, ∀ t' ∈ Oₐ, t ≠ t' →
      (Dₚ).pinning.rootDatum.IsOrthogonal t t')
    (u : (Dₚ).pinning.base.support → Kˣ) :
    SplitPinning.orbitCoroot k K (Dₚ).pinning (Dₚ).rootMaps Oₐ hO u =
      rationalPoints.map (Dₚ).pinning.inclusion
        (∏ b : Oₐ, (Dₚ).pinning.simpleCorootPoint b (u b)) := by
  rw [← Finset.noncommProd_eq_prod, Finset.map_noncommProd, SplitPinning.orbitCoroot,
    Langlands.Algebra.RankOneRelation.prodHom, Subgroup.noncommPiCoprod_apply]
  rfl

omit [IsGalois k K] [Fintype ↑Oₐ] in
/-- The scalar extension of `j` is the pinning inclusion after the inverse torus
identification. -/
theorem map_baseChange_map_fiber
    (y : rationalPoints ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T).toGrp) :
    rationalPoints.map ((GroupScheme.baseChange (algebraBaseMap k K)).map j) y =
      rationalPoints.map (Dₚ).pinning.inclusion
        (rationalPoints.map (CommGroupScheme.groupHom (Dₚ).torusIso.inv) y) := by
  have hcomp : ∀ {H₁ H₂ H₃ : GroupScheme (Spec (CommRingCat.of K))} (f : H₁ ⟶ H₂)
      (f' : H₂ ⟶ H₃) (y : rationalPoints H₁),
      rationalPoints.map (f ≫ f') y = rationalPoints.map f' (rationalPoints.map f y) := by
    intro H₁ H₂ H₃ f f' y
    rw [rationalPoints.map_apply, rationalPoints.map_apply, rationalPoints.map_apply,
      Grp.comp_hom_hom, Category.assoc]
  rw [← hcomp, (Dₚ).inclusion_eq, ← Category.assoc]
  have h1 : CommGroupScheme.groupHom (Dₚ).torusIso.inv ≫
      CommGroupScheme.groupHom (Dₚ).torusIso.hom = 𝟙 _ :=
    congrArg CommGroupScheme.groupHom (Dₚ).torusIso.inv_hom_id
  rw [h1, Category.id_comp]
  rfl

omit [Fintype ↑Oₐ] in
/-- Restriction of characters along the scalar extension of the coroot is the coroot
character map. -/
theorem characterRestrict_fiberCoroot (χ : characterLattice T_K) :
    characterRestrict (CommGroupScheme.groupHom ((CommGroupScheme.baseChange bK).map
        (fiberCoroot k K f j hP hf hcent hT ν hν hGK hi hjc ha)))
        ((rationalCharacters.equivCharacterLattice T_K).symm χ) =
      corootCharacterMap k K f j hP hf hcent hT ν hν hGK hi hjc ha χ := by
  rw [← fiberCoroot_comp]
  rfl

/-- After scalar extension, the coroot sends `u` to the product of the simple-coroot points
`α_b^∨(τ_b u)` over the members `b` of the fiber. -/
theorem fiberCoroot_extendedUnitPoint (u : Eₐˣ) :
    rationalPoints.map (CommGroupScheme.groupHom ((CommGroupScheme.baseChange bK).map
        (fiberCoroot k K f j hP hf hcent hT ν hν hGK hi hjc ha)))
        (WeilGm.extendedUnitPoint k Eₐ K u) =
      ((∏ b : Oₐ, (Dₚ).pinning.simpleCorootPoint b
        (Units.map (τₐ b).toRingHom.toMonoidHom u)) : rationalPoints (T_K).toGrp) := by
  classical
  let : Fintype (Eₐ →ₐ[k] K) := Fintype.ofFinite _
  apply IsSplitTorus.rationalPoint_ext (A := T_K) hT
  intro χ
  rw [← rationalCharacterEval_characterRestrict, characterRestrict_fiberCoroot]
  refine (WeilGm.rationalCharacterEval_extendedUnitPoint_eq_prod k Eₐ K
      (fiberField_embeddingEvaluation_bijective k K f j hP hf hcent hT ν hν hGK hi ha)
      (corootCharacterMap k K f j hP hf hcent hT ν hν hGK hi hjc ha χ) u).trans ?_
  rw [corootCharacterMap_apply]
  change _ = rationalCharacterEval ((rationalCharacters.equivCharacterLattice (Dₚ).pinning.torus).symm χ)
    (∏ b : Oₐ, (Dₚ).pinning.simpleCorootPoint b (Units.map (τₐ b).toRingHom.toMonoidHom u))
  rw [map_prod]
  simp only [SplitPinning.rationalCharacterEval_simpleCorootPoint]
  symm
  apply Fintype.prod_equiv (memberEquiv k K f j hP hf hcent hT ν hν hGK hi hjc ha)
  intro b
  change _ = Units.map (τₐ b.1).toMonoidHom u ^ latticePairing T_K χ
    (P.coroot (memberIndex k K f j hP hf hcent hT ν hν hGK hi hjc ha (τₐ b.1)))
  unfold memberIndex
  rw [memberOf_fiberEmbedding k K f j hP hf hcent hT ν hν hGK hi hjc ha b.1 b.2]
  rfl

/-- The coroot realizes the diagonal torus of the descended `SL₂(E)` on rational points. -/
theorem fiberCoroot_points (h2a : 2 • a ∉ relativeRoots (CommGroupScheme.groupHom f ≫ j))
    (u : Eₐˣ) :
    rationalPoints.map j
        (rationalPoints.map
          (CommGroupScheme.groupHom (fiberCoroot k K f j hP hf hcent hT ν hν hGK hi hjc ha))
          ((WeilGm.rationalUnitsEquiv k Eₐ).symm u)) =
      SplitPinning.fieldSL2 k K j (Dₚ).pinning (Dₚ).torusIso (Dₚ).inclusion_eq (Dₚ).rootMaps
        (Dₚ).rootMaps_compatible (Dₚ).action_root Oₐ
        (fiberSet_galois k K f j hP hf hcent hT ν hν hGK hi a)
        (fiberSet_isOrthogonal k K f j hP hf hcent hT ν hν hGK hi ha h2a) τₐ
        (fiberEmbedding_galois k K f j hP hf hcent hT ν hν hGK hi hjc ha)
        (SpecialLinear.BinaryPresentation.diag u) := by
  have hid : ∀ z : rationalPoints (T_K).toGrp,
      rationalPoints.map (CommGroupScheme.groupHom (Dₚ).torusIso.inv) z = z := fun z => by
    rw [rationalPoints.map_apply]
    exact Category.comp_id z
  apply SplitPinning.rationalExtend_injective_of_isAffineHom k K
  rw [SplitPinning.rationalExtend_fieldSL2_diag, GaloisPointComparison.rationalExtend_map,
    GaloisPointComparison.rationalExtend_map,
    map_baseChange_map_fiber k K f j hP hf hcent hT ν hν hGK hi, hid,
    orbitCoroot_eq_map_prod]
  exact congrArg (rationalPoints.map (Dₚ).pinning.inclusion)
    (fiberCoroot_extendedUnitPoint k K f j hP hf hcent hT ν hν hGK hi hjc ha u)

end Points

end SimpleRootFiber

end Langlands.GroupScheme
