import Langlands.GroupScheme.Rational.SimpleRootFiberPinning
import Langlands.GroupScheme.Rational.OrthogonalOrbitRootCoordinates
import Langlands.GroupScheme.Lie.RootOrbitCharacterDescent
import Langlands.GroupScheme.Lie.RootOrbitCharacterAction
import Langlands.Geometry.Building.QuasiSplitValuedRankOneCoordinates

/-! # Root field coordinates on both signs of a simple relative root fiber -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- A negated rational character takes inverse values. -/
theorem rationalCharacterEval_neg {k : Type u} [Field k]
    {H : GroupScheme (Spec (CommRingCat.of k))} (χ : rationalCharacters H)
    (g : rationalPoints H) :
    rationalCharacterEval (-χ) g = (rationalCharacterEval χ g)⁻¹ := by
  have h := rationalCharacterEval_add (-χ) χ g
  rw [neg_add_cancel, rationalCharacterEval_zero] at h
  exact eq_inv_of_mul_eq_one_left h.symm

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
local notation "f_K" => CategoryTheory.Functor.map (CommGroupScheme.baseChange bK) f

local instance simpleRootFiberCoordinatesIsAffineHom : IsAffineHom (G_K).X.hom := by
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

section Embedding

/-- The embedding of a member is the Library orbit embedding of its root. -/
theorem fiberEmbedding_eq_rootOrbitEmbeddingEquiv (t : (Dₚ).pinning.base.support)
    (ht : t ∈ Oₐ) :
    ∃ ρ : MulAction.orbit (K ≃ₐ[k] K) β₀, ρ.val = rootOf k K j hP t.1 ∧
      τₐ t = rootOrbitEmbeddingEquiv k K j β₀ ρ := by
  refine ⟨⟨rootOf k K j hP t.1, ?_⟩, rfl, ?_⟩
  · rw [baseRoot_orbit k K f j hP hf hcent hT ν hν hGK hi hjc ha]
    exact rootOf_mem_restrictionFiber k K f j hP hf hcent hT ν hν hGK hi t ht
  · unfold fiberEmbedding
    rw [dite_eq_left_of_eq_true (eq_true ht)]
    rfl

/-- The embedding of a member sends the root-orbit value of a rational torus point to the
value of the member's root at its scalar extension. -/
theorem fiberEmbedding_rootOrbitCharacter (t : (Dₚ).pinning.base.support) (ht : t ∈ Oₐ)
    (z : rationalPoints T.toGrp) :
    τₐ t ((rationalCharacterEval (rootOrbitCharacter k K j β₀)
        (GaloisPointComparison.rationalExtend k Eₐ T.toGrp z) : Eₐ)) =
      (rationalCharacterEval ((rationalCharacters.equivCharacterLattice T_K).symm (P.root t.1))
        (GaloisPointComparison.rationalExtend k K T.toGrp z) : K) := by
  obtain ⟨ρ, hρ, hτ⟩ :=
    fiberEmbedding_eq_rootOrbitEmbeddingEquiv k K f j hP hf hcent hT ν hν hGK hi hjc ha t ht
  rw [hτ, rationalCharacterEval_rootOrbitCharacter, rootOrbitEmbeddingEquiv_characterValue, hρ]
  exact (rationalCharacterEval_baseChangedCharacter k K T (P.root t.1) z).symm

end Embedding

section Records

variable [Smooth G.X.hom] [Fintype (fiberSet k K f j hP hf hcent hT ν hν hGK hi a)]
  (h2a : 2 • a ∉ relativeRoots (CommGroupScheme.groupHom f ≫ j))

omit [IsGalois k K] [Smooth G.X.hom]
  [Fintype (fiberSet k K f j hP hf hcent hT ν hν hGK hi a)] in
/-- The scalar extension of `f` followed by the pinning inclusion is the scalar extension of
the split torus inclusion. -/
theorem fiber_hg :
    CommGroupScheme.groupHom f_K ≫ (Dₚ).pinning.inclusion =
      (GroupScheme.baseChange (algebraBaseMap k K)).map (CommGroupScheme.groupHom f ≫ j) := by
  rw [(Dₚ).inclusion_eq, Functor.map_comp]
  change CommGroupScheme.groupHom f_K ≫ (𝟙 _ ≫ j_K) = _
  rw [Category.id_comp]
  rfl

omit [IsGalois k K] [Smooth G.X.hom] in
/-- The torus identification of the pinning is the identity on rational points. -/
theorem fiber_torusIso_inv (y : rationalPoints (T_K).toGrp) :
    rationalPoints.map (CommGroupScheme.groupHom (Dₚ).torusIso.inv) y = y := by
  rw [rationalPoints.map_apply]
  exact Category.comp_id y

local notation "hOₐ" => fiberSet_isOrthogonal k K f j hP hf hcent hT ν hν hGK hi ha h2a

variable
  (hprodp : ∀ g, g ∈ Langlands.Geometry.Building.rootGroupPoints
      (S := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj S)
      ((GroupScheme.baseChange (algebraBaseMap k K)).map (CommGroupScheme.groupHom f ≫ j))
      (characterLattice.baseChange (algebraBaseMap k K) S a) →
        ∃ c :
        (fiberPinning k K f j hP hf hcent hT ν hν hGK hi).pinning.base.support → K,
          g = SplitPinning.orbitXp k K
            (fiberPinning k K f j hP hf hcent hT ν hν hGK hi).pinning
            (fiberPinning k K f j hP hf hcent hT ν hν hGK hi).rootMaps
            (fiberSet k K f j hP hf hcent hT ν hν hGK hi a)
            (fiberSet_isOrthogonal k K f j hP hf hcent hT ν hν hGK hi ha h2a) c)
  (huniqp : ∀ c c' :
        (fiberPinning k K f j hP hf hcent hT ν hν hGK hi).pinning.base.support → K,
      SplitPinning.orbitXp k K
            (fiberPinning k K f j hP hf hcent hT ν hν hGK hi).pinning
            (fiberPinning k K f j hP hf hcent hT ν hν hGK hi).rootMaps
            (fiberSet k K f j hP hf hcent hT ν hν hGK hi a)
            (fiberSet_isOrthogonal k K f j hP hf hcent hT ν hν hGK hi ha h2a) c =
        SplitPinning.orbitXp k K
            (fiberPinning k K f j hP hf hcent hT ν hν hGK hi).pinning
            (fiberPinning k K f j hP hf hcent hT ν hν hGK hi).rootMaps
            (fiberSet k K f j hP hf hcent hT ν hν hGK hi a)
            (fiberSet_isOrthogonal k K f j hP hf hcent hT ν hν hGK hi ha h2a) c' →
          ∀ t ∈ fiberSet k K f j hP hf hcent hT ν hν hGK hi a, c t = c' t)
  (hprodm : ∀ g, g ∈ Langlands.Geometry.Building.rootGroupPoints
      (S := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj S)
      ((GroupScheme.baseChange (algebraBaseMap k K)).map (CommGroupScheme.groupHom f ≫ j))
      (characterLattice.baseChange (algebraBaseMap k K) S (-a)) →
        ∃ c :
        (fiberPinning k K f j hP hf hcent hT ν hν hGK hi).pinning.base.support → K,
          g = SplitPinning.orbitXm k K
            (fiberPinning k K f j hP hf hcent hT ν hν hGK hi).pinning
            (fiberPinning k K f j hP hf hcent hT ν hν hGK hi).rootMaps
            (fiberSet k K f j hP hf hcent hT ν hν hGK hi a)
            (fiberSet_isOrthogonal k K f j hP hf hcent hT ν hν hGK hi ha h2a) c)
  (huniqm : ∀ c c' :
        (fiberPinning k K f j hP hf hcent hT ν hν hGK hi).pinning.base.support → K,
      SplitPinning.orbitXm k K
            (fiberPinning k K f j hP hf hcent hT ν hν hGK hi).pinning
            (fiberPinning k K f j hP hf hcent hT ν hν hGK hi).rootMaps
            (fiberSet k K f j hP hf hcent hT ν hν hGK hi a)
            (fiberSet_isOrthogonal k K f j hP hf hcent hT ν hν hGK hi ha h2a) c =
        SplitPinning.orbitXm k K
            (fiberPinning k K f j hP hf hcent hT ν hν hGK hi).pinning
            (fiberPinning k K f j hP hf hcent hT ν hν hGK hi).rootMaps
            (fiberSet k K f j hP hf hcent hT ν hν hGK hi a)
            (fiberSet_isOrthogonal k K f j hP hf hcent hT ν hν hGK hi ha h2a) c' →
          ∀ t ∈ fiberSet k K f j hP hf hcent hT ν hν hGK hi a, c t = c' t)

/-- Field coordinates on the root group of `a`: the upper unipotents of the descended
`SL₂(E)`, with the root-orbit character of the base root. -/
def positiveCoordinates :
    Langlands.Geometry.Building.RootFieldCoordinatesOn (CommGroupScheme.groupHom f ≫ j) j
      (CommGroupScheme.groupHom f) a Eₐ where
  equiv := SplitPinning.upperRootEquiv k K j (Dₚ).pinning (Dₚ).torusIso (Dₚ).inclusion_eq
    (Dₚ).rootMaps (Dₚ).rootMaps_compatible (Dₚ).action_root Oₐ
    (fiberSet_galois k K f j hP hf hcent hT ν hν hGK hi a) hOₐ τₐ
    (fiberEmbedding_galois k K f j hP hf hcent hT ν hν hGK hi hjc ha)
    (CommGroupScheme.groupHom f ≫ j) f_K (fiber_hg k K f j hP hf hcent hT ν hν hGK hi) a
    (fun t ht => (mem_fiberSet_iff k K f j hP hf hcent hT ν hν hGK hi a t).mp ht) hf.1.1
    ha.1.1.1 hprodp huniqp
    (fun c hc => exists_eq_fiberEmbedding k K f j hP hf hcent hT ν hν hGK hi hjc ha c hc)
    (basePoint_mem k K f j hP hf hcent hT ν hν hGK hi ha)
  character := rootOrbitCharacter k K j β₀
  restriction := by
    have : IsAffine T.toGrp.X.left := isAffine_of_isAffineHom T.toGrp.X.hom
    have : IsAffineHom S.toGrp.X.hom := hf.1.1.isAffineHom
    have : IsAffine S.toGrp.X.left := isAffine_of_isAffineHom S.toGrp.X.hom
    exact characterRestrict_rootOrbitCharacter k K j f a
      (rootOf_mem_restrictionFiber k K f j hP hf hcent hT ν hν hGK hi _
        (basePoint_mem k K f j hP hf hcent hT ν hν hGK hi ha))
  conjugation z t := by
    rw [SplitPinning.upperRootEquiv_apply, SplitPinning.upperRootEquiv_apply]
    refine SplitPinning.conj_fieldSL2_upper k K j (Dₚ).pinning (Dₚ).torusIso (Dₚ).inclusion_eq
      (Dₚ).rootMaps (Dₚ).rootMaps_compatible (Dₚ).action_root Oₐ
      (fiberSet_galois k K f j hP hf hcent hT ν hν hGK hi a) hOₐ τₐ
      (fiberEmbedding_galois k K f j hP hf hcent hT ν hν hGK hi hjc ha)
      (fun z => ((rationalCharacterEval (rootOrbitCharacter k K j β₀)
        (GaloisPointComparison.rationalExtend k Eₐ T.toGrp z) : Eₐˣ) : Eₐ)) ?_ z t
    intro z b hb
    refine (fiberEmbedding_rootOrbitCharacter k K f j hP hf hcent hT ν hν hGK hi hjc ha b hb
      z).trans ?_
    exact congrArg (fun y => ((rationalCharacterEval
      ((rationalCharacters.equivCharacterLattice (T_K)).symm (P.root b.1)) y : Kˣ) : K))
      (fiber_torusIso_inv k K f j hP hf hcent hT ν hν hGK hi _).symm

/-- Field coordinates on the root group of `-a`: the lower unipotents of the descended
`SL₂(E)`, with the negated root-orbit character. -/
def negativeCoordinates :
    Langlands.Geometry.Building.RootFieldCoordinatesOn (CommGroupScheme.groupHom f ≫ j) j
      (CommGroupScheme.groupHom f) (-a) Eₐ where
  equiv := SplitPinning.lowerRootEquiv k K j (Dₚ).pinning (Dₚ).torusIso (Dₚ).inclusion_eq
    (Dₚ).rootMaps (Dₚ).rootMaps_compatible (Dₚ).action_root Oₐ
    (fiberSet_galois k K f j hP hf hcent hT ν hν hGK hi a) hOₐ τₐ
    (fiberEmbedding_galois k K f j hP hf hcent hT ν hν hGK hi hjc ha)
    (CommGroupScheme.groupHom f ≫ j) f_K (fiber_hg k K f j hP hf hcent hT ν hν hGK hi) a
    (fun t ht => (mem_fiberSet_iff k K f j hP hf hcent hT ν hν hGK hi a t).mp ht) hf.1.1
    ha.1.1.1 hprodm huniqm
    (fun c hc => exists_eq_fiberEmbedding k K f j hP hf hcent hT ν hν hGK hi hjc ha c hc)
    (basePoint_mem k K f j hP hf hcent hT ν hν hGK hi ha)
  character := -rootOrbitCharacter k K j β₀
  restriction := by
    have : IsAffine T.toGrp.X.left := isAffine_of_isAffineHom T.toGrp.X.hom
    have : IsAffineHom S.toGrp.X.hom := hf.1.1.isAffineHom
    have : IsAffine S.toGrp.X.left := isAffine_of_isAffineHom S.toGrp.X.hom
    have hpos : characterRestrict ((GroupScheme.baseChange
        (GaloisPointComparison.baseMap k Eₐ)).map (CommGroupScheme.groupHom f))
        (rootOrbitCharacter k K j β₀) =
        rationalCharacters.baseChange (GaloisPointComparison.baseMap k Eₐ)
          ((rationalCharacters.equivCharacterLattice S).symm a) :=
      characterRestrict_rootOrbitCharacter k K j f a
        (rootOf_mem_restrictionFiber k K f j hP hf hcent hT ν hν hGK hi _
          (basePoint_mem k K f j hP hf hcent hT ν hν hGK hi ha))
    rw [map_neg, hpos, map_neg, map_neg]
  conjugation z t := by
    rw [SplitPinning.lowerRootEquiv_apply, SplitPinning.lowerRootEquiv_apply]
    refine SplitPinning.conj_fieldSL2_lower k K j (Dₚ).pinning (Dₚ).torusIso (Dₚ).inclusion_eq
      (Dₚ).rootMaps (Dₚ).rootMaps_compatible (Dₚ).action_root Oₐ
      (fiberSet_galois k K f j hP hf hcent hT ν hν hGK hi a) hOₐ τₐ
      (fiberEmbedding_galois k K f j hP hf hcent hT ν hν hGK hi hjc ha)
      (fun z => ((rationalCharacterEval (-rootOrbitCharacter k K j β₀)
        (GaloisPointComparison.rationalExtend k Eₐ T.toGrp z) : Eₐˣ) : Eₐ)) ?_ z t
    intro z b hb
    rw [rationalCharacterEval_neg, Units.val_inv_eq_inv_val, map_inv₀,
      fiberEmbedding_rootOrbitCharacter k K f j hP hf hcent hT ν hν hGK hi hjc ha b hb z]
    refine Eq.trans ?_ (congrArg (fun y => ((rationalCharacterEval
      ((rationalCharacters.equivCharacterLattice (T_K)).symm (-P.root b.1)) y : Kˣ) : K))
      (fiber_torusIso_inv k K f j hP hf hcent hT ν hν hGK hi _).symm)
    rw [map_neg, rationalCharacterEval_neg, Units.val_inv_eq_inv_val]

theorem positiveCoordinates_equiv (t : Eₐ) :
    ((positiveCoordinates k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a hprodp huniqp).equiv
        (Multiplicative.ofAdd t) : rationalPoints G) =
      SplitPinning.fieldSL2 k K j (Dₚ).pinning (Dₚ).torusIso (Dₚ).inclusion_eq (Dₚ).rootMaps
        (Dₚ).rootMaps_compatible (Dₚ).action_root Oₐ
        (fiberSet_galois k K f j hP hf hcent hT ν hν hGK hi a) hOₐ τₐ
        (fiberEmbedding_galois k K f j hP hf hcent hT ν hν hGK hi hjc ha)
        (SpecialLinear.BinaryPresentation.upper t) :=
  rfl

theorem negativeCoordinates_equiv (t : Eₐ) :
    ((negativeCoordinates k K f j hP hf hcent hT ν hν hGK hi hjc ha h2a hprodm huniqm).equiv
        (Multiplicative.ofAdd t) : rationalPoints G) =
      SplitPinning.fieldSL2 k K j (Dₚ).pinning (Dₚ).torusIso (Dₚ).inclusion_eq (Dₚ).rootMaps
        (Dₚ).rootMaps_compatible (Dₚ).action_root Oₐ
        (fiberSet_galois k K f j hP hf hcent hT ν hν hGK hi a) hOₐ τₐ
        (fiberEmbedding_galois k K f j hP hf hcent hT ν hν hGK hi hjc ha)
        (SpecialLinear.BinaryPresentation.lower t) :=
  rfl

end Records

end SimpleRootFiber

end Langlands.GroupScheme
