import Langlands.GroupScheme.Rational.RootPartnerFields
import Langlands.GroupScheme.Lie.RootOrbitCharacterDescent
import Langlands.GroupScheme.Rational.IndependentWeightProductProof
import Langlands.GroupScheme.Torus.RationalCharacterSeparation

/-! # Separation of actual root-partner character values over infinite fields -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.RootPartnerFields

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (j : T.toGrp ⟶ G)

local notation "b" => algebraBaseMap k L
local notation "T_L" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T
local notation "G_L" => CategoryTheory.Functor.obj (GroupScheme.baseChange b) G
local notation "j_L" => CategoryTheory.Functor.map (GroupScheme.baseChange b) j

attribute [local instance] rootsGaloisAction

/-- Actual root partners are preserved by Galois transport. -/
theorem IsRootPartner.smul {β β' : roots (T := T_L) (G := G_L) j_L}
    (h : IsRootPartner k L j β β') (σ : L ≃ₐ[k] L) :
    IsRootPartner k L j (σ • β) (σ • β') := by
  obtain ⟨⟨τ, hτ⟩, hne, hsum⟩ := h
  refine ⟨⟨σ * τ * σ⁻¹, ?_⟩, ?_, ?_⟩
  · rw [mul_smul, inv_smul_smul, mul_smul, hτ]
  · intro he
    exact hne (smul_left_cancel σ he)
  · let μ : roots (T := T_L) (G := G_L) j_L := ⟨β.val + β'.val, hsum⟩
    have hm := (σ • μ).property
    simpa only [rootsGaloisAction_coe, μ, map_add] using hm

section RootDatum

variable [LocallyOfFiniteType G.X.hom]
  (hT : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T).toGrp)
  (hj : IsClosedImmersion ((GroupScheme.baseChange (algebraBaseMap k L)).map j).hom.hom.left)
  {J : Type*} [Finite J]
  {P : RootDatum J
    (characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T))
    (cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T))}
  (hP : IsRootDatumOf (T := (CommGroupScheme.baseChange (algebraBaseMap k L)).obj T)
    ((GroupScheme.baseChange (algebraBaseMap k L)).map j) P)
  [Fintype (L ≃ₐ[k] L)]
  (hne : ∀ γ : roots
    (T := (CommGroupScheme.baseChange (algebraBaseMap k L)).obj T)
    (G := (GroupScheme.baseChange (algebraBaseMap k L)).obj G)
    ((GroupScheme.baseChange (algebraBaseMap k L)).map j),
    CharacterAveraging.galoisOrbitSum k L T γ.val ≠ 0)

include hT hj hP hne in
/-- A sum of actual root partners has a unique unordered decomposition into
two roots of their common Galois orbit. -/
theorem IsRootPartner.eq_or_eq_of_add_eq
    {β β' γ δ : roots (T := T_L) (G := G_L) j_L}
    (h : IsRootPartner k L j β β')
    (hγ : ∃ σ : L ≃ₐ[k] L, σ • β = γ)
    (hδ : ∃ σ : L ≃ₐ[k] L, σ • β = δ)
    (hsum : β.val + β'.val = γ.val + δ.val) :
    (γ = β ∧ δ = β') ∨ (γ = β' ∧ δ = β) := by
  classical
  by_cases h1 : γ = β
  · subst γ
    exact Or.inl ⟨rfl, Subtype.ext (add_left_cancel hsum).symm⟩
  by_cases h2 : δ = β
  · subst δ
    refine Or.inr ⟨Subtype.ext ?_, rfl⟩
    rw [add_comm γ.val β.val] at hsum
    exact (add_left_cancel hsum).symm
  exfalso
  obtain ⟨p, hp⟩ := exists_root_eq k L hP β
  obtain ⟨q, hq⟩ := exists_root_eq k L hP β'
  obtain ⟨r, hr⟩ := exists_root_eq k L hP γ
  obtain ⟨s, hs⟩ := exists_root_eq k L hP δ
  let μ : roots (T := T_L) (G := G_L) j_L := ⟨β.val + β'.val, h.2.2⟩
  obtain ⟨m, hm⟩ := exists_root_eq k L hP μ
  have hpq := isOrbitPartner k L hT hj hP h hp hq
  have hn := orbitSum_ne_zero k L hT hj hP hne
  have hmp : P.root m = P.root p + P.root q := by
    rw [hm, hp, hq]
  have hmp' : P.root m = P.root r + P.root s := by
    rw [hm, hr, hs]
    exact hsum
  have hpair : P.pairing m p = 1 := by
    rw [P.pairing_eq_add_of_root_eq_add hmp, P.pairing_same,
      hpq.symm.pairing_eq_neg_one hn]
    norm_num
  have hpair' := P.pairing_eq_add_of_root_eq_add hmp' (l := p)
  have horbit (α : roots (T := T_L) (G := G_L) j_L)
      (t : J) (ht : P.root t = α.val)
      (hα : ∃ σ : L ≃ₐ[k] L, σ • β = α) :
      ∃ σ : L ≃ₐ[k] L,
        IsRootDatumOf.galoisRootDatumActionOfClosedSplitTorus k L j hT hj hP σ • t = p := by
    obtain ⟨σ, hσ⟩ := hα
    have he :
        IsRootDatumOf.galoisRootDatumActionOfClosedSplitTorus k L j hT hj hP σ • p = t := by
      apply P.root.injective
      rw [root_smul k L hT hj hP, hp, ht, ← rootsGaloisAction_coe, hσ]
    refine ⟨σ⁻¹, ?_⟩
    rw [← he, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
  have hrp : r ≠ p := by
    intro he
    apply h1
    apply Subtype.ext
    rw [← hr, ← hp, he]
  have hsp : s ≠ p := by
    intro he
    apply h2
    apply Subtype.ext
    rw [← hs, ← hp, he]
  have a1 := RootPairing.OrbitPartner.pairing_nonpos hn (horbit γ r hr hγ) hrp
  have a2 := RootPairing.OrbitPartner.pairing_nonpos hn (horbit δ s hs hδ) hsp
  omega

end RootDatum

section Infinite

variable [Infinite k] [FiniteDimensional k L] [IsGalois k L]
  (hT : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T).toGrp)

include hT in
/-- Values on the original rational points determine a character of a split
base change of a torus over an infinite field. -/
theorem character_ext_of_rational_values {χ ψ : characterLattice T_L}
    (h : ∀ z : rationalPoints T.toGrp,
      (Lie.characterValue χ
        (rationalBaseChangePoint k L T (GaloisPointComparison.rationalCoeffEquiv k T.toGrp z)) :
          L) =
      Lie.characterValue ψ
        (rationalBaseChangePoint k L T (GaloisPointComparison.rationalCoeffEquiv k T.toGrp z))) :
    χ = ψ := by
  apply (rationalCharacters.equivCharacterLattice T_L).symm.injective
  change baseChangedCharacter k L T χ = baseChangedCharacter k L T ψ
  apply RationalCharacterSeparation.rationalCharacters_ext_of_isSplitTorus k L T.toGrp hT
  intro z
  apply Units.ext
  simpa only [rationalCharacterEval_baseChangedCharacter] using h z

end Infinite

section Separation

variable [Infinite k] [FiniteDimensional k L] [IsGalois k L]
  {β μ : roots
    (T := (CommGroupScheme.baseChange (algebraBaseMap k L)).obj T)
    (G := (GroupScheme.baseChange (algebraBaseMap k L)).obj G)
    ((GroupScheme.baseChange (algebraBaseMap k L)).map j)}
  [Algebra (rootOrbitField k L j μ) (rootOrbitField k L j β)]
  [IsScalarTower (rootOrbitField k L j μ) (rootOrbitField k L j β) L]
  [Algebra.IsQuadraticExtension (rootOrbitField k L j μ) (rootOrbitField k L j β)]
  [Algebra.IsSeparable (rootOrbitField k L j μ) (rootOrbitField k L j β)]

local instance : IsScalarTower k (rootOrbitField k L j μ) (rootOrbitField k L j β) :=
  Langlands.Algebra.QuadraticFixedFields.isScalarTower_base _ _

/-- Products of embeddings on the values of the actual descended root
character determine the unordered pair consisting of an embedding and its
composition with the quadratic conjugation. -/
def HasSeparatingCharacterValues [IsAffine T.toGrp.X.left] : Prop :=
  ∀ π τ ρ : rootOrbitField k L j β →ₐ[k] L,
    (∀ c ∈ Set.range (fun z : rationalPoints T.toGrp =>
        (rationalCharacterEval (rootOrbitCharacter k L j β)
          (GaloisPointComparison.rationalExtend k (rootOrbitField k L j β) T.toGrp z) :
            rootOrbitField k L j β)),
      τ c * ρ c = π c * π
        ((SU3Root.conjugation (rootOrbitField k L j μ)
          (rootOrbitField k L j β)).toAlgHom.restrictScalars k c)) →
      (τ = π ∧ ρ = π.comp
        ((SU3Root.conjugation (rootOrbitField k L j μ)
          (rootOrbitField k L j β)).toAlgHom.restrictScalars k)) ∨
      (τ = π.comp
        ((SU3Root.conjugation (rootOrbitField k L j μ)
          (rootOrbitField k L j β)).toAlgHom.restrictScalars k) ∧ ρ = π)

variable [LocallyOfFiniteType G.X.hom]
  (hT : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T).toGrp)
  (hj : IsClosedImmersion ((GroupScheme.baseChange (algebraBaseMap k L)).map j).hom.hom.left)
  {J : Type*} [Finite J]
  {P : RootDatum J
    (characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T))
    (cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T))}
  (hP : IsRootDatumOf (T := (CommGroupScheme.baseChange (algebraBaseMap k L)).obj T)
    ((GroupScheme.baseChange (algebraBaseMap k L)).map j) P)
  (hne : ∀ γ : roots
    (T := (CommGroupScheme.baseChange (algebraBaseMap k L)).obj T)
    (G := (GroupScheme.baseChange (algebraBaseMap k L)).obj G)
    ((GroupScheme.baseChange (algebraBaseMap k L)).map j),
    CharacterAveraging.galoisOrbitSum k L T γ.val ≠ 0)

include hT hj hP hne in
/-- Actual root-partner characters over an infinite base field have the
embedding-product separation required by the unitary Heisenberg construction. -/
theorem hasSeparatingCharacterValues [IsAffine T.toGrp.X.left]
    {β' : roots (T := T_L) (G := G_L) j_L}
    (h : IsRootPartner k L j β β') (hμ : μ.val = β.val + β'.val) :
    HasSeparatingCharacterValues k L j (β := β) (μ := μ) := by
  classical
  let e := rootOrbitEmbeddingEquiv k L j β
  let q := (SU3Root.conjugation (rootOrbitField k L j μ)
    (rootOrbitField k L j β)).toAlgHom.restrictScalars k
  intro π τ ρ hval
  obtain ⟨σ, hσ⟩ := Langlands.Algebra.FiniteGaloisOrbits.restriction_surjective k L
    (MulAction.stabilizer (L ≃ₐ[k] L) β) π
  obtain ⟨s, hs⟩ := h.1
  have hcomp : π.comp q =
      Langlands.Algebra.FiniteGaloisOrbits.restriction k L
        (MulAction.stabilizer (L ≃ₐ[k] L) β) (σ * s) := by
    ext x
    rw [← hσ]
    change σ (SU3Root.conjugation (rootOrbitField k L j μ)
      (rootOrbitField k L j β) x : L) = σ (s (x : L))
    rw [conjugation_apply k L hT hj hP hne h hμ hs]
  have hp : (e.symm π : roots (T := T_L) (G := G_L) j_L) = σ • β := by
    rw [← hσ]
    exact Langlands.Algebra.FiniteGaloisOrbits.orbitEmbeddingEquiv_symm_restriction k L β σ
  have hpbar : (e.symm (π.comp q) : roots (T := T_L) (G := G_L) j_L) = σ • β' := by
    rw [hcomp]
    change ((Langlands.Algebra.FiniteGaloisOrbits.orbitEmbeddingEquiv k L β).symm
      (Langlands.Algebra.FiniteGaloisOrbits.restriction k L
        (MulAction.stabilizer (L ≃ₐ[k] L) β) (σ * s)) :
          roots (T := T_L) (G := G_L) j_L) = _
    rw [Langlands.Algebra.FiniteGaloisOrbits.orbitEmbeddingEquiv_symm_restriction,
      mul_smul, hs]
  have hpartner : IsRootPartner k L j (e.symm π).val (e.symm (π.comp q)).val := by
    rw [hp, hpbar]
    exact h.smul k L j σ
  have hsum : (e.symm π).val.val + (e.symm (π.comp q)).val.val =
      (e.symm τ).val.val + (e.symm ρ).val.val := by
    apply character_ext_of_rational_values k L hT
    intro z
    simp only [IndependentWeightProduct.characterValue_add, Units.val_mul]
    have hc : τ (rootOrbitCharacterValue k L j β
        (GaloisPointComparison.rationalCoeffEquiv k T.toGrp z)) *
        ρ (rootOrbitCharacterValue k L j β
          (GaloisPointComparison.rationalCoeffEquiv k T.toGrp z)) =
      π (rootOrbitCharacterValue k L j β
        (GaloisPointComparison.rationalCoeffEquiv k T.toGrp z)) *
        (π.comp q) (rootOrbitCharacterValue k L j β
          (GaloisPointComparison.rationalCoeffEquiv k T.toGrp z)) := by
      simpa only [rationalCharacterEval_rootOrbitCharacter, q, AlgHom.comp_apply] using
        hval _ ⟨z, rfl⟩
    have heval (η : rootOrbitField k L j β →ₐ[k] L) :
        η (rootOrbitCharacterValue k L j β
          (GaloisPointComparison.rationalCoeffEquiv k T.toGrp z)) =
        Lie.characterValue (e.symm η).val.val
          (rationalBaseChangePoint k L T
            (GaloisPointComparison.rationalCoeffEquiv k T.toGrp z)) := by
      simpa only [e, Equiv.apply_symm_apply] using
        rootOrbitEmbeddingEquiv_characterValue k L j β (e.symm η)
          (GaloisPointComparison.rationalCoeffEquiv k T.toGrp z)
    rw [heval τ, heval ρ, heval π, heval (π.comp q)] at hc
    exact hc.symm
  have horbit (η : rootOrbitField k L j β →ₐ[k] L) :
      ∃ g : L ≃ₐ[k] L, g • (e.symm π).val = (e.symm η).val := by
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp (e.symm η).property
    refine ⟨g * σ⁻¹, ?_⟩
    rw [hp, mul_smul, inv_smul_smul]
    exact hg
  have heq (η η' : rootOrbitField k L j β →ₐ[k] L)
      (he : (e.symm η).val = (e.symm η').val) : η = η' :=
    e.symm.injective (Subtype.ext he)
  rcases hpartner.eq_or_eq_of_add_eq k L j hT hj hP hne
      (horbit τ) (horbit ρ) hsum with ⟨hτ, hρ⟩ | ⟨hτ, hρ⟩
  · exact Or.inl ⟨heq τ π hτ, heq ρ (π.comp q) hρ⟩
  · exact Or.inr ⟨heq τ (π.comp q) hτ, heq ρ π hρ⟩

end Separation

end Langlands.GroupScheme.RootPartnerFields
