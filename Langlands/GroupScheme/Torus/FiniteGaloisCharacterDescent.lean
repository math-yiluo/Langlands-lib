import Langlands.GroupScheme.Torus.CharacterMapHom
import Langlands.GroupScheme.Descent.FpqcHomDescent
import Langlands.GroupScheme.Rational.UnipotentRadicalDescent

/-! # Finite Galois descent of equivariant character maps -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace Descent

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
  [FiniteDimensional k L] [IsGalois k L]
  {C D : GroupScheme (Spec (CommRingCat.of k))}

/-- A homomorphism between base changes respects the canonical descent data if
it commutes with every finite Galois transport. -/
theorem compatible_of_galois
    (f : (GroupScheme.baseChange (fieldMap k L)).obj C ⟶
      (GroupScheme.baseChange (fieldMap k L)).obj D)
    (hf : ∀ σ : L ≃ₐ[k] L,
      f ≫ (descentBaseChangeIso (fieldMap k L) (galoisBaseMap k L σ)
        (galoisBaseMap_over k L σ) D).inv =
      (descentBaseChangeIso (fieldMap k L) (galoisBaseMap k L σ)
        (galoisBaseMap_over k L σ) C).inv ≫
        (GroupScheme.baseChange (galoisBaseMap k L σ)).map f) :
    Compatible (canonicalDatum (fieldMap k L) C)
      (canonicalDatum (fieldMap k L) D) f := by
  apply FiniteComponents.groupHom_ext (finiteGaloisComponent k L)
  intro j
  let q := finiteGaloisComponent k L j
  let a := galoisBaseMap k L (galoisIndexEquiv k L j)
  have hq₁ : q ≫ fst (fieldMap k L) = 𝟙 _ := finiteGaloisComponent_fst k L j
  have hq₂ : q ≫ snd (fieldMap k L) = a := finiteGaloisComponent_snd k L j
  apply (cancel_epi (pullbackComparison (fst (fieldMap k L)) q (𝟙 _) hq₁
    ((GroupScheme.baseChange (fieldMap k L)).obj C)).inv).mp
  apply (cancel_mono (pullbackComparison (snd (fieldMap k L)) q a hq₂
    ((GroupScheme.baseChange (fieldMap k L)).obj D)).hom).mp
  change pullHom q hq₁ hq₂
      ((GroupScheme.baseChange (fst (fieldMap k L))).map f ≫
        (canonicalOverlap (fieldMap k L) D).hom) =
    pullHom q hq₁ hq₂
      ((canonicalOverlap (fieldMap k L) C).hom ≫
        (GroupScheme.baseChange (snd (fieldMap k L))).map f)
  rw [pullHom_comp q hq₁ hq₁ hq₂, pullHom_map,
    pullHom_comp q hq₁ hq₂ hq₂, pullHom_map]
  rw [← pullIso_hom, ← pullIso_hom,
    pullIso_canonicalOverlap_eq (fieldMap k L) D a
      (galoisBaseMap_over k L (galoisIndexEquiv k L j)),
    pullIso_canonicalOverlap_eq (fieldMap k L) C a
      (galoisBaseMap_over k L (galoisIndexEquiv k L j))]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  have hid : (GroupScheme.baseChange (𝟙 _)).map f ≫
      (baseChangeIdIso ((GroupScheme.baseChange (fieldMap k L)).obj D)).hom =
    (baseChangeIdIso ((GroupScheme.baseChange (fieldMap k L)).obj C)).hom ≫ f :=
    (((Functor.mapGrpNatIso Over.pullbackId) ≪≫ Functor.mapGrpIdIso).hom.naturality f)
  rw [← Category.assoc, hid, Category.assoc, hf]

end Descent

section CharacterMaps

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
  {T T' : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Conjugation of a homomorphism of base-changed groups by canonical Galois
transport, expressed in the category of commutative group schemes. -/
def galoisHomTransport (σ : L ≃ₐ[k] L)
    (f : (CommGroupScheme.baseChange (algebraBaseMap k L)).obj T ⟶
      (CommGroupScheme.baseChange (algebraBaseMap k L)).obj T') :
    (CommGroupScheme.baseChange (algebraBaseMap k L)).obj T ⟶
      (CommGroupScheme.baseChange (algebraBaseMap k L)).obj T' :=
  Additive.ofMul
    ((descentBaseChangeIso (algebraBaseMap k L) (galoisBaseMap k L σ)
        (galoisBaseMap_over k L σ) T.toGrp).inv ≫
      (GroupScheme.baseChange (galoisBaseMap k L σ)).map (CommGroupScheme.groupHom f) ≫
      (descentBaseChangeIso (algebraBaseMap k L) (galoisBaseMap k L σ)
        (galoisBaseMap_over k L σ) T'.toGrp).hom)

/-- Conjugation of homomorphisms intertwines transport of characters with
pullback of characters. -/
theorem galoisHomTransport_comp (σ : L ≃ₐ[k] L)
    (f : (CommGroupScheme.baseChange (algebraBaseMap k L)).obj T ⟶
      (CommGroupScheme.baseChange (algebraBaseMap k L)).obj T')
    (χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T')) :
    galoisHomTransport σ f ≫ characterLattice.galoisRepresentation k L T' σ χ =
      characterLattice.galoisRepresentation k L T σ (f ≫ χ) := by
  change Additive.ofMul
      (((descentBaseChangeIso (algebraBaseMap k L) (galoisBaseMap k L σ)
          (galoisBaseMap_over k L σ) T.toGrp).inv ≫
        (GroupScheme.baseChange (galoisBaseMap k L σ)).map (CommGroupScheme.groupHom f) ≫
        (descentBaseChangeIso (algebraBaseMap k L) (galoisBaseMap k L σ)
          (galoisBaseMap_over k L σ) T'.toGrp).hom) ≫
        transportCharacter (algebraBaseMap k L) (galoisBaseMap k L σ)
          (galoisBaseMap_over k L σ) T'.toGrp (CommGroupScheme.groupHom χ)) =
    Additive.ofMul (transportCharacter (algebraBaseMap k L) (galoisBaseMap k L σ)
      (galoisBaseMap_over k L σ) T.toGrp (CommGroupScheme.groupHom f ≫
        CommGroupScheme.groupHom χ))
  simp only [transportCharacter, Category.assoc, Iso.hom_inv_id_assoc, Functor.map_comp]

/-- For a split target, equivariance of character pullback forces the actual
homomorphism to commute with canonical Galois transport. -/
theorem galoisHomTransport_eq
    (hT' : IsSplitTorus
      ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T').toGrp)
    (f : (CommGroupScheme.baseChange (algebraBaseMap k L)).obj T ⟶
      (CommGroupScheme.baseChange (algebraBaseMap k L)).obj T')
    (hf : ∀ (σ : L ≃ₐ[k] L)
      (χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T')),
      characterLattice.galoisRepresentation k L T σ (f ≫ χ) =
        f ≫ characterLattice.galoisRepresentation k L T' σ χ)
    (σ : L ≃ₐ[k] L) :
    galoisHomTransport σ f = f := by
  apply hT'.hom_ext_of_characters
  intro χ
  obtain ⟨ψ, hψ⟩ :=
    (Representation.apply_bijective (characterLattice.galoisRepresentation k L T') σ).2 χ
  rw [← hψ, galoisHomTransport_comp, hf]

variable [FiniteDimensional k L] [IsGalois k L]

/-- Equivariance of the pullback of actual characters gives canonical descent
compatibility when the target is split over the finite Galois extension. -/
theorem compatible_of_equivariant_characterPullback
    (hT' : IsSplitTorus
      ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T').toGrp)
    (f : (CommGroupScheme.baseChange (algebraBaseMap k L)).obj T ⟶
      (CommGroupScheme.baseChange (algebraBaseMap k L)).obj T')
    (hf : ∀ (σ : L ≃ₐ[k] L)
      (χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T')),
      characterLattice.galoisRepresentation k L T σ (f ≫ χ) =
        f ≫ characterLattice.galoisRepresentation k L T' σ χ) :
    Descent.Compatible (Descent.canonicalDatum (algebraBaseMap k L) T.toGrp)
      (Descent.canonicalDatum (algebraBaseMap k L) T'.toGrp) (CommGroupScheme.groupHom f) := by
  apply Descent.compatible_of_galois
  intro σ
  apply (cancel_mono (descentBaseChangeIso (algebraBaseMap k L) (galoisBaseMap k L σ)
    (galoisBaseMap_over k L σ) T'.toGrp).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (congrArg CommGroupScheme.groupHom (galoisHomTransport_eq hT' f hf σ)).symm

/-- Every equivariant additive map out of the characters of a torus split by
`L/k` is the character pullback of exactly one ground-field homomorphism.
The source is an arbitrary commutative group scheme. -/
theorem IsSplitTorus.existsUnique_hom_of_equivariant_characterMap
    (hT' : IsSplitTorus
      ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T').toGrp)
    (F : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T') →+
      characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T))
    (hF : ∀ (σ : L ≃ₐ[k] L)
      (χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T')),
      F (characterLattice.galoisRepresentation k L T' σ χ) =
        characterLattice.galoisRepresentation k L T σ (F χ)) :
    ∃! a : T ⟶ T',
      ∀ χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T'),
        (CommGroupScheme.baseChange (algebraBaseMap k L)).map a ≫ χ = F χ := by
  let : Flat (algebraBaseMap k L) := (fieldExtension_fpqc k L).2.1
  let : Surjective (algebraBaseMap k L) := (fieldExtension_fpqc k L).1
  let : QuasiCompact (algebraBaseMap k L) := (fieldExtension_fpqc k L).2.2
  let f := hT'.homOfCharacterMap F
  have hf : ∀ (σ : L ≃ₐ[k] L)
      (χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T')),
      characterLattice.galoisRepresentation k L T σ (f ≫ χ) =
        f ≫ characterLattice.galoisRepresentation k L T' σ χ := by
    intro σ χ
    simp only [f, IsSplitTorus.homOfCharacterMap_comp]
    exact (hF σ χ).symm
  let hc := compatible_of_equivariant_characterPullback hT' f hf
  let a : T ⟶ T' := Additive.ofMul
    (Descent.FpqcHomDescent.hom (algebraBaseMap k L) (CommGroupScheme.groupHom f) hc)
  have ha : (CommGroupScheme.baseChange (algebraBaseMap k L)).map a = f :=
    congrArg Additive.ofMul
      (Descent.FpqcHomDescent.baseChange_hom (algebraBaseMap k L)
        (CommGroupScheme.groupHom f) hc)
  refine ⟨a, fun χ => ?_, fun b hb => ?_⟩
  · rw [ha]
    exact hT'.homOfCharacterMap_comp F χ
  · have hbf : (CommGroupScheme.baseChange (algebraBaseMap k L)).map b = f :=
      hT'.eq_homOfCharacterMap F hb
    exact congrArg Additive.ofMul
      (Descent.FpqcHomDescent.unique (algebraBaseMap k L) (CommGroupScheme.groupHom f) hc
        (CommGroupScheme.groupHom b) (congrArg CommGroupScheme.groupHom hbf))

/-- An equivariant equivalence of the actual characters of two groups split
over a finite Galois extension is realized by a ground-field isomorphism. -/
theorem IsSplitTorus.exists_iso_of_equivariant_characterEquiv
    (hT : IsSplitTorus
      ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T).toGrp)
    (hT' : IsSplitTorus
      ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T').toGrp)
    (e : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T') ≃+
      characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T))
    (he : ∀ (σ : L ≃ₐ[k] L)
      (χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T')),
      e (characterLattice.galoisRepresentation k L T' σ χ) =
        characterLattice.galoisRepresentation k L T σ (e χ)) :
    ∃ a : T ≅ T',
      ∀ χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T'),
        (CommGroupScheme.baseChange (algebraBaseMap k L)).map a.hom ≫ χ = e χ := by
  let : Flat (algebraBaseMap k L) := (fieldExtension_fpqc k L).2.1
  let : Surjective (algebraBaseMap k L) := (fieldExtension_fpqc k L).1
  let : QuasiCompact (algebraBaseMap k L) := (fieldExtension_fpqc k L).2.2
  obtain ⟨a, ha, _⟩ := hT'.existsUnique_hom_of_equivariant_characterMap e.toAddMonoidHom he
  have hbij : Function.Bijective
      (fun χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T') =>
        (CommGroupScheme.baseChange (algebraBaseMap k L)).map a ≫ χ) := by
    constructor
    · intro χ ψ h
      apply e.injective
      exact (ha χ).symm.trans (h.trans (ha ψ))
    · intro χ
      obtain ⟨ψ, hψ⟩ := e.surjective χ
      exact ⟨ψ, (ha ψ).trans hψ⟩
  let eL := hT.isoOfBijectiveCharacterPullback hT'
    ((CommGroupScheme.baseChange (algebraBaseMap k L)).map a) hbij
  let eG :
      ((GroupScheme.baseChange (algebraBaseMap k L)).obj T.toGrp) ≅
        ((GroupScheme.baseChange (algebraBaseMap k L)).obj T'.toGrp) :=
    ⟨CommGroupScheme.groupHom eL.hom, CommGroupScheme.groupHom eL.inv,
      congrArg CommGroupScheme.groupHom eL.hom_inv_id,
      congrArg CommGroupScheme.groupHom eL.inv_hom_id⟩
  have hLocal : IsIso
      ((GroupScheme.baseChange (algebraBaseMap k L)).map (CommGroupScheme.groupHom a)) := by
    change IsIso (CommGroupScheme.groupHom
      ((CommGroupScheme.baseChange (algebraBaseMap k L)).map a))
    rw [← hT.isoOfBijectiveCharacterPullback_hom hT'
      ((CommGroupScheme.baseChange (algebraBaseMap k L)).map a) hbij]
    change IsIso eG.hom
    exact eG.isIso_hom
  let := isIso_of_baseChange (algebraBaseMap k L) (CommGroupScheme.groupHom a)
  exact ⟨CommGroupScheme.isoOfGroupIso (asIso (CommGroupScheme.groupHom a)), ha⟩

end CharacterMaps

end Langlands.GroupScheme
