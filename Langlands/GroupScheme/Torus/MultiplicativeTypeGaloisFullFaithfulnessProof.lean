import Langlands.GroupScheme.Torus.MultiplicativeTypeGaloisFullFaithfulnessStatement
import Langlands.GroupScheme.Torus.DiagonalizableCharacterProof
import Langlands.GroupScheme.Torus.MultiplicativeTypeSplitCategory
import Langlands.GroupScheme.Torus.FiniteGaloisCharacterDescent
import Langlands.GroupScheme.Torus.WeilRestrictionNormOneCharacters

/-! # Finite Galois full faithfulness for groups of multiplicative type: proof -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace MultiplicativeTypeGaloisFullFaithfulness

open DiagonalizableCharacter

section Split

variable {R : CommRingCat.{u}} {Λ Λ' : Type u} [AddCommGroup Λ] [AddCommGroup Λ']

/-- Evaluation characters of `D(Λ)` are additive in the evaluated element. -/
theorem evalCharacter_add (a b : Λ) :
    evalCharacter R Λ (a + b) = evalCharacter R Λ a + evalCharacter R Λ b := by
  apply CommGroupScheme.hom_ext_points
  intro U x
  apply (Gm.pointsEquiv _ U).injective
  rw [comp_groupHom_add, map_mul, evalCharacter_apply, evalCharacter_apply,
    evalCharacter_apply, ofAdd_add, map_mul]

/-- Homomorphisms into `D(Λ')` are determined by their pullbacks of the evaluation
characters. The source is an arbitrary commutative group scheme. -/
theorem hom_ext_evalCharacter {G : CommGroupScheme (Spec R)}
    {f g : G ⟶ Diagonalizable.groupScheme R Λ'}
    (h : ∀ m : Λ', f ≫ evalCharacter R Λ' m = g ≫ evalCharacter R Λ' m) : f = g := by
  apply CommGroupScheme.hom_ext_points
  intro U x
  apply (Diagonalizable.characterPointsEquiv R Λ' U).injective
  apply MonoidHom.ext
  intro m
  have h₁ := evalCharacter_apply R Λ' m.toAdd U (x ≫ (CommGroupScheme.groupHom f).hom.hom)
  have h₂ := evalCharacter_apply R Λ' m.toAdd U (x ≫ (CommGroupScheme.groupHom g).hom.hom)
  rw [ofAdd_toAdd] at h₁ h₂
  rw [← h₁, ← h₂, ← comp_groupHom_comp, ← comp_groupHom_comp, h]

/-- Homomorphisms into a group isomorphic to `D(Λ')` are determined by their pullbacks of
all characters. -/
theorem hom_ext_of_iso_diagonalizable {G H : CommGroupScheme (Spec R)}
    (i' : H ≅ Diagonalizable.groupScheme R Λ') {f g : G ⟶ H}
    (h : ∀ χ : characterLattice H, f ≫ χ = g ≫ χ) : f = g := by
  rw [← cancel_mono i'.hom]
  apply hom_ext_evalCharacter
  intro m
  simpa only [Category.assoc] using h (i'.hom ≫ evalCharacter R Λ' m)

/-- The diagonalizable homomorphism `D(g) : D(Λ) ⟶ D(Λ')` pulls evaluation at `m'` back to
evaluation at `g m'`. -/
theorem restrictMap_comp_evalCharacter (g : Λ' →+ Λ) (m' : Λ') :
    (Additive.ofMul (Diagonalizable.restrictMap R g) :
        Diagonalizable.groupScheme R Λ ⟶ Diagonalizable.groupScheme R Λ') ≫
      evalCharacter R Λ' m' = evalCharacter R Λ (g m') := by
  apply CommGroupScheme.hom_ext_points
  intro U x
  apply (Gm.pointsEquiv _ U).injective
  change Gm.pointsEquiv _ U ((x ≫ (Diagonalizable.restrictMap R g).hom.hom) ≫
    (CommGroupScheme.groupHom (evalCharacter R Λ' m')).hom.hom) = _
  rw [evalCharacter_apply, evalCharacter_apply]
  exact Diagonalizable.pointsEquiv_restrictMap _ g x m'

end Split

section Field

variable (K : Type u) [Field K] (Λ : Type u) [AddCommGroup Λ]

variable {K} {M M' : Type u} [AddCommGroup M] [AddCommGroup M']

/-- Over a field, every additive map between the actual characters of two groups isomorphic
to diagonalizable groups is the character pullback of a homomorphism. Torsion is allowed. -/
theorem exists_hom_of_characterMap {G H : CommGroupScheme (Spec (CommRingCat.of K))}
    (i : G ≅ Diagonalizable.groupScheme (CommRingCat.of K) M)
    (i' : H ≅ Diagonalizable.groupScheme (CommRingCat.of K) M')
    (F : characterLattice H →+ characterLattice G) :
    ∃ f : G ⟶ H, ∀ χ : characterLattice H, f ≫ χ = F χ := by
  let e := evalCharacterEquiv K M
  let e' := evalCharacterEquiv K M'
  let Φ : characterLattice (Diagonalizable.groupScheme (CommRingCat.of K) M') →+
      characterLattice (Diagonalizable.groupScheme (CommRingCat.of K) M) :=
    AddMonoidHom.mk' (fun ψ => i.inv ≫ F (i'.hom ≫ ψ)) (fun ψ ψ' => by
      rw [Preadditive.comp_add, map_add, Preadditive.comp_add])
  let g : M' →+ M := e.symm.toAddMonoidHom.comp (Φ.comp e'.toAddMonoidHom)
  refine ⟨i.hom ≫ (Additive.ofMul (Diagonalizable.restrictMap (CommRingCat.of K) g) :
      Diagonalizable.groupScheme (CommRingCat.of K) M ⟶
        Diagonalizable.groupScheme (CommRingCat.of K) M') ≫ i'.inv, fun χ => ?_⟩
  obtain ⟨m', hm'⟩ := e'.surjective (i'.inv ≫ χ)
  have hg : e (g m') = Φ (e' m') := e.apply_symm_apply _
  calc (i.hom ≫ (Additive.ofMul (Diagonalizable.restrictMap (CommRingCat.of K) g) :
        Diagonalizable.groupScheme (CommRingCat.of K) M ⟶
          Diagonalizable.groupScheme (CommRingCat.of K) M') ≫ i'.inv) ≫ χ
      = i.hom ≫ ((Additive.ofMul (Diagonalizable.restrictMap (CommRingCat.of K) g) :
          Diagonalizable.groupScheme (CommRingCat.of K) M ⟶
            Diagonalizable.groupScheme (CommRingCat.of K) M') ≫ e' m') := by
        rw [hm', Category.assoc, Category.assoc]
    _ = i.hom ≫ Φ (e' m') := by
        rw [evalCharacterEquiv_apply]
        refine (congrArg (i.hom ≫ ·) (restrictMap_comp_evalCharacter g m')).trans ?_
        rw [← evalCharacterEquiv_apply, hg]
        rfl
    _ = F χ := by
        change i.hom ≫ i.inv ≫ F (i'.hom ≫ e' m') = F χ
        rw [hm', Iso.hom_inv_id_assoc, Iso.hom_inv_id_assoc]

end Field

section Galois

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
  {T T' : CommGroupScheme (Spec (CommRingCat.of k))} {M' : Type u} [AddCommGroup M']

/-- If the target becomes diagonalizable over `L`, equivariance of character pullback forces
an actual homomorphism over `L` to commute with canonical Galois transport. -/
theorem galoisHomTransport_eq_of_diagonalizable
    (i' : (CommGroupScheme.baseChange (algebraBaseMap k L)).obj T' ≅
      Diagonalizable.groupScheme (CommRingCat.of L) M')
    (f : (CommGroupScheme.baseChange (algebraBaseMap k L)).obj T ⟶
      (CommGroupScheme.baseChange (algebraBaseMap k L)).obj T')
    (hf : ∀ (σ : L ≃ₐ[k] L)
      (χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T')),
      characterLattice.galoisRepresentation k L T σ (f ≫ χ) =
        f ≫ characterLattice.galoisRepresentation k L T' σ χ)
    (σ : L ≃ₐ[k] L) :
    galoisHomTransport σ f = f := by
  apply hom_ext_of_iso_diagonalizable i'
  intro χ
  obtain ⟨ψ, hψ⟩ :=
    (Representation.apply_bijective (characterLattice.galoisRepresentation k L T') σ).2 χ
  rw [← hψ, galoisHomTransport_comp, hf]

variable [FiniteDimensional k L] [IsGalois k L]

/-- Equivariance of the pullback of actual characters gives canonical descent compatibility
when the target becomes diagonalizable over the finite Galois extension. -/
theorem compatible_of_equivariant_characterPullback_of_diagonalizable
    (i' : (CommGroupScheme.baseChange (algebraBaseMap k L)).obj T' ≅
      Diagonalizable.groupScheme (CommRingCat.of L) M')
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
  exact (congrArg CommGroupScheme.groupHom
    (galoisHomTransport_eq_of_diagonalizable i' f hf σ)).symm

end Galois

end MultiplicativeTypeGaloisFullFaithfulness

open MultiplicativeTypeGaloisFullFaithfulness in
/-- **Finite Galois full faithfulness for groups of multiplicative type** (derived from Milne,
*Algebraic Groups* (2017), Theorem 12.23). -/
theorem multiplicativeTypeGaloisFullFaithfulness :
    MultiplicativeTypeGaloisFullFaithfulnessStatement.{u} := by
  intro k L _ _ _ _ _ T T' M M' _ _ _ _ i i' F
  constructor
  · intro hF
    let : Flat (algebraBaseMap k L) := (fieldExtension_fpqc k L).2.1
    let : Surjective (algebraBaseMap k L) := (fieldExtension_fpqc k L).1
    let : QuasiCompact (algebraBaseMap k L) := (fieldExtension_fpqc k L).2.2
    obtain ⟨f, hfF⟩ := exists_hom_of_characterMap i i' F
    have hf : ∀ (σ : L ≃ₐ[k] L)
        (χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T')),
        characterLattice.galoisRepresentation k L T σ (f ≫ χ) =
          f ≫ characterLattice.galoisRepresentation k L T' σ χ := by
      intro σ χ
      rw [hfF, hfF]
      exact (hF σ χ).symm
    let hc := compatible_of_equivariant_characterPullback_of_diagonalizable i' f hf
    let a : T ⟶ T' := Additive.ofMul
      (Descent.FpqcHomDescent.hom (algebraBaseMap k L) (CommGroupScheme.groupHom f) hc)
    have ha : (CommGroupScheme.baseChange (algebraBaseMap k L)).map a = f :=
      congrArg Additive.ofMul
        (Descent.FpqcHomDescent.baseChange_hom (algebraBaseMap k L)
          (CommGroupScheme.groupHom f) hc)
    refine ⟨a, fun χ => ?_, fun b hb => ?_⟩
    · rw [ha]
      exact hfF χ
    · have hbf : (CommGroupScheme.baseChange (algebraBaseMap k L)).map b = f :=
        hom_ext_of_iso_diagonalizable i' fun χ => by rw [hb, hfF]
      exact congrArg Additive.ofMul
        (Descent.FpqcHomDescent.unique (algebraBaseMap k L) (CommGroupScheme.groupHom f) hc
          (CommGroupScheme.groupHom b) (congrArg CommGroupScheme.groupHom hbf))
  · rintro ⟨a, ha, -⟩ σ χ
    rw [← ha, ← ha, characterLattice.galoisRepresentation_precompose]

end Langlands.GroupScheme
