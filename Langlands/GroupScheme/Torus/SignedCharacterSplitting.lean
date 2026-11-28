import Langlands.GroupScheme.Rational.RootFixedTorusSplitting
import Langlands.GroupScheme.Torus.LatticeGaloisScalarExtension
import Langlands.GroupScheme.Torus.MultiplicativeTypeAbsoluteEquivalenceProof

/-! # Splitting tori with signed absolute character action -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

open StarActionFiniteStage MultiplicativeTypeAbsoluteEquivalence

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

private theorem signedCharacters_of_finiteStage
    {F : Type u} [Field F] (T : CommGroupScheme (Spec (CommRingCat.of F)))
    (L : IntermediateField F (SeparableClosure F)) [FiniteDimensional F L] [IsGalois F L]
    (hsplit : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap F L)).obj T).toGrp)
    (hSign : ∀ σ : SeparableClosure F ≃ₐ[F] SeparableClosure F,
      (∀ χ, characterLattice.galoisRepresentation F (SeparableClosure F) T σ χ = χ) ∨
      (∀ χ, characterLattice.galoisRepresentation F (SeparableClosure F) T σ χ = -χ))
    (σ : L ≃ₐ[F] L) :
    characterLattice.galoisRepresentation F L T σ = 1 ∨
      characterLattice.galoisRepresentation F L T σ = -1 := by
  let E := SeparableClosure F
  let b := algebraBaseMap F L
  let j := algebraBaseMap L E
  let c := algebraBaseMap F E
  let hc : j ≫ b = c := algebraBaseMap_tower L E
  let TL := (CommGroupScheme.baseChange b).obj T
  let i := towerIsoOf b j T c hc
  let f := (characterLattice.congr i).symm.toAddMonoidHom.comp (characterLattice.baseChange j TL)
  have hf : Function.Injective f :=
    (characterLattice.congr i).symm.injective.comp
      (hsplit.characterLattice_baseChange_bijective j TL).injective
  obtain ⟨τ, hτ⟩ := AlgEquiv.restrictNormalHom_surjective E σ
  have h (χ : characterLattice TL) :
      f (characterLattice.galoisRepresentation F L T σ χ) =
        characterLattice.galoisRepresentation F E T τ (f χ) := by
    have hcomm := galoisBaseMap_restrictNormal L τ
    rw [hτ] at hcomm
    exact towerCharacterOf_transport b j T c hc (galoisBaseMap F L σ) (galoisBaseMap_over F L σ)
      (galoisBaseMap F E τ) (galoisBaseMap_over F E τ) hcomm χ
  rcases hSign τ with hplus | hminus
  · left
    ext χ
    exact hf ((h χ).trans (hplus (f χ)))
  · right
    ext χ
    apply hf
    change f (characterLattice.galoisRepresentation F L T σ χ) = f (-χ)
    rw [h, hminus, map_neg]

private theorem isSplitTorus_fixedField_characterKernel
    {F L : Type u} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    (T : CommGroupScheme (Spec (CommRingCat.of F)))
    (hsplit : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap F L)).obj T).toGrp) :
    let Q := IntermediateField.fixedField (characterLattice.galoisRepresentation F L T).asGroupHom.ker
    IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap F Q)).obj T).toGrp := by
  dsimp only
  let ρ := characterLattice.galoisRepresentation F L T
  let N := ρ.asGroupHom.ker
  let Q := IntermediateField.fixedField N
  let TQ := (CommGroupScheme.baseChange (algebraBaseMap F Q)).obj T
  have hTQL : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap Q L)).obj TQ).toGrp :=
    (IsSplitTorus.baseChange_fieldTower_iff F Q L T.toGrp).mp hsplit
  apply hTQL.of_galoisFixedCharacters
  intro σ χ
  have hσ : σ.restrictScalars F ∈ N := by
    rw [show N = Q.fixingSubgroup from (IntermediateField.fixingSubgroup_fixedField N).symm]
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mpr
      fun x hx => σ.commutes (⟨x, hx⟩ : Q)
  have hρ : ρ (σ.restrictScalars F) = 1 :=
    congrArg Units.val (MonoidHom.mem_ker.mp hσ)
  let e := characterLattice.scalarExtensionGaloisEquiv (algebraBaseMap_tower Q L) T
  obtain ⟨χ', rfl⟩ := e.toLinearEquiv.surjective χ
  have he : e.toLinearEquiv (ρ (σ.restrictScalars F) χ') =
      characterLattice.galoisRepresentation Q L TQ σ (e.toLinearEquiv χ') :=
    LinearMap.congr_fun (e.isIntertwining' σ) χ'
  rw [hρ] at he
  exact he.symm

private theorem finrank_fixedField_le_two_of_signed
    {F L : Type u} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    {M : Type u} [AddCommGroup M] (ρ : Representation ℤ (L ≃ₐ[F] L) M)
    (h : ∀ σ, ρ σ = 1 ∨ ρ σ = -1) :
    Module.finrank F (IntermediateField.fixedField ρ.asGroupHom.ker) ≤ 2 := by
  rw [← IsGalois.card_aut_eq_finrank, ← Nat.card_congr
    (IsGalois.normalAutEquivQuotient ρ.asGroupHom.ker).toEquiv,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ.asGroupHom).toEquiv]
  let s : Set (Module.End ℤ M) := {1, -1}
  have hs (x : ρ.asGroupHom.range) : x.val.val ∈ s := by
    obtain ⟨σ, hσ⟩ := x.property
    rw [← hσ]
    change ρ σ ∈ s
    rcases h σ with hσ | hσ <;> simp [s, hσ]
  let f (x : ρ.asGroupHom.range) : s := ⟨x.val.val, hs x⟩
  refine (Nat.card_le_card_of_injective f (fun x y hx => Subtype.ext (Units.ext
    (congrArg Subtype.val hx)))).trans ?_
  change s.ncard ≤ 2
  simpa only [s, Set.ncard_singleton] using
    Set.ncard_insert_le (1 : Module.End ℤ M) {(-1 : Module.End ℤ M)}

/-- A torus on whose absolute characters every Galois element acts as the
identity or as simultaneous negation splits over the ground field or a
quadratic Galois extension. -/
theorem IsTorus.isSplit_or_exists_quadratic_of_signed_characters
    {F : Type u} [Field F] {T : CommGroupScheme (Spec (CommRingCat.of F))} (hT : IsTorus T.toGrp)
    (hSign : ∀ σ : SeparableClosure F ≃ₐ[F] SeparableClosure F,
      (∀ χ, characterLattice.galoisRepresentation F (SeparableClosure F) T σ χ = χ) ∨
      (∀ χ, characterLattice.galoisRepresentation F (SeparableClosure F) T σ χ = -χ)) :
    IsSplitTorus T.toGrp ∨
      ∃ (Q : Type u) (_ : Field Q) (_ : Algebra F Q) (_ : FiniteDimensional F Q) (_ : IsGalois F Q),
        Module.finrank F Q = 2 ∧
          IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap F Q)).obj T).toGrp := by
  obtain ⟨K, _, _, _, _, hTK⟩ := torusFiniteGaloisSplitting F T.toGrp hT
  let φ : K →ₐ[F] SeparableClosure F := IsSepClosed.lift
  let : Algebra K (SeparableClosure F) := φ.toRingHom.toAlgebra
  let : IsScalarTower F K (SeparableClosure F) :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  let L := IntermediateField.normalClosure F K (SeparableClosure F)
  have hTL : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap F L)).obj T).toGrp :=
    hTK.baseChange_fieldTower F K L T.toGrp
  let ρ := characterLattice.galoisRepresentation F L T
  let Q := IntermediateField.fixedField ρ.asGroupHom.ker
  have hdeg : Module.finrank F Q ≤ 2 :=
    finrank_fixedField_le_two_of_signed ρ (signedCharacters_of_finiteStage T L hTL hSign)
  have hQsplit := isSplitTorus_fixedField_characterKernel T hTL
  rcases eq_or_lt_of_le hdeg with htwo | hlt
  · exact Or.inr ⟨Q, inferInstance, inferInstance, inferInstance, inferInstance, htwo, hQsplit⟩
  · have hone : Module.finrank F Q = 1 := by
      have := Module.finrank_pos (R := F) (M := Q)
      omega
    have hcard : Nat.card (Q ≃ₐ[F] Q) = 1 := (IsGalois.card_aut_eq_finrank F Q).trans hone
    let : Subsingleton (Q ≃ₐ[F] Q) := (Nat.card_eq_one_iff_unique.mp hcard).1
    apply Or.inl (hQsplit.of_galoisFixedCharacters ?_)
    intro σ χ
    rw [Subsingleton.elim σ 1, map_one]
    rfl

/-- The signed absolute character action forces a splitting field of degree
at most two for any torus. -/
def SignedCharacterSplittingStatement : Prop :=
  ∀ (F : Type u) [Field F] (T : CommGroupScheme (Spec (CommRingCat.of F))), IsTorus T.toGrp →
    (∀ σ : SeparableClosure F ≃ₐ[F] SeparableClosure F,
      (∀ χ, characterLattice.galoisRepresentation F (SeparableClosure F) T σ χ = χ) ∨
      (∀ χ, characterLattice.galoisRepresentation F (SeparableClosure F) T σ χ = -χ)) →
    IsSplitTorus T.toGrp ∨
      ∃ (Q : Type u) (_ : Field Q) (_ : Algebra F Q) (_ : FiniteDimensional F Q) (_ : IsGalois F Q),
        Module.finrank F Q = 2 ∧
          IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap F Q)).obj T).toGrp

theorem signedCharacterSplitting : SignedCharacterSplittingStatement.{u} := by
  intro F _ T hT hSign
  exact hT.isSplit_or_exists_quadratic_of_signed_characters hSign

end Langlands.GroupScheme
