import Langlands.AlgebraicGeometry.EtaleLocalCardinalityFinitenessStatement
import Langlands.AlgebraicGeometry.EtaleGeometricLifts
import Langlands.AlgebraicGeometry.AlgClosedValuativeSpecialization
import Langlands.CommutativeAlgebra.HenselianSections
import Langlands.Galois.Local.SeparableHenselian
import Langlands.Galois.Local.SpectralProof
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.AlgebraicGeometry

open _root_.AlgebraicGeometry

namespace EtaleLocalCardinality

/-- Equal finite closed and generic fibre counts exhaust the Henselian sections. -/
lemma valuation_extension {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [IsSeparated f] [Etale f]
    (h : HasLocalConstantGeometricLiftCardinality f)
    {K : Type u} [Field K] [IsAlgClosed K] (A : ValuationSubring K)
    (b : Spec (CommRingCat.of A) ⟶ Y) (a : Spec (CommRingCat.of K) ⟶ X)
    (ha : a ≫ f = Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ b) :
    ∃ l : Spec (CommRingCat.of A) ⟶ X,
      Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ l = a ∧ l ≫ f = b := by
  let : HenselianLocalRing A := Langlands.LocalGalois.Separable.sepClosed_henselian A
  let L := IsLocalRing.ResidueField A
  let : IsAlgClosed L := Langlands.LocalGalois.residue_isAlgClosed A
  let i : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of A) :=
    Spec.map (CommRingCat.ofHom (algebraMap A K))
  let j : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of A) :=
    Spec.map (CommRingCat.ofHom (algebraMap A L))
  let S := {l : Spec (CommRingCat.of A) ⟶ X // l ≫ f = b}
  let G := {l : Spec (CommRingCat.of K) ⟶ X // l ≫ f = i ≫ b}
  let C := {l : Spec (CommRingCat.of L) ⟶ X // l ≫ f = j ≫ b}
  let gen : S → G := fun l => ⟨i ≫ l.1, by rw [Category.assoc, l.2]⟩
  let closed : S → C := fun l => ⟨j ≫ l.1, by rw [Category.assoc, l.2]⟩
  have hgen : Function.Injective gen := by
    intro l₁ l₂ heq
    let q : ValuativeCommSq f :=
      { R := A, K := K, i₁ := (gen l₁).1, i₂ := b, commSq := ⟨(gen l₁).2⟩ }
    let : Subsingleton q.commSq.LiftStruct := IsSeparated.valuativeCriterion f q
    let s₁ : q.commSq.LiftStruct := ⟨l₁.1, rfl, l₁.2⟩
    let s₂ : q.commSq.LiftStruct :=
      ⟨l₂.1, (congrArg Subtype.val heq).symm, l₂.2⟩
    exact Subtype.ext (congrArg CommSq.LiftStruct.l (Subsingleton.elim s₁ s₂))
  have hclosed : Function.Surjective closed := by
    intro c
    let c' : Spec (CommRingCat.of L) ⟶ pullback f b :=
      pullback.lift c.1 j c.2
    obtain ⟨s, hs, hsj⟩ :=
      Langlands.CommutativeAlgebra.HenselianSections.exists_section_of_smooth_of_surjective
        (IsLocalRing.residue_surjective (R := A)) (pullback.snd f b) c'
        (pullback.lift_snd _ _ _)
    refine ⟨⟨s ≫ pullback.fst f b, ?_⟩, ?_⟩
    · rw [Category.assoc, pullback.condition, ← Category.assoc, hs, Category.id_comp]
    · apply Subtype.ext
      change j ≫ (s ≫ pullback.fst f b) = c.1
      rw [← Category.assoc, hsj]
      exact pullback.lift_fst _ _ _
  let : Finite G := finite_lifts_of_quasiCompact_etale f (i ≫ b)
  let : Finite S := Finite.of_injective gen hgen
  obtain ⟨n, hn⟩ := h A b
  have hcard : Nat.card G = Nat.card C := (hn K).trans (hn L).symm
  have hsurj : Function.Surjective gen :=
    (hgen.bijective_of_nat_card_le (hcard ▸ Nat.card_le_card_of_surjective closed hclosed)).2
  obtain ⟨l, hl⟩ := hsurj ⟨a, ha⟩
  exact ⟨l.1, congrArg Subtype.val hl, l.2⟩

/-- Specialization lifting after every base change makes this etale map finite. -/
lemma finite_of_specializing_pullbacks {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [IsSeparated f] [Etale f]
    (hs : ∀ {T : Scheme.{u}} (g : T ⟶ Y), SpecializingMap (pullback.snd f g)) :
    IsFinite f := by
  have hspec : (topologically @SpecializingMap).universally f := by
    intro X' Y' i₁ i₂ f' H
    rw [← H.flip.isoPullback_hom_snd]
    exact ((topologically @SpecializingMap).cancel_left_of_respectsIso _ _).mpr (hs i₂)
  have : UniversallyClosed f := by
    rw [universallyClosed_eq_universallySpecializing]
    exact ⟨hspec, inferInstance⟩
  have : IsProper f := ⟨⟩
  have : LocallyQuasiFinite f := locallyQuasiFinite_of_etale f
  exact IsFinite.of_isProper_of_locallyQuasiFinite f

end EtaleLocalCardinality

/-- A quasi-compact separated etale morphism with constant geometric lift counts
on every local base is finite. -/
theorem etaleLocalCardinalityFiniteness : EtaleLocalCardinalityFinitenessStatement.{u} := by
  intro X Y f hqc hsep het h
  let : QuasiCompact f := hqc
  let : IsSeparated f := hsep
  let : Etale f := het
  apply EtaleLocalCardinality.finite_of_specializing_pullbacks f
  intro T g
  apply specializingMap_of_algClosed_valuation_lifts (pullback.snd f g)
  intro K _ _ A b a ha
  exact EtaleLocalCardinality.valuation_extension _
    (HasLocalConstantGeometricLiftCardinality.pullback h g) A b a ha

end Langlands.AlgebraicGeometry
