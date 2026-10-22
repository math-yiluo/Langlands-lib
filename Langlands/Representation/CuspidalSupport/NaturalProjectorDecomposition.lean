import Langlands.Representation.Category.Subquotients
import Mathlib.LinearAlgebra.Projection

/-! Internal algebraic assembly for the eventual quasicuspidal projector. -/

namespace Langlands.SmoothRep

open CategoryTheory

universe uR uG uV

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G]

private theorem projector_zero_of_injective
    (e : ∀ A : SmoothRep.{uR, uG, uV} R G,
      A.representation.IntertwiningMap A.representation)
    (hnat : ∀ (A B : SmoothRep.{uR, uG, uV} R G) (f : A ⟶ B) (v : A),
      e B (hom f v) = hom f (e A v))
    {A B : SmoothRep.{uR, uG, uV} R G} (f : A ⟶ B)
    (hf : Function.Injective (hom f)) (hB : ∀ v : B, e B v = 0) :
    ∀ v : A, e A v = 0 := by
  intro v
  apply hf
  rw [← hnat A B f v, hB, map_zero]

private theorem projector_zero_of_surjective
    (e : ∀ A : SmoothRep.{uR, uG, uV} R G,
      A.representation.IntertwiningMap A.representation)
    (hnat : ∀ (A B : SmoothRep.{uR, uG, uV} R G) (f : A ⟶ B) (v : A),
      e B (hom f v) = hom f (e A v))
    {A B : SmoothRep.{uR, uG, uV} R G} (f : A ⟶ B)
    (hf : Function.Surjective (hom f)) (hA : ∀ v : A, e A v = 0) :
    ∀ v : B, e B v = 0 := by
  intro v
  obtain ⟨w, rfl⟩ := hf v
  rw [hnat A B f w, hA, map_zero]

/-- A natural idempotent whose image has property P and which fixes every
P-object gives an actual invariant complement with no nonzero P-subquotient. -/
theorem decomposition_of_natural_idempotent
    (P : SmoothRep.{uR, uG, uV} R G → Prop)
    (e : ∀ A : SmoothRep.{uR, uG, uV} R G,
      A.representation.IntertwiningMap A.representation)
    (hnat : ∀ (A B : SmoothRep.{uR, uG, uV} R G) (f : A ⟶ B) (v : A),
      e B (hom f v) = hom f (e A v))
    (hid : ∀ (A : SmoothRep.{uR, uG, uV} R G) (v : A), e A (e A v) = e A v)
    (himage : ∀ A : SmoothRep.{uR, uG, uV} R G,
      P (subrepresentation A (e A).range))
    (hfix : ∀ D : SmoothRep.{uR, uG, uV} R G, P D → ∀ v : D, e D v = v)
    (A : SmoothRep.{uR, uG, uV} R G) :
    ∃ S Q : Subrepresentation A.representation,
      IsCompl S.toSubmodule Q.toSubmodule ∧ P (subrepresentation A S) ∧
      ∀ D : SmoothRep.{uR, uG, uV} R G,
        IsSubquotient D (subrepresentation A Q) → P D → Subsingleton D := by
  refine ⟨(e A).range, (e A).ker, ?_, himage A, ?_⟩
  · have he : IsIdempotentElem (e A).toLinearMap := by
      ext v
      exact hid A v
    exact LinearMap.IsIdempotentElem.isCompl he
  · let Q := subrepresentation A (e A).ker
    have hQ : ∀ v : Q, e Q v = 0 := by
      intro v
      apply subtype_injective A (e A).ker
      change hom (subtype A (e A).ker) (e Q v) = 0
      rw [← hnat Q A (subtype A (e A).ker) v]
      exact v.property
    intro D hD hP
    obtain ⟨S, T, ⟨i⟩⟩ := hD
    have hS : ∀ v : subrepresentation Q S, e (subrepresentation Q S) v = 0 :=
      projector_zero_of_injective e hnat (subtype Q S) (subtype_injective Q S) hQ
    have hT : ∀ v : subquotient Q S T, e (subquotient Q S T) v = 0 :=
      projector_zero_of_surjective e hnat (mkQ (subrepresentation Q S) T)
        (mkQ_surjective (subrepresentation Q S) T) hS
    have hzero : ∀ v : D, e D v = 0 :=
      projector_zero_of_injective e hnat i.hom (equivOfIso i).injective hT
    refine ⟨fun x y => ?_⟩
    exact ((hfix D hP x).symm.trans (hzero x)).trans
      ((hfix D hP y).symm.trans (hzero y)).symm

end Langlands.SmoothRep
