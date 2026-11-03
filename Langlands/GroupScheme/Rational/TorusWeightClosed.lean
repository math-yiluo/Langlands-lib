import Langlands.GroupScheme.NormalizerRepresentability
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # Ideals of connected closed subgroups of corepresented groups -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry

namespace Langlands.GroupScheme.Corepresented

/-- A ring has no idempotents other than `0` and `1`. -/
def HasTrivialIdempotents (A : Type*) [CommRing A] : Prop :=
  ∀ c : A, IsIdempotentElem c → c = 0 ∨ c = 1

/-- A ring with connected prime spectrum has no idempotents other than `0` and `1`. -/
theorem hasTrivialIdempotents_of_connectedSpace (A : Type*) [CommRing A]
    [ConnectedSpace (PrimeSpectrum A)] : HasTrivialIdempotents A := by
  intro c hc
  set s := PrimeSpectrum.isIdempotentElemEquivClopens (R := A) ⟨c, hc⟩ with hs
  have hcs : (⟨c, hc⟩ : {e : A // IsIdempotentElem e}) =
      PrimeSpectrum.isIdempotentElemEquivClopens.symm s := by
    rw [hs, OrderIso.symm_apply_apply]
  rcases isClopen_iff.mp s.isClopen with h | h
  · left
    have hbot : s = ⊥ := TopologicalSpace.Clopens.ext h
    rw [hbot, PrimeSpectrum.isIdempotentElemEquivClopens_symm_bot] at hcs
    exact congrArg Subtype.val hcs
  · right
    have htop : s = ⊤ := TopologicalSpace.Clopens.ext h
    rw [htop, PrimeSpectrum.isIdempotentElemEquivClopens_symm_top] at hcs
    exact congrArg Subtype.val hcs

variable {R : CommRingCat.{u}} {F : CommAlgCat.{u} R ⥤ GrpCat.{u}} {B : CommAlgCat.{u} R}
  {e : (F ⋙ forget GrpCat).CorepresentableBy B}

/-- The points of a closed subgroup scheme of `Spec B` over every test scheme are those whose
classifying algebra map kills a fixed ideal `I` of `B`; if the subgroup is connected, `B ⧸ I` has
no idempotents other than `0` and `1`. -/
theorem exists_ideal_range_of_connectedSpace {K : GroupScheme (Spec R)}
    (j : K ⟶ groupScheme F e) [hj : IsClosedImmersion j.hom.hom.left]
    [ConnectedSpace K.X.left] :
    ∃ I : Ideal B, (∀ (U : Over (Spec R)) (y : U ⟶ (groupScheme F e).X),
      y ∈ (SubgroupFunctor.range j).carrier U ↔
        ∀ b ∈ I, (e.homEquiv.symm (pointsEquiv F e U y)).hom b = 0) ∧
      HasTrivialIdempotents (B ⧸ I) := by
  have hj' : IsClosedImmersion (j.hom.hom.left : K.X.left ⟶ Spec (CommRingCat.of B)) := hj
  obtain ⟨I, ε, hε⟩ := (IsClosedImmersion.Spec_iff (R := CommRingCat.of B)
    (f := j.hom.hom.left)).1 hj'
  refine ⟨I, fun U y => ?_, ?_⟩
  · simp only [homEquiv_symm_pointsEquiv_apply]
    have hfac := Langlands.AlgebraicGeometry.factorsThrough_affineQuotient_iff I
      (y.left : U.left ⟶ Spec (CommRingCat.of B))
    rw [SubgroupFunctor.mem_range]
    refine Iff.trans ?_ (hfac.trans ⟨fun h b hb => h hb, fun h b hb => h b hb⟩)
    constructor
    · rintro ⟨t, rfl⟩
      refine ⟨t.left ≫ ε.hom, ?_⟩
      rw [Category.assoc, ← hε]
      rfl
    · rintro ⟨z, hz⟩
      have hw : K.X.hom = j.hom.hom.left ≫ (groupScheme F e).X.hom := (Over.w j.hom.hom).symm
      have h3 : ε.inv ≫ j.hom.hom.left = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) :=
        (ε.inv ≫= hε).trans (Iso.inv_hom_id_assoc ε _)
      have h4 : (z ≫ ε.inv) ≫ j.hom.hom.left = y.left :=
        (Category.assoc _ _ _).trans ((z ≫= h3).trans hz)
      refine ⟨Over.homMk (z ≫ ε.inv) ?_, ?_⟩
      · change (z ≫ ε.inv) ≫ K.X.hom = U.hom
        rw [hw, ← Category.assoc, h4]
        exact Over.w y
      · apply Over.OverMorphism.ext
        exact h4
  · have hsurj : Function.Surjective (ε.hom.base : K.X.left → Spec (CommRingCat.of (B ⧸ I))) :=
      (ConcreteCategory.bijective_of_isIso ε.hom.base).2
    have : ConnectedSpace (Spec (CommRingCat.of (B ⧸ I))) :=
      hsurj.connectedSpace ε.hom.base.hom.continuous
    have : ConnectedSpace (PrimeSpectrum (B ⧸ I)) := this
    exact hasTrivialIdempotents_of_connectedSpace (B ⧸ I)

end Langlands.GroupScheme.Corepresented
