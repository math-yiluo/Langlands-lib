import Langlands.Representation.Aubert.General.AlternatingOperator
import Langlands.Representation.CuspidalSupport.LeviCuspidalQuotientProof

/-! # Smooth-dual compatibility with actual change of acting group -/

noncomputable section

open CategoryTheory

namespace Langlands.Aubert.General

universe uG uH uV

open SmoothRep

section Pullback

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {H : Type uH} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- The smooth dual of an actual pullback is the pullback of the smooth dual.
This is the published same-functional equivalence, bundled as an isomorphism. -/
def contragredientPullbackIso (e : H ≃ₜ* G) (A : SmoothRep.{0, uG, uV} ℂ G) :
    (SmoothRep.pullback e A).contragredient ≅ SmoothRep.pullback e A.contragredient :=
  SmoothRep.mkIso (CuspidalSupport.QuotientAssembly.smoothDualPullbackEquiv
    A.representation e)

/-- The pullback comparison retains each underlying linear functional. -/
@[simp]
theorem contragredientPullbackIso_hom_apply (e : H ≃ₜ* G)
    (A : SmoothRep.{0, uG, uV} ℂ G)
    (ℓ : (SmoothRep.pullback e A).contragredient) (v : A) :
    (SmoothRep.hom (contragredientPullbackIso e A).hom ℓ).val v = ℓ.val v :=
  rfl

/-- The actual pullback comparison is natural for the contravariant smooth
dual: both composites are precomposition by the original coefficient map. -/
theorem contragredientPullbackIso_natural (e : H ≃ₜ* G)
    {A B : SmoothRep.{0, uG, uV} ℂ G} (f : A ⟶ B) :
    contragredientHom ((pullbackFunctor e).map f) ≫ (contragredientPullbackIso e A).hom =
      (contragredientPullbackIso e B).hom ≫ (pullbackFunctor e).map (contragredientHom f) := by
  apply ObjectProperty.hom_ext
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro ℓ
  apply Subtype.ext
  rfl

/-- Exact-K0 pullback commutes with the actual smooth dual. The two named
finite-length premises only define the smooth-dual K0 maps; the comparison
itself is supplied by `contragredientPullbackIso`. -/
theorem contragredientK0_comp_pullback (e : H ≃ₜ* G)
    (hcofG : CompactOpenCofinal G) (hcofH : CompactOpenCofinal H)
    (hcG : ContragredientPreservesFiniteLength.{uG, uV} G)
    (hcH : ContragredientPreservesFiniteLength.{uH, uV} H) :
    (contragredientK0 H hcofH hcH).comp
        (FiniteLengthGrothendieckGroup.pullback.{uG, uH, uV} e) =
      (FiniteLengthGrothendieckGroup.pullback e).comp (contragredientK0 G hcofG hcG) := by
  apply FiniteLengthGrothendieckGroup.hom_ext_object ℂ G
  intro A
  change contragredientK0 H hcofH hcH
      (FiniteLengthGrothendieckGroup.pullback e
        (FiniteLengthGrothendieckGroup.ofRepresentation A.val A.property)) =
    FiniteLengthGrothendieckGroup.pullback e
      (contragredientK0 G hcofG hcG
        (FiniteLengthGrothendieckGroup.ofRepresentation A.val A.property))
  have hE : (SmoothRep.pullback e A.val).HasFiniteLength :=
    pullbackFunctor_preservesFiniteLength e A.val A.property
  have hD : (SmoothRep.pullback e A.val.contragredient).HasFiniteLength :=
    pullbackFunctor_preservesFiniteLength e A.val.contragredient (hcG A.val A.property)
  rw [FiniteLengthGrothendieckGroup.pullback_ofRepresentation e A.val A.property hE,
    contragredientK0_ofRepresentation H hcofH hcH (SmoothRep.pullback e A.val) hE,
    contragredientK0_ofRepresentation G hcofG hcG A.val A.property,
    FiniteLengthGrothendieckGroup.pullback_ofRepresentation e A.val.contragredient
      (hcG A.val A.property) hD]
  exact FiniteLengthGrothendieckGroup.ofObject_eq_of_iso (contragredientPullbackIso e A.val)

end Pullback

section Conjugation

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M N : Subgroup G}

/-- The actual exact-K0 conjugation map commutes with the actual smooth dual.
This requires no parabolic or opposite-parabolic class invariance theorem. -/
theorem contragredientK0_comp_conjugationK0 (g : G)
    (hMN : ∀ x : G, x ∈ N ↔ g⁻¹ * x * g ∈ M)
    (hcofM : CompactOpenCofinal M) (hcofN : CompactOpenCofinal N)
    (hcM : ContragredientPreservesFiniteLength.{uG, uV} M)
    (hcN : ContragredientPreservesFiniteLength.{uG, uV} N) :
    (contragredientK0 N hcofN hcN).comp (conjugationK0.{uG, uV} g hMN) =
      (conjugationK0 g hMN).comp (contragredientK0 M hcofM hcM) :=
  contragredientK0_comp_pullback (conjugationEquiv g hMN) hcofM hcofN hcM hcN

end Conjugation

end Langlands.Aubert.General
