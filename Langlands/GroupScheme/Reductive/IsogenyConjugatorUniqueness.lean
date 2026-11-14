import Langlands.GroupScheme.Adjoint.InnerActionFaithful
import Langlands.GroupScheme.Reductive.SplitIsogenyUniquenessStatement

/-! # Uniqueness of actual adjoint-torus isogeny conjugators -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace IsAdjointQuotient

variable {k : Type u} [Field k]
    {C G A : GroupScheme (Spec (CommRingCat.of k))}
    {q : G ⟶ A} (hq : IsAdjointQuotient q)

/-- An actual isogeny followed by an adjoint inner automorphism determines the
acting adjoint rational point. -/
theorem eq_of_comp_basePointIso_hom_eq
    (φ : C ⟶ G) (hφ : IsIsogeny φ)
    {x y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A.X}
    (hxy : φ ≫ (hq.innerAction.basePointIso x).hom =
      φ ≫ (hq.innerAction.basePointIso y).hom) : x = y := by
  apply hq.innerAction_point_ext_of_isogeny φ hφ x y
  intro U b g
  have he := congrArg (fun f : C ⟶ G => g ≫ f.hom.hom) hxy
  rw [Grp.comp_hom_hom, Grp.comp_hom_hom, ← Category.assoc,
    ← Category.assoc, hq.innerAction.comp_basePointIso_hom,
    hq.innerAction.comp_basePointIso_hom] at he
  have hb : b = Over.homMk U.hom (by simp) := by
    apply Over.OverMorphism.ext
    simpa using b.w
  simpa only [GroupScheme.constantPoint, ← hb] using he

end IsAdjointQuotient

namespace IsAdjointSplitTorusImage

variable {k : Type u} [Field k]
    {C G A : GroupScheme (Spec (CommRingCat.of k))}
    {T T_ad : CommGroupScheme (Spec (CommRingCat.of k))}
    {q : G ⟶ A} {i : T.toGrp ⟶ G} {j : T_ad.toGrp ⟶ A} {p : T ⟶ T_ad}
    (h : IsAdjointSplitTorusImage q i j p)

/-- The specified actual adjoint torus has at most one rational conjugator
after an arbitrary finite flat surjective homomorphism. -/
theorem conjugator_point_unique
    (φ : C ⟶ G) (hφ : IsIsogeny φ)
    {x y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ T_ad.toGrp.X}
    (hxy : φ ≫ (h.isAdjointQuotient.innerAction.basePointIso (x ≫ j.hom.hom)).hom =
      φ ≫ (h.isAdjointQuotient.innerAction.basePointIso (y ≫ j.hom.hom)).hom) :
    x = y := by
  let : IsClosedImmersion j.hom.hom.left := h.targetMaximal.1.2
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  apply (cancel_mono j.hom.hom).mp
  exact h.isAdjointQuotient.eq_of_comp_basePointIso_hom_eq φ hφ hxy

/-- Existence of an actual adjoint-torus rational conjugator implies unique
existence; no rational lift to the original torus is needed. -/
theorem existsUnique_conjugator_of_exists
    (φ ψ : C ⟶ G) (hφ : IsIsogeny φ)
    (hex : ∃ x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ T_ad.toGrp.X,
      φ ≫ (h.isAdjointQuotient.innerAction.basePointIso (x ≫ j.hom.hom)).hom = ψ) :
    ∃! x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ T_ad.toGrp.X,
      φ ≫ (h.isAdjointQuotient.innerAction.basePointIso (x ≫ j.hom.hom)).hom = ψ := by
  obtain ⟨x, hx⟩ := hex
  refine ⟨x, hx, ?_⟩
  intro y hy
  exact h.conjugator_point_unique φ hφ (hy.trans hx.symm)

end IsAdjointSplitTorusImage

/-- The existence-only form of the unpinned split-isogeny theorem suffices:
the supplied actual adjoint-torus rational point is automatically unique. -/
def SplitIsogenyConjugatorExistenceStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G G' A : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
    ∀ (T T' T'_ad : CommGroupScheme (Spec (CommRingCat.of k))),
      IsSplitTorus T.toGrp →
      ∀ (i : T.toGrp ⟶ G) (i' : T'.toGrp ⟶ G')
        (q : G' ⟶ A) (j : T'_ad.toGrp ⟶ A) (π : T' ⟶ T'_ad)
        (h : IsAdjointSplitTorusImage q i' j π),
        IsMaximalTorus i → IsMaximalTorus i' →
        ∀ (φ₁ φ₂ : G ⟶ G') (t₁ t₂ : T ⟶ T'),
          IsIsogeny φ₁ → IsIsogeny φ₂ →
          i ≫ φ₁ = CommGroupScheme.groupHom t₁ ≫ i' →
          i ≫ φ₂ = CommGroupScheme.groupHom t₂ ≫ i' →
          (∀ χ : characterLattice T', t₁ ≫ χ = t₂ ≫ χ) →
          ∃ x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ T'_ad.toGrp.X,
            φ₁ ≫
              (h.isAdjointQuotient.innerAction.basePointIso (x ≫ j.hom.hom)).hom = φ₂

/-- Faithfulness upgrades the existence-only statement to the exact published
unique-existence target. -/
theorem splitIsogenyUniqueness_of_conjugatorExistence
    (hex : SplitIsogenyConjugatorExistenceStatement.{u}) :
    SplitIsogenyUniquenessStatement.{u} := by
  intro k _ G G' A hG T T' T'_ad hT i i' q j π h hi hi' φ₁ φ₂ t₁ t₂
    hφ₁ hφ₂ ht₁ ht₂ hchar
  apply h.existsUnique_conjugator_of_exists φ₁ φ₂ hφ₁
  exact hex k G G' A hG T T' T'_ad hT i i' q j π h hi hi'
    φ₁ φ₂ t₁ t₂ hφ₁ hφ₂ ht₁ ht₂ hchar

end Langlands.GroupScheme
