import Langlands.Representation.Exponents.LeviNormalizerQuotientStatements
import Langlands.Representation.Exponents.DynamicLeviNormalizer
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof

/-! # Finiteness and faithfulness of `N_G(M)(F)/M(F)` for a rational Levi

Proofs of `LeviNormalizerFiniteQuotientStatement`, `LeviNormalizerNormFixingStatement` and
their conjunction `LeviNormalizerWeylGroupStatements` (Renard 2026, V.3.5 and V.4.3.3).
Milne's Theorem 25.1 (`parabolicDynamic`) presents every parabolic as a dynamic parabolic
`P(χ)` over `k`; the published results of `DynamicLeviNormalizer` conclude from such a
presentation.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Every parabolic subgroup of a connected reductive group over a field is the dynamic
parabolic of a cocharacter defined over the field, in the form used by
`DynamicLeviNormalizer`. -/
theorem exists_dynamicParabolic_isRepresentedBy {k : Type u} [Field k]
    {G P : GroupScheme (Spec (CommRingCat.of k))} (hG : IsConnectedReductive G)
    {p : P ⟶ G} (hp : IsParabolicSubgroup p) :
    ∃ χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G,
      (Dynamic.parabolic χ).IsRepresentedBy p := by
  obtain ⟨χ, hχ⟩ := (parabolicDynamic k G hG P p hp.isClosedSubgroup).1 hp
  have : Mono p.hom.hom.left := hp.isClosedSubgroup.mono
  exact ⟨χ, Over.mono_of_mono_left _, hχ⟩

/-- **Renard V.4.3.3.** `N_G(M)(F)/M(F)` is finite for a rational Levi `M` of a
parabolic of a connected reductive group over a nonarchimedean local field. -/
theorem leviNormalizerFiniteQuotient : LeviNormalizerFiniteQuotientStatement.{u} := by
  intro k _ _ _ _ G hG P M p l hp hl
  obtain ⟨χ, hP⟩ := exists_dynamicParabolic_isRepresentedBy hG hp
  exact hl.exists_finite_normalizer_representatives_of_dynamicParabolic hG hp χ hP

/-- **Renard V.3.5.** A point normalizing a rational Levi `M` whose automorphism preserves
the norm of every rational character of `M` on the centre of `M(F)` lies in `M(F)`. -/
theorem leviNormalizerNormFixing : LeviNormalizerNormFixingStatement.{u} := by
  intro k _ _ _ _ G hG P M p l hp hl w φ hw hnorm
  obtain ⟨χ, hP⟩ := exists_dynamicParabolic_isRepresentedBy hG hp
  exact hl.mem_pointImage_of_normalizes_of_norm_of_dynamicParabolic hG χ hP hw hnorm

/-- Both facts about `W(A) = N_G(M)(F)/M(F)`: it is finite and acts faithfully through the
norms of rational characters on the centre of `M(F)`. -/
theorem leviNormalizerWeylGroupStatements : LeviNormalizerWeylGroupStatements.{u} :=
  ⟨leviNormalizerFiniteQuotient, leviNormalizerNormFixing⟩

end Langlands.Aubert.General.RepresentedParabolic
