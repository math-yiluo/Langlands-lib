import Langlands.GroupScheme.RelativeLevi.DynamicNormalizer
import Langlands.GroupScheme.Rational.OriginalLeviCocharacter
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Dynamic.UnipotentCocharacterConjugacy

/-! # Self-normalization of a complement to a field parabolic radical -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace RelativeLevi

variable {k : Type u} [Field k]
    {G P L U : GroupScheme (Spec (CommRingCat.of k))}
    (j : P ⟶ G) (l : L ⟶ P) (r : U ⟶ P)

/-- Any complement to the unipotent radical of a parabolic in a connected
reductive group is its own all-test normalizer. No reductivity hypothesis on
the supplied complement is needed. -/
theorem normalizer_eq_of_field_radical (hG : IsConnectedReductive G)
    (hP : IsParabolicSubgroup j) (hr : IsUnipotentRadical r)
    [IsIso (subgroupMultiplication l r)] :
    (SubgroupFunctor.range l).normalizer = SubgroupFunctor.range l := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsSeparated G.X.hom := hG.isSeparated
  let : IsClosedImmersion j.hom.hom.left := hP.isClosedSubgroup
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  obtain ⟨χ, hχ⟩ := (parabolicDynamic k G hG P j hP.isClosedSubgroup).1 hP
  have hj : (Dynamic.parabolic χ).IsRepresentedBy j := ⟨inferInstance, hχ⟩
  let q := leviRetraction l r hr.isNormal
  have hlq : l ≫ q = 𝟙 L := levi_comp_leviRetraction l r hr.isNormal
  have hker : ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ P.X),
      x ≫ q.hom.hom = 1 ↔ x ≫ j.hom.hom ∈ (Dynamic.unipotent χ).carrier T := by
    intro T x
    rw [comp_leviRetraction_eq_one_iff,
      DynamicLeviConjugacy.mem_range_radical_iff_of_reductive hG χ hj hr x]
  obtain ⟨u, hu, hμ⟩ := Dynamic.exists_unipotent_conj_of_mul_inv_mem χ
    ((DynamicLeviConjugacy.parabolicCocharacter χ hj ≫ q) ≫ l ≫ j)
    (DynamicLeviConjugacy.leviCocharacter_mul_inv_mem (hj := hj) l q hlq hker)
  exact DynamicLeviConjugacy.normalizer_eq_range_of_retraction l q hlq hj hker hu hμ

/-- For a supplied field parabolic complement, the multiplication retraction
identifies normalizer points with complement points on every test scheme. -/
def fieldNormalizerPointsEquiv (hG : IsConnectedReductive G)
    (hP : IsParabolicSubgroup j) (hr : IsUnipotentRadical r)
    [IsIso (subgroupMultiplication l r)] (T : Over (Spec (CommRingCat.of k))) :
    (SubgroupFunctor.range l).normalizer.carrier T ≃* (T ⟶ L.X) :=
  DynamicLeviConjugacy.normalizerPointsEquivOfRetraction l
    (leviRetraction l r hr.isNormal) (levi_comp_leviRetraction l r hr.isNormal)
    (normalizer_eq_of_field_radical j l r hG hP hr) T

end RelativeLevi

end Langlands.GroupScheme
