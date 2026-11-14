import Langlands.GroupScheme.RelativeLevi.ConjugatorUniqueness
import Langlands.GroupScheme.Rational.SplitUnipotentProductBaseChange
import Langlands.GroupScheme.SubgroupFunctor.NormalizerBaseChange
import Langlands.GroupScheme.CocharacterTransport

/-! # Uniqueness of unipotent conjugators on arbitrary test schemes -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeLevi

variable {S S' : Scheme.{u}} {P L U V : GroupScheme S}

/-- Radical conjugation over the base of an arbitrary test scheme, expressed
using the actual pullback group schemes. -/
def radicalConjugateAt (l : L ⟶ P) (r : U ⟶ P) (T : Over S)
    (u : T ⟶ U.X) : SubgroupFunctor ((GroupScheme.baseChange T.hom).obj P) :=
  radicalConjugate ((GroupScheme.baseChange T.hom).map l)
    ((GroupScheme.baseChange T.hom).map r)
    ((baseChangeBasePointsEquiv T.hom U).symm u)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- An actual two-subgroup multiplication isomorphism remains an isomorphism
after arbitrary base change. -/
theorem isIso_subgroupMultiplication_baseChange (b : S' ⟶ S) (l : L ⟶ P) (s : V ⟶ P)
    [IsIso (subgroupMultiplication l s)] :
    IsIso (subgroupMultiplication ((GroupScheme.baseChange b).map l)
      ((GroupScheme.baseChange b).map s)) := by
  have he : subgroupMultiplication ((GroupScheme.baseChange b).map l)
      ((GroupScheme.baseChange b).map s) =
      (subgroupMultiplicationBaseChangeIso b L V).inv ≫
        (Over.pullback b).map (subgroupMultiplication l s) := by
    rw [← subgroupMultiplication_baseChange b l s, Iso.inv_hom_id_assoc]
  rw [he]
  infer_instance

/-- The algebraic uniqueness criterion persists under every base change,
without any smoothness, flatness or surjectivity hypothesis on the base map. -/
theorem radicalConjugate_baseChange_injective_of_range_le
    (b : S' ⟶ S) (l : L ⟶ P) (r : U ⟶ P) (s : V ⟶ P)
    [Mono l.hom.hom] [Mono r.hom.hom] [IsIso (subgroupMultiplication l s)]
    (hrs : SubgroupFunctor.range r ≤ SubgroupFunctor.range s)
    (hN : (SubgroupFunctor.range l).normalizer ≤ SubgroupFunctor.range l) :
    Function.Injective (radicalConjugate ((GroupScheme.baseChange b).map l)
      ((GroupScheme.baseChange b).map r)) := by
  let : Mono ((GroupScheme.baseChange b).map l).hom.hom :=
    inferInstanceAs (Mono ((Over.pullback b).map l.hom.hom))
  let : Mono ((GroupScheme.baseChange b).map r).hom.hom :=
    inferInstanceAs (Mono ((Over.pullback b).map r.hom.hom))
  let := isIso_subgroupMultiplication_baseChange b l s
  apply radicalConjugate_injective_of_range_le _ _ ((GroupScheme.baseChange b).map s)
  · simpa only [SubgroupFunctor.range_baseChangeHom] using
      SubgroupFunctor.baseChange_mono b hrs
  · simpa only [SubgroupFunctor.range_baseChangeHom,
      ← SubgroupFunctor.normalizer_baseChange] using SubgroupFunctor.baseChange_mono b hN

/-- Uniqueness holds for actual points on every test scheme, under the original
base's algebraic hypotheses. -/
theorem radicalConjugateAt_injective_of_range_le
    (l : L ⟶ P) (r : U ⟶ P) (s : V ⟶ P)
    [Mono l.hom.hom] [Mono r.hom.hom] [IsIso (subgroupMultiplication l s)]
    (hrs : SubgroupFunctor.range r ≤ SubgroupFunctor.range s)
    (hN : (SubgroupFunctor.range l).normalizer ≤ SubgroupFunctor.range l)
    (T : Over S) : Function.Injective (radicalConjugateAt l r T) :=
  (radicalConjugate_baseChange_injective_of_range_le T.hom l r s hrs hN).comp
    (baseChangeBasePointsEquiv T.hom U).symm.injective

/-- The supplied global geometric statements give uniqueness over every test
scheme without transporting any relative predicate to that test scheme. -/
theorem relative_radicalConjugateAt_injective
    (hRadical : RelativeUnipotentRadicalStatement.{u})
    (hNormalizer : RelativeLeviSelfNormalizerStatement.{u})
    (G P U L : GroupScheme S) (i : P ⟶ G) (r : U ⟶ P) (l : L ⟶ P)
    (hG : IsReductive G) (hi : IsRelativeParabolicSubgroup i)
    (hr : IsRelativeUnipotentRadical r) (hl : IsRelativeLeviSubgroup l)
    (T : Over S) : Function.Injective (radicalConjugateAt l r T) := by
  obtain ⟨V, s, hs, hmul⟩ := hl.exists_unipotentRadical
  obtain ⟨W, t, _, ht⟩ := hRadical S G P i hG hi
  have hrs : SubgroupFunctor.range r ≤ SubgroupFunctor.range s :=
    ((ht U r hr).trans (ht V s hs).symm).le
  let : IsClosedImmersion l.hom.hom.left := hl.isClosedSubgroup
  let : IsClosedImmersion r.hom.hom.left := hr.isClosedSubgroup
  let : Mono l.hom.hom := Over.mono_of_mono_left _
  let : Mono r.hom.hom := Over.mono_of_mono_left _
  let : IsIso (subgroupMultiplication l s) := hmul
  exact radicalConjugateAt_injective_of_range_le l r s hrs
    (hNormalizer S G P L i l hG hi hl).le T

end Langlands.GroupScheme.RelativeLevi
