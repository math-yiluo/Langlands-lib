import Langlands.Representation.Category.Subquotients
import Langlands.Representation.CompactCoefficient.Classes
import Langlands.Representation.Exponents.LeviSupercuspidalInductionSupport
import Langlands.GroupScheme.Reductive.Basic

/-! Renard VI.2.1, the remarks after the definition and after the Theorem: subquotients of
supercuspidal representations are supercuspidal; when the centre is compact, supercuspidal
means compact; and supercuspidality is detected by the functions `f_{K,v}` of IV.1.3 having
compact support modulo the centre. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.Aubert.General.RepresentedParabolic

universe u v

open GroupScheme

/-- Renard VI.2.1, remarks. In the represented setting (nonarchimedean local field `k`,
connected reductive `G`, canonical point topology, `LocallyCompactSpace` and
`NonarchimedeanGroup` binders), with `Z` the centre of `G(F)` and supercuspidality the
published represented predicate:

1. (first Remark 2) every subquotient of a supercuspidal smooth representation is
   supercuspidal;
2. (second Remark 1) if `Z` is compact, a smooth representation is supercuspidal if and only
   if all its coefficients against smooth vectors of the dual have compact support;
3. (second Remark 2) a smooth representation `A` is supercuspidal if and only if for every
   compact open `K` and every `w ∈ A` the function `f_{K,w} : g ↦ A(e_K) A(g⁻¹) w` has
   support compact modulo `Z`. This support is the union, over the `K`-invariant linear
   forms `ℓ`, of the supports of `g ↦ ℓ(A(g⁻¹) w)`, which is how it is stated. -/
def SupercuspidalRemarksStatements : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)],
      (∀ A B : SmoothRep.{0, u, v} ℂ (rationalPoints G),
        SmoothRep.IsSubquotient B A → IsSupercuspidal A → IsSupercuspidal B) ∧
      (IsCompact (Subgroup.center (rationalPoints G) : Set (rationalPoints G)) →
        ∀ A : SmoothRep.{0, u, v} ℂ (rationalPoints G),
          IsSupercuspidal A ↔ HasCompactSmoothDualCoefficients A.representation) ∧
      ∀ A : SmoothRep.{0, u, v} ℂ (rationalPoints G),
        IsSupercuspidal A ↔
          ∀ (K : OpenSubgroup (rationalPoints G)), IsCompact (K : Set (rationalPoints G)) →
            ∀ w : A, ∃ C : Set (rationalPoints G), IsCompact C ∧
              ∀ ℓ : Module.Dual ℂ A, (∀ x ∈ K, ∀ y : A, ℓ (A.representation x y) = ℓ y) →
                Function.support (fun g : rationalPoints G => ℓ (A.representation g⁻¹ w)) ⊆
                  C * (Subgroup.center (rationalPoints G) : Set (rationalPoints G))

end Langlands.Aubert.General.RepresentedParabolic
