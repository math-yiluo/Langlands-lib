import Langlands.Representation.Aubert.General.CuspidalInductionExclusion
import Langlands.Representation.Category.UniverseLift
import Langlands.Representation.Jacquet.LocalizationExactnessProof

/-!
# Cuspidal projections from actual remainder splittings

Internal consequences of a supplied actual binary coproduct. No existence
of a whole-category splitting is asserted.
-/

noncomputable section

open CategoryTheory Limits

namespace Langlands.Aubert.General

universe uK uG uV uW uX

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {κ : Type uK} {P M U : κ → Subgroup G}
  {h : ∀ k, IsSemidirectDecomposition (P k) (M k) (U k)}
  {hU : ∀ k, IsClosed (U k : Set G)}

/-- The actual projection to the `true` component of a Boolean coproduct. -/
def boolCoproductTrueProjection
    {A : SmoothRep.{0, uG, uV} ℂ G} {Y : Bool → SmoothRep.{0, uG, uV} ℂ G}
    {ι : ∀ b, Y b ⟶ A} (hc : IsColimit (Cofan.mk A ι)) :
    A ⟶ Y true :=
  Cofan.IsColimit.desc hc (fun b => match b with
    | false => 0
    | true => 𝟙 (Y true))

/-- Surjective actual intertwiners preserve cuspidality even when their
source and target carrier universes differ. -/
theorem IsCuspidalFor.of_surjective_intertwiner
    {A : SmoothRep.{0, uG, uV} ℂ G} {B : SmoothRep.{0, uG, uW} ℂ G}
    (hA : IsCuspidalFor P M U h hU A)
    (q : A.representation.IntertwiningMap B.representation)
    (hq : Function.Surjective q) :
    IsCuspidalFor P M U h hU B := by
  intro k
  let : Subsingleton (Jacquet.Localization.Coinvariants A.representation (U k) 1) := hA k
  exact (Jacquet.Localization.map_surjective (U k) 1 (M k)
    (h k).levi_le_normalizer (Jacquet.Localization.isInvariant_one _ _ _) q hq).subsingleton

/-- Every actual map from a cuspidal object into a remainder without nonzero
cuspidal subquotients vanishes. The source carrier can have any universe. -/
theorem hom_eq_zero_of_no_cuspidal_subquotient
    {R : SmoothRep.{0, uG, uV} ℂ G}
    (hR : ∀ D : SmoothRep.{0, uG, uV} ℂ G,
      Nontrivial D → SmoothRep.IsSubquotient D R → ¬ IsCuspidalFor P M U h hU D)
    {B : SmoothRep.{0, uG, uW} ℂ G} (hB : IsCuspidalFor P M U h hU B)
    (f : B.representation.IntertwiningMap R.representation) :
    f = 0 := by
  by_contra hf
  have hv : ∃ v : B, f v ≠ 0 := by
    by_contra hn
    apply hf
    ext v
    exact Classical.not_not.mp (not_exists.mp hn v)
  obtain ⟨v, hv⟩ := hv
  let D := SmoothRep.subrepresentation R f.range
  have hD : Nontrivial D :=
    ⟨⟨⟨f v, ⟨v, rfl⟩⟩, 0, fun heq => hv (congrArg Subtype.val heq)⟩⟩
  let q : B.representation.IntertwiningMap D.representation := {
    toLinearMap := f.toLinearMap.rangeRestrict
    isIntertwining' g := by
      ext w
      exact Subtype.ext
        (Representation.IntertwiningMap.isIntertwining _ _ f g w) }
  have hDc : IsCuspidalFor P M U h hU D :=
    hB.of_surjective_intertwiner q (LinearMap.surjective_rangeRestrict _)
  exact hR D hD
    (SmoothRep.subrepresentation_isSubrepresentation f.range).isSubquotient hDc

/-- The cuspidal projection of a supplied binary coproduct detects every
actual map from a cuspidal object, in an independent source universe. -/
theorem HasCuspidalRemainderSplitting.exists_projection
    {A : SmoothRep.{0, uG, uV} ℂ G}
    (hsplit : HasCuspidalRemainderSplitting P M U h hU A) :
    ∃ C : SmoothRep.{0, uG, uV} ℂ G,
      IsCuspidalFor P M U h hU C ∧
      ∃ p : A.representation.IntertwiningMap C.representation,
        ∀ (B : SmoothRep.{0, uG, uW} ℂ G), IsCuspidalFor P M U h hU B →
          ∀ j : B.representation.IntertwiningMap A.representation,
            p.comp j = 0 → j = 0 := by
  obtain ⟨Y, ι, hC, hR, ⟨hc⟩⟩ := hsplit
  let f : ∀ b, Y b ⟶ Y true := fun b => match b with
    | false => 0
    | true => 𝟙 (Y true)
  let g : ∀ b, Y b ⟶ Y false := fun b => match b with
    | false => 𝟙 (Y false)
    | true => 0
  let p : A ⟶ Y true := boolCoproductTrueProjection hc
  let r : A ⟶ Y false := Cofan.IsColimit.desc hc g
  have hp (b : Bool) : ι b ≫ p = f b := Cofan.IsColimit.fac hc f b
  have hr (b : Bool) : ι b ≫ r = g b := Cofan.IsColimit.fac hc g b
  have hid : p ≫ ι true + r ≫ ι false = 𝟙 A := by
    apply Cofan.IsColimit.hom_ext hc
    intro b
    change ι b ≫ (p ≫ ι true + r ≫ ι false) = ι b ≫ 𝟙 A
    rw [Preadditive.comp_add, ← Category.assoc, ← Category.assoc, hp, hr]
    cases b <;> simp [f, g]
  refine ⟨Y true, hC, SmoothRep.hom p, ?_⟩
  intro B hB j hj
  have hjr : (SmoothRep.hom r).comp j = 0 :=
    hom_eq_zero_of_no_cuspidal_subquotient hR hB _
  ext v
  have hpv := congrArg (fun t => t v) hj
  have hrv := congrArg (fun t => t v) hjr
  change SmoothRep.hom p (j v) = 0 at hpv
  change SmoothRep.hom r (j v) = 0 at hrv
  have hv := congrArg (fun t => SmoothRep.hom t (j v)) hid
  change SmoothRep.hom (ι true) (SmoothRep.hom p (j v)) +
    SmoothRep.hom (ι false) (SmoothRep.hom r (j v)) = j v at hv
  rw [hpv, hrv, map_zero, map_zero, add_zero] at hv
  exact hv.symm

/-- Raising only the cuspidal carrier preserves the detecting property of
the projection. This uses the actual heterogeneous `ULift` equivalence. -/
theorem HasCuspidalRemainderSplitting.exists_lifted_projection
    {A : SmoothRep.{0, uG, uV} ℂ G}
    (hsplit : HasCuspidalRemainderSplitting P M U h hU A) :
    ∃ C : SmoothRep.{0, uG, max uV uX} ℂ G,
      IsCuspidalFor P M U h hU C ∧
      ∃ p : A.representation.IntertwiningMap C.representation,
        ∀ (B : SmoothRep.{0, uG, uW} ℂ G), IsCuspidalFor P M U h hU B →
          ∀ j : B.representation.IntertwiningMap A.representation,
            p.comp j = 0 → j = 0 := by
  obtain ⟨C, hC, p, hp⟩ := hsplit.exists_projection
  let e := SmoothRep.universeLiftEquiv.{uX} C
  refine ⟨SmoothRep.universeLift.{uX} C,
    hC.of_surjective_intertwiner e.toIntertwiningMap e.surjective,
    e.toIntertwiningMap.comp p, ?_⟩
  intro B hB j hj
  apply hp B hB j
  ext v
  apply e.injective
  change e (p (j v)) = e 0
  have hv := congrArg (fun t => t v) hj
  change e (p (j v)) = 0 at hv
  exact hv.trans (map_zero e).symm

end Langlands.Aubert.General
