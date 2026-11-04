import Langlands.GroupScheme.Descent.FppfQuotientDatum
import Langlands.GroupScheme.Descent.AffineDatumMorphisms
import Langlands.GroupScheme.CentralIsogeny.FpqcReflection
import Langlands.GroupScheme.SubgroupFunctor.FpqcDescent

/-! # Effective affine descent of represented fppf quotients -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace RelativeRoot.IsFppfQuotient

/-- An fpqc base change detects the fppf quotient by a represented subgroup,
allowing an actual isomorphism of the base-changed target. -/
theorem of_baseChange_iso {B S : Scheme.{u}} (p : S ⟶ B)
    [Flat p] [Surjective p] [QuasiCompact p]
    {G N R : GroupScheme B} (i : N ⟶ G) [Mono i.hom.hom]
    {Q : GroupScheme S} (r : G ⟶ R)
    (q : (GroupScheme.baseChange p).obj G ⟶ Q)
    (e : (GroupScheme.baseChange p).obj R ≅ Q)
    (he : (GroupScheme.baseChange p).map r ≫ e.hom = q)
    (hq : RelativeRoot.IsFppfQuotient
      (SubgroupFunctor.range ((GroupScheme.baseChange p).map i)) q) :
    RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) r := by
  let r' := (GroupScheme.baseChange p).map r
  have he' : r'.hom.hom.left ≫ e.hom.hom.hom.left = q.hom.hom.left :=
    congrArg (fun f => f.hom.hom.left) he
  have : IsIso e.hom.hom.hom.left :=
    (Over.forget S).map_isIso e.hom.hom.hom
  have hf' : Flat r'.hom.hom.left := by
    apply (MorphismProperty.cancel_right_of_respectsIso @Flat _ e.hom.hom.hom.left).mp
    rw [he']
    exact hq.1
  have hs' : Surjective r'.hom.hom.left := by
    apply (MorphismProperty.cancel_right_of_respectsIso @Surjective _ e.hom.hom.hom.left).mp
    rw [he']
    exact hq.2.1
  have hl' : LocallyOfFinitePresentation r'.hom.hom.left := by
    apply (MorphismProperty.cancel_right_of_respectsIso @LocallyOfFinitePresentation
      _ e.hom.hom.hom.left).mp
    rw [he']
    exact hq.2.2.1
  have hp := baseChange_map_isPullback p r
  have hfpqc : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u})
      (pullback.fst R.X.hom p) :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  have hf : Flat r.hom.hom.left :=
    MorphismProperty.of_isPullback_of_descendsAlong hp hfpqc hf'
  have hs : Surjective r.hom.hom.left :=
    MorphismProperty.of_isPullback_of_descendsAlong hp hfpqc hs'
  have hl : LocallyOfFinitePresentation r.hom.hom.left :=
    MorphismProperty.of_isPullback_of_descendsAlong hp hfpqc hl'
  refine ⟨hf, hs, hl, ?_⟩
  apply SubgroupFunctor.range_eq_of_baseChange_eq p (kernelι r) i
  rw [← kernel_range_baseChange, ← SubgroupFunctor.range_baseChangeHom]
  calc
    SubgroupFunctor.range (kernelι ((GroupScheme.baseChange p).map r)) =
        SubgroupFunctor.range (kernelι q) := by
      apply SubgroupFunctor.ext
      intro T
      apply Subgroup.ext
      intro x
      rw [mem_range_kernelι_iff, mem_range_kernelι_iff]
      constructor
      · intro hx
        rw [← he, Grp.comp_hom_hom, ← Category.assoc, hx, MonObj.one_comp]
      · intro hx
        apply (cancel_mono e.hom.hom.hom).mp
        rw [Category.assoc, ← Grp.comp_hom_hom, he, hx, MonObj.one_comp]
    _ = _ := hq.2.2.2

end RelativeRoot.IsFppfQuotient

namespace Descent

/-- A supplied affine quotient after an affine fpqc base change descends to
an actual affine quotient over the original base, retaining its original map. -/
theorem exists_affine_fppfQuotient {B S : Scheme.{u}}
    [IsAffine B] [IsAffine S] (p : S ⟶ B)
    [Flat p] [Surjective p] [QuasiCompact p]
    {G N : GroupScheme B} (i : N ⟶ G) [Mono i.hom.hom]
    (Q : GroupScheme S) [IsAffine Q.X.left]
    (q : (GroupScheme.baseChange p).obj G ⟶ Q) [QuasiCompact q.hom.hom.left]
    (hq : RelativeRoot.IsFppfQuotient
      (SubgroupFunctor.range ((GroupScheme.baseChange p).map i)) q) :
    ∃ (R : GroupScheme B) (r : G ⟶ R), IsAffine R.X.left ∧
      RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) r ∧
      ∃ e : (GroupScheme.baseChange p).obj R ≅ Q, (GroupScheme.baseChange p).map r ≫ e.hom = q := by
  let D := quotientDatum (canonicalDatum p G) (canonicalDatum p N)
    ((GroupScheme.baseChange p).map i) q (canonicalDatum_compatible p i) hq
  let s : Solution D := D.affineSolution
  have hc : Compatible (canonicalDatum p G) D q :=
    compatible_quotientDatum _ _ _ _ _ _
  let r : G ⟶ s.obj := Solution.descendHom (canonicalSolution p G) s q hc
  have hr : (GroupScheme.baseChange p).map r ≫ s.iso.hom = q := by
    simpa only [r, canonicalSolution, Iso.refl_hom, Category.id_comp] using
      Solution.baseChange_descendHom (canonicalSolution p G) s q hc
  refine ⟨s.obj, r, ?_, RelativeRoot.IsFppfQuotient.of_baseChange_iso p i r q s.iso hr hq,
    s.iso, hr⟩
  exact inferInstanceAs (IsAffine D.affineSolution.obj.X.left)

end Descent
end Langlands.GroupScheme

namespace Langlands.GroupScheme

/-- Effective affine descent for a supplied fppf quotient by a full represented kernel. -/
def AffineFppfQuotientDescentStatement : Prop :=
  ∀ (B S : Scheme.{u}) [IsAffine B] [IsAffine S] (p : S ⟶ B)
    [Flat p] [Surjective p] [QuasiCompact p]
    (G N : GroupScheme B) (i : N ⟶ G) [Mono i.hom.hom]
    (Q : GroupScheme S) [IsAffine Q.X.left]
    (q : (baseChange p).obj G ⟶ Q) [QuasiCompact q.hom.hom.left],
    RelativeRoot.IsFppfQuotient (SubgroupFunctor.range ((baseChange p).map i)) q →
      ∃ (R : GroupScheme B) (r : G ⟶ R), IsAffine R.X.left ∧
        RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) r ∧
        ∃ e : (baseChange p).obj R ≅ Q, (baseChange p).map r ≫ e.hom = q

/-- The universe-general effective affine quotient-descent statement. -/
theorem affineFppfQuotientDescent : AffineFppfQuotientDescentStatement.{u} := by
  intro B S _ _ p _ _ _ G N i _ Q _ q _ hq
  exact Descent.exists_affine_fppfQuotient p i Q q hq

end Langlands.GroupScheme
