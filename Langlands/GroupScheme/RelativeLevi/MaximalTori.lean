import Langlands.GroupScheme.RelativeLevi.ConjugatorUniquenessBaseChange
import Langlands.GroupScheme.Rational.LeviRetraction
import Langlands.GroupScheme.Torus.FieldPointMaximality
import Langlands.GroupScheme.Torus.UnipotentQuotientClosed
import Langlands.GroupScheme.UnipotentClosedSubgroupProof

/-! # Maximal tori in a relative Levi subgroup -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

section Field

variable {k : Type u} [Field k]
    {P L U : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom P.X.hom] [LocallyOfFiniteType L.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {t : T.toGrp ⟶ L} (ht : IsMaximalTorus t)
    (l : L ⟶ P) (r : U ⟶ P) [IsIso (subgroupMultiplication l r)]

include ht in
/-- A maximal torus in a closed complement to a represented unipotent radical
is maximal in the ambient group. -/
theorem IsMaximalTorus.comp_of_radical_complement
    (hl : IsClosedSubgroup l) (hr : IsUnipotentRadical r) :
    IsMaximalTorus (t ≫ l) := by
  let : IsClosedImmersion l.hom.hom.left := hl
  let : IsClosedImmersion r.hom.hom.left := hr.isClosedSubgroup
  let : IsAffineHom L.X.hom := by
    rw [← Over.w l.hom.hom]
    infer_instance
  let : IsAffineHom U.X.hom := by
    rw [← Over.w r.hom.hom]
    infer_instance
  let : Smooth U.X.hom := hr.smooth
  let q := leviRetraction l r hr.isNormal
  have hker : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range r := by
    apply SubgroupFunctor.ext
    intro A
    apply SetLike.ext
    intro x
    exact (mem_range_kernelι_iff q x).trans
      (comp_leviRetraction_eq_one_iff l r hr.isNormal x)
  refine ⟨ht.1, ht.2.1.comp hl, ?_⟩
  intro T' j f hT' hj hf
  have hjq : IsClosedSubgroup (j ≫ q) :=
    hr.isUnipotent.closed_torus_quotient unipotentClosedSubgroup hT' r j hj q hker.le
  apply ht.2.2 T' (j ≫ q) f hT' hjq
  rw [← Category.assoc, hf, Category.assoc, levi_comp_leviRetraction, Category.comp_id]

end Field

section Base

variable {S : Scheme.{u}} {P L : GroupScheme S}
    [IsAffineHom P.X.hom] {l : L ⟶ P}
    {T : CommGroupScheme S} {t : T.toGrp ⟶ L}

/-- A fibrewise maximal closed torus of a relative Levi remains maximal on
every residue fibre of the ambient group. -/
theorem IsFibrewiseMaximalTorus.comp_relativeLevi
    (ht : IsFibrewiseMaximalTorus t) (hc : IsClosedSubgroup t)
    (hl : IsRelativeLeviSubgroup l) : IsFibrewiseMaximalTorus (t ≫ l) := by
  let : IsClosedImmersion l.hom.hom.left := hl.isClosedSubgroup
  let : IsAffineHom L.X.hom := by
    rw [← Over.w l.hom.hom]
    infer_instance
  let : Smooth L.X.hom := hl.smooth
  obtain ⟨U, r, hr, hmul⟩ := hl.exists_unipotentRadical
  let : IsIso (subgroupMultiplication l r) := hmul
  intro s
  let b := geometricPoint S s
  let : IsAffineHom (geometricFiber P s).X.hom :=
    inferInstanceAs (IsAffineHom (Limits.pullback.snd P.X.hom b))
  let : Smooth (geometricFiber L s).X.hom :=
    inferInstanceAs (Smooth (Limits.pullback.snd L.X.hom b))
  let := RelativeLevi.isIso_subgroupMultiplication_baseChange b l r
  have hgeom : IsMaximalTorus
      (T := (CommGroupScheme.baseChange b).obj T) ((baseChange b).map (t ≫ l)) := by
    rw [Functor.map_comp]
    exact (ht.fieldPoint b).comp_of_radical_complement
      ((baseChange b).map l) ((baseChange b).map r)
      (hl.isClosedSubgroup.baseChange b) (hr.geometricFiber s)
  have hdouble := isMaximalTorus_baseChange_comp (S.fromSpecResidueField s)
    (toAlgebraicClosure (S.residueField s)) T (t ≫ l) hgeom
  exact IsMaximalTorus.of_baseChange
    (k := S.residueField s) (K := AlgebraicClosure (S.residueField s))
    ((hc.comp hl.isClosedSubgroup).baseChange _) hdouble

/-- The actual ambient embedding of a maximal torus of the Levi, retaining
closedness, fibrewise maximality and all-test containment. -/
def RelativeLevi.ambientMaximalTorus
    (ht : IsFibrewiseMaximalTorus t) (hc : IsClosedSubgroup t)
    (hl : IsRelativeLeviSubgroup l) :
    {a : T.toGrp ⟶ P // IsClosedSubgroup a ∧ IsFibrewiseMaximalTorus a ∧
      SubgroupFunctor.range a ≤ SubgroupFunctor.range l} :=
  ⟨t ≫ l, hc.comp hl.isClosedSubgroup, ht.comp_relativeLevi hc hl,
    SubgroupFunctor.range_comp_le t l⟩

@[simp]
theorem RelativeLevi.ambientMaximalTorus_val
    (ht : IsFibrewiseMaximalTorus t) (hc : IsClosedSubgroup t)
    (hl : IsRelativeLeviSubgroup l) :
    (RelativeLevi.ambientMaximalTorus ht hc hl).val = t ≫ l := rfl

end Base

end Langlands.GroupScheme
