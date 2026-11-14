import Langlands.GroupScheme.Absolute.UnipotentQuotientParabolicOrder
import Langlands.GroupScheme.Rational.MaximalLeviDynamicReduction

/-! # Proper parabolics and smooth connected unipotent quotients -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SubgroupFunctor

/-- A monic representative of a full inverse image is an isomorphism exactly
when the monic representative of the original subgroup is an isomorphism. -/
theorem isIso_iff_of_range_eq_comap
    {S : Scheme.{u}} {G Q P H : GroupScheme S}
    (q : G ⟶ Q)
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [QuasiCompact q.hom.hom.left]
    (j : P ⟶ Q) [Mono j.hom.hom]
    (i : H ⟶ G) [Mono i.hom.hom]
    (hrange : range i = (range j).comap q) :
    IsIso i ↔ IsIso j := by
  constructor
  · intro hi
    let : IsIso i := hi
    apply isIso_of_full_range j inferInstance
    apply le_antisymm (fun _ _ _ => Subgroup.mem_top _)
    apply (comap_le_range_iff q j).mp
    rw [comap_top, ← hrange, full_range_of_isIso i]
  · intro hj
    let : IsIso j := hj
    apply isIso_of_full_range i inferInstance
    rw [hrange, full_range_of_isIso j, comap_top]

end SubgroupFunctor

namespace UnipotentQuotientParabolics

variable {k : Type u} [Field k]
    {G Q : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [ConnectedSpace G.X.left] [IsAffineHom G.X.hom]
    [IsAffineHom Q.X.hom]
    (q : G ⟶ Q)
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [LocallyOfFinitePresentation q.hom.hom.left]
    (hq : HasSmoothConnectedUnipotentKernel q)

include hq

/-- Absence of proper rational parabolics is preserved and reflected by the
actual quotient. Properness is tested by the original subgroup embeddings. -/
theorem noProperParabolic_iff :
    (∀ (P : GroupScheme (Spec (CommRingCat.of k))) (i : P ⟶ G),
      IsParabolicSubgroup i → IsIso i) ↔
    (∀ (P : GroupScheme (Spec (CommRingCat.of k))) (j : P ⟶ Q),
      IsParabolicSubgroup j → IsIso j) := by
  let e := parabolicComapOrderIso q hq
  constructor
  · intro hpar P j hj
    have : Mono j.hom.hom := hj.isClosedSubgroup.mono_overHom
    let F : ParabolicFunctor Q :=
      ⟨SubgroupFunctor.range j, ⟨P, j, hj, rfl⟩⟩
    obtain ⟨R, i, hi, hrange⟩ := (e F).property
    have : Mono i.hom.hom := hi.isClosedSubgroup.mono_overHom
    have hcomap : SubgroupFunctor.range i = (SubgroupFunctor.range j).comap q :=
      hrange.trans (parabolicComapOrderIso_apply_coe q hq F)
    exact (SubgroupFunctor.isIso_iff_of_range_eq_comap q j i hcomap).mp (hpar R i hi)
  · intro hpar P i hi
    have : Mono i.hom.hom := hi.isClosedSubgroup.mono_overHom
    let F : ParabolicFunctor G :=
      ⟨SubgroupFunctor.range i, ⟨P, i, hi, rfl⟩⟩
    obtain ⟨R, j, hj, hrange⟩ := (e.symm F).property
    have : Mono j.hom.hom := hj.isClosedSubgroup.mono_overHom
    have hcomap : SubgroupFunctor.range i = (SubgroupFunctor.range j).comap q := by
      calc
        SubgroupFunctor.range i = (e.symm F).val.comap q :=
          (parabolicComapOrderIso_symm_comap q hq F).symm
        _ = (SubgroupFunctor.range j).comap q := by rw [hrange]
    exact (SubgroupFunctor.isIso_iff_of_range_eq_comap q j i hcomap).mpr (hpar R j hj)

/-- Existence of a proper actual rational parabolic is also unchanged. -/
theorem exists_properParabolic_iff :
    (∃ (P : GroupScheme (Spec (CommRingCat.of k))) (i : P ⟶ G),
      IsParabolicSubgroup i ∧ ¬ IsIso i) ↔
    (∃ (P : GroupScheme (Spec (CommRingCat.of k))) (j : P ⟶ Q),
      IsParabolicSubgroup j ∧ ¬ IsIso j) := by
  classical
  simpa only [not_forall, not_imp, exists_prop] using not_congr (noProperParabolic_iff q hq)

end UnipotentQuotientParabolics

/-- The exact actual-embedding formulation needed after the descended
neutral residue group and its unipotent quotient have been constructed. -/
def UnipotentQuotientNoProperParabolicStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G Q : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [ConnectedSpace G.X.left] [IsAffineHom G.X.hom]
    [IsAffineHom Q.X.hom]
    (q : G ⟶ Q)
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [LocallyOfFinitePresentation q.hom.hom.left],
    HasSmoothConnectedUnipotentKernel q →
      ((∀ (P : GroupScheme (Spec (CommRingCat.of k))) (i : P ⟶ G),
          IsParabolicSubgroup i → IsIso i) ↔
        (∀ (P : GroupScheme (Spec (CommRingCat.of k))) (j : P ⟶ Q),
          IsParabolicSubgroup j → IsIso j))

/-- Proof using the actual parabolic order isomorphism and fpqc reflection
of fullness of monic represented subgroups. -/
theorem unipotentQuotientNoProperParabolic :
    UnipotentQuotientNoProperParabolicStatement.{u} := by
  intro k _ G Q _ _ _ _ q _ _ _ hq
  exact UnipotentQuotientParabolics.noProperParabolic_iff q hq

end Langlands.GroupScheme
