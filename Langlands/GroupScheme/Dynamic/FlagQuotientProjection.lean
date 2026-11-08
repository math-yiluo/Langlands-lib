import Langlands.GroupScheme.QuotientCell
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-! # Flatness of a quotient map with local sections near rational points

Let `Ω` be an algebraically closed field, `P ⟶ H` a subgroup of a group scheme over `Ω` whose
structure morphism is flat, surjective and quasi-compact, and `π₀ : H ⟶ Q₀` a morphism to a
`Ω`-scheme of finite type whose fibres on all test schemes are the right cosets of `P`. If `π₀`
has a section on an open neighbourhood of every `Ω`-point of `Q₀`, then `π₀` is flat,
surjective and quasi-compact: these opens cover `Q₀`, and over each of them `π₀` is the
projection `U ×_Ω P ⟶ U`.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic

set_option backward.isDefEq.respectTransparency.types false in
/-- A Zariski-local property at the target holds for `f` when, over every member of an open
cover of the target, some pullback of `f` has it. -/
theorem of_isPullback_of_iSup_eq_top {Pr : MorphismProperty Scheme.{u}}
    [IsZariskiLocalAtTarget Pr] {X Y : Scheme.{u}} (f : X ⟶ Y) {κ : Type*} (U : κ → Y.Opens)
    (hU : iSup U = ⊤)
    (H : ∀ i, ∃ (Z : Scheme.{u}) (a : Z ⟶ X) (b : Z ⟶ U i), IsPullback a b f (U i).ι ∧ Pr b) :
    Pr f := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top U hU fun i => ?_
  obtain ⟨Z, a, b, h, hb⟩ := H i
  rw [← h.isoIsPullback_inv_snd _ _ (isPullback_morphismRestrict f (U i)).flip]
  exact (MorphismProperty.cancel_left_of_respectsIso Pr _ _).mpr hb

variable {Ω : Type u} [Field Ω] [IsAlgClosed Ω]

/-- Over an algebraically closed field, every point of a finite type scheme specializes to a
closed point, which is the image of an `Ω`-point. -/
theorem exists_ringPoint_specializes {Q₀ : Over (Spec (CommRingCat.of Ω))}
    [LocallyOfFiniteType Q₀.hom] [QuasiCompact Q₀.hom] (y : Q₀.left) :
    ∃ (p : RingPoint Ω Q₀ Ω) (c : Q₀.left), c ∈ Set.range p.left ∧ y ⤳ c := by
  have : CompactSpace Q₀.left := QuasiCompact.compactSpace_of_compactSpace Q₀.hom
  obtain ⟨c, hcy, hc⟩ :=
    (isClosed_closure (s := ({y} : Set Q₀.left))).exists_closed_singleton
      ⟨y, subset_closure rfl⟩
  refine ⟨Over.homMk (pointOfClosedPoint Q₀.hom c hc) ?_, c,
    ⟨IsLocalRing.closedPoint Ω, pointOfClosedPoint_apply _ _ _ _⟩,
    specializes_iff_mem_closure.mpr hcy⟩
  change pointOfClosedPoint Q₀.hom c hc ≫ Q₀.hom = Spec.algebraMap Ω Ω
  rw [pointOfClosedPoint_comp, Spec.algebraMap, Algebra.algebraMap_self, CommRingCat.ofHom_id,
    Spec.map_id]

set_option backward.isDefEq.respectTransparency.types false in
/-- **Flatness from local sections.** A morphism `π₀ : H ⟶ Q₀` with the right cosets of `P` as
fibres and with sections near all `Ω`-points is flat, surjective and quasi-compact. -/
theorem flat_surjective_quasiCompact_of_localSections
    {H P : GroupScheme (Spec (CommRingCat.of Ω))} (iP : P ⟶ H) [Mono iP.hom.hom]
    [Flat P.X.hom] [Surjective P.X.hom] [QuasiCompact P.X.hom]
    {Q₀ : Over (Spec (CommRingCat.of Ω))} [LocallyOfFiniteType Q₀.hom] [QuasiCompact Q₀.hom]
    (π₀ : H.X ⟶ Q₀)
    (hf : ∀ (T : Over (Spec (CommRingCat.of Ω))) (g h : T ⟶ H.X),
      g ≫ π₀ = h ≫ π₀ ↔ g⁻¹ * h ∈ (SubgroupFunctor.range iP).carrier T)
    (hsec : ∀ p : RingPoint Ω Q₀ Ω, ∃ (U : Q₀.left.Opens) (s : openOver Ω Q₀ U ⟶ H.X),
      Set.range p.left ⊆ U ∧ s ≫ π₀ = openOverι Ω Q₀ U) :
    Flat π₀.left ∧ Surjective π₀.left ∧ QuasiCompact π₀.left := by
  have hcov : ∀ y : Q₀.left, ∃ (U : Q₀.left.Opens) (s : openOver Ω Q₀ U ⟶ H.X),
      y ∈ U ∧ s ≫ π₀ = openOverι Ω Q₀ U := by
    intro y
    obtain ⟨p, c, hcp, hyc⟩ := exists_ringPoint_specializes y
    obtain ⟨U, s, hpU, hs⟩ := hsec p
    exact ⟨U, s, hyc.mem_open U.isOpen (hpU hcp), hs⟩
  choose U s hyU hs using hcov
  have hU : iSup U = ⊤ :=
    eq_top_iff.mpr fun y _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hyU y⟩
  have hpb : ∀ y, IsPullback (QuotientCell.multiplication iP (s y)).left
      (fst (openOver Ω Q₀ (U y)) P.X).left π₀.left (U y).ι := by
    intro y
    have h : IsPullback (QuotientCell.multiplication iP (s y)).left
        (fst (openOver Ω Q₀ (U y)) P.X).left π₀.left (s y ≫ π₀).left :=
      (QuotientCell.multiplication_isPullback iP (s y) π₀ hf).map (Over.forget _)
    rw [hs y] at h
    exact h
  have key : ∀ (Pr : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget Pr]
      [Pr.IsStableUnderBaseChange], Pr P.X.hom → Pr π₀.left := by
    intro Pr _ _ hP
    refine of_isPullback_of_iSup_eq_top π₀.left U hU fun y => ⟨_, _, _, hpb y, ?_⟩
    exact MorphismProperty.pullback_fst (P := Pr) _ _ hP
  exact ⟨key @Flat inferInstance, key @Surjective inferInstance,
    key @QuasiCompact inferInstance⟩

end Langlands.GroupScheme.Dynamic
