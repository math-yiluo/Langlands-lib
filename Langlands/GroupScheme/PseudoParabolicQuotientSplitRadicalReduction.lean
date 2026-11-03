import Langlands.GroupScheme.HomogeneousQuotientFactorization
import Langlands.GroupScheme.HomogeneousQuotientSectionTransport
import Langlands.GroupScheme.PseudoParabolic
import Langlands.GroupScheme.Rational.FppfQuotientSmooth
import Langlands.AlgebraicGeometry.SmoothEtaleSourceDescentProof

/-! # Actual quotient maps in the split-radical reduction

Given an fppf quotient by a represented split ground-field unipotent radical,
the supplied pseudo-parabolic quotient factors through it. Its actual target,
geometric projection properties and all-test coset condition are retained.
Structural existence of the group quotient and its pseudo-parabolic subgroup
are separate prerequisites.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
variable {G P N H K : GroupScheme (Spec (CommRingCat.of k))}

/-- A represented split ground-field radical lies in every pseudo-parabolic
subgroup, on all relative scheme tests. -/
theorem IsPseudoParabolicSubgroup.splitRadical_le {i : P ⟶ G}
    (hi : IsPseudoParabolicSubgroup i) {n : N ⟶ G}
    (hn : IsSplitUnipotentRadical n) :
    SubgroupFunctor.range n ≤ SubgroupFunctor.range i := by
  obtain ⟨U, j, χ, hj, hprod⟩ := hi.presentation
  exact (hn.range_le_unipotentRadical hj).trans hprod.right_le

namespace PseudoParabolicQuotientSplitRadicalReduction

private theorem quasiCompact_of_surjective_comp
    {X Y Z : Scheme.{u}} (p : X ⟶ Y) (r : Y ⟶ Z)
    [Surjective p] [QuasiCompact (p ≫ r)] : QuasiCompact r := by
  constructor
  intro U hU hc
  have he : p '' ((p ≫ r) ⁻¹' U) = r ⁻¹' U := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      obtain ⟨x, rfl⟩ := p.surjective y
      exact ⟨x, hy, rfl⟩
  rw [← he]
  exact (QuasiCompact.isCompact_preimage (f := p ≫ r) U hU hc).image p.continuous

variable (i : P ⟶ G) (hi : IsPseudoParabolicSubgroup i)
variable (n : N ⟶ G) (hn : IsSplitUnipotentRadical n)
variable (f : G ⟶ H)
variable (hf : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range n) f)
variable {Q : Over (Spec (CommRingCat.of k))} (q : G.X ⟶ Q)
variable (hfib : ∀ (T : Over (Spec (CommRingCat.of k))) (a b : T ⟶ G.X),
  a ≫ q = b ≫ q ↔ a⁻¹ * b ∈ (SubgroupFunctor.range i).carrier T)

include hi hn hf in
/-- The supplied split-radical quotient has kernel contained in the original
pseudo-parabolic subgroup. -/
theorem kernel_le : SubgroupFunctor.range (kernelι f) ≤ SubgroupFunctor.range i := by
  rw [hf.2.2.2]
  exact hi.splitRadical_le hn

variable [QuasiCompact f.hom.hom.left]

include hn hf in
/-- The group quotient is smooth because its represented split-radical kernel
is smooth; this requires no additional smoothness premise on the projection. -/
theorem groupQuotient_smooth : Smooth f.hom.hom.left := by
  let : IsClosedImmersion n.hom.hom.left := hn.isClosedSubgroup
  have hrep : (SubgroupFunctor.range n).IsRepresentedBy n :=
    ⟨Over.mono_of_mono_left n.hom.hom, rfl⟩
  exact hf.smooth_of_smooth_kernel hrep hn.smooth

section Map

include hi hn hf hfib

/-- The actual projection from the supplied split-radical group quotient to
the same original homogeneous quotient target. -/
def quotientMap : H.X ⟶ Q := by
  let : Flat f.hom.hom.left := hf.1
  let : Surjective f.hom.hom.left := hf.2.1
  exact HomogeneousQuotientFactorization.desc f (SubgroupFunctor.range i) q hfib
    (kernel_le i hi n hn f hf)

@[reassoc]
theorem fac_quotientMap :
    f.hom.hom ≫ quotientMap i hi n hn f hf q hfib = q := by
  let : Flat f.hom.hom.left := hf.1
  let : Surjective f.hom.hom.left := hf.2.1
  exact HomogeneousQuotientFactorization.fac_desc f (SubgroupFunctor.range i) q hfib
    (kernel_le i hi n hn f hf)

/-- The original projection equation uniquely determines the reduced map. -/
theorem quotientMap_unique (r : H.X ⟶ Q) (hr : f.hom.hom ≫ r = q) :
    r = quotientMap i hi n hn f hf q hfib := by
  let : Flat f.hom.hom.left := hf.1
  let : Surjective f.hom.hom.left := hf.2.1
  exact HomogeneousQuotientFactorization.desc_unique f (SubgroupFunctor.range i) q hfib
    (kernel_le i hi n hn f hf) r hr

/-- The reduced projection is surjective whenever the original is. -/
theorem quotientMap_surjective [Surjective q.left] :
    Surjective (quotientMap i hi n hn f hf q hfib).left := by
  have he : f.hom.hom.left ≫ (quotientMap i hi n hn f hf q hfib).left = q.left :=
    congrArg (fun a => a.left) (fac_quotientMap i hi n hn f hf q hfib)
  have : Surjective (f.hom.hom.left ≫ (quotientMap i hi n hn f hf q hfib).left) := by
    rw [he]
    infer_instance
  exact Surjective.of_comp f.hom.hom.left _

/-- The reduced projection is quasi-compact whenever the original is. -/
theorem quotientMap_quasiCompact [QuasiCompact q.left] :
    QuasiCompact (quotientMap i hi n hn f hf q hfib).left := by
  let : Surjective f.hom.hom.left := hf.2.1
  have he : f.hom.hom.left ≫ (quotientMap i hi n hn f hf q hfib).left = q.left :=
    congrArg (fun a => a.left) (fac_quotientMap i hi n hn f hf q hfib)
  have : QuasiCompact (f.hom.hom.left ≫ (quotientMap i hi n hn f hf q hfib).left) := by
    rw [he]
    infer_instance
  exact quasiCompact_of_surjective_comp f.hom.hom.left _

/-- Smoothness of the original projection descends along the group quotient,
whose smoothness follows from the represented split radical. -/
theorem quotientMap_smooth [Smooth q.left] :
    Smooth (quotientMap i hi n hn f hf q hfib).left := by
  let : Smooth f.hom.hom.left := groupQuotient_smooth n hn f hf
  let : Surjective f.hom.hom.left := hf.2.1
  have he : f.hom.hom.left ≫ (quotientMap i hi n hn f hf q hfib).left = q.left :=
    congrArg (fun a => a.left) (fac_quotientMap i hi n hn f hf q hfib)
  have : Smooth (f.hom.hom.left ≫ (quotientMap i hi n hn f hf q hfib).left) := by
    rw [he]
    infer_instance
  exact Langlands.AlgebraicGeometry.smooth_of_smooth_of_surjective_of_smooth_comp
    f.hom.hom.left _

/-- A supplied pseudo-parabolic subgroup in the reduced group with the exact
full preimage gives the original all-test right-coset condition for the map. -/
theorem quotientMap_fibers (j : K ⟶ H) (hj : IsPseudoParabolicSubgroup j)
    (hpre : SubgroupFunctor.range i = (SubgroupFunctor.range j).comap f)
    (T : Over (Spec (CommRingCat.of k))) (a b : T ⟶ H.X) :
    a ≫ quotientMap i hi n hn f hf q hfib = b ≫ quotientMap i hi n hn f hf q hfib ↔
      a⁻¹ * b ∈ (SubgroupFunctor.range j).carrier T := by
  let : Flat f.hom.hom.left := hf.1
  let : Surjective f.hom.hom.left := hf.2.1
  let : IsClosedImmersion j.hom.hom.left := hj.isClosedSubgroup
  let : Mono j.hom.hom := Over.mono_of_mono_left j.hom.hom
  exact HomogeneousQuotientFactorization.fibers_of_factorization
    f (SubgroupFunctor.range i) q hfib (quotientMap i hi n hn f hf q hfib)
    (fac_quotientMap i hi n hn f hf q hfib) j hpre T a b

/-- If the group quotient lifts every affine test, all-point local sections
of the reduced projection lift to the original supplied projection. -/
theorem localSections_of_quotientMap
    (hlift : ∀ (T : Over (Spec (CommRingCat.of k))) [IsAffine T.left]
      (a : T ⟶ H.X), ∃ b : T ⟶ G.X, b ≫ f.hom.hom = a)
    (hsec : ∀ x : Q.left, ∃ (U : Q.left.Opens) (s : openOver k Q U ⟶ H.X),
      x ∈ U ∧ s ≫ quotientMap i hi n hn f hf q hfib = openOverι k Q U) :
    ∀ x : Q.left, ∃ (U : Q.left.Opens) (s : openOver k Q U ⟶ G.X),
      x ∈ U ∧ s ≫ q = openOverι k Q U := by
  have h := HomogeneousQuotientSectionTransport.localSections_comp_of_affine_lifts
    k f.hom.hom (quotientMap i hi n hn f hf q hfib) hlift hsec
  simpa only [fac_quotientMap] using h

end Map
end PseudoParabolicQuotientSplitRadicalReduction
end Langlands.GroupScheme
