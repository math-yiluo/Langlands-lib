import Langlands.GroupScheme.Rational.RootSignCoxeterComparison

/-! # Positive simple-root conjugacy from actual root-span reflections -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme

open RelativeRootSystem Langlands.Aubert.General.RationalPointFamily

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : T.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
  {ν : cocharacterLattice T} {C : CoxeterMatrix (SimpleRoot i ν)}
  (cs : CoxeterSystem C (relativeWeylGroup i))

/-- With a positive image root, conjugacy of labelled simple reflections is
exactly equality of their actual character labels. -/
def PositiveSimpleReflectionLaw : Prop :=
  ∀ (w : relativeWeylGroup i) (a b : SimpleRoot i ν),
    schemeWeylCharacterAction i w a.val ∈ positiveRelativeRoots i ν →
      (w * cs.simple a * w⁻¹ = cs.simple b ↔
        schemeWeylCharacterAction i w a.val = b.val)

/-- Actual root-span reflection generators detect their positive root labels,
without any integral-coroot realization. -/
theorem HasRelativeRootSystem.root_eq_of_conj_simple_reflections
    (hroot : HasRelativeRootSystem i) (hT : IsSplitTorus T.toGrp)
    (hν : IsGenericCocharacter i ν)
    (hSimple : ∀ a : SimpleRoot i ν, IsRelativeReflection i a.val (cs.simple a))
    (w : relativeWeylGroup i) (a b : SimpleRoot i ν)
    (hpos : schemeWeylCharacterAction i w a.val ∈ positiveRelativeRoots i ν)
    (heq : w * cs.simple a * w⁻¹ = cs.simple b) :
    schemeWeylCharacterAction i w a.val = b.val := by
  classical
  have hrootCopy := hroot
  rcases hrootCopy with ⟨R, hR, P, hP, hcrys, _, hroots, hW, hfaithful⟩
  have := hR
  have := hP
  have := hcrys
  let e := RelativeRootCoxeter.rootIndexEquiv P hT hroots
  let σ := RelativeRootCoxeter.baseEquiv P hT hroots ν
  let φ := RelativeRootCoxeter.weylEquiv P hW hfaithful
  have hf (r : R) : corootFunctional i ν (P.root r) ≠ 0 := by
    rw [RelativeRootCoxeter.functional_root P hT hroots]
    exact_mod_cast hν _ (e r).property
  have hlabel (c : SimpleRoot i ν) : (e (σ.symm c).val).val = c.val :=
    congrArg Subtype.val (σ.apply_symm_apply c)
  have hs (c : SimpleRoot i ν) :
      cs.simple c = φ (RootPairing.weylGroup.ofIdx P (σ.symm c).val) := by
    apply hroot.eq_of_isRelativeReflection (hSimple c)
    have hr := RelativeRootCoxeter.reflection_weylEquiv P hT hroots hW hfaithful (σ.symm c).val
    change IsRelativeReflection i (e (σ.symm c).val).val
      (φ (RootPairing.weylGroup.ofIdx P (σ.symm c).val)) at hr
    simpa only [hlabel] using hr
  have hp : 0 < corootFunctional i ν (φ.symm w • P.root (σ.symm a).val) := by
    rw [RelativeRootCoxeter.functional_smul_root P hT hroots hW hfaithful,
      φ.apply_symm_apply, hlabel, Int.cast_pos]
    exact hpos.2
  have hconj : φ.symm w * RootPairing.weylGroup.ofIdx P (σ.symm a).val *
      (φ.symm w)⁻¹ = RootPairing.weylGroup.ofIdx P (σ.symm b).val := by
    apply φ.injective
    simpa only [map_mul, map_inv, φ.apply_symm_apply, ← hs] using heq
  have hvec := Group.RootPairingSigns.root_eq_of_conj_simple P
    (corootFunctional i ν) hf (φ.symm w) (σ.symm a).property (σ.symm b).property hp hconj
  have hv : φ.symm w • P.root (σ.symm a).val =
      relativeWeylAction i w (rootVector i (e (σ.symm a).val)) := by
    calc
      _ = relativeWeylAction i (φ (φ.symm w)) (rootVector i (e (σ.symm a).val)) := by
        rw [RelativeRootCoxeter.action_weylEquiv,
          RelativeRootCoxeter.rootVector_rootIndexEquiv]
        rfl
      _ = _ := by rw [φ.apply_symm_apply]
  rw [hv, relativeWeylAction_rootVector,
    ← RelativeRootCoxeter.rootVector_rootIndexEquiv P hT hroots] at hvec
  apply hT.character_toRat_injective
  have hchars := congrArg Subtype.val hvec
  change toRat (schemeWeylCharacterAction i w (e (σ.symm a).val).val) =
    toRat (e (σ.symm b).val).val at hchars
  simpa only [hlabel] using hchars

/-- The positive conjugacy criterion holds for any system whose simple
matrices are actual root-span reflections. -/
theorem HasRelativeRootSystem.positiveSimpleReflectionLaw_of_reflections
    (hroot : HasRelativeRootSystem i) (hT : IsSplitTorus T.toGrp)
    (hν : IsGenericCocharacter i ν)
    (hSimple : ∀ a : SimpleRoot i ν, IsRelativeReflection i a.val (cs.simple a)) :
    PositiveSimpleReflectionLaw cs := by
  intro w a b hpos
  refine ⟨hroot.root_eq_of_conj_simple_reflections cs hT hν hSimple w a b hpos, ?_⟩
  intro hab
  have hr := (hSimple a).conj w
  rw [hab] at hr
  exact hroot.eq_of_isRelativeReflection hr (hSimple b)

/-- In particular the root-sign length law alone supplies the criterion for
a given system, since it determines the actual simple reflections. -/
theorem HasRelativeRootSystem.positiveSimpleReflectionLaw_of_rootLength
    (hroot : HasRelativeRootSystem i) (hT : IsSplitTorus T.toGrp)
    (hν : IsGenericCocharacter i ν)
    (hLength : ∀ (w : relativeWeylGroup i) (a : SimpleRoot i ν),
      cs.length w < cs.length (w * cs.simple a) ↔
        schemeWeylCharacterAction i w a.val ∈ positiveRelativeRoots i ν) :
    PositiveSimpleReflectionLaw cs :=
  hroot.positiveSimpleReflectionLaw_of_reflections cs hT hν
    (hroot.isRelativeReflection_simple_of_rootLength hT hν cs hLength)

end Langlands.GroupScheme
