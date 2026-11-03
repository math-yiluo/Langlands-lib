import Langlands.GroupScheme.Rational.RelativeRootCoxeterConstruction
import Langlands.GroupScheme.Rational.SimpleReflectionConjugacy
import Langlands.Group.RootPairingCoxeterUniqueness

/-! # Supplied root-sign Coxeter systems and actual relative reflections -/

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

namespace RelativeRootCoxeter

variable {R : Type u}
  (P : RootPairing R ℚ (relativeRootSpan i) (Module.Dual ℚ (relativeRootSpan i)))
  (hT : IsSplitTorus T.toGrp)
  (hroots : Subtype.val '' Set.range P.root = toRat '' relativeRoots i)
  (hW : P.weylGroup.map (RootPairing.Equiv.weightHom P) =
    (relativeWeylAction i).range)
  (hfaithful : Function.Injective (relativeWeylAction i))
  (ν : cocharacterLattice T) {C : CoxeterMatrix (SimpleRoot i ν)}
  (cs : CoxeterSystem C (relativeWeylGroup i))

/-- Pull back a supplied system through the faithful-image and actual-base
identifications, preserving its root labels. -/
def pullbackSystem : CoxeterSystem (C.reindex (baseEquiv P hT hroots ν).symm) P.weylGroup :=
  (cs.reindex (baseEquiv P hT hroots ν).symm).map (weylEquiv P hW hfaithful).symm

theorem pullbackSystem_length (w : P.weylGroup) :
    (pullbackSystem P hT hroots hW hfaithful ν cs).length w =
      cs.length (weylEquiv P hW hfaithful w) := by
  symm
  exact coxeterLength_map_eq _ cs (weylEquiv P hW hfaithful)
    (baseEquiv P hT hroots ν) (fun b => by
      change (weylEquiv P hW hfaithful)
        ((weylEquiv P hW hfaithful).symm (cs.simple (baseEquiv P hT hroots ν b))) = _
      exact (weylEquiv P hW hfaithful).apply_symm_apply _) w

theorem pullbackSystem_rootSignLengthLaw
    (hLength : ∀ (w : relativeWeylGroup i) (a : SimpleRoot i ν),
      cs.length w < cs.length (w * cs.simple a) ↔
        schemeWeylCharacterAction i w a.val ∈ positiveRelativeRoots i ν) :
    Group.RootPairingSigns.RootSignLengthLaw P (corootFunctional i ν)
      (pullbackSystem P hT hroots hW hfaithful ν cs) := by
  intro w b
  let φ := weylEquiv P hW hfaithful
  let σ := baseEquiv P hT hroots ν
  have hmul : φ (w * (pullbackSystem P hT hroots hW hfaithful ν cs).simple b) =
      φ w * cs.simple (σ b) := by
    rw [map_mul]
    change φ w * φ (φ.symm (cs.simple (σ b))) = _
    rw [φ.apply_symm_apply]
  rw [pullbackSystem_length, pullbackSystem_length, hmul, hLength,
    functional_smul_root P hT hroots hW hfaithful, Int.cast_pos]
  change (schemeWeylCharacterAction i (φ w) (σ b).val ∈ positiveRelativeRoots i ν) ↔ _
  exact ⟨And.right, fun hp =>
    ⟨schemeWeylCharacterAction_mem_relativeRoots _ (σ b).property.1.1, hp⟩⟩

end RelativeRootCoxeter

/-- The root-sign length law forces every supplied simple generator to be
an actual relative reflection, without an integral-coroot realization. -/
theorem HasRelativeRootSystem.isRelativeReflection_simple_of_rootLength
    (hroot : HasRelativeRootSystem i) (hT : IsSplitTorus T.toGrp)
    {ν : cocharacterLattice T} (hν : IsGenericCocharacter i ν)
    {C : CoxeterMatrix (SimpleRoot i ν)} (cs : CoxeterSystem C (relativeWeylGroup i))
    (hLength : ∀ (w : relativeWeylGroup i) (a : SimpleRoot i ν),
      cs.length w < cs.length (w * cs.simple a) ↔
        schemeWeylCharacterAction i w a.val ∈ positiveRelativeRoots i ν)
    (a : SimpleRoot i ν) : IsRelativeReflection i a.val (cs.simple a) := by
  classical
  obtain ⟨R, hR, P, hP, hcrys, _, hroots, hW, hfaithful⟩ := hroot
  have := hR
  have := hP
  have := hcrys
  let σ := RelativeRootCoxeter.baseEquiv P hT hroots ν
  let φ := RelativeRootCoxeter.weylEquiv P hW hfaithful
  have hf (r : R) : corootFunctional i ν (P.root r) ≠ 0 := by
    rw [RelativeRootCoxeter.functional_root P hT hroots]
    exact_mod_cast hν _ (RelativeRootCoxeter.rootIndexEquiv P hT hroots r).property
  let csP := RelativeRootCoxeter.pullbackSystem P hT hroots hW hfaithful ν cs
  have hEq := Group.RootPairingSigns.simple_eq_of_rootSignLengthLaw P
    (corootFunctional i ν) hf csP
    (RelativeRootCoxeter.pullbackSystem_rootSignLengthLaw P hT hroots hW hfaithful ν cs hLength)
    (σ.symm a)
  have hs : cs.simple a = φ (RootPairing.weylGroup.ofIdx P (σ.symm a)) := by
    have hh := congrArg φ hEq
    change φ (φ.symm (cs.simple (σ (σ.symm a)))) = _ at hh
    simpa only [σ.apply_symm_apply, φ.apply_symm_apply] using hh
  rw [hs]
  have ha : (RelativeRootCoxeter.rootIndexEquiv P hT hroots (σ.symm a).val).val = a.val :=
    congrArg Subtype.val (σ.apply_symm_apply a)
  simpa only [ha] using RelativeRootCoxeter.reflection_weylEquiv P hT hroots hW hfaithful
    (σ.symm a).val

end Langlands.GroupScheme
