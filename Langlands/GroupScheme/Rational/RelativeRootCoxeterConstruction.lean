import Langlands.GroupScheme.Rational.RelativeWeylCoxeterAssembly
import Langlands.GroupScheme.Rational.RelativeReflectionProperties
import Langlands.Group.RootPairingCoxeterProof

/-! # A Coxeter system from the given relative root system -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
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

omit [Mono i.hom.hom.left] in
include hroots in
private theorem exists_character (r : R) :
    ∃ a : relativeRoots i, rootVector i a = P.root r := by
  have hx : (P.root r : ℚ ⊗[ℤ] characterLattice T) ∈ toRat '' relativeRoots i := by
    rw [← hroots]
    exact ⟨P.root r, Set.mem_range_self r, rfl⟩
  obtain ⟨a, ha, heq⟩ := hx
  exact ⟨⟨a, ha⟩, Subtype.ext heq⟩

/-- The root indices in the witness are exactly the actual relative roots. -/
def rootIndexEquiv : R ≃ relativeRoots i :=
  Equiv.ofBijective (fun r => (exists_character P hroots r).choose) (by
    constructor
    · intro r s hrs
      apply P.root.injective
      rw [← (exists_character P hroots r).choose_spec,
        ← (exists_character P hroots s).choose_spec]
      exact congrArg (rootVector i) hrs
    · intro a
      have hx : toRat a.val ∈ Subtype.val '' Set.range P.root := by
        rw [hroots]
        exact ⟨a.val, a.property, rfl⟩
      obtain ⟨_, ⟨r, rfl⟩, hr⟩ := hx
      refine ⟨r, ?_⟩
      apply Subtype.ext
      apply hT.character_toRat_injective
      exact (congrArg Subtype.val (exists_character P hroots r).choose_spec).trans hr)

omit [Mono i.hom.hom.left] in
@[simp] theorem rootVector_rootIndexEquiv (r : R) :
    rootVector i (rootIndexEquiv P hT hroots r) = P.root r :=
  (exists_character P hroots r).choose_spec

@[simp] theorem functional_root (ν : cocharacterLattice T) (r : R) :
    corootFunctional i ν (P.root r) =
      (latticePairing T (rootIndexEquiv P hT hroots r).val ν : ℚ) := by
  rw [← rootVector_rootIndexEquiv P hT hroots r, corootFunctional_rootVector]

/-- Base membership is the actual indecomposability of positive characters. -/
theorem mem_base_iff (ν : cocharacterLattice T) (r : R) :
    r ∈ IsAddIndecomposable.baseOf P.root
        (corootFunctional i ν : relativeRootSpan i →+ ℚ) ↔
      (rootIndexEquiv P hT hroots r).val ∈ simpleRelativeRoots i ν := by
  let e := rootIndexEquiv P hT hroots
  have hf := functional_root P hT hroots ν
  constructor
  · rintro ⟨hpos, hind⟩
    have hpos' : 0 < latticePairing T (e r).val ν := by
      have : (0 : ℚ) < latticePairing T (e r).val ν := by
        rw [← hf]
        exact hpos
      exact_mod_cast this
    refine ⟨⟨(e r).property, hpos'⟩, ?_⟩
    rintro ⟨β, hβ, γ, hγ, heq⟩
    let b := e.symm ⟨β, hβ.1⟩
    let c := e.symm ⟨γ, hγ.1⟩
    have hb : P.root b = rootVector i ⟨β, hβ.1⟩ := by
      rw [← rootVector_rootIndexEquiv P hT hroots b]
      simp [b, e]
    have hc : P.root c = rootVector i ⟨γ, hγ.1⟩ := by
      rw [← rootVector_rootIndexEquiv P hT hroots c]
      simp [c, e]
    have hsum : P.root r = P.root b + P.root c := by
      rw [hb, hc, ← rootVector_rootIndexEquiv P hT hroots r]
      apply Subtype.ext
      change toRat (e r).val = toRat β + toRat γ
      rw [heq, map_add]
    have hbp : 0 < corootFunctional i ν (P.root b) := by
      rw [hb, corootFunctional_rootVector]
      exact_mod_cast hβ.2
    have hcp : 0 < corootFunctional i ν (P.root c) := by
      rw [hc, corootFunctional_rootVector]
      exact_mod_cast hγ.2
    rcases hind b hbp c hcp hsum with hzero | hzero
    · exact P.ne_zero _ hzero
    · exact P.ne_zero _ hzero
  · intro ha
    refine ⟨?_, fun b hb c hc heq => ?_⟩
    · change 0 < corootFunctional i ν (P.root r)
      rw [hf]
      exact_mod_cast ha.1.2
    · exfalso
      apply ha.2
      have hb' : 0 < latticePairing T (e b).val ν := by
        have : (0 : ℚ) < latticePairing T (e b).val ν := by
          rw [← hf]
          exact hb
        exact_mod_cast this
      have hc' : 0 < latticePairing T (e c).val ν := by
        have : (0 : ℚ) < latticePairing T (e c).val ν := by
          rw [← hf]
          exact hc
        exact_mod_cast this
      refine ⟨(e b).val, ⟨(e b).property, hb'⟩,
        (e c).val, ⟨(e c).property, hc'⟩, ?_⟩
      apply hT.character_toRat_injective
      rw [map_add]
      have hvec := congrArg Subtype.val heq
      simpa only [← rootVector_rootIndexEquiv P hT hroots, rootVector,
        Submodule.coe_add] using hvec

/-- The witness base, labelled by the original simple characters. -/
def baseEquiv (ν : cocharacterLattice T) :
    IsAddIndecomposable.baseOf P.root
      (corootFunctional i ν : relativeRootSpan i →+ ℚ) ≃ SimpleRoot i ν where
  toFun b := ⟨(rootIndexEquiv P hT hroots b.val).val,
    (mem_base_iff P hT hroots ν b.val).mp b.property⟩
  invFun a := ⟨(rootIndexEquiv P hT hroots).symm ⟨a.val, a.property.1.1⟩,
    (mem_base_iff P hT hroots ν _).mpr (by simp)⟩
  left_inv b := Subtype.ext ((rootIndexEquiv P hT hroots).symm_apply_apply b.val)
  right_inv a := by
    apply Subtype.ext
    change ((rootIndexEquiv P hT hroots)
      ((rootIndexEquiv P hT hroots).symm ⟨a.val, a.property.1.1⟩)).val = a.val
    exact congrArg Subtype.val
      ((rootIndexEquiv P hT hroots).apply_symm_apply ⟨a.val, a.property.1.1⟩)

variable (hW : P.weylGroup.map (RootPairing.Equiv.weightHom P) =
    (relativeWeylAction i).range)
  (hfaithful : Function.Injective (relativeWeylAction i))

/-- Both groups have the same faithful linear image. -/
def weylEquiv : P.weylGroup ≃* relativeWeylGroup i :=
  (MonoidHom.ofInjective (fun a b hab => Subtype.ext
    (RootPairing.Equiv.weightHom_injective P hab))).trans
    ((MulEquiv.subgroupCongr (by
        rw [MonoidHom.domRestrict_range]
        exact hW)).trans (MonoidHom.ofInjective hfaithful).symm)

theorem action_weylEquiv (w : P.weylGroup) :
    relativeWeylAction i (weylEquiv P hW hfaithful w) =
      RootPairing.Equiv.weightHom P w.val := by
  change relativeWeylAction i ((MonoidHom.ofInjective hfaithful).symm _) = _
  rw [← MonoidHom.ofInjective_apply hfaithful, MulEquiv.apply_symm_apply]
  rfl

theorem reflection_weylEquiv (r : R) :
    IsRelativeReflection i (rootIndexEquiv P hT hroots r).val
      (weylEquiv P hW hfaithful (RootPairing.weylGroup.ofIdx P r)) := by
  have hf : P.coroot' r (rootVector i (rootIndexEquiv P hT hroots r)) = 2 := by
    rw [rootVector_rootIndexEquiv]
    exact P.coroot_root_two r
  refine ⟨(rootIndexEquiv P hT hroots r).property, P.coroot' r, hf, ?_⟩
  change relativeWeylAction i
    (weylEquiv P hW hfaithful (RootPairing.weylGroup.ofIdx P r)) =
      Module.reflection (x := rootVector i (rootIndexEquiv P hT hroots r)) hf
  rw [action_weylEquiv]
  simp only [RootPairing.weylGroup.ofIdx, RootPairing.Equiv.weightHom_apply,
    RootPairing.Equiv.reflection_weightEquiv]
  apply LinearEquiv.ext
  intro x
  rw [P.reflection_apply, Module.reflection_apply, rootVector_rootIndexEquiv]

theorem functional_smul_root (ν : cocharacterLattice T) (w : P.weylGroup) (r : R) :
    corootFunctional i ν (w • P.root r) =
      (latticePairing T (schemeWeylCharacterAction i
        (weylEquiv P hW hfaithful w) (rootIndexEquiv P hT hroots r).val) ν : ℚ) := by
  have hv : w • P.root r = relativeWeylAction i (weylEquiv P hW hfaithful w)
      (rootVector i (rootIndexEquiv P hT hroots r)) := by
    rw [action_weylEquiv, rootVector_rootIndexEquiv]
    rfl
  rw [hv, relativeWeylAction_rootVector, corootFunctional_rootVector]

end RelativeRootCoxeter

/-- The given relative-root-system witness suffices for a finite Coxeter system
whose simple generators are actual root-span reflections and whose right length
increases precisely on positive simple-root images. -/
theorem HasRelativeRootSystem.exists_rootSpanCoxeterSystem
    (hroot : HasRelativeRootSystem i) (hT : IsSplitTorus T.toGrp)
    {ν : cocharacterLattice T} (hν : IsGenericCocharacter i ν) :
    Finite (relativeWeylGroup i) ∧ Finite (SimpleRoot i ν) ∧
      ∃ (C : CoxeterMatrix (SimpleRoot i ν))
        (cs : CoxeterSystem C (relativeWeylGroup i)),
        (∀ a : SimpleRoot i ν, IsRelativeReflection i a.val (cs.simple a)) ∧
        (∀ (w : relativeWeylGroup i) (a : SimpleRoot i ν),
          cs.length w < cs.length (w * cs.simple a) ↔
            schemeWeylCharacterAction i w a.val ∈ positiveRelativeRoots i ν) := by
  classical
  obtain ⟨R, hR, P, hP, hcrys, _, hroots, hW, hfaithful⟩ := hroot
  have := hR
  have := hP
  have := hcrys
  let e := RelativeRootCoxeter.rootIndexEquiv P hT hroots
  let σ := RelativeRootCoxeter.baseEquiv P hT hroots ν
  let φ := RelativeRootCoxeter.weylEquiv P hW hfaithful
  have hf (r : R) : corootFunctional i ν (P.root r) ≠ 0 := by
    rw [RelativeRootCoxeter.functional_root P hT hroots]
    exact_mod_cast hν (e r).val (e r).property
  obtain ⟨hfin, C, cs, hsimple, _, hdescent⟩ :=
    Langlands.Group.rootPairingWeylCoxeterStatement_proof R ℚ _ _ P
      (corootFunctional i ν) hf
  have := hfin
  let cs' := (cs.reindex σ).map φ
  have hlen (w : P.weylGroup) : cs'.length (φ w) = cs.length w :=
    coxeterLength_map_eq cs cs' φ σ (fun b => by
      change φ (cs.simple b) = φ (cs.simple (σ.symm (σ b)))
      rw [Equiv.symm_apply_apply]) w
  refine ⟨Finite.of_equiv P.weylGroup φ.toEquiv,
    Finite.of_equiv _ σ, _, cs', ?_, ?_⟩
  · intro a
    change IsRelativeReflection i a.val (φ (cs.simple (σ.symm a)))
    rw [hsimple]
    have h := RelativeRootCoxeter.reflection_weylEquiv P hT hroots hW hfaithful
      (σ.symm a).val
    have ha : (e (σ.symm a).val).val = a.val :=
      congrArg Subtype.val (σ.apply_symm_apply a)
    simpa only [φ, ← ha] using h
  · intro w a
    obtain ⟨v, rfl⟩ := φ.surjective w
    have hmul : φ v * cs'.simple a = φ (v * cs.simple (σ.symm a)) := by
      rw [map_mul]
      rfl
    rw [hmul, hlen, hlen, hdescent,
      RelativeRootCoxeter.functional_smul_root P hT hroots hW hfaithful,
      Int.cast_pos]
    have ha : (e (σ.symm a).val).val = a.val :=
      congrArg Subtype.val (σ.apply_symm_apply a)
    rw [ha]
    exact ⟨fun hp => ⟨schemeWeylCharacterAction_mem_relativeRoots _ a.property.1.1, hp⟩,
      And.right⟩

end Langlands.GroupScheme
