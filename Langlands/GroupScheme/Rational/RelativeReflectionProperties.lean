import Langlands.GroupScheme.Rational.RelativeReflection
import Langlands.GroupScheme.Rational.RootReflectionAssembly
import Langlands.GroupScheme.Rational.RelativeRootStandardCocharacter

/-! # Relative reflection properties under the actual root-system realization -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : T.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]

/-- A relative reflection is nontrivial, without a structural root-system hypothesis. -/
theorem IsRelativeReflection.ne_one {α : characterLattice T} {w : relativeWeylGroup i}
    (h : IsRelativeReflection i α w) : w ≠ 1 := by
  have heq := h.relativeWeylAction_apply_self
  obtain ⟨hα, f, hf, hw⟩ := h
  intro hw1
  have hsame : RelativeRootSystem.rootVector i ⟨α, hα⟩ =
      -RelativeRootSystem.rootVector i ⟨α, hα⟩ :=
    (DFunLike.congr_fun ((congrArg (relativeWeylAction i) hw1).trans (map_one _)) _).symm.trans heq
  have htwo := congrArg f hsame
  have hf' : f (RelativeRootSystem.rootVector i ⟨α, hα⟩) = 2 := hf
  rw [map_neg, hf'] at htwo
  norm_num at htwo

/-- In the faithful actual root action, every relative reflection squares to one. -/
theorem HasRelativeRootSystem.mul_self_of_isRelativeReflection
    (hroot : HasRelativeRootSystem i) {α : characterLattice T} {w : relativeWeylGroup i}
    (h : IsRelativeReflection i α w) : w * w = 1 := by
  obtain ⟨hα, f, hf, hw⟩ := h
  apply hroot.choose_spec.choose_spec.choose_spec.2.2.2.2.2
  rw [map_mul, map_one, hw]
  apply LinearEquiv.ext
  exact Module.involutive_reflection hf

/-- Every actual relative root has a reflection in the actual quotient when that quotient
realizes the published root system. -/
theorem HasRelativeRootSystem.exists_isRelativeReflection
    (hroot : HasRelativeRootSystem i) {α : characterLattice T} (hα : α ∈ relativeRoots i) :
    ∃ w : relativeWeylGroup i, IsRelativeReflection i α w := by
  obtain ⟨J, hJ, P, hP, hcrys, heval, hroots, hW, hfaithful⟩ := hroot
  have hx : toRat α ∈ Subtype.val '' Set.range P.root := by
    rw [hroots]
    exact Set.mem_image_of_mem _ hα
  obtain ⟨_, ⟨j, rfl⟩, hj⟩ := hx
  have hj' : P.root j = RelativeRootSystem.rootVector i ⟨α, hα⟩ := Subtype.ext hj
  have hr : P.reflection j ∈ (relativeWeylAction i).range := by
    rw [← hW]
    exact Subgroup.mem_map.mpr ⟨RootPairing.Equiv.reflection P j,
      P.reflection_mem_weylGroup j, RootPairing.Equiv.reflection_weightEquiv P j⟩
  obtain ⟨w, hw⟩ := hr
  have hf : P.coroot' j (RelativeRootSystem.rootVector i ⟨α, hα⟩) = 2 := by
    rw [← hj']
    exact P.coroot_root_two j
  refine ⟨w, hα, P.coroot' j, hf, ?_⟩
  rw [hw]
  apply LinearEquiv.ext
  intro x
  calc
    P.reflection j x = x - P.coroot' j x • P.root j := P.reflection_apply j x
    _ = x - P.coroot' j x • RelativeRootSystem.rootVector i ⟨α, hα⟩ := by rw [hj']
    _ = Module.reflection hf x := (Module.reflection_apply x hf).symm

/-- Finiteness and spanning of the realized root system make a relative reflection unique. -/
theorem HasRelativeRootSystem.eq_of_isRelativeReflection
    (hroot : HasRelativeRootSystem i) {α : characterLattice T} {w w' : relativeWeylGroup i}
    (h : IsRelativeReflection i α w) (h' : IsRelativeReflection i α w') : w = w' := by
  obtain ⟨J, hJ, P, hP, _, _, _, hW, hfaithful⟩ := hroot
  have := hJ
  have := hP
  have hmaps (v : relativeWeylGroup i) :
      Set.MapsTo (relativeWeylAction i v) (Set.range P.root) (Set.range P.root) := by
    have hv : relativeWeylAction i v ∈ P.weylGroup.map (RootPairing.Equiv.weightHom P) := by
      rw [hW]
      exact MonoidHom.mem_range.mpr ⟨v, rfl⟩
    obtain ⟨e, he, hev⟩ := Subgroup.mem_map.mp hv
    rintro _ ⟨j, rfl⟩
    rw [← hev]
    exact ⟨e.indexEquiv j, (RootPairing.Hom.root_weightMap_apply _ _ _ _).symm⟩
  obtain ⟨hα, f, hf, hw⟩ := h
  obtain ⟨hα', g, hg, hw'⟩ := h'
  have hfg : f = g := Module.Dual.eq_of_preReflection_mapsTo (Set.finite_range P.root)
    (RootPairing.IsRootSystem.span_root_eq_top (P := P)) hf
    (by
      intro x hx
      change Module.reflection hf x ∈ Set.range P.root
      rw [← hw]
      exact hmaps w hx) hg (by
      intro x hx
      change Module.reflection hg x ∈ Set.range P.root
      rw [← hw']
      exact hmaps w' hx)
  apply hfaithful
  subst g
  exact hw.trans hw'.symm

/-- The existence and uniqueness clause needed in the relative Tits-system target. -/
theorem HasRelativeRootSystem.existsUnique_isRelativeReflection
    (hroot : HasRelativeRootSystem i) {α : characterLattice T} (hα : α ∈ relativeRoots i) :
    ∃! w : relativeWeylGroup i, IsRelativeReflection i α w := by
  obtain ⟨w, hw⟩ := hroot.exists_isRelativeReflection hα
  exact ⟨w, hw, fun v hv => hroot.eq_of_isRelativeReflection hv hw⟩

/-- The uniquely determined actual quotient reflection of a relative root,
chosen under the published root-system predicate. -/
def relativeReflectionOfRootSystem (hroot : HasRelativeRootSystem i) (α : relativeRoots i) :
    relativeWeylGroup i :=
  (hroot.exists_isRelativeReflection α.property).choose

theorem isRelativeReflection_relativeReflectionOfRootSystem
    (hroot : HasRelativeRootSystem i) (α : relativeRoots i) :
    IsRelativeReflection i α.val (relativeReflectionOfRootSystem hroot α) :=
  (hroot.exists_isRelativeReflection α.property).choose_spec

/-- Distinct simple roots have distinct relative reflections, including for nonreduced systems. -/
theorem HasRelativeRootSystem.eq_of_simple_isRelativeReflection
    (hroot : HasRelativeRootSystem i) (hT : IsSplitTorus T.toGrp)
    {ν : cocharacterLattice T} (hν : IsGenericCocharacter i ν)
    {α β : characterLattice T} (hα : α ∈ simpleRelativeRoots i ν)
    (hβ : β ∈ simpleRelativeRoots i ν) {w : relativeWeylGroup i}
    (hαw : IsRelativeReflection i α w) (hβw : IsRelativeReflection i β w) : α = β := by
  obtain ⟨hαr, f, hf, hw⟩ := hαw
  let x := RelativeRootSystem.rootVector i ⟨α, hαr⟩
  let y := RelativeRootSystem.rootVector i ⟨β, hβw.mem_relativeRoots⟩
  have heq : y - f y • x = -y := by
    calc
      y - f y • x = Module.reflection hf y := (Module.reflection_apply y hf).symm
      _ = relativeWeylAction i w y := by rw [hw]
      _ = -y := hβw.relativeWeylAction_apply_self
  have hsmul : (2 : ℚ) • y = f y • x := by
    calc
      (2 : ℚ) • y = y + y := two_smul _ _
      _ = (y - f y • x) + (f y • x + y) := by abel
      _ = f y • x := by rw [heq]; abel
  have hsmul' : (2 : ℚ) • toRat β = f y • toRat α := congrArg Subtype.val hsmul
  have hli := hroot.linearIndependent_simpleRelativeRoots i ν hT hν
  have hab := hli.eq_of_smul_apply_eq_smul_apply 2 (f y) ⟨β, hβ⟩ ⟨α, hα⟩
    (by norm_num) hsmul'
  exact (congrArg Subtype.val hab).symm

end Langlands.GroupScheme
