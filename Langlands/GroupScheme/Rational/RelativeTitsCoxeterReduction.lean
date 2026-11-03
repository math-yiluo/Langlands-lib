import Langlands.GroupScheme.Rational.RelativeTitsSystemStatement
import Langlands.GroupScheme.Rational.StandardRelativeWeylGenerationReduction
import Langlands.Group.CoxeterSimpleInjective

/-! # The Weyl-group part of the relative Tits system from a Coxeter realization

A Coxeter realization of the actual relative Weyl group `N(k)/Z(k)`, labelled by the simple
relative roots (the conclusion of `RelativeWeylCoxeterStatement`, not proved here), gives every
part of `HasRelativeTitsSystem` that concerns only the Weyl group: the simple relative
reflections are the Coxeter generators, so they generate the group and are nontrivial
involutions, each simple root has exactly one reflection, and distinct simple roots have
distinct reflections. The remaining Tits axioms, which concern `B = P_∅(k)` and `N(k)`, are
hypotheses of the packaging theorems.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open Langlands.Aubert.General.RationalPointFamily

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}

/-- The Tits axioms of the relative data `(G(k), B, N(k), S)`, with `B = P_∅(k)`,
`N(k) = normalizerPoints i`, `π : N(k) → N(k)/Z(k)` and `S = simpleRelativeReflections i ν`,
that involve `B`: the kernel identity `ker π = B ∩ N(k)`, generation `B ⊔ N(k) = G(k)`, the
Bruhat multiplication axiom `s B w ⊆ B w B ∪ B s w B` for every representative, and
nondegeneracy `n B n⁻¹ ⊈ B` for every representative `n` of `s ∈ S`. These are the fields
`ker_eq`, `sup_eq`, `mul_mem_cell` and `conj_not_le` of `Langlands.Group.IsTitsSystem`. -/
def HasRelativeTitsBorelAxioms (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
    (ν : cocharacterLattice T) : Prop :=
  (QuotientGroup.mk' ((centralizerPoints i).subgroupOf (normalizerPoints i))).ker =
      (standardParabolicPoints i ν ∅).subgroupOf (normalizerPoints i) ∧
    standardParabolicPoints i ν ∅ ⊔ normalizerPoints i = ⊤ ∧
    (∀ s ∈ simpleRelativeReflections i ν, ∀ n m : normalizerPoints i,
      QuotientGroup.mk' ((centralizerPoints i).subgroupOf (normalizerPoints i)) n = s →
      ∀ b ∈ standardParabolicPoints i ν ∅,
        (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) * b * m ∈
          Langlands.Group.TitsSystem.cell (standardParabolicPoints i ν ∅)
              (QuotientGroup.mk' ((centralizerPoints i).subgroupOf (normalizerPoints i)))
              (QuotientGroup.mk' ((centralizerPoints i).subgroupOf (normalizerPoints i)) m) ∪
            Langlands.Group.TitsSystem.cell (standardParabolicPoints i ν ∅)
              (QuotientGroup.mk' ((centralizerPoints i).subgroupOf (normalizerPoints i)))
              (s * QuotientGroup.mk' ((centralizerPoints i).subgroupOf (normalizerPoints i)) m)) ∧
    ∀ s ∈ simpleRelativeReflections i ν, ∀ n : normalizerPoints i,
      QuotientGroup.mk' ((centralizerPoints i).subgroupOf (normalizerPoints i)) n = s →
      ∃ b ∈ standardParabolicPoints i ν ∅,
        (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) * b *
          (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)⁻¹ ∉
            standardParabolicPoints i ν ∅

variable {i : T.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom] {ν : cocharacterLattice T}
  {M : CoxeterMatrix (SimpleRoot i ν)} {cs : CoxeterSystem M (relativeWeylGroup i)}

/-- A relative Tits system satisfies the Tits axioms that involve `B = P_∅(k)`. -/
theorem HasRelativeTitsSystem.hasRelativeTitsBorelAxioms (h : HasRelativeTitsSystem i ν) :
    HasRelativeTitsBorelAxioms i ν :=
  ⟨h.1.ker_eq, h.1.sup_eq, h.1.mul_mem_cell, h.1.conj_not_le⟩

namespace IsRelativeWeylCoxeterRealization

/-- In a Coxeter realization, the simple relative reflections generate the relative Weyl
group. -/
theorem closure_simpleRelativeReflections_eq_top (h : IsRelativeWeylCoxeterRealization i ν cs) :
    Subgroup.closure (simpleRelativeReflections i ν) = ⊤ := by
  rw [eq_top_iff, ← cs.subgroup_closure_range_simple]
  apply Subgroup.closure_mono
  rintro _ ⟨a, rfl⟩
  exact ⟨a.1, a.2, h.isRelativeReflection_simple a⟩

variable [Finite (relativeWeylGroup i)] (hT : IsSplitTorus T.toGrp)
include hT

/-- In a Coxeter realization of a finite relative Weyl group of a split torus, the simple
relative reflections are exactly the Coxeter generators. -/
theorem simpleRelativeReflections_eq_range (h : IsRelativeWeylCoxeterRealization i ν cs) :
    simpleRelativeReflections i ν = Set.range cs.simple := by
  ext w
  constructor
  · rintro ⟨α, hα, hw⟩
    exact ⟨⟨α, hα⟩, (h.eq_simple_of_isRelativeReflection hT ⟨α, hα⟩ hw).symm⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a.1, a.2, h.isRelativeReflection_simple a⟩

/-- A simple relative reflection is nontrivial. -/
theorem ne_one_of_mem_simpleRelativeReflections (h : IsRelativeWeylCoxeterRealization i ν cs)
    {s : relativeWeylGroup i} (hs : s ∈ simpleRelativeReflections i ν) : s ≠ 1 := by
  rw [h.simpleRelativeReflections_eq_range hT] at hs
  obtain ⟨a, rfl⟩ := hs
  intro h1
  have hlen := cs.length_simple a
  rw [h1, cs.length_one] at hlen
  exact zero_ne_one hlen

/-- A simple relative reflection is an involution. -/
theorem mul_self_of_mem_simpleRelativeReflections (h : IsRelativeWeylCoxeterRealization i ν cs)
    {s : relativeWeylGroup i} (hs : s ∈ simpleRelativeReflections i ν) : s * s = 1 := by
  rw [h.simpleRelativeReflections_eq_range hT] at hs
  obtain ⟨a, rfl⟩ := hs
  exact cs.simple_mul_simple_self a

/-- Every simple relative root has exactly one relative reflection, its Coxeter generator. -/
theorem existsUnique_isRelativeReflection (h : IsRelativeWeylCoxeterRealization i ν cs)
    {α : characterLattice T} (hα : α ∈ simpleRelativeRoots i ν) :
    ∃! w : relativeWeylGroup i, IsRelativeReflection i α w :=
  ⟨cs.simple ⟨α, hα⟩, h.isRelativeReflection_simple ⟨α, hα⟩,
    fun _ hw => h.eq_simple_of_isRelativeReflection hT ⟨α, hα⟩ hw⟩

/-- Two simple relative roots with a common relative reflection are equal: both reflections
are Coxeter generators, and distinct indices give distinct simple reflections. -/
theorem eq_of_isRelativeReflection (h : IsRelativeWeylCoxeterRealization i ν cs)
    {α β : characterLattice T} (hα : α ∈ simpleRelativeRoots i ν)
    (hβ : β ∈ simpleRelativeRoots i ν) {w : relativeWeylGroup i}
    (hαw : IsRelativeReflection i α w) (hβw : IsRelativeReflection i β w) : α = β := by
  have hα' := h.eq_simple_of_isRelativeReflection hT ⟨α, hα⟩ hαw
  have hβ' := h.eq_simple_of_isRelativeReflection hT ⟨β, hβ⟩ hβw
  have hab := Langlands.Group.RelativeWeylIndexing.simple_injective cs (hα'.symm.trans hβ')
  exact congrArg Subtype.val hab

/-- **Packaging.** A Coxeter realization of a finite relative Weyl group of a split torus,
together with the Tits axioms that involve `B = P_∅(k)`, gives the relative Tits system. -/
theorem hasRelativeTitsSystem (h : IsRelativeWeylCoxeterRealization i ν cs)
    (hax : HasRelativeTitsBorelAxioms i ν) : HasRelativeTitsSystem i ν :=
  ⟨{ surjective := QuotientGroup.mk'_surjective _
     ker_eq := hax.1
     sup_eq := hax.2.1
     closure_eq := h.closure_simpleRelativeReflections_eq_top
     ne_one := fun _ hs => h.ne_one_of_mem_simpleRelativeReflections hT hs
     mul_self := fun _ hs => h.mul_self_of_mem_simpleRelativeReflections hT hs
     mul_mem_cell := hax.2.2.1
     conj_not_le := hax.2.2.2 },
    fun _ hα => h.existsUnique_isRelativeReflection hT hα,
    fun _ hα _ hβ _ hαw hβw => h.eq_of_isRelativeReflection hT hα hβ hαw hβw⟩

/-- Under a Coxeter realization of a finite relative Weyl group of a split torus, the relative
Tits system is equivalent to the Tits axioms that involve `B = P_∅(k)`. -/
theorem hasRelativeTitsSystem_iff (h : IsRelativeWeylCoxeterRealization i ν cs) :
    HasRelativeTitsSystem i ν ↔ HasRelativeTitsBorelAxioms i ν :=
  ⟨HasRelativeTitsSystem.hasRelativeTitsBorelAxioms, h.hasRelativeTitsSystem hT⟩

end IsRelativeWeylCoxeterRealization

namespace HasRelativeWeylCoxeterSystem

/-- Under `HasRelativeWeylCoxeterSystem`, the simple relative reflections generate the
relative Weyl group. -/
theorem closure_simpleRelativeReflections_eq_top (h : HasRelativeWeylCoxeterSystem i ν) :
    Subgroup.closure (simpleRelativeReflections i ν) = ⊤ := by
  obtain ⟨-, -, M, cs, hcs⟩ := h
  exact hcs.closure_simpleRelativeReflections_eq_top

/-- **Packaging.** `HasRelativeWeylCoxeterSystem` for a split torus, together with the Tits
axioms that involve `B = P_∅(k)`, gives the relative Tits system. -/
theorem hasRelativeTitsSystem (h : HasRelativeWeylCoxeterSystem i ν)
    (hT : IsSplitTorus T.toGrp) (hax : HasRelativeTitsBorelAxioms i ν) :
    HasRelativeTitsSystem i ν := by
  obtain ⟨hW, -, M, cs, hcs⟩ := h
  exact hcs.hasRelativeTitsSystem hT hax

/-- Under `HasRelativeWeylCoxeterSystem` for a split torus, the relative Tits system is
equivalent to the Tits axioms that involve `B = P_∅(k)`. -/
theorem hasRelativeTitsSystem_iff (h : HasRelativeWeylCoxeterSystem i ν)
    (hT : IsSplitTorus T.toGrp) :
    HasRelativeTitsSystem i ν ↔ HasRelativeTitsBorelAxioms i ν :=
  ⟨HasRelativeTitsSystem.hasRelativeTitsBorelAxioms, h.hasRelativeTitsSystem hT⟩

end HasRelativeWeylCoxeterSystem

/-- **Reduction of the relative Tits system to the Coxeter statement and the Borel axioms.**
`RelativeWeylCoxeterStatement`, together with the Tits axioms that involve `B = P_∅(k)` for
every maximal split torus of a connected reductive group and every generic cocharacter, gives
`RelativeTitsSystemStatement`. -/
theorem relativeTitsSystemStatement_of_relativeWeylCoxeter
    (hcox : RelativeWeylCoxeterStatement.{u})
    (hax : ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
      (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
      (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T),
      haveI := hG.isAffineHom
      haveI := hi.isSplitSubtorus.mono
      IsGenericCocharacter i ν → HasRelativeTitsBorelAxioms i ν) :
    RelativeTitsSystemStatement.{u} := by
  intro k _ G hG T i hi ν
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  intro hν
  exact (hcox k G hG T i hi ν hν).hasRelativeTitsSystem hi.isSplitSubtorus.1
    (hax k G hG T i hi ν hν)

end Langlands.GroupScheme
