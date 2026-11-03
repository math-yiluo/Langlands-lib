import Langlands.GroupScheme.Rational.RelativeWeylCoxeterAssembly
import Langlands.GroupScheme.Rational.StandardCocharacterFiniteness
import Langlands.GroupScheme.Rational.RootSupportFiniteness
import Langlands.Group.RelativeWeylSolomonProof

/-! # Actual root supports for twisted standard-Levi intersections -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj
open Langlands.LinearAlgebra.RationalSpan
open Langlands.Aubert.General.RationalPointFamily Langlands.Group.RelativeWeylIndexing

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : T.toGrp ⟶ G} [IsAffineHom G.X.hom] [Mono i.hom.hom.left]
  {ν : cocharacterLattice T} {CM : CoxeterMatrix (SimpleRoot i ν)}
  {cs : CoxeterSystem CM (relativeWeylGroup i)}

/-- The parabolic-subgroup clause of a realization forces every finite standard
face to have a standard cocharacter. Otherwise its choice-free Levi is the whole
ambient group and its Weyl subgroup contains every simple reflection. -/
theorem IsRelativeWeylCoxeterRealization.exists_standardCocharacter_finset
    [Finite (SimpleRoot i ν)] (h : IsRelativeWeylCoxeterRealization i ν cs)
    (I : Finset (SimpleRoot i ν)) :
    ∃ ζ : cocharacterLattice T, IsStandardCocharacter i ν (rootSet i ν I) ζ := by
  classical
  let := Fintype.ofFinite (SimpleRoot i ν)
  by_contra hno
  have hall (a : SimpleRoot i ν) : a ∈ I := by
    apply mem_of_simple_mem_standardSubgroup cs
    rw [h.2.2.2.2 I]
    obtain ⟨n, hn⟩ := QuotientGroup.mk_surjective (cs.simple a)
    apply (mem_standardRelativeWeylGroup_iff i ν).2
    refine ⟨n, ?_, hn⟩
    change (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) ∈
      (standardLevi i ν (rootSet i ν I)).carrier _
    rw [mem_standardLevi]
    intro ζ hζ
    exact False.elim (hno ⟨ζ, hζ⟩)
  apply hno
  refine ⟨0, ?_, ?_, ?_⟩
  · rintro _ ⟨a, -, rfl⟩
    exact a.2
  · intro α _
    exact map_zero (latticePairing T α)
  · intro α hα hnot
    exact False.elim (hnot ⟨⟨α, hα⟩, hall _, rfl⟩)

/-- Existence holds for every subset of the simple roots when that root set is
finite. This uses the supplied Coxeter realization, without a root-system premise. -/
theorem IsRelativeWeylCoxeterRealization.exists_standardCocharacter
    [Finite (SimpleRoot i ν)] (h : IsRelativeWeylCoxeterRealization i ν cs)
    (J : Set (characterLattice T)) (hJ : J ⊆ simpleRelativeRoots i ν) :
    ∃ ζ : cocharacterLattice T, IsStandardCocharacter i ν J ζ := by
  classical
  let := Fintype.ofFinite (SimpleRoot i ν)
  let I : Finset (SimpleRoot i ν) := Finset.univ.filter (fun a => a.1 ∈ J)
  have hI : rootSet i ν I = J := by
    ext α
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact (Finset.mem_filter.mp ha).2
    · intro hα
      exact ⟨⟨α, hJ hα⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hα⟩, rfl⟩
  simpa only [hI] using h.exists_standardCocharacter_finset I

/-- A realization and finitely many simple roots imply rational independence
of the actual simple roots, through the separating standard cocharacters. -/
theorem IsRelativeWeylCoxeterRealization.linearIndependent_simpleRelativeRoots
    [Finite (SimpleRoot i ν)] (h : IsRelativeWeylCoxeterRealization i ν cs) :
    LinearIndependent ℚ (fun a : SimpleRoot i ν => toRat a.1) :=
  Module.Flat.linearIndependent_one_tmul
    (linearIndependent_simpleRelativeRoots_of_standardCocharacter_exists i ν
      h.exists_standardCocharacter)

/-- A standard cocharacter for a selected face, constructed using a supplied
Coxeter realization and its actual standard-Levi parabolic clause. -/
def standardCocharacterOfCoxeterRealization
    [Finite (SimpleRoot i ν)] (h : IsRelativeWeylCoxeterRealization i ν cs)
    (J : Set (characterLattice T)) (hJ : J ⊆ simpleRelativeRoots i ν) :
    {ζ : cocharacterLattice T // IsStandardCocharacter i ν J ζ} :=
  ⟨(h.exists_standardCocharacter J hJ).choose,
    (h.exists_standardCocharacter J hJ).choose_spec⟩

end Langlands.GroupScheme
