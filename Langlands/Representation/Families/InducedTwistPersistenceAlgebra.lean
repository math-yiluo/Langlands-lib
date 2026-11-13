import Langlands.Representation.Families.InducedTwistExclusionAlgebra
import Langlands.Representation.Classification.SegmentHeadSupportStep
import Langlands.Representation.Smooth.IrreducibleGrothendieckProof
import Langlands.Representation.Filtration.LengthCriterionProof
import Langlands.Representation.Plancherel.RationalUnramifiedCharacterCoordinates
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.GroupTheory.Index

/-! # Algebraic helpers for the persistence of the inducing exponent

Generalized eigencharacters along injective intertwiners, an irreducible subrepresentation
carrying a prescribed exponent inside a finite-length representation, finite length from a
composition series, and divisibility of groups isomorphic to a power of `ℂˣ`.
-/

noncomputable section

open CategoryTheory

namespace Langlands.InducedTwistPersistence

universe uM uA uV uW

section Exponent

variable {M : Type uM} [Group M] {A : Type uA} [Group A] (ι : A →* M)
  {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {π : Representation ℂ M V} {σ : Representation ℂ M W}

/-- An intertwiner restricted along `ι`. -/
def restrictComp (f : π.IntertwiningMap σ) :
    Representation.IntertwiningMap (π.comp ι) (σ.comp ι) where
  toLinearMap := f.toLinearMap
  isIntertwining' a := f.isIntertwining' (ι a)

@[simp]
theorem restrictComp_apply (f : π.IntertwiningMap σ) (v : V) : restrictComp ι f v = f v := rfl

/-- A generalized eigencharacter is carried along an injective intertwiner. -/
theorem isGeneralizedEigencharacter_of_injective (f : π.IntertwiningMap σ)
    (hf : Function.Injective f) (χ : A →* ℂˣ)
    (h : IsGeneralizedEigencharacter (π.comp ι) χ) :
    IsGeneralizedEigencharacter (σ.comp ι) χ := by
  obtain ⟨k, hk⟩ := h
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hk
  refine isGeneralizedEigencharacter_of_map_ne_zero (restrictComp ι f) χ k hv ?_
  intro h0
  exact hv0 (hf (by rw [restrictComp_apply] at h0; rw [h0, map_zero]))

/-- A generalized eigencharacter of the image of an injective intertwiner is one of the
source. -/
theorem isGeneralizedEigencharacter_of_injective_of_mem (f : π.IntertwiningMap σ)
    (hf : Function.Injective f) (χ : A →* ℂˣ) {v : V} (hv : v ≠ 0) (d : ℕ)
    (hd : ∀ a : A, ((σ (ι a) - (χ a : ℂ) • 1) ^ d) (f v) = 0) :
    IsGeneralizedEigencharacter (π.comp ι) χ := by
  refine (isGeneralizedEigencharacter_iff _ _).mpr ⟨d, v, hv, fun a => ?_⟩
  apply hf
  rw [map_zero, ← hd a]
  have hcomm : ∀ (n : ℕ) (w : V), f (((π (ι a) - (χ a : ℂ) • 1) ^ n) w) =
      ((σ (ι a) - (χ a : ℂ) • 1) ^ n) (f w) := by
    intro n
    induction n with
    | zero => intro w; simp
    | succ n ih =>
      intro w
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]
      congr 1
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub,
        map_smul]
      rw [show f (π (ι a) w) = σ (ι a) (f w) from congr($(f.isIntertwining' (ι a)) w)]
  exact hcomm d v

end Exponent

section Smooth

variable {G : Type uM} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
  [WeaklyLocallyCompactSpace G] {A : Type uA} [Group A] (ι : A →* G) (hι : ∀ t : A, ι t ∈ Subgroup.center G)

include hι in
/-- A finite-length smooth representation with a generalized eigencharacter `χ` of a
central subgroup has an irreducible subrepresentation with the same exponent. -/
theorem exists_irreducible_sub_isGeneralizedEigencharacter
    {X : SmoothRep.{0, uM, uV} ℂ G} (hX : X.HasFiniteLength) (χ : A →* ℂˣ)
    (hχ : IsGeneralizedEigencharacter (X.representation.comp ι) χ) :
    ∃ C : SmoothRep.{0, uM, uV} ℂ G, C.IsIrreducible ∧
      ∃ j : C ⟶ X, Function.Injective (SmoothRep.hom j) ∧
        IsGeneralizedEigencharacter (C.representation.comp ι) χ := by
  let Wχ := generalizedWeightSpace X.representation ι χ hι
  have hW : Wχ ≠ ⊥ := (generalizedWeightSpace_ne_bot_iff ι χ hι X.isSmooth).mpr hχ
  let Y := SmoothRep.subrepresentation X Wχ
  have hY : Y.HasFiniteLength :=
    SmoothRep.IrreducibleGrothendieckProof.subrepresentation_hasFiniteLength hX Wχ
  have : Nontrivial Y := by
    obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).mp
      (fun h => hW (Subrepresentation.toSubmodule_injective h))
    exact ⟨⟨⟨w, hw⟩, 0, fun h => hw0 (congrArg Subtype.val h)⟩⟩
  obtain ⟨C, hC, j, hj⟩ :=
    Classification.SegmentHeadSupport.exists_irreducible_subrepresentation hY
  have hC' : C.representation.IsIrreducible := hC
  have : Nontrivial C := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) C.representation.asModule
  obtain ⟨c, hc⟩ := exists_ne (0 : C)
  let incl := SmoothRep.subtype X Wχ
  refine ⟨C, hC, j ≫ incl, ?_, ?_⟩
  · exact (SmoothRep.subtype_injective X Wχ).comp hj
  · have hmem : SmoothRep.hom incl (SmoothRep.hom j c) ∈ Wχ.toSubmodule :=
      (SmoothRep.hom j c).2
    obtain ⟨d, hd⟩ := (mem_generalizedWeightSpace_of_isSmooth ι χ hι X.isSmooth _).mp hmem
    exact isGeneralizedEigencharacter_of_injective_of_mem ι (SmoothRep.hom (j ≫ incl))
      ((SmoothRep.subtype_injective X Wχ).comp hj) χ hc d (fun a => hd a)

end Smooth

section FiniteLength

variable {G : Type uM} [Group G] [TopologicalSpace G]

/-- A smooth representation with a composition series has finite length. -/
theorem hasFiniteLength_of_hasSimpleFactors {X : SmoothRep.{0, uM, uV} ℂ G} {n : ℕ}
    (s : ObjectRepFiltration (Rep.of X.representation) n) (hs : s.HasSimpleFactors) :
    X.HasFiniteLength :=
  LengthCriterionProof.isFiniteLength_of_hasCompositionSeriesLength ⟨s, hs⟩

end FiniteLength

section Divisible

/-- `(ℂˣ)ⁿ` is divisible. -/
theorem exists_pow_eq_units_pi {ι : Type*} (c : ι → ℂˣ) (n : ℕ) (hn : n ≠ 0) :
    ∃ c' : ι → ℂˣ, c' ^ n = c := by
  have h : ∀ i, ∃ z : ℂˣ, z ^ n = c i := by
    intro i
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq ((c i : ℂ)) (Nat.pos_of_ne_zero hn)
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow hn] at hz
      exact (c i).ne_zero hz.symm
    exact ⟨Units.mk0 z hz0, Units.ext (by simpa using hz)⟩
  choose c' hc' using h
  exact ⟨c', funext fun i => by simpa using hc' i⟩

/-- A group topologically isomorphic to `(ℂˣ)ⁿ` is divisible. -/
theorem exists_pow_eq_of_mulEquiv {X : Type uA} [CommGroup X] {ι : Type*}
    (e : X ≃* (ι → ℂˣ)) (x : X) (n : ℕ) (hn : n ≠ 0) : ∃ y : X, y ^ n = x := by
  obtain ⟨c', hc'⟩ := exists_pow_eq_units_pi (e x) n hn
  refine ⟨e.symm c', ?_⟩
  apply e.injective
  rw [map_pow, MulEquiv.apply_symm_apply, hc']

end Divisible

end Langlands.InducedTwistPersistence
