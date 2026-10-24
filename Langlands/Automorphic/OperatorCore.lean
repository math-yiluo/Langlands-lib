import Langlands.Automorphic.FiniteRealization
import Langlands.Automorphic.PreservationStatement
import Mathlib.Algebra.Algebra.Subalgebra.Lattice

/-! # The concrete operator algebra and invariant core of actual forms -/

noncomputable section
universe u

namespace Langlands.Automorphic

open Langlands.Global

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

local instance : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _

/-- Endomorphisms of the actual finite-smooth rational-invariant ambient space. -/
abbrev FiniteSmoothEnd := Module.End ℂ (FiniteSmoothRationalFunctions F n)

/-- The actual standard infinite compact acts on the ambient space. -/
def finiteSmoothCompactRightAction :
    Representation ℂ (standardInfiniteCompact F n) (FiniteSmoothRationalFunctions F n) :=
  (finiteSmoothRightAction F n).comp
    ((AdelicGL.ofInfinite F n).toMonoidHom.comp (standardInfiniteCompact F n).subtype)

/-- The three concrete operator families; the differential action is genuine. -/
def automorphicOperatorGenerators : Set (FiniteSmoothEnd F n) :=
  (Set.range (finiteSmoothFiniteRightAction F n) ∪
    Set.range (finiteSmoothCompactRightAction F n)) ∪
      Set.range (finiteSmoothEnvelopingAction F n)

/-- The subalgebra generated inside actual endomorphisms, not a freely presented algebra. -/
def automorphicOperatorAlgebra : Subalgebra ℂ (FiniteSmoothEnd F n) :=
  Algebra.adjoin ℂ (automorphicOperatorGenerators F n)

/-- The faithful ambient action of this concrete operator algebra's multiplicative monoid. -/
def automorphicOperatorAction :
    Representation ℂ (automorphicOperatorAlgebra F n) (FiniteSmoothRationalFunctions F n) :=
  (automorphicOperatorAlgebra F n).val.toMonoidHom

def finiteOperator : FiniteAdelicGL F n →* automorphicOperatorAlgebra F n where
  toFun d := ⟨finiteSmoothFiniteRightAction F n d,
    Algebra.subset_adjoin (Or.inl (Or.inl ⟨d, rfl⟩))⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' d e := Subtype.ext (map_mul _ d e)

def compactOperator : standardInfiniteCompact F n →* automorphicOperatorAlgebra F n where
  toFun k := ⟨finiteSmoothCompactRightAction F n k,
    Algebra.subset_adjoin (Or.inl (Or.inr ⟨k, rfl⟩))⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' k l := Subtype.ext (map_mul _ k l)

def differentialOperator :
    ArchimedeanGL.EnvelopingAlgebra F n →ₐ[ℂ] automorphicOperatorAlgebra F n :=
  (finiteSmoothEnvelopingAction F n).codRestrict (automorphicOperatorAlgebra F n)
    (fun a => Algebra.subset_adjoin (Or.inr ⟨a, rfl⟩))

/-- The largest operator-invariant subspace contained in a given ambient subspace. -/
def operatorCore (P : Submodule ℂ (FiniteSmoothRationalFunctions F n)) :
    Subrepresentation (automorphicOperatorAction F n) where
  toSubmodule :=
    { carrier := {f | ∀ a : automorphicOperatorAlgebra F n, a.val f ∈ P}
      zero_mem' := fun a => by simp
      add_mem' := fun hf hg a => by simpa using P.add_mem (hf a) (hg a)
      smul_mem' := fun c f hf a => by simpa using P.smul_mem c (hf a) }
  apply_mem_toSubmodule b f hf a := hf (a * b)

@[simp]
theorem mem_operatorCore (P : Submodule ℂ (FiniteSmoothRationalFunctions F n))
    (f : FiniteSmoothRationalFunctions F n) :
    f ∈ operatorCore F n P ↔
      ∀ a : automorphicOperatorAlgebra F n, a.val f ∈ P := Iff.rfl

theorem operatorCore_le (P : Submodule ℂ (FiniteSmoothRationalFunctions F n)) :
    (operatorCore F n P).toSubmodule ≤ P := by
  intro f hf
  exact hf 1

/-- This universal property rules out an arbitrary choice of stable subspace. -/
theorem le_operatorCore_iff (P : Submodule ℂ (FiniteSmoothRationalFunctions F n))
    (S : Subrepresentation (automorphicOperatorAction F n)) :
    S ≤ operatorCore F n P ↔ S.toSubmodule ≤ P := by
  constructor
  · intro h f hf
    exact operatorCore_le F n P (h hf)
  · intro h f hf a
    exact h (S.apply_mem_toSubmodule a hf)

/-- Stability under the three families is equivalent to stability under their algebra. -/
theorem operator_invariant_iff (P : Submodule ℂ (FiniteSmoothRationalFunctions F n)) :
    (∀ (a : automorphicOperatorAlgebra F n) (f), f ∈ P → a.val f ∈ P) ↔
      (∀ d f, f ∈ P → finiteSmoothFiniteRightAction F n d f ∈ P) ∧
      (∀ k f, f ∈ P → finiteSmoothCompactRightAction F n k f ∈ P) ∧
      (∀ a f, f ∈ P → finiteSmoothEnvelopingAction F n a f ∈ P) := by
  constructor
  · intro h
    exact ⟨fun d => h (finiteOperator F n d),
      fun k => h (compactOperator F n k), fun a => h (differentialOperator F n a)⟩
  · rintro ⟨hd, hk, hu⟩ a
    refine Algebra.adjoin_induction (p := fun a _ => ∀ f, f ∈ P → a f ∈ P)
      ?_ ?_ ?_ ?_ a.property
    · rintro a ((⟨d, rfl⟩ | ⟨k, rfl⟩) | ⟨u, rfl⟩)
      · exact hd d
      · exact hk k
      · exact hu u
    · intro c f hf
      exact P.smul_mem c hf
    · intro a b _ _ ha hb f hf
      exact P.add_mem (ha f hf) (hb f hf)
    · intro a b _ _ ha hb f hf
      exact ha (b f) (hb f hf)

theorem operatorCore_eq_iff (P : Submodule ℂ (FiniteSmoothRationalFunctions F n)) :
    (operatorCore F n P).toSubmodule = P ↔
      ∀ (a : automorphicOperatorAlgebra F n) (f), f ∈ P → a.val f ∈ P := by
  constructor
  · intro h a f hf
    have hcore : f ∈ operatorCore F n P := by
      change f ∈ (operatorCore F n P).toSubmodule
      rw [h]
      exact hf
    exact hcore a
  · intro h
    exact le_antisymm (operatorCore_le F n P) (fun f hf a => h a f hf)

/-- The constructed maximal stable part of the actual automorphic form space. -/
def automorphicOperatorCore : Subrepresentation (automorphicOperatorAction F n) :=
  operatorCore F n (automorphicSubrepresentation F n).toSubmodule

abbrev StableAutomorphicFunctions := (automorphicOperatorCore F n).toSubmodule

local instance : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

/-- All three families act by their actual ambient operators on this constructed space. -/
def stableAutomorphicAction :
    Representation ℂ (automorphicOperatorAlgebra F n) (StableAutomorphicFunctions F n) :=
  (automorphicOperatorCore F n).toRepresentation

def stableAutomorphicFiniteAction :
    Representation ℂ (FiniteAdelicGL F n) (StableAutomorphicFunctions F n) :=
  (stableAutomorphicAction F n).comp (finiteOperator F n)

def stableAutomorphicCompactAction :
    Representation ℂ (standardInfiniteCompact F n) (StableAutomorphicFunctions F n) :=
  (stableAutomorphicAction F n).comp (compactOperator F n)

/-- Restriction remains a complex algebra action, not just a multiplicative action. -/
def stableAutomorphicEnvelopingAction :
    ArchimedeanGL.EnvelopingAlgebra F n →ₐ[ℂ]
      Module.End ℂ (StableAutomorphicFunctions F n) where
  toFun a := stableAutomorphicAction F n (differentialOperator F n a)
  map_one' := by simp only [map_one]
  map_mul' a b := by simp only [map_mul]
  map_zero' := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    change finiteSmoothEnvelopingAction F n 0 f.val = 0
    simp only [map_zero, LinearMap.zero_apply]
  map_add' a b := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    change finiteSmoothEnvelopingAction F n (a + b) f.val =
      finiteSmoothEnvelopingAction F n a f.val + finiteSmoothEnvelopingAction F n b f.val
    simp only [map_add, LinearMap.add_apply]
  commutes' c := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    change finiteSmoothEnvelopingAction F n (algebraMap ℂ _ c) f.val = c • f.val
    rw [AlgHom.commutes]
    rfl

@[simp]
theorem stableAutomorphicFiniteAction_val (d : FiniteAdelicGL F n)
    (f : StableAutomorphicFunctions F n) :
    (stableAutomorphicFiniteAction F n d f).val =
      finiteSmoothFiniteRightAction F n d f.val := rfl

@[simp]
theorem stableAutomorphicCompactAction_val (k : standardInfiniteCompact F n)
    (f : StableAutomorphicFunctions F n) :
    (stableAutomorphicCompactAction F n k f).val =
      finiteSmoothRightAction F n (AdelicGL.ofInfinite F n k.val) f.val := rfl

@[simp]
theorem stableAutomorphicEnvelopingAction_val (a : ArchimedeanGL.EnvelopingAlgebra F n)
    (f : StableAutomorphicFunctions F n) :
    (stableAutomorphicEnvelopingAction F n a f).val =
      finiteSmoothEnvelopingAction F n a f.val := rfl

/-- Finite translations still commute with the actual differentials after restriction. -/
theorem stableAutomorphicFiniteAction_envelopingAction (d : FiniteAdelicGL F n)
    (a : ArchimedeanGL.EnvelopingAlgebra F n) (f : StableAutomorphicFunctions F n) :
    stableAutomorphicFiniteAction F n d (stableAutomorphicEnvelopingAction F n a f) =
      stableAutomorphicEnvelopingAction F n a (stableAutomorphicFiniteAction F n d f) := by
  apply Subtype.ext
  exact finiteSmoothFiniteRightAction_envelopingAction F n d a f.val

/-- The core consists of actual forms, with a faithful finite-equivariant inclusion. -/
def stableAutomorphicInclusion :
    (stableAutomorphicFiniteAction F n).IntertwiningMap (automorphicFiniteRightAction F n) where
  toLinearMap := (automorphicOperatorCore F n).toSubmodule.inclusion
    (operatorCore_le F n _)
  isIntertwining' d := by ext f; rfl

theorem stableAutomorphicInclusion_injective :
    Function.Injective (stableAutomorphicInclusion F n) := by
  intro f g h
  apply Subtype.ext
  exact congrArg (fun x : AutomorphicForms F n => x.val) h

theorem stableAutomorphicFiniteAction_isSmooth :
    Langlands.IsSmooth (stableAutomorphicFiniteAction F n) :=
  Langlands.isSmooth_of_injective (stableAutomorphicInclusion F n)
    (stableAutomorphicInclusion_injective F n) (automorphicFiniteRightAction_isSmooth F n)

/-- No global preservation result is concealed: equality is exactly the two missing closures. -/
theorem automorphicOperatorCore_eq_iff :
    (automorphicOperatorCore F n).toSubmodule =
      (automorphicSubrepresentation F n).toSubmodule ↔
      AutomorphicCompactTranslationStatement F n ∧
        AutomorphicDifferentialPreservationStatement F n := by
  rw [automorphicOperatorCore, operatorCore_eq_iff, operator_invariant_iff]
  constructor
  · rintro ⟨_, hk, hu⟩
    refine ⟨?_, hu⟩
    intro k f hf
    obtain ⟨g, hg, rfl⟩ := (isAutomorphicForm_iff_exists_finiteSmooth F n f).mp hf
    exact (mem_automorphicSubrepresentation F n _).mp (hk k g hg)
  · rintro ⟨hk, hu⟩
    refine ⟨fun d f hf => (automorphicSubrepresentation F n).apply_mem_toSubmodule d hf,
      ?_, hu⟩
    intro k f hf
    exact (mem_automorphicSubrepresentation F n _).mpr
      (hk k _ ((mem_automorphicSubrepresentation F n f).mp hf))

end Langlands.Automorphic
