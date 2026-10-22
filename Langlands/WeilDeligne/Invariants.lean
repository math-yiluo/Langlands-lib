import Langlands.WeilDeligne.Parameters
import Langlands.Weil.Representation.InertiaOperations
import Mathlib.RingTheory.Nilpotent.Lemmas

/-!
# Weil–Deligne pairs on invariant subspaces

If a normal subgroup lies in the norm kernel, its fixed subspace is stable
under monodromy as well as the ambient group action.
-/

noncomputable section

universe uK uG uV uW

open CategoryTheory

namespace Langlands.WeilDeligneRepresentation

variable {K : Type uK} {G : Type uG} [Field K] [Group G] {ν : G →* Kˣ}
  (J : Subgroup G) (hν : ∀ j : J, ν (j : G) = 1)

include hν in
/-- The fixed subspace is stable under monodromy when the norm is trivial on
the subgroup. This is derived from the pair's covariance, not supplied as data. -/
theorem monodromy_mem_invariants (A : WeilDeligneRepresentation K G ν)
    {x : A} (hx : x ∈ FiniteRepresentation.invariantSubspace A.toFiniteRepresentation J) :
    A.monodromy x ∈ FiniteRepresentation.invariantSubspace A.toFiniteRepresentation J := by
  intro j
  have hi : A.representation (j : G)⁻¹ x = x := hx j⁻¹
  have h := LinearMap.congr_fun (A.covariance (j : G)) x
  simp only [Module.End.mul_apply, hi, hν j,
    Units.val_one, one_smul] at h
  exact h

variable [J.Normal]

/-- The actual invariant-subspace pair with restricted, possibly nonzero,
monodromy. -/
def invariants (A : WeilDeligneRepresentation.{uK, uG, uV} K G ν) :
    WeilDeligneRepresentation.{uK, uG, uV} K G ν where
  toFiniteRepresentation := FiniteRepresentation.invariants J A.toFiniteRepresentation
  monodromy := A.monodromy.restrict (fun _ hx => monodromy_mem_invariants J hν A hx)
  nilpotent := Module.End.isNilpotent.restrict
    (fun _ hx => monodromy_mem_invariants J hν A hx) A.nilpotent
  covariance g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact LinearMap.congr_fun (A.covariance g) x.val

/-- The invariant pair includes into the original pair by an actual morphism. -/
def invariantsInclusion (A : WeilDeligneRepresentation K G ν) :
    Hom (invariants J hν A) A :=
  ⟨FiniteRepresentation.invariantsInclusion J A.toFiniteRepresentation, rfl⟩

/-- Restrict a pair morphism to invariant subspaces. -/
def invariantsMap {A : WeilDeligneRepresentation.{uK, uG, uV} K G ν}
    {B : WeilDeligneRepresentation.{uK, uG, uW} K G ν} (f : Hom A B) :
    Hom (invariants J hν A) (invariants J hν B) where
  intertwiner := FiniteRepresentation.invariantsMap J f.intertwiner
  comm_monodromy := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact LinearMap.congr_fun f.comm_monodromy x.val

/-- Invariant pairs form a functor for the fixed normal subgroup. -/
def invariantsFunctor :
    WeilDeligneRepresentation.{uK, uG, uV} K G ν ⥤
      WeilDeligneRepresentation.{uK, uG, uV} K G ν where
  obj := invariants J hν
  map := invariantsMap J hν
  map_id _ := by apply Hom.ext; rfl
  map_comp _ _ := by apply Hom.ext; rfl

/-- Actual equivalences restrict to invariant pair equivalences. -/
def invariantsEquiv {A B : WeilDeligneRepresentation.{uK, uG, uV} K G ν}
    (e : Equiv A B) : Equiv (invariants J hν A) (invariants J hν B) :=
  Equiv.ofIso ((invariantsFunctor J hν).mapIso e.toIso)

/-- Invariant pairs descend to genuine isomorphism classes. -/
def invariantsClass :
    IsomorphismClasses.{uK, uG, uV} K G ν → IsomorphismClasses.{uK, uG, uV} K G ν :=
  Quotient.map (invariants J hν) (fun _ _ ⟨e⟩ => ⟨invariantsEquiv J hν e⟩)

section Complex

variable [TopologicalSpace G] [IsTopologicalGroup G] {ν : G →* ℂˣ}
  (J : Subgroup G) [J.Normal] (hν : ∀ j : J, ν (j : G) = 1) (I : Subgroup G)

/-- The actual invariant pair retains an open inertia kernel. -/
def parameterInvariants (A : ParameterObjects.{uG, uV} (ν := ν) I) :
    ParameterObjects.{uG, uV} (ν := ν) I :=
  ⟨invariants J hν A.val,
    FiniteRepresentation.hasOpenInertiaKernel_of_injective I
      (FiniteRepresentation.invariantsInclusion J A.val.toFiniteRepresentation)
      Subtype.val_injective A.property⟩

/-- The invariant-pair operation on genuine parameter classes. -/
def parameterInvariantsClass :
    ParameterClasses.{uG, uV} (ν := ν) I → ParameterClasses.{uG, uV} (ν := ν) I :=
  Quotient.map (parameterInvariants J hν I) (fun _ _ ⟨e⟩ => ⟨invariantsEquiv J hν e⟩)

end Complex

end Langlands.WeilDeligneRepresentation
