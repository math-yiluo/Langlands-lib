import Langlands.Representation.Aubert.General.SharpConsequenceStatements

/-! # Finite length of the actual terminal quotient from its normalized terms -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open scoped MonoidAlgebra

namespace Langlands.Aubert.General

universe uI uG uV

variable {ι : Type uI} [LinearOrder ι] [Fintype ι]
variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable (P M U : Finset ι → Subgroup G)
  (h : ∀ J, IsSemidirectDecomposition (P J) (M J) (U J))
  (hclosed : ∀ J, IsClosed (U J : Set G))

namespace Complex

omit [LinearOrder ι] in
/-- Coordinate evaluation on the actual degree as an equivariant map. -/
def degreeCoordinate
    (A : SmoothRep.{0, uG, max uG uV} ℂ G) (k : ℕ)
    (s : {s : Finset ι // s.card = k}) :
    (degreeRepresentation P M U h hclosed A k).IntertwiningMap
      (termRepresentation P M U h hclosed A s.1) where
  toLinearMap := LinearMap.proj s
  isIntertwining' _ := rfl

omit [LinearOrder ι] in
/-- Finite length of the actual normalized terms gives finite length of every
homogeneous degree, which is their finite pointwise product. -/
theorem degreeObject_hasFiniteLength_of_terms
    (A : SmoothRep.{0, uG, max uG uV} ℂ G)
    (hA : ∀ s, (termObject P M U h hclosed A s).HasFiniteLength) (k : ℕ) :
    (degreeObject P M U h hclosed A k).HasFiniteLength := by
  let J := {s : Finset ι // s.card = k}
  let τ := degreeRepresentation P M U h hclosed A k
  let ρ : ∀ s : J, Representation ℂ G (Term P M U h hclosed A s.1) :=
    fun s => termRepresentation P M U h hclosed A s.1
  let f : ∀ s : J, τ.IntertwiningMap (ρ s) :=
    fun s => degreeCoordinate P M U h hclosed A k s
  let L : τ.asModule →ₗ[ℂ[G]] ∀ s : J, (ρ s).asModule :=
    LinearMap.pi fun s => Representation.IntertwiningMap.equivLinearMapAsModule _ _ (f s)
  have hL : Function.Injective L := by
    intro x y hxy
    apply τ.asModuleEquiv.injective
    funext s
    exact congrFun hxy s
  have hρ : ∀ s : J, IsFiniteLength ℂ[G] (ρ s).asModule := fun s => hA s.1
  have : ∀ s : J, IsNoetherian ℂ[G] (ρ s).asModule :=
    fun s => (isFiniteLength_iff_isNoetherian_isArtinian.mp (hρ s)).1
  have : ∀ s : J, IsArtinian ℂ[G] (ρ s).asModule :=
    fun s => (isFiniteLength_iff_isNoetherian_isArtinian.mp (hρ s)).2
  have hprod : IsFiniteLength ℂ[G] (∀ s : J, (ρ s).asModule) :=
    isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩
  exact hprod.of_injective (f := L) hL

variable (hδ : ∀ J, IsUnimodularModulus (U J) (hclosed J))
  (hP : Antitone P) (hU : Monotone U)

/-- The actual quotient by the incoming differential has finite length whenever
its source homogeneous degree has finite length. -/
theorem terminalObject_hasFiniteLength_of_degree
    (A : SmoothRep.{0, uG, max uG uV} ℂ G) (k : ℕ)
    (hA : (degreeObject P M U h hclosed A k).HasFiniteLength) :
    (terminalObject P M U h hclosed hδ hP hU A k).HasFiniteLength :=
  hA.of_surjective
    (f := Representation.IntertwiningMap.equivLinearMapAsModule _ _
      (terminalProjection P M U h hclosed hδ hP hU A k))
    (terminalProjection_surjective P M U h hclosed hδ hP hU A k)

/-- Finite length of the actual terms implies finite length of their actual
terminal cokernel at every retained support rank. -/
theorem sharpObject_hasFiniteLength_of_terms
    (A : SmoothRep.{0, uG, max uG uV} ℂ G)
    (hA : ∀ s, (termObject P M U h hclosed A s).HasFiniteLength) (I : Finset ι) :
    (sharpObject P M U h hclosed hδ hP hU A I).HasFiniteLength :=
  terminalObject_hasFiniteLength_of_degree P M U h hclosed hδ hP hU A _
    (degreeObject_hasFiniteLength_of_terms P M U h hclosed A hA _)

end Complex

/-- Reindexing by removed roots preserves the termwise argument for the actual
standard-family terminal cokernel. -/
theorem StandardComplex.sharpObject_hasFiniteLength_of_terms
    (hδ : ∀ J, IsUnimodularModulus (U J) (hclosed J))
    (hP : Monotone P) (hU : Antitone U)
    (A : SmoothRep.{0, uG, max uG uV} ℂ G)
    (hA : ∀ J, ((inductionJacquetFunctor.{uG, uV} (h J) (hclosed J)).obj A).HasFiniteLength)
    (I : Finset ι) :
    (StandardComplex.sharpObject P M U h hclosed hδ hP hU A I).HasFiniteLength :=
  Complex.sharpObject_hasFiniteLength_of_terms _ _ _ _ _ _ _ _ A
    (fun s => hA (Finset.univ \ s)) I

/-- Preservation of finite length by each actual normalized composite suffices
for the entire generic sharp finite-length target. -/
theorem sharpFiniteLengthTarget_of_inductionJacquet
    (hδ : ∀ J, IsUnimodularModulus (U J) (hclosed J))
    (hP : Monotone P) (hU : Antitone U)
    (hfl : ∀ J, SmoothRep.PreservesFiniteLength
      (inductionJacquetFunctor.{uG, max uI uV} (h J) (hclosed J))) :
    SharpFiniteLengthTarget.{uI, uG, uV} P M U h hclosed hδ hP hU := by
  intro I A hA
  exact StandardComplex.sharpObject_hasFiniteLength_of_terms P M U h hclosed
    hδ hP hU A (fun J => hfl J A hA) I

end Langlands.Aubert.General
