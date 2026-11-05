import Langlands.Representation.CuspidalSupport.RationalNormKernelFiniteRestrictionStatement

/-! # Constituent existence from an irreducible spanning family -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uK uG uV uI u

/-- A spanning family of irreducible subrepresentations of a nonzero
representation contains an irreducible subrepresentation. The index type
need not be finite. -/
theorem exists_irreducible_of_spanning_family
    {K : Type uK} [Field K] {A : Type uG} [Monoid A]
    {V : Type uV} [AddCommGroup V] [Module K V] [Nontrivial V]
    (ρ : Representation K A V) {Idx : Type uI}
    (W : Idx → Subrepresentation ρ)
    (hW : ∀ i, (W i).toRepresentation.IsIrreducible)
    (hspan : (⨆ i, (W i).toSubmodule) = ⊤) :
    ∃ S : Subrepresentation ρ, S.toRepresentation.IsIrreducible := by
  classical
  by_cases hIdx : Nonempty Idx
  · obtain ⟨i⟩ := hIdx
    exact ⟨W i, hW i⟩
  · have : IsEmpty Idx := not_nonempty_iff.mp hIdx
    simp at hspan

/-- Select an irreducible constituent from a spanning family on a nonzero
carrier. The chosen subrepresentation comes with its irreducibility proof. -/
def irreducibleConstituentOfSpanningFamily
    {K : Type uK} [Field K] {A : Type uG} [Monoid A]
    {V : Type uV} [AddCommGroup V] [Module K V] [Nontrivial V]
    (ρ : Representation K A V) {Idx : Type uI}
    (W : Idx → Subrepresentation ρ)
    (hW : ∀ i, (W i).toRepresentation.IsIrreducible)
    (hspan : (⨆ i, (W i).toSubmodule) = ⊤) :
    {S : Subrepresentation ρ // S.toRepresentation.IsIrreducible} :=
  Classical.indefiniteDescription _
    (exists_irreducible_of_spanning_family ρ W hW hspan)

/-- The finite-family clause of Renard VI.3.2(ii) supplies a constituent of
an irreducible smooth representation on the actual norm kernel. This is
an implication from the named proposition, not a proof of that proposition. -/
theorem rationalNormKernelConstituent_of_finiteRestriction
    (hfinite : RationalNormKernelFiniteRestrictionStatement.{u, uV})
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    (hG : GroupScheme.IsConnectedReductive G) :
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
    ∀ π : SmoothRep.{0, u, uV} ℂ (GroupScheme.rationalPoints G),
      π.IsIrreducible →
      ∃ W : Subrepresentation
          (π.representation.comp (Plancherel.rationalCommonNormKernel G).subtype),
        W.toRepresentation.IsIrreducible := by
  let := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
  intro π hπ
  let : π.representation.IsIrreducible := hπ
  let : Nontrivial π :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (GroupScheme.rationalPoints G))
      π.representation.asModule
  obtain ⟨m, W, hW, hspan⟩ := (hfinite F G hG π hπ).2.2
  exact exists_irreducible_of_spanning_family _ W hW hspan

end Langlands.CuspidalSupport
