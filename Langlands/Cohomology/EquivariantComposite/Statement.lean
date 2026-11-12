import Langlands.Cohomology.EquivariantDerivedComplex
import Langlands.Cohomology.SmoothSheafDerivedComplex
import Mathlib.RepresentationTheory.Rep.Basic

/-!
# Invariant cohomology of equivariant sheaves as derived `Hom` from the trivial representation

For a group `G` acting on a space `X`, the invariant global sections of an equivariant sheaf
are the composite of the global sections, a representation of `G`, with the invariants functor.
Grothendieck's Tohoku, Chapter V, Theorem 5.2.1, derives this composite: the cohomology
`H^n(X; G, F)` of invariant global sections is the abutment of a spectral sequence with
`E_2^{p,q} = H^p(G, H^q(X, F))`. Berkovich's Corollary 1.5.2(i) asserts the analogue with
compact supports for any topological group acting smoothly; that claim fails for noncompact
groups (the Markdown gives a counterexample), so it is stated here for compact groups only.

The propositions below assert the composite-functor identification underlying these spectral
sequences: the derived invariant sections are, naturally in the sheaf, the groups of morphisms
in the derived category of representations from the trivial representation to the shifted
derived section complex. For ordinary cohomology this is stated for every group acting by
homeomorphisms; for compact supports it is stated for a compact topological group acting by
homeomorphisms with stable neighbourhoods, with smooth sheaves and smooth representations.
These identifications are conclusions; none is supplied as data.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Langlands.Sheaf.Equivariant

namespace Langlands.Cohomology

namespace EquivariantComposite

universe w w' u

section Trivial

variable (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G]

/-- The trivial representation of `G` on `R`, as a smooth representation: every vector is fixed
by the open subgroup `G` itself. -/
def trivialSmoothRep : Langlands.SmoothRep.{u, u, u} R G :=
  Langlands.SmoothRep.of (Representation.trivial R G R) fun v =>
    ⟨⊤, fun g => by simp⟩

end Trivial

/-- Tohoku V 5.2.1, composite form, for a group acting by homeomorphisms. For every commutative
ring `R`, group `G` and topological space `X` on which each element of `G` acts continuously,
for all models of the derived categories of equivariant sheaves and of representations, and for
every degree `n`, there are isomorphisms
`H^n(X; G, F) ≅ Hom_{D(Rep R G)}(R, RΓ(X, F)⟦n⟧)`
between the derived invariant global sections and the morphisms from the trivial
representation `R` in degree `0` to the shifted derived global section complex, natural in the
equivariant sheaf `F`. -/
def EquivariantGlobalCompositeStatement : Prop :=
  ∀ (R G X : Type u) [CommRing R] [Group G] [TopologicalSpace X] [MulAction G X]
    [ContinuousConstSMul G X]
    [HasDerivedCategory.{w} (TopologicalSheaf G X (ModuleCat.{u} R))]
    [HasDerivedCategory.{w'} (Rep.{u} R G)] (n : ℕ),
    ∃ e : ∀ F : TopologicalSheaf G X (ModuleCat.{u} R),
        (EquivariantDerivedSections.invariantGlobalDerived R G X n).obj F ≃+
          ShiftedHom ((DerivedCategory.singleFunctor (Rep.{u} R G) 0).obj (Rep.trivial R G R))
            (DerivedCategory.Plus.ι.obj ((EquivariantDerivedComplex.globalComplex R G X).obj F))
            (n : ℤ),
      ∀ {F F' : TopologicalSheaf G X (ModuleCat.{u} R)} (f : F ⟶ F')
        (x : (EquivariantDerivedSections.invariantGlobalDerived R G X n).obj F),
        e F' ((EquivariantDerivedSections.invariantGlobalDerived R G X n).map f x) =
          e F x ≫ (DerivedCategory.Plus.ι.map
            ((EquivariantDerivedComplex.globalComplex R G X).map f))⟦(n : ℤ)⟧'

/-- Berkovich Cor. 1.5.2(i), composite form, for a compact group. For every commutative ring
`R` and compact topological group `G` acting by homeomorphisms on a topological space `X` in
which every point has arbitrarily small open neighbourhoods stabilized by open subgroups
(`HasStableNeighbourhoods`), for all models of the derived
categories of smooth equivariant sheaves and of smooth representations, and for every degree
`n`, there are isomorphisms
`H^n_c(X; G, F) ≅ Hom_{D(SmoothRep R G)}(R, RΓ_c(X, F)⟦n⟧)`
between the derived invariant compactly supported sections of smooth sheaves and the morphisms
from the trivial smooth representation `R` in degree `0` to the shifted derived compact section
complex, natural in the smooth sheaf `F`. -/
def CompactGroupCompactCompositeStatement : Prop :=
  ∀ (R G X : Type u) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]
    [HasStableNeighbourhoods G X]
    [HasDerivedCategory.{w} (SmoothTopologicalSheaf R G X)]
    [HasDerivedCategory.{w'} (Langlands.SmoothRep.{u, u, u} R G)] (n : ℕ),
    ∃ e : ∀ F : SmoothTopologicalSheaf R G X,
        (SmoothSheafCohomology.invariantCompactDerived R G X n).obj F ≃+
          ShiftedHom ((DerivedCategory.singleFunctor (Langlands.SmoothRep.{u, u, u} R G) 0).obj
              (trivialSmoothRep R G))
            (DerivedCategory.Plus.ι.obj ((SmoothSheafDerivedComplex.compactComplex R G X).obj F))
            (n : ℤ),
      ∀ {F F' : SmoothTopologicalSheaf R G X} (f : F ⟶ F')
        (x : (SmoothSheafCohomology.invariantCompactDerived R G X n).obj F),
        e F' ((SmoothSheafCohomology.invariantCompactDerived R G X n).map f x) =
          e F x ≫ (DerivedCategory.Plus.ι.map
            ((SmoothSheafDerivedComplex.compactComplex R G X).map f))⟦(n : ℤ)⟧'

/-- The two composite-functor identifications, taken together. -/
def EquivariantCompositeStatements : Prop :=
  EquivariantGlobalCompositeStatement.{w, w', u} ∧ CompactGroupCompactCompositeStatement.{w, w', u}

end EquivariantComposite

end Langlands.Cohomology
