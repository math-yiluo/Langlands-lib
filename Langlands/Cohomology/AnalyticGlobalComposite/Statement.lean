import Langlands.Sheaf.Equivariant.AnalyticEtaleGlobalComplex
import Langlands.Sheaf.Equivariant.AnalyticQuasiEtaleGlobalComplex

/-!
# Berkovich's composite-functor identification for étale and quasi-étale `G`-sheaves

Let a topological group `G` act on an analytic space `X`. Berkovich, *Étale equivariant
sheaves on p-adic analytic spaces*, §1.2, writes `Γ_{X(G)}` for the global sections on
`X(G)` and `Γ_{X{G}}` for the functor to discrete `G`-modules, and asserts for every abelian
sheaf `F` a spectral sequence `E_2^{p,q} = H^p(G, H^q(X{G}, F)) ⇒ H^{p+q}(X(G), F)`. It
comes from `Γ_{X(G)} = (-)^G ∘ Γ_{X{G}}`.

The propositions below state the composite-functor identification behind that spectral
sequence, for étale and for quasi-étale `G`-sheaves of `R`-modules. The derived functors
`H^n(X(G), F)` of the invariant global sections are, naturally in `F`, the groups of
morphisms in the derived category of smooth representations from the trivial representation
`R` in degree `0` to the shifted complex `RΓ(X{G}, F)⟦n⟧`. These identifications are
conclusions; none is supplied as data.
-/

noncomputable section

open CategoryTheory
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.Analytic

namespace Langlands.Cohomology.AnalyticGlobalComposite

universe w u v uL z uR uG

section Trivial

variable (R : Type uR) [CommRing R] (G : Type uG) [Group G] [TopologicalSpace G]

/-- The trivial representation of `G` on `R`, as a smooth representation whose carrier is
`R` itself: every vector is fixed by the open subgroup `G`. The ring, the group and the
carrier may lie in independent universes, apart from the carrier being `R`. -/
def trivialSmoothRep : Langlands.SmoothRep.{uR, uG, uR} R G :=
  Langlands.SmoothRep.of (Representation.trivial R G R) fun _ => ⟨⊤, fun g => by simp⟩

end Trivial

/-- Berkovich §1.2, composite form, for étale `G`-sheaves. Let `ρ` be an action of a
topological group `G` on an analytic space `X` over a complete non-archimedean field `K`,
by automorphisms over `K`, and `R` a commutative ring. Neither continuity of the action nor
a Hausdorff property of `X` is assumed. Smallness of `G` and admissible refinements of the distinguished
lift system are the hypotheses under which the objects are defined. Then for every model of
the derived category of smooth representations of `G` over `R`, and for every degree `n`,
there are isomorphisms
`H^n(X(G), F) ≅ Hom_{D(SmoothRep R G)}(R, RΓ(X{G}, F)⟦n⟧)`
between the derived invariant global sections of étale `G`-sheaves of `R`-modules and the
morphisms from the trivial smooth representation `R` in degree `0` to the shifted complex
`RΓ(X{G}, F)`, natural in the étale `G`-sheaf `F`. -/
def AnalyticEtaleGlobalCompositeStatement
    {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (X : LocalizedCategory.{u, v, v} (K := K))
    (G : Type z) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Small.{max u (v + 1) uL} G] (ρ : G →* Aut X)
    [(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]
    (R : Type (max u (v + 1) uL)) [CommRing R] : Prop :=
  ∀ [HasDerivedCategory.{w} (SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G)]
    (n : ℕ),
    ∃ e : ∀ F : EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R),
        (etaleGSheafInvariantCohomology.{u, v, uL} ρ R n).obj F ≃+
          ShiftedHom
            ((DerivedCategory.singleFunctor
                (SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G) 0).obj
              (trivialSmoothRep R G))
            (DerivedCategory.Plus.ι.obj ((etaleGSheafComplex.{u, v, uL} ρ R).obj F))
            (n : ℤ),
      ∀ {F F' : EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)} (f : F ⟶ F')
        (x : (etaleGSheafInvariantCohomology.{u, v, uL} ρ R n).obj F),
        e F' ((etaleGSheafInvariantCohomology.{u, v, uL} ρ R n).map f x) =
          e F x ≫ (DerivedCategory.Plus.ι.map
            ((etaleGSheafComplex.{u, v, uL} ρ R).map f))⟦(n : ℤ)⟧'

/-- Berkovich §1.2, composite form, for quasi-étale `G`-sheaves. Let `ρ` be an action of a
topological group `G` on an analytic space `X` over a complete non-archimedean field `K`,
by automorphisms over `K`, and `R` a commutative ring. Neither continuity of the action nor
a Hausdorff property of `X` is assumed. Smallness of `G` and finite equivariant refinements of the
compact lift system are the hypotheses under which the objects are defined. Then for every
model of the derived category of smooth representations of `G` over `R`, and for every
degree `n`, there are isomorphisms
`H^n(X(G), F) ≅ Hom_{D(SmoothRep R G)}(R, RΓ(X{G}, F)⟦n⟧)`
between the derived invariant global sections of quasi-étale `G`-sheaves of `R`-modules and
the morphisms from the trivial smooth representation `R` in degree `0` to the shifted
complex `RΓ(X{G}, F)`, natural in the quasi-étale `G`-sheaf `F`. -/
def AnalyticQuasiEtaleGlobalCompositeStatement
    {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (X : LocalizedCategory.{u, v, v} (K := K))
    (G : Type z) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Small.{max u (v + 1) uL} G] (ρ : G →* Aut X)
    [(compactLiftSystem ρ).HasFiniteEquivariantRefinements (twistedQuasiEtaleTopology ρ)]
    (R : Type (max u (v + 1) uL)) [CommRing R] : Prop :=
  ∀ [HasDerivedCategory.{w} (SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G)]
    (n : ℕ),
    ∃ e : ∀ F : QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R),
        (quasiEtaleGSheafInvariantCohomology.{u, v, uL} ρ R n).obj F ≃+
          ShiftedHom
            ((DerivedCategory.singleFunctor
                (SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G) 0).obj
              (trivialSmoothRep R G))
            (DerivedCategory.Plus.ι.obj ((quasiEtaleGSheafComplex.{u, v, uL} ρ R).obj F))
            (n : ℤ),
      ∀ {F F' : QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)} (f : F ⟶ F')
        (x : (quasiEtaleGSheafInvariantCohomology.{u, v, uL} ρ R n).obj F),
        e F' ((quasiEtaleGSheafInvariantCohomology.{u, v, uL} ρ R n).map f x) =
          e F x ≫ (DerivedCategory.Plus.ι.map
            ((quasiEtaleGSheafComplex.{u, v, uL} ρ R).map f))⟦(n : ℤ)⟧'

end Langlands.Cohomology.AnalyticGlobalComposite
