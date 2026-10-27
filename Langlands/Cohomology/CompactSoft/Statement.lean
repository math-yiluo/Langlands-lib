import Langlands.Sheaf.CompactSoft
import Langlands.Cohomology.TopologicalDerivedSections
import Langlands.Sheaf.Equivariant.Godement.Smooth

/-!
# Statements on `c`-soft module sheaves

These proposition definitions concern the published `c`-softness predicate
`Langlands.Sheaf.CompactSoft.IsCSoft`. On a locally compact Hausdorff space, the
first two are the case of compact supports of Grothendieck's Proposition 3.3.2 and
its Corollary (Tohoku, §3.3, p.159), in the form of Kashiwara–Schapira, *Sheaves on
Manifolds*, Proposition 2.5.8, Corollary 2.5.9 and the remark following it (§2.5,
p.105): compact sections are exact on short exact sequences with `c`-soft first
term, quotients of `c`-soft sheaves by `c`-soft subsheaves are `c`-soft, and
`c`-soft sheaves have no compactly supported cohomology in positive degrees. The
third proposition says that the underlying sheaf of the degree-zero smooth Godement
sheaf is `c`-soft, the ordinary-topology counterpart of part (2') of the proof of
Proposition 1.5.1 in Berkovich's manuscript on étale equivariant sheaves. All three
are conclusions; none is supplied as data. `CSoftStatements` is their conjunction.
-/

namespace Langlands.Cohomology

open CategoryTheory CategoryTheory.Limits Langlands.Sheaf.CompactSoft

universe u

/-- Compact sections and `c`-soft sheaves on a locally compact Hausdorff space
(Kashiwara–Schapira, Proposition 2.5.8 and Corollary 2.5.9; Tohoku, Proposition
3.3.2 for compact supports): compact sections send a short exact sequence of module
sheaves whose first term is `c`-soft to a short exact sequence, and if the first
two terms are `c`-soft, so is the third. -/
def CSoftShortExactStatement : Prop :=
  ∀ (X : TopCat.{u}) [T2Space X] [LocallyCompactSpace X] (R : Type u) [CommRing R]
    (S : ShortComplex (TopCat.Sheaf (ModuleCat.{u} R) X)),
    S.ShortExact → IsCSoft S.X₁ →
      (S.map (Sheaf.CompactSupport.functor (X := X) (R := R))).ShortExact ∧
        (IsCSoft S.X₂ → IsCSoft S.X₃)

/-- The Corollary of Grothendieck's Proposition 3.3.2 for compact supports: on a
locally compact Hausdorff space, a `c`-soft module sheaf has no compactly supported
cohomology in positive degrees, computed as the right derived functors of compact
sections. -/
def CSoftAcyclicityStatement : Prop :=
  ∀ (X : TopCat.{u}) [T2Space X] [LocallyCompactSpace X] (R : Type u) [CommRing R]
    (F : TopCat.Sheaf (ModuleCat.{u} R) X), IsCSoft F →
    ∀ q : ℕ, IsZero ((TopologicalDerivedSections.compactCohomology X R (q + 1)).obj F)

/-- On a locally compact Hausdorff space, the module sheaf underlying the
degree-zero smooth Godement sheaf of every smooth sheaf is `c`-soft. -/
def SmoothGodementZeroCSoftStatement (R : Type u) [CommRing R]
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [MulAction G X] [ContinuousConstSMul G X]
    [Langlands.Sheaf.Equivariant.HasStableNeighbourhoods G X] : Prop :=
  ∀ M : Langlands.Sheaf.Equivariant.SmoothTopologicalSheaf R G X,
    IsCSoft ((Langlands.Sheaf.Equivariant.Godement.smoothForget R G X).obj
      ((Langlands.Sheaf.Equivariant.Godement.smoothZeroFunctor R G X).obj M))

/-- The three statements together, the third for all admissible `R`, `G` and `X`.
No component is assumed to define the conjunction. -/
def CSoftStatements : Prop :=
  CSoftShortExactStatement.{u} ∧ CSoftAcyclicityStatement.{u} ∧
    ∀ (R : Type u) [CommRing R]
      (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
      (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
      [MulAction G X] [ContinuousConstSMul G X]
      [Langlands.Sheaf.Equivariant.HasStableNeighbourhoods G X],
      SmoothGodementZeroCSoftStatement R G X

end Langlands.Cohomology
