import Langlands.Representation.Category.Subquotients
import Langlands.Representation.Exponents.LeviSupercuspidalInductionSupport
import Langlands.GroupScheme.Reductive.Basic

/-! Renard VI.6.3, Proposition: if the `K`-fixed vectors generate a smooth
representation `V`, every nonzero supercuspidal subquotient of `V` has nonzero
`K`-fixed vectors. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe u v

open GroupScheme

/-- VI.6.3, Proposition, for every compact open subgroup `K` of `G(F)`: if the
`K`-fixed vectors of a smooth representation `V` generate `V` (every subrepresentation
containing them is all of `V`), then every nonzero subquotient `D` of `V` that is
supercuspidal (published represented predicate) has a nonzero `K`-fixed vector.
Renard assumes `K` contained and normal in `K₀`; his proof does not use this, and the
statement is made for every compact open `K`. -/
def SupercuspidalSubquotientFixedVectorsStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) :=
      Aubert.General.RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (K : OpenSubgroup (rationalPoints G)),
      IsCompact (K : Set (rationalPoints G)) →
      ∀ V : SmoothRep.{0, u, v} ℂ (rationalPoints G),
        (∀ T : Subrepresentation V.representation,
          fixedVectors V.representation K.toSubgroup ≤ T.toSubmodule → T = ⊤) →
        ∀ D : SmoothRep.{0, u, v} ℂ (rationalPoints G), SmoothRep.IsSubquotient D V →
          Aubert.General.RepresentedParabolic.IsSupercuspidal D → Nontrivial D →
          fixedVectors D.representation K.toSubgroup ≠ ⊥

end Langlands.CuspidalSupport
