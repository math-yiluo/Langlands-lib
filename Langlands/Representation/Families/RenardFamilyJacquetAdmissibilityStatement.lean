import Langlands.Representation.Families.RenardFamilyParabolicFunctors
import Langlands.GroupScheme.Reductive.Basic

/-!
# Renard VI.9.5: the Jacquet module of an admissible `(G, B)`-module is admissible

For a rational parabolic `P = MN` of a connected reductive group `G` over a
nonarchimedean local field and a reduced Noetherian finitely generated `ℂ`-algebra `B`,
the normalized Jacquet module `r_P^G(V)` of an admissible `(G(F), B)`-module `V` has
finitely generated `B`-modules of fixed vectors under every compact open subgroup of
`M(F)`. Compact open subgroups are open subgroups with compact carrier.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Renard.AlgebraicFamily

open Langlands.Aubert.General Langlands.Aubert.General.RepresentedParabolic GroupScheme

/-- VI.9.5: the normalized Jacquet functor `r_P^G` sends admissible `(G(F), B)`-modules to
families whose compact-open fixed modules are finitely generated over `B`. -/
def JacquetAdmissibleStatement.{u', uB', uV'} : Prop :=
  ∀ (k : Type u') [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (P M U : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
      (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
      (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
      (hmul : IsIso (subgroupMultiplication l r)),
      haveI := hl.isConnectedReductive.isAffineHom
      letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
      ∀ (B : Type uB') [CommRing B] [Algebra ℂ B] [IsNoetherianRing B]
        [Algebra.FiniteType ℂ B] [IsReduced B]
        (V : Type uV') [AddCommGroup V] [Module B V]
        (ρ : Representation B (rationalPoints G) V),
        IsSmooth ρ → Module.Flat B V →
          (∀ K : OpenSubgroup (rationalPoints G), IsCompact (K : Set (rationalPoints G)) →
            Module.Finite B (fixedVectors ρ K.toSubgroup)) →
            ∀ K : OpenSubgroup (rationalPoints M), IsCompact (K : Set (rationalPoints M)) →
              Module.Finite B
                (fixedVectors (leviJacquetRepresentation p l r hp hr hl hmul ρ) K.toSubgroup)

end Langlands.Renard.AlgebraicFamily
