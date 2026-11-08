import Langlands.Representation.Exponents.ArbitraryParabolicLeviPoints
import Langlands.GroupScheme.Reductive.Basic
import Mathlib.CategoryTheory.Center.Basic

/-! # Finite type, admissibility and `ℨ(G)`-finiteness (Renard VI.10.8)

For a smooth representation `π` of `G(F)`, any two of the properties "finite type",
"admissible" and "`ℨ(G)`-finite" imply the third, and then `π` has finite length. Here
`ℨ(G)` is the centre of the category of smooth representations.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VI.10.8, Theorem: let `π` be a smooth representation of `G(F)` and consider

1. `π` is of finite type (finitely generated over `ℂ[G(F)]`);
2. `π` is admissible;
3. `π` is `ℨ(G)`-finite: the image of the centre `ℨ(G) = CatCenter` of the category of smooth
   representations in the linear endomorphisms of `π` spans a finite-dimensional space, i.e.
   the annihilator of `π` in `ℨ(G)` has finite codimension.

If two of these hold, then all three hold and `π` has finite length. -/
def CenterFiniteHoweStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)),
      let FiniteType : Prop :=
        Module.Finite (MonoidAlgebra ℂ (rationalPoints G)) π.representation.asModule
      let CenterFinite : Prop :=
        FiniteDimensional ℂ (Submodule.span ℂ (Set.range
          (fun z : CatCenter (SmoothRep.{0, u, v} ℂ (rationalPoints G)) =>
            (SmoothRep.hom (z.app π)).toLinearMap)))
      (FiniteType ∧ π.IsAdmissible) ∨ (FiniteType ∧ CenterFinite) ∨
          (π.IsAdmissible ∧ CenterFinite) →
        FiniteType ∧ π.IsAdmissible ∧ CenterFinite ∧ π.HasFiniteLength

end Langlands.Aubert.General.RepresentedParabolic
