import Langlands.Representation.Smooth.Definitions
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.GroupTheory.PGroup
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Abelian.RightDerived

/-!
# Pro-p invariants and finite acyclic resolutions

These proposition definitions state two algebraic inputs of Harris 1999,
section 2: exactness of invariants of a pro-`p` group on smooth modules over a
ring in which `p` is invertible, and acyclicity of the cycles of an acyclic
resolution beyond the cohomological dimension. The inclusion of invariants is
constructed below; exactness and acyclicity are conclusions.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Cohomology

universe uH uR uV u v u' v'

/-- The inclusion of the invariant submodule into the underlying module. -/
def invariantsInclusion (R : Type uR) [CommRing R] (H : Type uH) [Group H] :
    Rep.invariantsFunctor.{uV} R H ⟶ forget₂ (Rep.{uV} R H) (ModuleCat.{uV} R) where
  app A := ModuleCat.ofHom A.ρ.invariants.subtype
  naturality _ _ _ := by
    ext
    rfl

/-- For a profinite pro-`p` group and coefficients in which `p` is invertible,
taking invariants carries short exact sequences of smooth representations
to short exact sequences of modules. -/
def ProPInvariantsExactStatement : Prop :=
  ∀ (p : ℕ), p.Prime →
    ∀ (H : Type uH) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
      [CompactSpace H] [TotallyDisconnectedSpace H],
      (∀ N : OpenNormalSubgroup H, IsPGroup p (H ⧸ N.toSubgroup)) →
      ∀ (R : Type uR) [CommRing R], IsUnit (p : R) →
      ∀ (S : ShortComplex (Rep.{uV} R H)), S.ShortExact →
        IsSmooth S.X₁.ρ → IsSmooth S.X₂.ρ → IsSmooth S.X₃.ρ →
        (S.map (Rep.invariantsFunctor R H)).ShortExact

/-- If such a group acts trivially on the cohomology of a complex of smooth
representations, the subcomplex of invariants is quasi-isomorphic to it. -/
def ProPInvariantSubcomplexStatement : Prop :=
  ∀ (p : ℕ), p.Prime →
    ∀ (H : Type uH) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
      [CompactSpace H] [TotallyDisconnectedSpace H],
      (∀ N : OpenNormalSubgroup H, IsPGroup p (H ⧸ N.toSubgroup)) →
      ∀ (R : Type uR) [CommRing R], IsUnit (p : R) →
      ∀ (C : CochainComplex (Rep.{uV} R H) ℤ),
        (∀ i : ℤ, IsSmooth (C.X i).ρ) →
        (∀ (q : ℤ) (h : H), (C.homology q).ρ h = LinearMap.id) →
        QuasiIso ((NatTrans.mapHomologicalComplex
          (invariantsInclusion.{uH, uR, uV} R H) (ComplexShape.up ℤ)).app C)

/-- Beyond the cohomological dimension of the resolved object, the cycles of
an acyclic resolution are again acyclic, so truncating there gives a finite
acyclic resolution. -/
def AcyclicResolutionCyclesStatement : Prop :=
  ∀ (C : Type u) [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
    (D : Type u') [Category.{v'} D] [Abelian D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    (A : C) (K : CochainComplex C ℕ)
    (ε : (CochainComplex.single₀ C).obj A ⟶ K),
    QuasiIso ε →
    (∀ (i n : ℕ), IsZero ((F.rightDerived (n + 1)).obj (K.X i))) →
    ∀ d : ℕ, (∀ q : ℕ, d < q → IsZero ((F.rightDerived q).obj A)) →
      ∀ n : ℕ, d ≤ n → ∀ q : ℕ, IsZero ((F.rightDerived (q + 1)).obj (K.cycles n))

/-- The pro-`p` invariants and finite-resolution family. No component is
assumed to define the conjunction. -/
def ProPInvariantTruncationStatements : Prop :=
  ProPInvariantsExactStatement.{uH, uR, uV} ∧
  ProPInvariantSubcomplexStatement.{uH, uR, uV} ∧
  AcyclicResolutionCyclesStatement.{u, v, u', v'}

end Langlands.Cohomology
