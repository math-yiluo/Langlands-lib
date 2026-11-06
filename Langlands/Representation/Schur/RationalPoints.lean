import Langlands.Representation.Category.Basic
import Langlands.Representation.Whittaker.MirabolicPairingRigidityElementary
import Langlands.AlgebraicGeometry.PointTopology.RationalPointHaarProof
import Langlands.GroupScheme.Reductive.Basic
import Langlands.Representation.Exponents.ArbitraryParabolicLeviPoints

/-! # Scalar endomorphisms for smooth representations of actual rational points -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.Schur

universe uG uV u

/-- Countable-dimensional Schur applies to every irreducible smooth representation
of a separable topological group. -/
theorem separableSmooth_scalarEndomorphism
    {H : Type uG} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace.SeparableSpace H]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ H V) (hρ : IsSmooth ρ) (hi : ρ.IsIrreducible)
    (f : ρ.IntertwiningMap ρ) :
    ∃! c : ℂ, f = c • Representation.IntertwiningMap.id ρ :=
  countableDimensionalSchur ρ
    (Whittaker.MirabolicRigidity.rank_le_aleph0 ρ hρ hi) hi f

/-- Scalars identify the endomorphism space with the complex field. The forward
map is the actual scalar multiple of the identity intertwiner. -/
def separableSmoothEndomorphismEquiv
    {H : Type uG} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace.SeparableSpace H]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ H V) (hρ : IsSmooth ρ) (hi : ρ.IsIrreducible) :
    ℂ ≃ₗ[ℂ] ρ.IntertwiningMap ρ :=
  LinearEquiv.ofBijective
    (LinearMap.toSpanSingleton ℂ _ (Representation.IntertwiningMap.id ρ)) (by
      constructor
      · intro a b hab
        obtain ⟨c, -, hc⟩ :=
          separableSmooth_scalarEndomorphism ρ hρ hi
            (a • Representation.IntertwiningMap.id ρ)
        exact (hc a rfl).trans (hc b hab).symm
      · intro f
        obtain ⟨c, hc, -⟩ := separableSmooth_scalarEndomorphism ρ hρ hi f
        exact ⟨c, hc.symm⟩)

@[simp] theorem separableSmoothEndomorphismEquiv_apply
    {H : Type uG} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace.SeparableSpace H]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ H V) (hρ : IsSmooth ρ) (hi : ρ.IsIrreducible)
    (c : ℂ) :
    separableSmoothEndomorphismEquiv ρ hρ hi c =
      c • Representation.IntertwiningMap.id ρ := rfl

/-- The algebraic dimension is at most countable in the canonical point topology. -/
theorem rationalPoint_rank_le_aleph0
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : GroupScheme.IsConnectedReductive G) :
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
    ∀ π : SmoothRep.{0, u, uV} ℂ (GroupScheme.rationalPoints G), π.IsIrreducible →
      Module.rank ℂ π ≤ Cardinal.aleph0 := by
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : Smooth G.X.hom := hG.smooth
  let : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
  have := rationalPoint_secondCountableTopology F G
  have := rationalPoint_isTopologicalGroup F G
  intro π hi
  exact Whittaker.MirabolicRigidity.rank_le_aleph0 π.representation π.isSmooth hi

/-- Every intertwining endomorphism of an irreducible smooth representation of
the actual rational-point group is a unique scalar. -/
theorem rationalPoint_scalarEndomorphism
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : GroupScheme.IsConnectedReductive G) :
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
    ∀ (π : SmoothRep.{0, u, uV} ℂ (GroupScheme.rationalPoints G)) (_ : π.IsIrreducible)
      (f : π.representation.IntertwiningMap π.representation),
      ∃! c : ℂ, f = c • Representation.IntertwiningMap.id π.representation := by
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
  intro π hi f
  exact countableDimensionalSchur π.representation
    (rationalPoint_rank_le_aleph0 F G hG π hi) hi f

/-- The scalar parametrization in the actual rational-point topology. -/
def rationalPointEndomorphismEquiv
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : GroupScheme.IsConnectedReductive G) :
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
    ∀ (π : SmoothRep.{0, u, uV} ℂ (GroupScheme.rationalPoints G)) (_ : π.IsIrreducible),
      ℂ ≃ₗ[ℂ] π.representation.IntertwiningMap π.representation := by
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : Smooth G.X.hom := hG.smooth
  let : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
  have := rationalPoint_secondCountableTopology F G
  have := rationalPoint_isTopologicalGroup F G
  intro π hi
  exact separableSmoothEndomorphismEquiv π.representation π.isSmooth hi

/-- The same scalar conclusion in the exact canonical Levi topology used by the
induction and Jacquet functors of a represented rational parabolic. -/
theorem leviPoint_scalarEndomorphism
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {P M : GroupScheme (Spec (CommRingCat.of F))}
    (l : M ⟶ P) (hl : GroupScheme.IsRationalLeviSubgroup l) :
    haveI := hl.isConnectedReductive.isAffineHom
    letI : TopologicalSpace (GroupScheme.rationalPoints M) :=
      Aubert.General.RepresentedParabolic.leviPointTopology l hl
    ∀ (π : SmoothRep.{0, u, uV} ℂ (GroupScheme.rationalPoints M)) (_ : π.IsIrreducible)
      (f : π.representation.IntertwiningMap π.representation),
      ∃! c : ℂ, f = c • Representation.IntertwiningMap.id π.representation := by
  have := hl.isConnectedReductive.isAffineHom
  have : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  exact rationalPoint_scalarEndomorphism F M hl.isConnectedReductive

end Langlands.Schur
