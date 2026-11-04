import Langlands.AlgebraicGeometry.SchemeLocalFiberDimension
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.Artinian
import Mathlib.Topology.Constructible

/-! # Relative dimension sublevels and the actual quasi-finite locus -/

noncomputable section

universe u

open Set Order Topology TopologicalSpace CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

/-- The actual source locus where the dimension of the residue-field fibre
at the given point is at most `n`. -/
def relativeDimensionSublevel {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) : Set X :=
  {x | relativeTopologicalKrullDimAt f x ≤ (n : WithBot ℕ∞)}

theorem relativeDimensionSublevel_mono {X Y : Scheme.{u}} (f : X ⟶ Y)
    {m n : ℕ} (h : m ≤ n) : relativeDimensionSublevel f m ⊆ relativeDimensionSublevel f n := by
  intro x hx
  change relativeTopologicalKrullDimAt f x ≤ (n : WithBot ℕ∞)
  exact hx.trans (show (m : WithBot ℕ∞) ≤ (n : WithBot ℕ∞) by exact_mod_cast h)

/-- For a locally Noetherian scheme, local dimension at most zero means
that the actual singleton is open. -/
theorem topologicalKrullDimAt_le_zero_iff_isOpen_singleton
    (X : Scheme.{u}) [IsLocallyNoetherian X] (x : X) :
    topologicalKrullDimAt x ≤ 0 ↔ IsOpen ({x} : Set X) := by
  constructor
  · intro hx
    obtain ⟨U, hxU, hU⟩ := (topologicalKrullDimAt_le_iff x 0).mp hx
    let V : X.Opens := U
    have : IsLocallyArtinian V.toScheme :=
      IsLocallyArtinian.of_topologicalKrullDim_le_zero hU
    have : DiscreteTopology V.toScheme := inferInstance
    have hs :=
      V.ι.isOpenMap ({⟨x, hxU⟩} : Set V.toScheme) (isOpen_discrete _)
    change IsOpen ((Subtype.val : V.toScheme → X) '' {⟨x, hxU⟩}) at hs
    simpa only [Set.image_singleton] using hs
  · intro hx
    let U : Opens X := ⟨{x}, hx⟩
    have : Subsingleton U := inferInstanceAs (Subsingleton ({x} : Set X))
    exact (topologicalKrullDimAt_le_open x U (by simp [U])).trans
      (topologicalKrullDim_zero_of_discreteTopology U)

/-- This bridge identifies the zero-dimensional locus with Mathlib's
quasi-finiteness predicate, rather than using it to define dimension. -/
theorem relativeTopologicalKrullDimAt_le_zero_iff_quasiFiniteAt
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] (x : X) :
    relativeTopologicalKrullDimAt f x ≤ 0 ↔ f.QuasiFiniteAt x := by
  have : LocallyOfFiniteType (f.fiberToSpecResidueField (f x)) :=
    inferInstanceAs (LocallyOfFiniteType
      (CategoryTheory.Limits.pullback.snd f (Y.fromSpecResidueField (f x))))
  have : IsLocallyNoetherian (f.fiber (f x)) :=
    LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField (f x))
  exact (topologicalKrullDimAt_le_zero_iff_isOpen_singleton
    (f.fiber (f x)) (f.asFiber x)).trans
      Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.symm

/-- The first relative-dimension sublevel is exactly the actual quasi-finite
locus of a locally finite-type morphism. -/
theorem relativeDimensionSublevel_zero_eq_quasiFiniteLocus
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] :
    relativeDimensionSublevel f 0 = (f.quasiFiniteLocus : Set X) := by
  ext x
  change relativeTopologicalKrullDimAt f x ≤ 0 ↔ f.QuasiFiniteAt x
  exact relativeTopologicalKrullDimAt_le_zero_iff_quasiFiniteAt f x

/-- The `n = 0` case of openness of relative dimension sublevels. -/
theorem isOpen_relativeDimensionSublevel_zero
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] :
    IsOpen (relativeDimensionSublevel f 0) := by
  rw [relativeDimensionSublevel_zero_eq_quasiFiniteLocus]
  exact f.quasiFiniteLocus.isOpen

/-- Pure-dimensional zero-dimensional fibres are equivalent to local
quasi-finiteness, with empty fibres allowed by the dimension predicate. -/
theorem hasPureDimensionFibers_zero_iff_locallyQuasiFinite
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] :
    HasPureDimensionFibers 0 f ↔ LocallyQuasiFinite f := by
  rw [← Scheme.Hom.quasiFiniteLocus_eq_top_iff]
  constructor
  · intro h
    apply top_le_iff.mp
    intro x _
    exact (relativeTopologicalKrullDimAt_le_zero_iff_quasiFiniteAt f x).mp
      ((hasPureDimensionFibers_iff_relativeTopologicalKrullDimAt_eq f 0).mp h x).le
  · intro h
    rw [hasPureDimensionFibers_iff_relativeTopologicalKrullDimAt_eq]
    intro x
    apply le_antisymm
    · exact (relativeTopologicalKrullDimAt_le_zero_iff_quasiFiniteAt f x).mpr
        (h.ge (show x ∈ (⊤ : X.Opens) from trivial))
    · obtain ⟨U, hxU, hU⟩ := exists_open_topologicalKrullDim_eq_at (f.asFiber x)
      change (0 : WithBot ℕ∞) ≤ topologicalKrullDimAt (f.asFiber x)
      rw [← hU]
      exact Order.krullDim_nonneg_iff.mpr
        ⟨⟨closure {⟨f.asFiber x, hxU⟩}, isIrreducible_singleton.closure, isClosed_closure⟩⟩

end Langlands.AlgebraicGeometry.SchemeFiberGeometry
