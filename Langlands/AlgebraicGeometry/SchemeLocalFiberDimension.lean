import Langlands.AlgebraicGeometry.LocalTopologicalDimension
import Langlands.AlgebraicGeometry.SchemeComponentDimension
import Langlands.AlgebraicGeometry.SchemePureDimensionFibers
import Langlands.AlgebraicGeometry.SchemeFiberGeometryLoci
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Actual local fibre dimension and componentwise pure dimension -/

noncomputable section

universe u v

open Set Order Topology TopologicalSpace CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

variable {X : Type u} [TopologicalSpace X]

/-- Global dimension is the supremum of the dimensions of actual components. -/
theorem topologicalKrullDim_eq_iSup_irreducibleComponents :
    topologicalKrullDim X = ⨆ Z : irreducibleComponents X, topologicalKrullDim Z.1 := by
  apply le_antisymm
  · change (⨆ p : LTSeries (IrreducibleCloseds X), (p.length : WithBot ℕ∞)) ≤ _
    refine iSup_le fun p => ?_
    obtain ⟨Z, hZ, hpZ⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
      (p.last : Set X) p.last.isIrreducible
    have hsub (i : Fin (p.length + 1)) : (p i : Set X) ⊆ Z :=
      Subset.trans (p.monotone (Fin.le_last i)) hpZ
    have hirr (i : Fin (p.length + 1)) :
        IsIrreducible ((Subtype.val : Z → X) ⁻¹' (p i : Set X)) := by
      let : IrreducibleSpace (p i : Set X) := Subtype.irreducibleSpace (p i).isIrreducible
      change IsIrreducible {z : Z | (z : X) ∈ (p i : Set X)}
      simpa only [image_univ, range_inclusion] using
        (IrreducibleSpace.isIrreducible_univ (p i : Set X)).image
          (inclusion (hsub i)) (continuous_inclusion (hsub i)).continuousOn
    let q : LTSeries (IrreducibleCloseds Z) := LTSeries.mk p.length
      (fun i => ⟨(Subtype.val : Z → X) ⁻¹' (p i : Set X), hirr i,
        (p i).isClosed.preimage continuous_subtype_val⟩)
      (by
        intro i j hij
        apply lt_of_le_not_ge (preimage_mono (p.monotone hij.le))
        intro hji
        apply (p.strictMono hij).not_ge
        intro x hx
        exact hji (show (⟨x, hsub j hx⟩ : Z) ∈
          (Subtype.val : Z → X) ⁻¹' (p j : Set X) from hx))
    exact q.length_le_krullDim.trans
      (le_iSup (fun T : irreducibleComponents X => topologicalKrullDim T.1) ⟨Z, hZ⟩)
  · exact iSup_le fun Z => topologicalKrullDim_subspace_le X Z.1

/-- Equal dimensions on components give that dimension at every point when
nonempty opens of components retain their dimension. -/
theorem topologicalKrullDimAt_eq_of_component_dimensions
    (hcomp : ComponentOpenDimensionInvariant X) (r : WithBot ℕ∞)
    (hdim : ∀ Z : Set X, Z ∈ irreducibleComponents X → topologicalKrullDim Z = r)
    (x : X) : topologicalKrullDimAt x = r := by
  apply le_antisymm
  · refine (topologicalKrullDimAt_le x).trans ?_
    rw [topologicalKrullDim_eq_iSup_irreducibleComponents]
    exact iSup_le fun Z => (hdim Z.1 Z.2).le
  · obtain ⟨U, hxU, hU⟩ := exists_open_topologicalKrullDim_eq_at x
    let Z := irreducibleComponent x
    have hZ : Z ∈ irreducibleComponents X := irreducibleComponent_mem_irreducibleComponents x
    let V := openInSubspace Z U
    have hV : (V : Set Z).Nonempty := ⟨⟨x, mem_irreducibleComponent⟩, hxU⟩
    calc
      r = topologicalKrullDim Z := (hdim Z hZ).symm
      _ = topologicalKrullDim V := (hcomp Z hZ V hV).symm
      _ = topologicalKrullDim ((Subtype.val : U → X) ⁻¹' Z) :=
        (subtypePreimageCommHomeomorph Z (U : Set X)).isHomeomorph.topologicalKrullDim_eq _
      _ ≤ topologicalKrullDim U := topologicalKrullDim_subspace_le U _
      _ = topologicalKrullDimAt x := hU

/-- In a Noetherian space, constant local dimension determines the dimension
of each component with invariant nonempty-open dimension. -/
theorem component_dimensions_eq_of_topologicalKrullDimAt_eq [NoetherianSpace X]
    (hcomp : ComponentOpenDimensionInvariant X) (r : WithBot ℕ∞)
    (hdim : ∀ x : X, topologicalKrullDimAt x = r)
    (Z : Set X) (hZ : Z ∈ irreducibleComponents X) :
    topologicalKrullDim Z = r := by
  obtain ⟨W, hWo, hWne, hWZ⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent Z hZ
  let U : Opens X := ⟨W, hWo⟩
  let V := openInSubspace Z U
  have hV : (V : Set Z).Nonempty := by
    obtain ⟨x, hx⟩ := hWne
    exact ⟨⟨x, hWZ hx⟩, hx⟩
  have e : V ≃ₜ U :=
    (subtypePreimageCommHomeomorph Z (U : Set X)).trans
      ((Homeomorph.setCongr (show (Subtype.val : U → X) ⁻¹' Z = univ from
        eq_univ_of_forall fun x => hWZ x.2)).trans (Homeomorph.Set.univ U))
  have : Nonempty U := hWne.to_subtype
  calc
    topologicalKrullDim Z = topologicalKrullDim V := (hcomp Z hZ V hV).symm
    _ = topologicalKrullDim U := e.isHomeomorph.topologicalKrullDim_eq _
    _ = ⨆ x : U, topologicalKrullDimAt x := topologicalKrullDim_eq_iSup_at
    _ = r := by simp only [topologicalKrullDimAt_open, hdim, ciSup_const]

/-- For a scheme locally of finite type over a field, componentwise pure
dimension is equivalent to constant actual dimension at every point.
The empty scheme satisfies both conditions. -/
theorem hasPureDimension_iff_topologicalKrullDimAt_eq_locallyOfFiniteType
    (k : Type u) [Field k] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f] (d : ℕ) :
    HasPureDimension X d ↔ ∀ x : X, topologicalKrullDimAt x = (d : WithBot ℕ∞) := by
  have hcomp := componentOpenDimensionInvariant_locallyOfFiniteType k X f
  constructor
  · intro h x
    exact topologicalKrullDimAt_eq_of_component_dimensions hcomp _ h x
  · intro h Z hZ
    obtain ⟨x, hxZ⟩ := hZ.1.nonempty
    obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
      (show x ∈ (⊤ : X.Opens) from trivial)
    have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    have : IsNoetherianRing Γ(X, U) :=
      IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    let : IsAffine U.toScheme := hU
    let : NoetherianSpace U := noetherianSpace_of_isAffineOpen U hU
    let T : Set U := (Subtype.val : U → X) ⁻¹' Z
    have hT : T ∈ irreducibleComponents U :=
      preimage_mem_irreducibleComponents hZ U.isOpenEmbedding'
        ⟨x, hxZ, ⟨⟨x, hxU⟩, rfl⟩⟩
    have hcompU : ComponentOpenDimensionInvariant U :=
      componentOpenDimensionInvariant_affine k U.toScheme (U.ι ≫ f)
    have hTdim := component_dimensions_eq_of_topologicalKrullDimAt_eq
      hcompU (d : WithBot ℕ∞)
      (fun y : U => (topologicalKrullDimAt_open U y).trans (h y)) T hT
    let V := openInSubspace Z U
    have hV : (V : Set Z).Nonempty := ⟨⟨x, hxZ⟩, hxU⟩
    exact (hcomp Z hZ V hV).symm.trans
      (((subtypePreimageCommHomeomorph Z (U : Set X)).isHomeomorph.topologicalKrullDim_eq _).trans
        hTdim)

/-- The relative local dimension uses the actual point in the scheme-theoretic
residue-field fibre, provided by Mathlib's canonical `asFiber`. -/
def relativeTopologicalKrullDimAt {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) : WithBot ℕ∞ :=
  topologicalKrullDimAt (f.asFiber x)

/-- The dimension is measured in the actual set-theoretic fibre with its
subspace topology, via Mathlib's canonical fibre homeomorphism. -/
theorem relativeTopologicalKrullDimAt_eq_preimage_singleton
    {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    relativeTopologicalKrullDimAt f x =
      topologicalKrullDimAt (⟨x, rfl⟩ : f ⁻¹' {f x}) := by
  exact (topologicalKrullDimAt_homeomorph (f.fiberHomeo (f x)) (f.asFiber x)).trans
    (congrArg topologicalKrullDimAt ((f.fiberHomeo (f x)).apply_symm_apply _))

theorem relativeTopologicalKrullDimAt_eq_of_eq
    {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) (y : Y) (h : f x = y) :
    relativeTopologicalKrullDimAt f x =
      topologicalKrullDimAt ((f.fiberHomeo y).symm ⟨x, h⟩) := by
  subst y
  rfl

/-- Every actual fibre point gives the same local dimension as its image in
the source, without finite-type hypotheses. -/
theorem relativeTopologicalKrullDimAt_fiberι
    {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) (x : f.fiber y) :
    relativeTopologicalKrullDimAt f (f.fiberι y x) = topologicalKrullDimAt x := by
  have hx : f (f.fiberι y x) = y := (f.fiberHomeo y x).2
  rw [relativeTopologicalKrullDimAt_eq_of_eq f _ y hx]
  exact congrArg topologicalKrullDimAt ((f.fiberHomeo y).symm_apply_apply x)

/-- A pure-dimensional actual fibre is characterized by the relative local
dimension at precisely the points mapping to its base point. -/
theorem hasPureDimension_fiber_iff_relativeTopologicalKrullDimAt_eq
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] (y : Y) (d : ℕ) :
    HasPureDimension (f.fiber y) d ↔
      ∀ x : X, f x = y → relativeTopologicalKrullDimAt f x = (d : WithBot ℕ∞) := by
  have : LocallyOfFiniteType (f.fiberToSpecResidueField y) :=
    inferInstanceAs (LocallyOfFiniteType
      (CategoryTheory.Limits.pullback.snd f (Y.fromSpecResidueField y)))
  rw [hasPureDimension_iff_topologicalKrullDimAt_eq_locallyOfFiniteType
    (Y.residueField y) (f.fiber y) (f.fiberToSpecResidueField y) d]
  constructor
  · intro h x hx
    rw [relativeTopologicalKrullDimAt_eq_of_eq f x y hx]
    exact h _
  · intro h x
    rw [← relativeTopologicalKrullDimAt_fiberι f y x]
    exact h _ (f.fiberHomeo y x).2

/-- The all-fibres componentwise condition is exactly constancy of the
actual relative local dimension on the source. -/
theorem hasPureDimensionFibers_iff_relativeTopologicalKrullDimAt_eq
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] (d : ℕ) :
    HasPureDimensionFibers d f ↔
      ∀ x : X, relativeTopologicalKrullDimAt f x = (d : WithBot ℕ∞) := by
  constructor
  · intro h x
    exact (hasPureDimension_fiber_iff_relativeTopologicalKrullDimAt_eq f (f x) d).mp
      (h (f x)) x rfl
  · intro h y
    exact (hasPureDimension_fiber_iff_relativeTopologicalKrullDimAt_eq f y d).mpr
      (fun x _ => h x)

/-- The exact Conrad property can use the constructed relative dimension
without changing its geometric-connectedness or nonemptiness convention. -/
theorem nonemptyGeometricallyConnectedPureDimensionFibers_iff_relativeTopologicalKrullDimAt_eq
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] (d : ℕ) :
    NonemptyGeometricallyConnectedPureDimensionFibers d f ↔
      GeometricallyConnected f ∧
        ∀ x : X, relativeTopologicalKrullDimAt f x = (d : WithBot ℕ∞) := by
  exact (nonemptyGeometricallyConnectedPureDimensionFibers_iff f).trans
    (and_congr_right fun _ => hasPureDimensionFibers_iff_relativeTopologicalKrullDimAt_eq f d)

/-- The dimension locus is the complement of the actual image of the source
points whose relative dimension differs from the prescribed value. -/
theorem pureDimensionFiberLocus_eq_compl_image
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] (d : ℕ) :
    pureDimensionFiberLocus d f =
      (f '' {x | relativeTopologicalKrullDimAt f x ≠ (d : WithBot ℕ∞)})ᶜ := by
  ext y
  change HasPureDimension (f.fiber y) d ↔
    y ∉ f '' {x | relativeTopologicalKrullDimAt f x ≠ (d : WithBot ℕ∞)}
  rw [hasPureDimension_fiber_iff_relativeTopologicalKrullDimAt_eq f y d]
  constructor
  · intro h ⟨x, hbad, hxy⟩
    exact hbad (h x hxy)
  · intro h x hxy
    by_contra hbad
    exact h ⟨x, hbad, hxy⟩

end Langlands.AlgebraicGeometry.SchemeFiberGeometry
