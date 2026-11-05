import Langlands.AlgebraicGeometry.SchemeComponentGeometry
import Langlands.AlgebraicGeometry.GenericPointAvoidance

/-! # Generic-point open reduction for geometric component properties -/

universe u

open Set Topology TopologicalSpace CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

variable {U X Y : Scheme.{u}}

/-- Finitely many components admit a quasi-compact open containing every generic point. -/
theorem exists_isCompact_open_containing_genericPoints (X : Scheme.{u})
    [Finite (irreducibleComponents X)] :
    ∃ V : X.Opens, IsCompact (V : Set X) ∧ genericPoints X ⊆ V := by
  classical
  have hfin : (genericPoints X).Finite :=
    genericPoints.finite (Set.toFinite (irreducibleComponents X))
  let := hfin.to_subtype
  have hex (x : genericPoints X) :
      ∃ V : X.Opens, IsAffineOpen V ∧ (x : X) ∈ V := by
    obtain ⟨V, hV, hxV, -⟩ :=
      exists_isAffineOpen_mem_and_subset (U := (⊤ : X.Opens))
        (show (x : X) ∈ (⊤ : X.Opens) from trivial)
    exact ⟨V, hV, hxV⟩
  choose V hVa hxV using hex
  refine ⟨⨆ x, V x, ?_, ?_⟩
  · simpa only [Opens.coe_iSup] using isCompact_iUnion (fun x => (hVa x).isCompact)
  · intro x hx
    exact (le_iSup V ⟨x, hx⟩) (hxV ⟨x, hx⟩)

/-- A chosen compact open neighbourhood of all generic points. -/
noncomputable def genericPointCompactOpen (X : Scheme.{u})
    [Finite (irreducibleComponents X)] :
    {V : X.Opens // IsCompact (V : Set X) ∧ genericPoints X ⊆ V} :=
  ⟨Classical.choose (exists_isCompact_open_containing_genericPoints X),
    Classical.choose_spec (exists_isCompact_open_containing_genericPoints X)⟩

/-- A dense open subscheme that is geometrically irreducible makes the ambient field
scheme geometrically irreducible. -/
theorem geometricallyIrreducible_of_dense_open {K : Type u} [Field K]
    (j : U ⟶ X) [IsOpenImmersion j] (f : X ⟶ Spec (.of K))
    (hj : DenseRange j) [GeometricallyIrreducible (j ≫ f)] :
    GeometricallyIrreducible f := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun L _ e => ?_⟩
  let q := pullback.snd j (pullback.fst f e)
  have hq : DenseRange q := by
    change Dense (Set.range q)
    dsimp only [q]
    rw [Scheme.Pullback.range_snd]
    exact hj.preimage (pullback.fst f e).isOpenMap
  have hI : IrreducibleSpace (pullback j (pullback.fst f e) : Scheme.{u}) :=
    (pullbackRightPullbackFstIso f e j).hom.homeomorph.irreducibleSpace_iff.mpr
      (inferInstanceAs (IrreducibleSpace (pullback (j ≫ f) e : Scheme.{u})))
  have hr : IsIrreducible (Set.range q) := by
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image q q.continuous.continuousOn
  rw [irreducibleSpace_def]
  change IsIrreducible (Set.univ : Set (pullback f e : Scheme.{u}))
  rw [← hq.closure_range]
  exact hr.closure

/-- The component property can be recovered from an open containing all generic points.
Actual vanishing-ideal closed subschemes are compared by their supports. -/
theorem ComponentsGeometricallyIrreducible.of_open_containing_genericPoints
    {K : Type u} [Field K] (f : X ⟶ Spec (.of K)) (V : X.Opens)
    (hV : genericPoints X ⊆ V)
    (h : ComponentsGeometricallyIrreducible (V.ι ≫ f)) :
    ComponentsGeometricallyIrreducible f := by
  intro C
  have hmeet : (C.val ∩ Set.range V.ι).Nonempty := by
    rw [Scheme.Opens.range_ι]
    exact ⟨(genericPoints.ofComponent C).1,
      (genericPoints.isGenericPoint_ofComponent C).mem,
      hV (genericPoints.ofComponent C).2⟩
  let D : irreducibleComponents V.toScheme :=
    ⟨V.ι ⁻¹' C.val,
      preimage_mem_irreducibleComponents C.property V.ι.isOpenEmbedding hmeet⟩
  let I := Scheme.IdealSheafData.vanishingIdeal
    (⟨C.val, isClosed_of_mem_irreducibleComponents C.val C.property⟩ : Closeds X)
  let i := I.subschemeι
  let j := pullback.fst i V.ι
  let q := pullback.snd i V.ι
  let k := (Scheme.IdealSheafData.vanishingIdeal
    (⟨D.val, isClosed_of_mem_irreducibleComponents D.val D.property⟩ :
      Closeds V.toScheme)).subschemeι
  have hr : Set.range q = Set.range k := by
    simp only [q, Scheme.Pullback.range_snd, k, i, I,
      Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have hq : GeometricallyIrreducible (q ≫ V.ι ≫ f) :=
    (GenericImagePattern.geometricallyIrreducible_iff_of_closedImmersion_range_eq
      (V.ι ≫ f) q k hr).mpr (h D)
  have hjGI : GeometricallyIrreducible (j ≫ i ≫ f) := by
    rw [← Category.assoc, show j ≫ i = q ≫ V.ι from pullback.condition, Category.assoc]
    exact hq
  have hI : IrreducibleSpace I.subscheme := by
    exact (i.isEmbedding.toHomeomorph.trans
      (.setCongr (show Set.range i = C.val from
        Scheme.IdealSheafData.range_subschemeι I))).irreducibleSpace_iff.mpr
          (Subtype.irreducibleSpace C.property.1)
  have hj : DenseRange j := by
    change Dense (Set.range j)
    dsimp only [j]
    rw [Scheme.Pullback.range_fst, Scheme.Opens.range_ι]
    apply (V.isOpen.preimage i.continuous).dense
    obtain ⟨x, hxC, hxV⟩ := hmeet
    have hx : x ∈ Set.range i := by
      rw [show Set.range i = C.val from Scheme.IdealSheafData.range_subschemeι I]
      exact hxC
    obtain ⟨z, rfl⟩ := hx
    refine ⟨z, ?_⟩
    change i z ∈ (V : Set X)
    simpa only [Scheme.Opens.range_ι] using hxV
  exact geometricallyIrreducible_of_dense_open j (i ≫ f) hj

/-- A flat map pulls a generic-point neighbourhood back to another such neighbourhood. -/
theorem genericPoints_subset_preimage_of_flat (p : Y ⟶ X) [Flat p]
    (V : X.Opens) (hV : genericPoints X ⊆ V) :
    genericPoints Y ⊆ p ⁻¹ᵁ V := by
  intro y hy
  exact hV (GenericPointAvoidance.mem_genericPoints_of_generalizingMap
    (Flat.generalizingMap p) hy)

end Langlands.AlgebraicGeometry.SchemeFiberGeometry
