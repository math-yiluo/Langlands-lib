import Langlands.AlgebraicGeometry.RelativeDimensionAffineOpenness

/-! # Openness of relative local fibre dimension sublevels -/

noncomputable section

universe u v w

open Set Topology TopologicalSpace CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

/-- An injective change of target does not change a point fibre as a subspace
of the source. -/
theorem topologicalKrullDimAt_fiber_injective_target
    {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : X → Y) (j : Y → Z) (hj : Function.Injective j) (x : X) :
    topologicalKrullDimAt (⟨x, rfl⟩ : (j ∘ f) ⁻¹' {j (f x)}) =
      topologicalKrullDimAt (⟨x, rfl⟩ : f ⁻¹' {f x}) := by
  let e : ((j ∘ f) ⁻¹' {j (f x)}) ≃ₜ (f ⁻¹' {f x}) :=
    Homeomorph.setCongr (by
      ext y
      exact hj.eq_iff)
  exact topologicalKrullDimAt_homeomorph e ⟨x, rfl⟩

/-- Open source restrictions preserve the actual relative local dimension. -/
theorem relativeTopologicalKrullDimAt_open_source
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (i : Z ⟶ X)
    [IsOpenImmersion i] (z : Z) :
    relativeTopologicalKrullDimAt (i ≫ f) z =
      relativeTopologicalKrullDimAt f (i z) :=
  (relativeTopologicalKrullDimAt_eq_preimage_singleton (i ≫ f) z).trans
    ((topologicalKrullDimAt_fiber_openEmbedding f i i.isOpenEmbedding z).trans
      (relativeTopologicalKrullDimAt_eq_preimage_singleton f (i z)).symm)

/-- The target comparison uses only injectivity on points. -/
theorem relativeTopologicalKrullDimAt_injective_target
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (j : Y ⟶ Z)
    (hj : Function.Injective j) (x : X) :
    relativeTopologicalKrullDimAt (f ≫ j) x =
      relativeTopologicalKrullDimAt f x :=
  (relativeTopologicalKrullDimAt_eq_preimage_singleton (f ≫ j) x).trans
    ((topologicalKrullDimAt_fiber_injective_target f j hj x).trans
      (relativeTopologicalKrullDimAt_eq_preimage_singleton f x).symm)

private theorem isOpen_relativeDimensionSublevel_spec
    (R S : CommRingCat.{u}) (g : R ⟶ S) (hg : g.hom.FiniteType) (n : ℕ) :
    IsOpen (relativeDimensionSublevel (Spec.map g) n) := by
  let : Algebra R S := g.hom.toAlgebra
  let : Algebra.FiniteType R S := hg
  have hd (q : PrimeSpectrum S) :
      relativeTopologicalKrullDimAt (Spec.map g) q =
        topologicalKrullDimAt
          ((PrimeSpectrum.preimageHomeomorphFiber R S (q.comap (algebraMap R S)))
            ⟨q, rfl⟩) :=
    (relativeTopologicalKrullDimAt_eq_preimage_singleton (Spec.map g) q).trans
      (topologicalKrullDimAt_homeomorph _ _)
  have hset : relativeDimensionSublevel (Spec.map g) n =
      {q : PrimeSpectrum S |
        topologicalKrullDimAt
          ((PrimeSpectrum.preimageHomeomorphFiber R S (q.comap (algebraMap R S)))
            ⟨q, rfl⟩) ≤ (n : WithBot ℕ∞)} := by
    ext q
    exact (congrArg (fun d : WithBot ℕ∞ => d ≤ (n : WithBot ℕ∞)) (hd q)).to_iff
  rw [hset]
  exact isOpen_affine_fiber_dimension_sublevel R S n

/-- The affine-scheme assertion is transported along the canonical global
section spectrum isomorphisms on both source and target. -/
theorem isOpen_relativeDimensionSublevel_affine
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) [LocallyOfFiniteType f] (n : ℕ) :
    IsOpen (relativeDimensionSublevel f n) := by
  have h := isOpen_relativeDimensionSublevel_spec Γ(Y, ⊤) Γ(X, ⊤) f.appTop
    (HasRingHomProperty.appTop (P := @LocallyOfFiniteType) f inferInstance) n
  have hd (x : X) :
      relativeTopologicalKrullDimAt (Spec.map f.appTop) (X.isoSpec.hom x) =
        relativeTopologicalKrullDimAt f x := by
    calc
      _ = relativeTopologicalKrullDimAt (X.isoSpec.hom ≫ Spec.map f.appTop) x :=
        (relativeTopologicalKrullDimAt_open_source (Spec.map f.appTop)
          X.isoSpec.hom x).symm
      _ = relativeTopologicalKrullDimAt (f ≫ Y.isoSpec.hom) x := by
        rw [Scheme.isoSpec_hom_naturality]
      _ = _ := relativeTopologicalKrullDimAt_injective_target f Y.isoSpec.hom
        Y.isoSpec.hom.isOpenEmbedding.injective x
  have hset : relativeDimensionSublevel f n =
      X.isoSpec.hom ⁻¹' relativeDimensionSublevel (Spec.map f.appTop) n := by
    ext x
    exact (congrArg (fun d : WithBot ℕ∞ => d ≤ (n : WithBot ℕ∞)) (hd x).symm).to_iff
  rw [hset]
  exact h.preimage X.isoSpec.hom.continuous

/-- Restricting to affine source and target neighbourhoods computes the
original relative local dimension at every point of the source neighbourhood. -/
theorem relativeTopologicalKrullDimAt_resLE
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ f ⁻¹ᵁ U) (x : V) :
    relativeTopologicalKrullDimAt (f.resLE U V e) x =
      relativeTopologicalKrullDimAt f (V.ι x) := by
  calc
    _ = relativeTopologicalKrullDimAt (f.resLE U V e ≫ U.ι) x :=
      (relativeTopologicalKrullDimAt_injective_target (f.resLE U V e) U.ι
        U.ι.isOpenEmbedding.injective x).symm
    _ = relativeTopologicalKrullDimAt (V.ι ≫ f) x := by
      rw [Scheme.Hom.resLE_comp_ι]
    _ = _ := relativeTopologicalKrullDimAt_open_source f V.ι x

/-- Every relative local fibre dimension sublevel of a locally finite-type
scheme morphism is open, with no separation or quasi-compactness assumption. -/
theorem relativeDimensionSublevelOpenness_proof :
    RelativeDimensionSublevelOpenness.{u} := by
  intro X Y f _ n
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
    (show f x ∈ (⊤ : Y.Opens) from trivial)
  obtain ⟨V, hV, hxV, e⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ f ⁻¹ᵁ U from hxU)
  have e' : V ≤ f ⁻¹ᵁ U := e
  let g := f.resLE U V e'
  let : IsAffine U.toScheme := hU
  let : IsAffine V.toScheme := hV
  have : LocallyOfFiniteType (g ≫ U.ι) := by
    dsimp only [g]
    rw [Scheme.Hom.resLE_comp_ι]
    infer_instance
  have hg : LocallyOfFiniteType g := locallyOfFiniteType_of_comp g U.ι
  have ho := isOpen_relativeDimensionSublevel_affine g n
  refine ⟨V.ι '' relativeDimensionSublevel g n, ?_,
    V.ι.isOpenEmbedding.isOpenMap _ ho, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact (relativeTopologicalKrullDimAt_resLE f U V e' z).symm.trans_le hz
  · refine ⟨⟨x, hxV⟩, ?_, rfl⟩
    exact (relativeTopologicalKrullDimAt_resLE f U V e' ⟨x, hxV⟩).trans_le hx

end Langlands.AlgebraicGeometry.SchemeFiberGeometry
