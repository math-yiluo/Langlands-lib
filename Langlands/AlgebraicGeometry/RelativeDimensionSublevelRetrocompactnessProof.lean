import Langlands.AlgebraicGeometry.SchemeLocalDimensionBaseChangeProof
import Langlands.AlgebraicGeometry.RelativeDimensionSublevelOpennessProof
import Langlands.Algebra.FinitePresentationStages
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Extension.Presentation.Basic

/-! # Retrocompactness of relative local fibre dimension sublevels -/

noncomputable section

universe u

open Set Topology TopologicalSpace CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

private theorem isCompact_relativeDimensionSublevel_spec
    (R S : CommRingCat.{u}) (g : R ⟶ S) (hg : g.hom.FinitePresentation) (n : ℕ) :
    IsCompact (relativeDimensionSublevel (Spec.map g) n) := by
  let : Algebra R S := g.hom.toAlgebra
  let : Algebra.FinitePresentation R S := hg
  let P := Algebra.Presentation.ofFinitePresentation R S
  let R₀ := Langlands.Algebra.FinitePresentationStages.base P ∅
  let S₀ := Langlands.Algebra.FinitePresentationStages.model P ∅
  let t : S₀ →ₐ[R₀] S := Langlands.Algebra.FinitePresentationStages.toB P ∅
  let : Algebra S₀ S := t.toRingHom.toAlgebra
  have : IsScalarTower R₀ S₀ S := IsScalarTower.of_algebraMap_eq fun r =>
    (t.commutes r).symm
  have : Algebra.IsPushout R₀ S₀ R S := by
    refine Algebra.IsPushout.symm ⟨?_⟩
    refine IsBaseChange.of_equiv (P.tensorModelOfHasCoeffsEquiv R₀).toLinearEquiv
      fun x => ?_
    exact Langlands.Algebra.FinitePresentationStages.tensorModelOfHasCoeffsEquiv_one_tmul
      P ∅ x
  have : IsNoetherianRing S₀ := Algebra.FiniteType.isNoetherianRing R₀ S₀
  let f₀ := Spec.map (CommRingCat.ofHom (algebraMap R₀ S₀))
  have : LocallyOfFinitePresentation f₀ :=
    (LocallyOfFinitePresentation.SpecMap_iff _).mpr (by
      change (algebraMap R₀ S₀).FinitePresentation
      rw [RingHom.finitePresentation_algebraMap]
      infer_instance)
  have hsq := isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isPushout R₀ S₀ R S)
  have hset := relativeDimensionSublevel_baseChange hsq n
  change IsCompact (relativeDimensionSublevel
    (Spec.map (CommRingCat.ofHom (algebraMap R S))) n)
  rw [hset]
  exact QuasiCompact.isCompact_preimage _
    (relativeDimensionSublevelOpenness_proof f₀ n) (NoetherianSpace.isCompact _)

/-- On affine source and target the sublevel is compact, by the actual
Noetherian coefficient model. -/
theorem isCompact_relativeDimensionSublevel_affine
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) [LocallyOfFinitePresentation f] (n : ℕ) :
    IsCompact (relativeDimensionSublevel f n) := by
  have h := isCompact_relativeDimensionSublevel_spec Γ(Y, ⊤) Γ(X, ⊤) f.appTop
    f.finitePresentation_appTop n
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
  exact X.isoSpec.hom.homeomorph.isCompact_preimage.mpr h

set_option backward.isDefEq.respectTransparency.types false in
/-- A compact source requires only finitely many subordinate affine charts.
Neither the source nor the target needs any separation hypothesis. -/
theorem isCompact_relativeDimensionSublevel_of_compactSpace
    {X Y : Scheme.{u}} [CompactSpace X]
    (f : X ⟶ Y) [LocallyOfFinitePresentation f] (n : ℕ) :
    IsCompact (relativeDimensionSublevel f n) := by
  classical
  choose U hU hxU _ using fun x : X => exists_isAffineOpen_mem_and_subset
    (show f x ∈ (⊤ : Y.Opens) from trivial)
  choose V hV hxV e using fun x : X => exists_isAffineOpen_mem_and_subset
    (show x ∈ f ⁻¹ᵁ U x from hxU x)
  have hcover : (univ : Set X) ⊆ ⋃ x : X, (V x : Set X) := by
    intro x _
    exact mem_iUnion.mpr ⟨x, hxV x⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x : X => (V x : Set X)) (fun x => (V x).isOpen) hcover
  have hcomp (x : X) : IsCompact
      ((V x).ι '' relativeDimensionSublevel (f.resLE (U x) (V x) (e x)) n) := by
    let : IsAffine (U x).toScheme := hU x
    let : IsAffine (V x).toScheme := hV x
    exact (isCompact_relativeDimensionSublevel_affine
      (f.resLE (U x) (V x) (e x)) n).image (V x).ι.continuous
  have hset : relativeDimensionSublevel f n =
      ⋃ x ∈ s, (V x).ι '' relativeDimensionSublevel (f.resLE (U x) (V x) (e x)) n := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hs (mem_univ x))
      refine mem_iUnion₂.mpr ⟨i, hi, ⟨⟨x, hxi⟩, ?_, rfl⟩⟩
      exact (relativeTopologicalKrullDimAt_resLE f (U i) (V i) (e i) ⟨x, hxi⟩).trans_le hx
    · intro hx
      obtain ⟨i, _, z, hz, rfl⟩ := mem_iUnion₂.mp hx
      exact (relativeTopologicalKrullDimAt_resLE f (U i) (V i) (e i) z).symm.trans_le hz
  rw [hset]
  exact s.isCompact_biUnion fun x _ => hcomp x

/-- The actual sublevel of a locally finitely presented morphism is
retrocompact on an arbitrary scheme. -/
theorem relativeDimensionSublevelRetrocompactness_proof :
    RelativeDimensionSublevelRetrocompactness.{u} := by
  intro X Y f _ n K hK hKo
  let U : X.Opens := ⟨K, hKo⟩
  have : CompactSpace U := isCompact_iff_compactSpace.mp hK
  have h := isCompact_relativeDimensionSublevel_of_compactSpace (U.ι ≫ f) n
  have hset : U.ι '' relativeDimensionSublevel (U.ι ≫ f) n =
      relativeDimensionSublevel f n ∩ K := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨(relativeTopologicalKrullDimAt_open_source f U.ι z).symm.trans_le hz, z.2⟩
    · rintro ⟨hx, hxK⟩
      refine ⟨⟨x, hxK⟩, ?_, rfl⟩
      exact (relativeTopologicalKrullDimAt_open_source f U.ι ⟨x, hxK⟩).trans_le hx
  rw [← hset]
  exact h.image U.ι.continuous

/-- The exact published conjunction retains local finite type for openness
and local finite presentation for retrocompactness. -/
theorem relativeDimensionSublevelProperties_proof :
    RelativeDimensionSublevelProperties.{u} :=
  ⟨relativeDimensionSublevelOpenness_proof, relativeDimensionSublevelRetrocompactness_proof⟩

end Langlands.AlgebraicGeometry.SchemeFiberGeometry
