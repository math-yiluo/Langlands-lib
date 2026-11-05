import Langlands.AlgebraicGeometry.FieldExtensionLocalDimension
import Langlands.AlgebraicGeometry.AffineSchemeScalarExtension
import Langlands.AlgebraicGeometry.SchemeLocalFiberDimension
import Langlands.AlgebraicGeometry.SchemeFiberBaseChange
import Langlands.AlgebraicGeometry.RelativeDimensionBaseChangeStatement

/-! # Local dimension on actual scheme scalar extensions -/

noncomputable section

universe u

open Set Topology TopologicalSpace CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

/-- The affine scalar-extension comparison uses the original projection. -/
theorem topologicalKrullDimAt_affine_fieldExtension
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : Scheme.{u}) [IsAffine X] (f : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f]
    (q : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u})) :
    topologicalKrullDimAt q = topologicalKrullDimAt (pullback.fst f
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) q) := by
  let : Algebra k Γ(X, ⊤) := (affineStructureMap f).hom.toAlgebra
  let : Algebra.FiniteType k Γ(X, ⊤) := affineStructureMap_finiteType f
  let g := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let e := affinePullbackTensorIso K f
  have hp : (e.hom q).comap (algebraMap Γ(X, ⊤) (Γ(X, ⊤) ⊗[k] K)) =
      X.isoSpec.hom (pullback.fst f g q) := by
    exact congrArg (fun j => j q) (affinePullbackTensorIso_hom_fst K f)
  calc
    topologicalKrullDimAt q = topologicalKrullDimAt (e.hom q) :=
      topologicalKrullDimAt_eq_of_isOpenEmbedding e.hom.isOpenEmbedding q
    _ = topologicalKrullDimAt ((e.hom q).comap
        (algebraMap Γ(X, ⊤) (Γ(X, ⊤) ⊗[k] K))) :=
      topologicalKrullDimAt_tensorProduct_eq k K Γ(X, ⊤) (e.hom q)
    _ = topologicalKrullDimAt (X.isoSpec.hom (pullback.fst f g q)) :=
      congrArg topologicalKrullDimAt hp
    _ = topologicalKrullDimAt (pullback.fst f g q) :=
      (topologicalKrullDimAt_eq_of_isOpenEmbedding X.isoSpec.hom.isOpenEmbedding _).symm

/-- Affine source neighbourhoods and their inverse images compare local
 dimension on an arbitrary locally finite-type scalar extension. -/
theorem topologicalKrullDimAt_fieldExtension
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f]
    (q : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u})) :
    topologicalKrullDimAt q = topologicalKrullDimAt (pullback.fst f
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) q) := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let pr := pullback.fst f g
  obtain ⟨U, hU, hqU, _⟩ := exists_isAffineOpen_mem_and_subset
    (show pr q ∈ (⊤ : X.Opens) from trivial)
  let : IsAffine U.toScheme := hU
  let V := pr ⁻¹ᵁ U
  let z : V := ⟨q, hqU⟩
  let square := (isPullback_morphismRestrict pr U).paste_vert
    (IsPullback.of_hasPullback f g)
  let e : V.toScheme ≅ pullback (U.ι ≫ f) g := square.isoPullback
  have hp : U.ι (pullback.fst (U.ι ≫ f) g (e.hom z)) = pr q := by
    have he := congrArg (fun j => j z) square.isoPullback_hom_fst
    have hi := congrArg (fun j => j z) (morphismRestrict_ι pr U)
    exact (congrArg U.ι he).trans hi
  calc
    topologicalKrullDimAt q = topologicalKrullDimAt z :=
      (topologicalKrullDimAt_open V z).symm
    _ = topologicalKrullDimAt (e.hom z) :=
      topologicalKrullDimAt_eq_of_isOpenEmbedding e.hom.isOpenEmbedding z
    _ = topologicalKrullDimAt (pullback.fst (U.ι ≫ f) g (e.hom z)) :=
      topologicalKrullDimAt_affine_fieldExtension k K U.toScheme (U.ι ≫ f) (e.hom z)
    _ = topologicalKrullDimAt (U.ι (pullback.fst (U.ι ≫ f) g (e.hom z))) :=
      topologicalKrullDimAt_eq_of_isOpenEmbedding U.ι.isOpenEmbedding _
    _ = topologicalKrullDimAt (pr q) := congrArg topologicalKrullDimAt hp

/-- The comparison holds on any cartesian square realizing field extension. -/
theorem topologicalKrullDimAt_isPullback_fieldExtension
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {P X : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ Spec (CommRingCat.of K)}
    {f : X ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType f]
    (h : IsPullback a b f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) (q : P) :
    topologicalKrullDimAt q = topologicalKrullDimAt (a q) := by
  let e := h.isoPullback
  have hp : pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))) (e.hom q) = a q :=
    congrArg (fun j => j q) h.isoPullback_hom_fst
  exact (topologicalKrullDimAt_eq_of_isOpenEmbedding e.hom.isOpenEmbedding q).trans
    ((topologicalKrullDimAt_fieldExtension k K X f (e.hom q)).trans
      (congrArg topologicalKrullDimAt hp))

/-- The actual fibre comparison retains the projection to the original source. -/
@[reassoc (attr := simp)]
theorem fiberBaseChangeMap_fiberι
    {P X Y Z : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback a b f g) (y : Y) :
    fiberBaseChangeMap h y ≫ f.fiberι (g y) = b.fiberι y ≫ a := by
  dsimp only [fiberBaseChangeMap, Scheme.Hom.fiberι, pullback.map]
  exact pullback.lift_fst _ _ _

set_option backward.isDefEq.respectTransparency.types false in
/-- Actual residue-field scalar extension preserves relative local dimension
 under arbitrary base change of a locally finite-type scheme morphism. -/
theorem relativeTopologicalKrullDimAt_baseChange
    {P X Y Z : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} [LocallyOfFiniteType f]
    (h : IsPullback a b f g) (x : P) :
    relativeTopologicalKrullDimAt b x = relativeTopologicalKrullDimAt f (a x) := by
  let y := b x
  let : Algebra (Z.residueField (g y)) (Y.residueField y) :=
    (g.residueFieldMap y).hom.toAlgebra
  have : LocallyOfFiniteType (f.fiberToSpecResidueField (g y)) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  let z := b.asFiber x
  have hp : f.fiberι (g y) (fiberBaseChangeMap h y z) = a x := by
    rw [← Scheme.Hom.comp_apply, fiberBaseChangeMap_fiberι]
    exact congrArg a (b.fiberι_asFiber x)
  calc
    relativeTopologicalKrullDimAt b x = topologicalKrullDimAt z := rfl
    _ = topologicalKrullDimAt (fiberBaseChangeMap h y z) :=
      topologicalKrullDimAt_isPullback_fieldExtension
        (Z.residueField (g y)) (Y.residueField y) (fiberBaseChangeSquare h y) z
    _ = relativeTopologicalKrullDimAt f (f.fiberι (g y) (fiberBaseChangeMap h y z)) :=
      (relativeTopologicalKrullDimAt_fiberι f (g y) _).symm
    _ = relativeTopologicalKrullDimAt f (a x) :=
      congrArg (relativeTopologicalKrullDimAt f) hp

/-- The actual local-dimension sublevels commute with arbitrary base change. -/
theorem relativeDimensionSublevel_baseChange
    {P X Y Z : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} [LocallyOfFiniteType f]
    (h : IsPullback a b f g) (n : ℕ) :
    relativeDimensionSublevel b n = a ⁻¹' relativeDimensionSublevel f n := by
  ext x
  change relativeTopologicalKrullDimAt b x ≤ (n : WithBot ℕ∞) ↔
    relativeTopologicalKrullDimAt f (a x) ≤ (n : WithBot ℕ∞)
  rw [relativeTopologicalKrullDimAt_baseChange h x]

/-- Stacks Lemma 29.29.3(1) and its actual sublevel consequence. -/
theorem relativeDimensionBaseChangeInvariance :
    RelativeDimensionBaseChangeInvariance.{u} := by
  intro P X Y Z a b f g _ h
  exact ⟨relativeTopologicalKrullDimAt_baseChange h, relativeDimensionSublevel_baseChange h⟩

end Langlands.AlgebraicGeometry.SchemeFiberGeometry
