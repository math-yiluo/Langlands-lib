import Langlands.AlgebraicGeometry.SmoothReducedProof
import Langlands.CommutativeAlgebra.SeparablyClosedRationalPointStatement
import Langlands.AlgebraicGeometry.PointTopology.RationalDensityStatement

/-! # Conditional rational density for smooth schemes over separably closed fields -/

noncomputable section

universe u v

open CategoryTheory
open _root_.AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.PointTopology

/-- Smooth algebras over fields are geometrically reduced. -/
theorem isGeometricallyReduced_of_smooth
    (k : Type u) (R : Type v) [Field k] [CommRing R] [Algebra k R]
    [Algebra.Smooth k R] : Algebra.IsGeometricallyReduced k R := by
  apply (Algebra.isGeometricallyReduced_field_iff k R).mpr
  exact SmoothReducedProof.isReduced_of_smooth_of_domain
    (AlgebraicClosure k) (AlgebraicClosure k ⊗[k] R)

/-- The algebraic rational-point proposition gives an actual rational section
of every nonempty smooth affine scheme over a separably closed field. -/
theorem nonempty_rationalPoint_of_smooth_spec
    (hP : Langlands.CommutativeAlgebra.SeparablyClosedRationalPointStatement.{u,u})
    (k : Type u) [Field k] [IsSepClosed k]
    (R : CommRingCat.{u}) [Nontrivial R]
    (f : Spec R ⟶ Spec (CommRingCat.of k)) [Smooth f] :
    Nonempty (RationalPoint k (Over.mk f)) := by
  obtain ⟨φ, rfl⟩ := Spec.homEquiv.symm.surjective f
  algebraize [φ.hom]
  have : Algebra.Smooth k R := RingHom.smooth_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P := @Smooth)).mp ‹Smooth (Spec.map φ)›)
  have : Algebra.IsGeometricallyReduced k R := isGeometricallyReduced_of_smooth k R
  obtain ⟨a⟩ := hP k R
  refine ⟨Over.homMk (Spec.map (CommRingCat.ofHom a.toRingHom)) ?_⟩
  change Spec.map (CommRingCat.ofHom a.toRingHom) ≫ Spec.map φ = 𝟙 _
  rw [← Spec.map_comp]
  convert Spec.map_id (CommRingCat.of k) using 1
  congr 1
  ext r
  exact a.commutes r

/-- Choose an actual rational section of the given nonempty smooth affine
scheme using the algebraic rational-point proposition. -/
def rationalPointOfSmoothSpec
    (hP : Langlands.CommutativeAlgebra.SeparablyClosedRationalPointStatement.{u,u})
    (k : Type u) [Field k] [IsSepClosed k]
    (R : CommRingCat.{u}) [Nontrivial R]
    (f : Spec R ⟶ Spec (CommRingCat.of k)) [Smooth f] :
    RationalPoint k (Over.mk f) :=
  (nonempty_rationalPoint_of_smooth_spec hP k R f).some

/-- Conditional on the exact algebraic rational-point proposition, every smooth
scheme over a separably closed field has dense actual rational sections. -/
theorem hasDenseRationalPoints_of_smooth_of_rationalPointStatement
    (hP : Langlands.CommutativeAlgebra.SeparablyClosedRationalPointStatement.{u,u})
    (k : Type u) [Field k] [IsSepClosed k]
    (X : Over (Spec (CommRingCat.of k))) [Smooth X.hom] :
    HasDenseRationalPoints k X := by
  apply dense_iff_inter_open.mpr
  intro U hU ⟨x, hx⟩
  obtain ⟨R, j, hj, hxj, hjU⟩ :=
    Scheme.exists_affine_mem_range_and_range_subset (U := ⟨U, hU⟩) hx
  have : IsOpenImmersion j := hj
  obtain ⟨y, -⟩ := hxj
  have : Nontrivial R := PrimeSpectrum.nonempty_iff_nontrivial.mp ⟨y⟩
  let p := rationalPointOfSmoothSpec hP k R (j ≫ X.hom)
  let q : RationalPoint k X := p ≫ Over.homMk j rfl
  let z : Spec (CommRingCat.of k) := (⟨⊥, inferInstance⟩ : PrimeSpectrum k)
  refine ⟨q.left z, ?_, Set.mem_iUnion.mpr ⟨q, z, rfl⟩⟩
  apply hjU
  exact ⟨p.left z, rfl⟩

end Langlands.AlgebraicGeometry.PointTopology
