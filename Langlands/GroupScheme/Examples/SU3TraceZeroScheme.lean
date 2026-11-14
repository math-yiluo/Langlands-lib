import Langlands.GroupScheme.Examples.SU3TraceZeroCoordinates
import Langlands.GroupScheme.Rational.VectorGroupCoordinates

/-! # The represented quadratic trace-zero group -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry Algebra
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.SU3Root

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [IsQuadraticExtension k L] [Algebra.IsSeparable k L]

/-- Coefficient change on the actual additive tensor trace kernel. -/
def tensorTraceZeroMap {R S : Type u} [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] (f : R →ₐ[k] S) :
    Parameters.traceZero (tensorInvolution k L R) →+
      Parameters.traceZero (tensorInvolution k L S) where
  toFun x := ⟨tensorCoefficientMap k L f x, by
    change tensorCoefficientMap k L f x +
      (tensorInvolution k L S).bar (tensorCoefficientMap k L f x) = 0
    rw [← tensorCoefficientMap_bar, ← map_add, x.property, map_zero]⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ _ _)

/-- The functor of the actual conjugation-trace kernel on test algebras. -/
def traceZeroFunctor : CommAlgCat.{u} (CommRingCat.of k) ⥤ GrpCat.{u} where
  obj R := GrpCat.of (Multiplicative (Parameters.traceZero (tensorInvolution k L R)))
  map f := GrpCat.ofHom (AddMonoidHom.toMultiplicative (tensorTraceZeroMap k L f.hom))
  map_id R := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact congrArg (fun f : R ⊗[k] L →ₐ[k] R ⊗[k] L => f x.toAdd.val)
      (tensorCoefficientMap_id k L)
  map_comp f g := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact congrArg (fun q => q x.toAdd.val) (tensorCoefficientMap_comp k L f.hom g.hom)

variable (eta : Parameters.traceZero (fieldInvolution k L)) (hEta : (eta : L) ≠ 0)

/-- The tensor parametrization in the vector-group functor's one-coordinate notation. -/
def traceZeroAlgebraEquiv (R : CommAlgCat.{u} (CommRingCat.of k)) :
    Multiplicative (Fin 1 → R) ≃* (traceZeroFunctor k L).obj R := by
  change Multiplicative (Fin 1 → R) ≃*
    Multiplicative (Parameters.traceZero (tensorInvolution k L R))
  exact AddEquiv.toMultiplicative ((AddEquiv.piUnique (fun _ : Fin 1 => R)).trans
    (tensorTraceZeroEquiv k L eta hEta R))

/-- The polynomial line corepresents the actual tensor trace kernel. -/
def traceZeroCorepresentableBy :
    (traceZeroFunctor k L ⋙ forget GrpCat).CorepresentableBy
      (VectorGroup.coordinateAlgebra (CommRingCat.of k) 1) where
  homEquiv := (VectorGroup.corepresentableBy (CommRingCat.of k) 1).homEquiv.trans
    (traceZeroAlgebraEquiv k L eta hEta _).toEquiv
  homEquiv_comp _ _ := rfl

/-- The affine group scheme representing trace-zero tensors. -/
abbrev traceZeroGroupScheme : GroupScheme (Spec (CommRingCat.of k)) :=
  Corepresented.groupScheme (traceZeroFunctor k L) (traceZeroCorepresentableBy k L eta hEta)

/-- Every test scheme recovers the actual trace kernel on its relative global sections. -/
def traceZeroPointsEquiv (T : Over (Spec (CommRingCat.of k))) :
    (T ⟶ (traceZeroGroupScheme k L eta hEta).X) ≃*
      Multiplicative (Parameters.traceZero
        (tensorInvolution k L ((algΓ (CommRingCat.of k)).obj T).unop)) :=
  Corepresented.pointsEquiv (traceZeroFunctor k L) (traceZeroCorepresentableBy k L eta hEta) T

/-- The all-test tensor comparison is natural for every scheme restriction. -/
theorem traceZeroPointsEquiv_naturality {T W : Over (Spec (CommRingCat.of k))}
    (a : W ⟶ T) (x : T ⟶ (traceZeroGroupScheme k L eta hEta).X) :
    (traceZeroPointsEquiv k L eta hEta W (a ≫ x)).toAdd =
      tensorTraceZeroMap k L ((algΓ (CommRingCat.of k)).map a).unop.hom
        (traceZeroPointsEquiv k L eta hEta T x).toAdd :=
  congrArg Multiplicative.toAdd
    (Corepresented.pointsEquiv_naturality (traceZeroFunctor k L)
      (traceZeroCorepresentableBy k L eta hEta) a x)

/-- The inverse scalar coordinate commutes with arbitrary coefficient change. -/
theorem tensorTraceZeroEquiv_symm_map {R S : Type u} [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] (f : R →ₐ[k] S)
    (x : Parameters.traceZero (tensorInvolution k L R)) :
    (tensorTraceZeroEquiv k L eta hEta S).symm (tensorTraceZeroMap k L f x) =
      f ((tensorTraceZeroEquiv k L eta hEta R).symm x) := by
  apply (tensorTraceZeroEquiv k L eta hEta S).injective
  rw [AddEquiv.apply_symm_apply]
  have h : tensorTraceZeroMap k L f
      (tensorTraceZeroEquiv k L eta hEta R ((tensorTraceZeroEquiv k L eta hEta R).symm x)) =
      tensorTraceZeroEquiv k L eta hEta S
        (f ((tensorTraceZeroEquiv k L eta hEta R).symm x)) := Subtype.ext rfl
  rwa [AddEquiv.apply_symm_apply] at h

/-- Scalar coordinates on every test scheme, obtained from the actual tensor trace kernel. -/
def traceZeroVectorCoordinates (T : Over (Spec (CommRingCat.of k))) :
    (T ⟶ (traceZeroGroupScheme k L eta hEta).X) ≃*
      Multiplicative (Fin 1 → Γ(T.left, ⊤)) :=
  (traceZeroPointsEquiv k L eta hEta T).trans
    (traceZeroAlgebraEquiv k L eta hEta ((algΓ (CommRingCat.of k)).obj T).unop).symm

/-- The scalar coordinates are natural on all scheme tests, including nonaffine tests. -/
theorem traceZeroVectorCoordinates_natural :
    RelativeRoot.IsNaturalVectorCoordinates (traceZeroVectorCoordinates k L eta hEta) := by
  intro T W a x
  funext j
  change (tensorTraceZeroEquiv k L eta hEta
      ((algΓ (CommRingCat.of k)).obj W).unop).symm
      (traceZeroPointsEquiv k L eta hEta W (a ≫ x)).toAdd =
    a.left.appTop ((tensorTraceZeroEquiv k L eta hEta
      ((algΓ (CommRingCat.of k)).obj T).unop).symm
      (traceZeroPointsEquiv k L eta hEta T x).toAdd)
  rw [traceZeroPointsEquiv_naturality]
  exact tensorTraceZeroEquiv_symm_map k L eta hEta _ _

/-- The actual trace-zero group is isomorphic to the polynomial additive line. -/
def traceZeroVectorIso :
    traceZeroGroupScheme k L eta hEta ≅ VectorGroup.groupScheme (CommRingCat.of k) 1 :=
  RelativeRoot.vectorGroupIso (traceZeroVectorCoordinates k L eta hEta)
    (traceZeroVectorCoordinates_natural k L eta hEta)

/-- Its isomorphism recovers the scalar extracted from the actual tensor on every test. -/
theorem coordinates_traceZeroVectorIso (T : Over (Spec (CommRingCat.of k)))
    (x : T ⟶ (traceZeroGroupScheme k L eta hEta).X) :
    VectorGroup.coordinates (CommRingCat.of k) 1 T
      (x ≫ (traceZeroVectorIso k L eta hEta).hom.hom.hom) =
      traceZeroVectorCoordinates k L eta hEta T x :=
  RelativeRoot.coordinates_comp_vectorGroupIso_hom _ _ T x

end Langlands.GroupScheme.SU3Root
