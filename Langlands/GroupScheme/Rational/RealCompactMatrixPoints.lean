import Langlands.AlgebraicGeometry.PointTopology.AffineBoundedTransport
import Langlands.AlgebraicGeometry.PointTopology.DenseRationalFamily
import Langlands.GroupScheme.Dynamic.GeneralLinearStabilizer
import Langlands.GroupScheme.Rational.ScalarExtensionTopology
import Langlands.GroupScheme.Rational.SubquotientSpectralIntegrality
import Langlands.GroupScheme.Rational.ValuedRepresentationBaseChange
import Langlands.GroupScheme.Reductive.SelfAdjointRealizationProof
import Langlands.GroupScheme.Torus.RationalCharacterSeparation

/-! # Matrix coordinates of compact real forms -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry Matrix MvPolynomial
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RealCompactForm

open GaloisPointComparison Langlands.GroupScheme.GeneralLinear
open MatrixRepresentation (rationalMatrix_apply_apply)

section Coordinates

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  {n : Type} [Fintype n] [DecidableEq n]

/-- The rational matrix is the coefficient matrix at the ground algebra. -/
theorem rationalMatrix_eq_coeffMatrix (ρ : MatrixRepresentation G n) (x : rationalPoints G) :
    ρ.rationalMatrix x =
      ρ.affineMatrix (CommAlgCat.of k k) (rationalCoeffEquiv k G x) := by
  rw [ρ.rationalMatrix_eq_affineMatrix]
  congr 1

/-- A polynomial in the entries and inverse entries that vanishes on a dense
family of rational points vanishes on every rational matrix of the representation. -/
theorem eval_eq_zero_of_dense [IsAffine G.X.left] (ρ : MatrixRepresentation G n)
    {I : Type v} (x : I → rationalPoints G) (hd : HasDenseRationalPointFamily x)
    (p : MvPolynomial (Coordinate n) k)
    (hp : ∀ i, eval (values (ρ.rationalMatrix (x i))) p = 0)
    (g : rationalPoints G) [IsReduced G.X.left] :
    eval (values (ρ.rationalMatrix g)) p = 0 := by
  let M : GL n (AffineCoordinateRing k G.X) := ρ.pointMatrix G.X (𝟙 _)
  let s := aeval (values M) p
  have h_eval (y : rationalPoints G) :
      rationalPointAlgebraHom k G.X y s = eval (values (ρ.rationalMatrix y)) p := by
    have hm : Matrix.GeneralLinearGroup.map (rationalPointAlgebraHom k G.X y).toRingHom M =
        ρ.rationalMatrix y := by
      apply Units.ext
      ext i j
      change rationalPointAlgebraHom k G.X y (M i j) = _
      rw [rationalPointAlgebraHom_apply_appTop, rationalMatrix_apply_apply]
      change (Scheme.ΓSpecIso (CommRingCat.of k)).hom
        (y.left.appTop ((𝟙 G.X ≫ ρ.hom.hom).left.appTop (entrySection n _ i j))) =
          (Scheme.ΓSpecIso (CommRingCat.of k)).hom
            ((y ≫ ρ.hom.hom).left.appTop (entrySection n _ i j))
      rw [Category.id_comp, Over.comp_left, Scheme.Hom.comp_appTop]
      rfl
    change rationalPointAlgebraHom k G.X y (aeval (values M) p) = _
    rw [comp_aeval_apply]
    change aeval ((rationalPointAlgebraHom k G.X y).toRingHom ∘ values M) p = _
    rw [← values_map (rationalPointAlgebraHom k G.X y).toRingHom, hm, aeval_def,
      Algebra.algebraMap_self, eval₂_id]
  let globalSection : Γ(G.X.left, ⊤) := s
  have hs (i : I) : (x i).left.appTop globalSection = 0 := by
    apply (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.injective
    change (Scheme.ΓSpecIso (CommRingCat.of k)).hom ((x i).left.appTop s) = _
    rw [← rationalPointAlgebraHom_apply_appTop, h_eval, hp, map_zero]
  have hzero : s = 0 := by
    apply (AlgebraicGeometry.basicOpen_eq_bot_iff globalSection).mp
    by_contra hne
    obtain ⟨z, hzO, hz⟩ := hd.inter_open_nonempty (G.X.left.basicOpen globalSection : Set G.X.left)
      (G.X.left.basicOpen globalSection).isOpen
      ((TopologicalSpace.Opens.ne_bot_iff_nonempty _).mp hne)
    obtain ⟨i, a, rfl⟩ := Set.mem_iUnion.mp hz
    have ha : a ∈ (x i).left ⁻¹ᵁ G.X.left.basicOpen globalSection := hzO
    rw [Scheme.preimage_basicOpen_top, hs i, Scheme.basicOpen_zero] at ha
    simp at ha
  rw [← h_eval, hzero, map_zero]

variable {L : Type u} [Field L] [Algebra k L]

theorem rationalMatrix_baseChange_extend (ρ : MatrixRepresentation G n) (x : rationalPoints G) :
    (ρ.baseChange (baseMap k L)).rationalMatrix (rationalExtend k L G x) =
      Matrix.GeneralLinearGroup.map (algebraMap k L) (ρ.rationalMatrix x) := by
  rw [RationalCharacterSeparation.rationalExtend_eq_geometricRationalPointHom,
    geometricRationalPointHom_apply]
  exact ρ.rationalMatrix_baseChange_geometricRationalPoint x

private theorem rationalMatrix_baseChange_coeff (ρ : MatrixRepresentation G n)
    (x : rationalPoints (baseChanged k L G)) :
    (ρ.baseChange (baseMap k L)).rationalMatrix x =
      ρ.affineMatrix (CommAlgCat.of k L) (baseChangeCoeffEquiv k L G x) := by
  rw [rationalMatrix_eq_coeffMatrix, baseChangeCoeffEquiv_eq_affineBaseChange,
    rationalCoeffEquiv_eq]
  let e := affinePointsBaseChangeMulEquiv k L L G
  let y : ((baseChange (Spec.algebraMap k L)).obj G).affinePoints (CommAlgCat.of L L) :=
    rationalPointEquiv L (baseChanged k L G).X x
  have h := ρ.baseChange_affineMatrix_affinePointsBaseChangeMulEquiv (e.symm y)
  change (ρ.baseChange (Spec.algebraMap k L)).affineMatrix _ (e (e.symm y)) = _ at h
  rw [e.apply_symm_apply] at h
  exact h

/-- In the base-changed representation the point action of a field automorphism
acts on matrix entries through the same field automorphism. -/
theorem rationalMatrix_baseChange_conjugate (ρ : MatrixRepresentation G n)
    (σ : L ≃ₐ[k] L) (x : rationalPoints (baseChanged k L G)) :
    (ρ.baseChange (baseMap k L)).rationalMatrix (rationalConjugate k L G σ x) =
      Matrix.GeneralLinearGroup.map σ.toRingHom ((ρ.baseChange (baseMap k L)).rationalMatrix x) := by
  rw [rationalMatrix_baseChange_coeff, rationalMatrix_baseChange_coeff,
    baseChangeCoeffEquiv_rationalConjugate]
  exact ρ.affineMatrix_naturality (CommAlgCat.ofHom σ.toAlgHom) (baseChangeCoeffEquiv k L G x)

/-- Extend a rational point and evaluate its matrix after applying the given homomorphism. -/
def extendedRationalMatrix {H : GroupScheme (Spec (CommRingCat.of k))}
    (ρ : MatrixRepresentation (baseChanged k L G) n)
    (f : baseChanged k L H ⟶ baseChanged k L G) : rationalPoints H →* GL n L :=
  (ρ.rationalMatrix.comp (rationalPoints.map f)).comp (rationalExtend k L H)

/-- All automorphisms of the coefficient field over the base field fix this matrix. -/
def MatrixFixedByBaseAutomorphisms (m : GL n L) : Prop :=
  ∀ σ : L ≃ₐ[k] L, Matrix.GeneralLinearGroup.map σ.toRingHom m = m

/-- A normalizing matrix carries the images of extended points into Galois-fixed matrices. -/
def HasConjugatorToGaloisFixedPoints {H : GroupScheme (Spec (CommRingCat.of k))}
    (ρ : MatrixRepresentation (baseChanged k L G) n)
    (f : baseChanged k L H ⟶ baseChanged k L G) : Prop :=
  ∃ c ∈ Subgroup.normalizer (ρ.rationalMatrix.range : Set (GL n L)),
    ∀ x : rationalPoints H, MatrixFixedByBaseAutomorphisms (k := k)
      (c * extendedRationalMatrix (G := G) (H := H) ρ f x * c⁻¹)

end Coordinates

end Langlands.GroupScheme.RealCompactForm
