import Langlands.GroupScheme.ChevalleyIntegral.RootClosure
import Langlands.GroupScheme.SplitExistence.RootSubgroupRepresentation

/-! # Closed integral additive root homomorphisms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Matrix
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitExistence.ChevalleyData

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y]
  {P : RootDatum J X Y} {b : P.Base} (D : ChevalleyData P b)
  (R : CommRingCat.{u}) (j : J)

/-- The natural root representation on affine algebras. -/
def rootTransformation : VectorGroup.functor R 1 ⟶ GeneralLinear.functor (Fin D.n) R where
  app A := GrpCat.ofHom ((D.rootHom (K := A) j).comp
    (AddMonoidHom.toMultiplicative (Pi.evalAddMonoidHom (fun _ : Fin 1 => A) 0)))
  naturality A B f := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    exact (D.x_map f.hom.toRingHom j (x.toAdd 0)).symm

/-- The integral root map is induced by the natural transformation of represented functors. -/
theorem rootToGLOver_eq_groupSchemeMap :
    D.rootToGLOver R j = Corepresented.groupSchemeMap (VectorGroup.corepresentableBy R 1)
      (GeneralLinear.corepresentableBy (Fin D.n) R) (D.rootTransformation R j) := by
  refine hom_ext_points fun T x => (GeneralLinear.pointsEquiv (Fin D.n) R T).injective ?_
  rw [D.pointsEquiv_rootToGLOver]
  exact (Corepresented.groupSchemeMap_points (VectorGroup.corepresentableBy R 1)
    (GeneralLinear.corepresentableBy (Fin D.n) R) (D.rootTransformation R j) x).symm

/-- The algebra map classifying the root matrix at the universal scalar. -/
def rootClassify : GeneralLinear.CoordinateRing (Fin D.n) R →ₐ[R] MvPolynomial (Fin 1) R :=
  GeneralLinear.classify (D.x j (MvPolynomial.X 0))

/-- The underlying root morphism is the spectrum of the explicit coordinate map. -/
theorem rootToGLOver_hom_left :
    (D.rootToGLOver R j).hom.hom.left =
      Spec.map (CommRingCat.ofHom (D.rootClassify R j).toRingHom) := by
  rw [rootToGLOver_eq_groupSchemeMap, Corepresented.groupSchemeMap_hom]
  rfl

/-- A first divided-power entry gives a scalar multiple of the universal coordinate. -/
theorem rootClassify_entry {c d : Fin D.n} (h : D.e j 1 c d ≠ 0) :
    D.rootClassify R j
      (GeneralLinear.quotient (Fin D.n) R
        (MvPolynomial.X (GeneralLinear.Coordinate.entry c d))) =
      MvPolynomial.X 0 * (D.e j 1 c d : MvPolynomial (Fin 1) R) := by
  rw [rootClassify, GeneralLinear.classify_entry]
  exact D.x_apply_of_e_one_ne_zero j (MvPolynomial.X 0) h

/-- Primitivity of the first root matrix makes the coordinate map surjective. -/
theorem rootClassify_surjective : Function.Surjective (D.rootClassify R j) := by
  let φ := D.rootClassify R j
  have hentry (cd : Fin D.n × Fin D.n) :
      MvPolynomial.X 0 * (D.e j 1 cd.1 cd.2 : MvPolynomial (Fin 1) R) ∈ φ.range := by
    by_cases h : D.e j 1 cd.1 cd.2 = 0
    · simp [h]
    · exact ⟨_, D.rootClassify_entry R j h⟩
  have hspan : ∀ z ∈ Ideal.span (Set.range fun cd : Fin D.n × Fin D.n =>
      D.e j 1 cd.1 cd.2), MvPolynomial.X 0 * (z : MvPolynomial (Fin 1) R) ∈ φ.range := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨cd, rfl⟩ := hz
      exact hentry cd
    | zero => simp
    | add a c _ _ ha hc =>
      simpa only [Int.cast_add, mul_add] using φ.range.add_mem ha hc
    | smul a c _ hc =>
      have ha : (a : MvPolynomial (Fin 1) R) ∈ φ.range := by
        simpa only [map_intCast] using φ.range.algebraMap_mem (a : R)
      simpa only [smul_eq_mul, Int.cast_mul, mul_left_comm] using φ.range.mul_mem ha hc
  have hX : MvPolynomial.X (0 : Fin 1) ∈ φ.range := by
    simpa only [Int.cast_one, mul_one] using hspan 1 (D.one_mem_span_e_one j)
  apply (AlgHom.range_eq_top φ).1
  apply Algebra.eq_top_iff.2
  intro f
  induction f using MvPolynomial.induction_on with
  | C r => exact φ.range.algebraMap_mem r
  | add f g hf hg => exact φ.range.add_mem hf hg
  | mul_X f i hf =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    exact φ.range.mul_mem hf hX

/-- Each additive root is a closed subgroup of the matrix group over every base ring. -/
theorem isClosedSubgroup_rootToGLOver : IsClosedSubgroup (D.rootToGLOver R j) := by
  change IsClosedImmersion (D.rootToGLOver R j).hom.hom.left
  rw [D.rootToGLOver_hom_left]
  exact IsClosedImmersion.spec_of_surjective _ (D.rootClassify_surjective R j)

end Langlands.GroupScheme.SplitExistence.ChevalleyData

namespace Langlands.GroupScheme.ChevalleyIntegral

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y]
  {P : RootDatum J X Y} {b : P.Base}
  (D : SplitExistence.ChevalleyData P b)
  (R K : Type u) [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] (C : D.ChevGroup K) (j : J)

/-- Each root homomorphism into the same integral model is a closed immersion. -/
theorem root_closed : IsClosedSubgroup (root D R K C j) := by
  apply IsClosedSubgroup.of_comp (modelInclusion_closed D R K C)
  rw [root_comp]
  exact D.isClosedSubgroup_rootToGLOver (CommRingCat.of R) j

end Langlands.GroupScheme.ChevalleyIntegral
