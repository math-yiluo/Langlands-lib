import Langlands.GroupScheme.Rational.InfiniteFieldStronglyRegularPointStatement
import Langlands.GroupScheme.Absolute.StronglyRegularTorusPointStatement
import Langlands.GroupScheme.Absolute.AlgebraicClosureBaseChange
import Langlands.GroupScheme.Torus.ExistenceProof
import Langlands.GroupScheme.Torus.MaximalBaseChangeProof
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof
import Langlands.GroupScheme.Rational.TorusGeneratedEnvelopeDensity
import Langlands.GroupScheme.Rational.TorusGeneratedEnvelopeBaseChange
import Langlands.GroupScheme.Rational.ValuedRepresentationBaseChange
import Langlands.GroupScheme.SubgroupFunctor.FpqcDescent
import Langlands.GroupScheme.BaseChangeReflection
import Langlands.AlgebraicGeometry.PointTopology.GeometricRationalDensityExtension

/-! # Strongly regular rational points from the algebraically closed case -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The algebraically closed case of strongly regular torus points implies the existence of
strongly regular rational points over every infinite field. -/
def InfiniteFieldStronglyRegularPointReductionStatement : Prop :=
  AlgClosedStronglyRegularTorusPointStatement.{u} →
    InfiniteFieldStronglyRegularPointStatement.{u}

/-- Choose a maximal `K`-torus `T`, a `K`-point `p` of `T` whose scalar extension to `K̄` lies
in the strongly regular open set of `T_K̄`, and descend the factorization of every commuting point
along the faithfully flat extension `K̄ / K`. -/
theorem infiniteFieldStronglyRegularPointReduction :
    InfiniteFieldStronglyRegularPointReductionStatement.{u} := by
  intro hB K _ _ H hH
  have := hH.smooth
  have := hH.isAffineHom
  -- A maximal `K`-torus stays maximal over `K̄`, where it has a strongly regular open set.
  obtain ⟨T, j, hj⟩ := maximalTorusExistence K H
  obtain ⟨hbsurj, hbflat, hbqc⟩ := fieldExtension_fpqc K (AlgebraicClosure K)
  set b := toAlgebraicClosure K
  have hjΩ := (maximalTorusBaseChange K (AlgebraicClosure K) H T j hj.1 hj.2.1).mp hj
  obtain ⟨U, hU, hUne, hUreg⟩ :=
    hB (AlgebraicClosure K) _ hH.baseChange_toAlgebraicClosure _ _ hjΩ
  -- Scalar extensions of `K`-points of the torus are dense in `T_K̄`, so one lies in `U`.
  have hdense : HasDenseRationalPoints K T.X :=
    IsTorus.hasDenseRationalPoints_of_finiteGaloisSplitting torusFiniteGaloisSplitting hj.1
  have hgeo := hasDenseGeometricRationalPoints_of_hasDenseRationalPoints
    (K := AlgebraicClosure K) T.X hdense
  obtain ⟨y, hyU, hy⟩ := hgeo.inter_open_nonempty U hU hUne
  simp only [Set.mem_iUnion, Set.mem_range] at hy
  obtain ⟨p, a, rfl⟩ := hy
  set t := geometricRationalPoint (K := AlgebraicClosure K) T.X p
  have ht : Set.range t.left ⊆ U := by
    have : Subsingleton (Spec (CommRingCat.of (AlgebraicClosure K))) :=
      inferInstanceAs (Subsingleton (PrimeSpectrum (AlgebraicClosure K)))
    rintro _ ⟨a', rfl⟩
    rwa [Subsingleton.elim (α := Spec (CommRingCat.of (AlgebraicClosure K))) a' a]
  refine ⟨p ≫ j.hom.hom, T.toGrp, j, hj.1, hj.2.1, ?_⟩
  intro Z c hc
  -- Descend the factorization of `c` through `j` from `Z_K̄` to `Z`.
  have : Mono j.hom.hom.left := hj.2.1.mono
  have : Mono j.hom.hom := Over.mono_of_mono_left _
  let V : Over (Spec (CommRingCat.of (AlgebraicClosure K))) := (Over.pullback b).obj Z
  let q : (Over.map b).obj V ⟶ Z := EnvelopeBaseChange.pullbackFst b Z
  have : EffectiveEpi q.left := by
    change EffectiveEpi (pullback.fst Z.hom b)
    infer_instance
  apply SubgroupFunctor.mem_range_of_comp_mem_range j q
  let c' : V ⟶ ((GroupScheme.baseChange b).obj H).X := (Over.pullback b).map c
  have hc'q : baseChangePointsEquiv b H V c' = q ≫ c :=
    EnvelopeBaseChange.baseChangePointsEquiv_pullback_map b H c
  have hx : baseChangePointsEquiv b H V
      (toUnit V ≫ t ≫ ((GroupScheme.baseChange b).map j).hom.hom) =
        q ≫ toUnit Z ≫ p ≫ j.hom.hom := by
    rw [baseChangePointsEquiv_naturality]
    have htj : t ≫ ((GroupScheme.baseChange b).map j).hom.hom =
        geometricRationalPoint (K := AlgebraicClosure K) H.X (p ≫ j.hom.hom) :=
      geometricRationalPoint_natural (K := AlgebraicClosure K) j.hom.hom p
    have hg : baseChangePointsEquiv b H (𝟙_ (Over (Spec (CommRingCat.of (AlgebraicClosure K)))))
        (geometricRationalPoint (K := AlgebraicClosure K) H.X (p ≫ j.hom.hom)) =
          toUnit _ ≫ p ≫ j.hom.hom :=
      MatrixRepresentation.baseChangePointsEquiv_geometricRationalPoint (p ≫ j.hom.hom)
    rw [htj, hg]
    simp only [← Category.assoc]
    congr 2
    apply toUnit_unique
  -- `c_K̄` commutes with the strongly regular point `t ≫ j_K̄`.
  have hc' : c' * (toUnit V ≫ t ≫ ((GroupScheme.baseChange b).map j).hom.hom) =
      (toUnit V ≫ t ≫ ((GroupScheme.baseChange b).map j).hom.hom) * c' := by
    apply (baseChangePointsEquiv b H V).injective
    rw [map_mul, map_mul, hc'q, hx, ← MonObj.comp_mul, ← MonObj.comp_mul, hc]
  obtain ⟨s, hs⟩ := hUreg t ht c' hc'
  have hmem : c' ∈ (SubgroupFunctor.range ((GroupScheme.baseChange b).map j)).carrier V :=
    SubgroupFunctor.mem_range.mpr ⟨s, hs⟩
  rw [SubgroupFunctor.range_baseChangeHom, SubgroupFunctor.mem_baseChange, hc'q] at hmem
  exact hmem

end Langlands.GroupScheme
