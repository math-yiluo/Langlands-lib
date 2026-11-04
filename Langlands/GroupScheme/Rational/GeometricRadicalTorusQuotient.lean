import Langlands.GroupScheme.Rational.LeviSubgroup
import Langlands.GroupScheme.Absolute.SolvableTorusQuotientStatement
import Langlands.GroupScheme.Absolute.SolvableFieldExtensionProof
import Langlands.GroupScheme.FppfQuotientComparison
import Langlands.GroupScheme.SmoothNormalQuotient
import Langlands.GroupScheme.GeometricConnectedness
import Langlands.GroupScheme.Torus.UnipotentHomNonsplit
import Langlands.GroupScheme.Torus.SplitReductiveProof

/-! # Torus quotients by supplied geometric unipotent radicals -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {G U V D Q : GroupScheme (Spec (CommRingCat.of k))}
    {i : U ⟶ G}

/-- A smooth connected normal unipotent kernel of a torus quotient is the
whole supplied unipotent radical, as a subgroup on every test scheme. -/
theorem IsUnipotentRadical.range_eq_of_torus_quotient
    [IsAffineHom G.X.hom] (hi : IsUnipotentRadical i)
    (j : V ⟶ G) (hj : IsClosedSubgroup j)
    (hs : Smooth V.X.hom) (hc : ConnectedSpace V.X.left)
    (hu : IsUnipotent V) (hn : (SubgroupFunctor.range j).IsNormal)
    (q : G ⟶ D)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range j) q)
    (hD : IsTorus D) :
    SubgroupFunctor.range i = SubgroupFunctor.range j := by
  have : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  have : IsAffineHom U.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  have hzero : i ≫ q = 0 :=
    hi.isUnipotent.hom_eq_zero_of_isTorus hD (i ≫ q)
  refine le_antisymm ?_ (hi.greatest V j hj hs hc hu hn)
  intro T x hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  rw [← hq.2.2.2, mem_range_kernelι_iff, Category.assoc,
    ← Grp.comp_hom_hom, hzero]
  exact MonObj.comp_one y

/-- Compare the base change of any actual quasi-compact radical quotient with
the absolute torus quotient. Only the latter existence theorem is retained. -/
theorem LeviSubgroup.IsGeometricUnipotentRadical.isSplitTorus_baseChange_quotient
    (hquot : SolvableTorusQuotientStatement.{u})
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (hi : LeviSubgroup.IsGeometricUnipotentRadical i)
    (hG : IsSolvableGroupScheme G)
    (q : G ⟶ Q) [QuasiCompact q.hom.hom.left]
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q) :
    IsSplitTorus ((GroupScheme.baseChange (toAlgebraicClosure k)).obj Q) := by
  let b := toAlgebraicClosure k
  let bc := GroupScheme.baseChange b
  have : Smooth (bc.obj G).X.hom :=
    inferInstanceAs (Smooth (pullback.snd G.X.hom b))
  have : IsAffineHom (bc.obj G).X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd G.X.hom b))
  have : ConnectedSpace (bc.obj G).X.left :=
    G.connectedSpace_baseChange_of_smooth_affine b
  have hGc : IsSolvableGroupScheme (bc.obj G) :=
    solvableFieldExtensionStatement k (AlgebraicClosure k) b G inferInstance hG
  obtain ⟨V, D, j, r, hj, hs, hc, hu, hn, hr, hD⟩ :=
    hquot (AlgebraicClosure k) (bc.obj G) hGc
  have heq : SubgroupFunctor.range (bc.map i) = SubgroupFunctor.range j :=
    hi.2.range_eq_of_torus_quotient j hj hs hc hu hn r hr hD.isTorus
  have hqb : RelativeRoot.IsFppfQuotient
      (SubgroupFunctor.range j) (bc.map q) := by
    have h := hq.baseChange b
    rw [← SubgroupFunctor.range_baseChangeHom, heq] at h
    exact h
  have : QuasiCompact (bc.map q).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @QuasiCompact) b q.hom.hom inferInstance
  have : IsAffine (bc.obj G).X.left := isAffine_of_isAffineHom (bc.obj G).X.hom
  have : IsAffineHom D.X.hom := hD.isAffineHom
  have : IsAffine D.X.left := isAffine_of_isAffineHom D.X.hom
  have : QuasiCompact r.hom.hom.left := inferInstance
  exact IsSplitTorus.of_iso (FppfQuotientComparison.iso hqb hr) hD

/-- An actual quotient by a supplied radical, with its geometric split-torus
property attached to that same target. -/
structure GeometricRadicalTorusQuotient (i : U ⟶ G) extends SmoothNormalQuotient i where
  isSplitTorus_baseChange :
    IsSplitTorus ((GroupScheme.baseChange (toAlgebraicClosure k)).obj quotient)

/-- The stored target is a torus over the original field. -/
theorem GeometricRadicalTorusQuotient.isTorus
    (D : GeometricRadicalTorusQuotient i) : IsTorus D.quotient :=
  ⟨AlgebraicClosure k, inferInstance, inferInstance, D.isSplitTorus_baseChange⟩

/-- Choose an actual smooth quotient by the given geometric radical, then
identify its geometric target with the absolute split-torus quotient. -/
def LeviSubgroup.IsGeometricUnipotentRadical.torusQuotient
    (hquot : SolvableTorusQuotientStatement.{u})
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (hi : LeviSubgroup.IsGeometricUnipotentRadical i)
    (hG : IsSolvableGroupScheme G) : GeometricRadicalTorusQuotient i := by
  let D := SmoothNormalQuotient.ofClosedNormal i
    hi.1.isClosedSubgroup hi.1.smooth hi.1.isNormal
  have : QuasiCompact D.projection.hom.hom.left := D.quasiCompact_projection
  exact {
    toSmoothNormalQuotient := D
    isSplitTorus_baseChange :=
      hi.isSplitTorus_baseChange_quotient hquot hG D.projection D.isFppfQuotient
  }

end Langlands.GroupScheme
