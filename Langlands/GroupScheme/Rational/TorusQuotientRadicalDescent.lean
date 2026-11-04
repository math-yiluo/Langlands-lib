import Langlands.GroupScheme.Rational.UnipotentRadicalProperties
import Langlands.GroupScheme.Rational.LeviSubgroup
import Langlands.GroupScheme.SmoothNormalQuotient
import Langlands.GroupScheme.FppfQuotientComparison
import Langlands.GroupScheme.HopfPrimitiveQuotient
import Langlands.GroupScheme.Torus.UnipotentHomNonsplit
import Langlands.GroupScheme.Torus.BaseChange
import Langlands.GroupScheme.Torus.MaximalTransport
import Langlands.GroupScheme.Torus.SplittingAssembly

/-! # Geometric radicals and actual finite Galois torus-quotient descent -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Recognition

variable {k : Type u} [Field k]
    {G U D : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] {i : U ⟶ G}

/-- A closed smooth connected unipotent full kernel of a torus quotient is
the represented unipotent radical over the ground field. -/
theorem IsUnipotentRadical.of_torus_quotient
    (hi : IsClosedSubgroup i) (hs : Smooth U.X.hom)
    (hc : ConnectedSpace U.X.left) (hu : IsUnipotent U)
    (q : G ⟶ D)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q)
    (hD : IsTorus D) : IsUnipotentRadical i := by
  refine ⟨hi, hs, hc, hu, ?_, ?_⟩
  · rw [← hq.2.2.2]
    exact HopfPrimitive.isNormal_range_kernelι q
  · intro H j hj _ _ hH _
    have : IsClosedImmersion j.hom.hom.left := hj
    have : IsAffineHom H.X.hom := by
      rw [← Over.w j.hom.hom]
      infer_instance
    have hz : j ≫ q = 0 := hH.hom_eq_zero_of_isTorus hD (j ≫ q)
    intro T x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    rw [← hq.2.2.2, mem_range_kernelι_iff, Category.assoc,
      ← Grp.comp_hom_hom, hz]
    exact MonObj.comp_one y

/-- The same kernel is a geometric radical, without a separate geometric
greatestness assumption. -/
theorem LeviSubgroup.IsGeometricUnipotentRadical.of_torus_quotient
    (hi : IsClosedSubgroup i) (hs : Smooth U.X.hom)
    (hc : ConnectedSpace U.X.left) (hu : IsUnipotent U)
    (q : G ⟶ D)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q)
    (hD : IsTorus D) : LeviSubgroup.IsGeometricUnipotentRadical i := by
  have hrad := IsUnipotentRadical.of_torus_quotient hi hs hc hu q hq hD
  refine ⟨hrad, ?_⟩
  let b := toAlgebraicClosure k
  let bc := GroupScheme.baseChange b
  have : IsClosedImmersion i.hom.hom.left := hi
  have : IsAffineHom U.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  have : Smooth U.X.hom := hs
  have : ConnectedSpace U.X.left := hc
  have : IsAffineHom (bc.obj G).X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd G.X.hom b))
  have hqb : RelativeRoot.IsFppfQuotient
      (SubgroupFunctor.range (bc.map i)) (bc.map q) := by
    rw [SubgroupFunctor.range_baseChangeHom]
    exact hq.baseChange b
  exact IsUnipotentRadical.of_torus_quotient (hi.baseChange b)
    (inferInstanceAs (Smooth (pullback.snd U.X.hom b)))
    (U.connectedSpace_baseChange_of_smooth_affine b)
    (hu.baseChange (K := AlgebraicClosure k)) (bc.map q) hqb hD.baseChange

end Recognition

section FiniteGalois

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L] [IsGalois k L]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {U D : GroupScheme (Spec (CommRingCat.of L))}

/-- Descent data retain an actual ground-field geometric radical and smooth
torus quotient, and recover both supplied objects over the extension. -/
structure FiniteGaloisTorusQuotientDescent
    (i : U ⟶ (GroupScheme.baseChange (algebraBaseMap k L)).obj G)
    (q : (GroupScheme.baseChange (algebraBaseMap k L)).obj G ⟶ D) where
  radical : GroupScheme (Spec (CommRingCat.of k))
  inclusion : radical ⟶ G
  sourceIso : (GroupScheme.baseChange (algebraBaseMap k L)).obj radical ≅ U
  inclusion_comp :
    (GroupScheme.baseChange (algebraBaseMap k L)).map inclusion = sourceIso.hom ≫ i
  isGeometricUnipotentRadical : LeviSubgroup.IsGeometricUnipotentRadical inclusion
  quotientData : SmoothNormalQuotient inclusion
  isTorus : IsTorus quotientData.quotient
  quotientIso :
    (GroupScheme.baseChange (algebraBaseMap k L)).obj quotientData.quotient ≅ D
  projection_comp :
    (GroupScheme.baseChange (algebraBaseMap k L)).map quotientData.projection ≫
      quotientIso.hom = q

/-- Descend a supplied actual finite Galois torus quotient with closed smooth
connected unipotent full kernel. -/
def finiteGaloisTorusQuotientDescent
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (i : U ⟶ (GroupScheme.baseChange (algebraBaseMap k L)).obj G)
    (hi : IsClosedSubgroup i) (hs : Smooth U.X.hom)
    (hc : ConnectedSpace U.X.left) (hu : IsUnipotent U)
    (q : (GroupScheme.baseChange (algebraBaseMap k L)).obj G ⟶ D)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q)
    (hD : IsTorus D) : FiniteGaloisTorusQuotientDescent i q := by
  let b := algebraBaseMap k L
  let bc := GroupScheme.baseChange b
  have : IsAffineHom (bc.obj G).X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd G.X.hom b))
  have hrad := IsUnipotentRadical.of_torus_quotient hi hs hc hu q hq hD
  obtain ⟨U₀, j, e, hj, he⟩ := hrad.finiteGaloisRadical
  let Q := SmoothNormalQuotient.ofClosedNormal j hj.isClosedSubgroup hj.smooth hj.isNormal
  have hr : SubgroupFunctor.range (bc.map j) = SubgroupFunctor.range i := by
    rw [he, SubgroupFunctor.range_iso_precomp]
  have hqb : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i)
      (bc.map Q.projection) := by
    have h := Q.isFppfQuotient.baseChange b
    rw [← SubgroupFunctor.range_baseChangeHom, hr] at h
    exact h
  have : QuasiCompact Q.projection.hom.hom.left := Q.quasiCompact_projection
  have : QuasiCompact (bc.map Q.projection).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @QuasiCompact) b Q.projection.hom.hom
      inferInstance
  have : IsAffine (bc.obj G).X.left := isAffine_of_isAffineHom (bc.obj G).X.hom
  have : IsAffine D.X.left := SplittingAssembly.isAffine_of_isTorus D hD
  have : QuasiCompact q.hom.hom.left := inferInstance
  let eQ := FppfQuotientComparison.iso hqb hq
  have hQ : IsTorus Q.quotient := IsTorus.of_baseChange (IsTorus.of_iso eQ hD)
  exact {
    radical := U₀
    inclusion := j
    sourceIso := e
    inclusion_comp := he
    isGeometricUnipotentRadical :=
      LeviSubgroup.IsGeometricUnipotentRadical.of_torus_quotient
        hj.isClosedSubgroup hj.smooth hj.connectedSpace hj.isUnipotent
        Q.projection Q.isFppfQuotient hQ
    quotientData := Q
    isTorus := hQ
    quotientIso := eQ
    projection_comp := FppfQuotientComparison.iso_fac hqb hq
  }

end FiniteGalois

end Langlands.GroupScheme
