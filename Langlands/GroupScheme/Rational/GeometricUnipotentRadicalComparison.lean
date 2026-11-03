import Langlands.GroupScheme.Rational.LeviSubgroup
import Langlands.GroupScheme.Rational.SemistandardIntersection
import Langlands.GroupScheme.Reductive.UnipotentFieldExtensionStatement
import Langlands.GroupScheme.GeometricConnectedness
import Langlands.GroupScheme.SubgroupFunctor.FpqcDescent
import Langlands.GroupScheme.BaseChangeReflection

/-! # Comparing two geometric unipotent radical predicates -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {U P : GroupScheme (Spec (CommRingCat.of k))} {r : U ⟶ P}

/-- The two-radical predicate supplies the semistandard geometric predicate. -/
theorem LeviSubgroup.IsGeometricUnipotentRadical.isGeometricUnipotentRadical
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r) :
    Langlands.GroupScheme.IsGeometricUnipotentRadical r := by
  exact ⟨hr.1.isClosedSubgroup, hr.1.smooth, hr.1.connectedSpace,
    hr.1.isUnipotent, hr.1.isNormal, hr.2.connectedSpace, hr.2.isUnipotent,
    hr.2.isNormal, hr.2.greatest⟩

/-- Geometric greatestness descends to the ground field, provided unipotence
is preserved by field extension. The ambient group is affine. -/
theorem IsGeometricUnipotentRadical.isUnipotentRadical_of_unipotentFieldExtension
    (hU : UnipotentFieldExtensionStatement.{u}) [IsAffineHom P.X.hom]
    (hr : IsGeometricUnipotentRadical r) : IsUnipotentRadical r := by
  refine ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, ?_⟩
  intro H j hj hs hc hu hn
  let : IsClosedImmersion j.hom.hom.left := hj
  let : IsAffineHom H.X.hom := by
    rw [← Over.w j.hom.hom]
    infer_instance
  let : Smooth H.X.hom := hs
  let : ConnectedSpace H.X.left := hc
  let b := toAlgebraicClosure k
  obtain ⟨hSurj, hFlat, hQC⟩ := fieldExtension_fpqc k (AlgebraicClosure k)
  let : Surjective b := hSurj
  let : Flat b := hFlat
  let : QuasiCompact b := hQC
  let : IsClosedImmersion r.hom.hom.left := hr.1
  let : Mono r.hom.hom := Over.mono_of_mono_left _
  apply SubgroupFunctor.le_range_of_baseChange_le b r
  rw [← SubgroupFunctor.range_baseChangeHom, ← SubgroupFunctor.range_baseChangeHom]
  apply hr.2.2.2.2.2.2.2.2
  · exact hj.baseChange b
  · change Smooth (pullback.snd H.X.hom b)
    infer_instance
  · exact H.connectedSpace_baseChange_of_smooth_affine b
  · exact hU k (AlgebraicClosure k) H inferInstance inferInstance hu
  · rw [SubgroupFunctor.range_baseChangeHom]
    exact hn.baseChange b

/-- In an affine ambient group, preservation of unipotence upgrades the
semistandard geometric predicate to the two-radical Levi predicate. -/
theorem IsGeometricUnipotentRadical.leviSubgroup_of_unipotentFieldExtension
    (hU : UnipotentFieldExtensionStatement.{u}) [IsAffineHom P.X.hom]
    (hr : IsGeometricUnipotentRadical r) :
    LeviSubgroup.IsGeometricUnipotentRadical r := by
  refine ⟨hr.isUnipotentRadical_of_unipotentFieldExtension hU, ?_⟩
  have : Smooth U.X.hom := hr.2.1
  refine ⟨hr.1.baseChange _, ?_, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1,
    hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2⟩
  change Smooth (pullback.snd U.X.hom (toAlgebraicClosure k))
  infer_instance

/-- The two geometric radical interfaces agree in an affine ambient group,
conditional on preservation of unipotence by field extension. -/
theorem leviSubgroup_isGeometricUnipotentRadical_iff
    (hU : UnipotentFieldExtensionStatement.{u}) [IsAffineHom P.X.hom] :
    LeviSubgroup.IsGeometricUnipotentRadical r ↔ IsGeometricUnipotentRadical r :=
  ⟨fun hr => hr.isGeometricUnipotentRadical,
    fun hr => hr.leviSubgroup_of_unipotentFieldExtension hU⟩

/-- A canonical equivalence of the two supplied radical witness types in an
 affine ambient group, using preservation of unipotence under field extension. -/
def LeviSubgroup.geometricUnipotentRadicalEquiv
    (hU : UnipotentFieldExtensionStatement.{u}) [IsAffineHom P.X.hom] :
    LeviSubgroup.IsGeometricUnipotentRadical r ≃
      Langlands.GroupScheme.IsGeometricUnipotentRadical r :=
  Equiv.ofIff (leviSubgroup_isGeometricUnipotentRadical_iff hU)

end Langlands.GroupScheme
