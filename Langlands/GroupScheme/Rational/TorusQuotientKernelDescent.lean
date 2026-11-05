import Langlands.GroupScheme.Rational.TorusQuotientRadicalDescent
import Langlands.GroupScheme.KernelRepresentativeTransport
import Langlands.GroupScheme.Descent.AffineFppfQuotient

/-! # Full kernels of descended torus quotient maps -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace DescendedQuotientKernel

section Base

variable {B S : Scheme.{u}} (b : S ⟶ B)
    {G R : GroupScheme B} {U Q : GroupScheme S}
    (r : G ⟶ R) (i : U ⟶ (GroupScheme.baseChange b).obj G)
    (q : (GroupScheme.baseChange b).obj G ⟶ Q)
    (e : (GroupScheme.baseChange b).obj R ≅ Q)
    (he : (GroupScheme.baseChange b).map r ≫ e.hom = q)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q)

include he hq

/-- A target recovery isomorphism identifies the full kernel on every test. -/
theorem kernel_range :
    SubgroupFunctor.range (kernelι ((GroupScheme.baseChange b).map r)) =
      SubgroupFunctor.range i := by
  calc
    SubgroupFunctor.range (kernelι ((GroupScheme.baseChange b).map r)) =
        SubgroupFunctor.range (kernelι q) := by
      apply SubgroupFunctor.ext
      intro T
      apply Subgroup.ext
      intro x
      rw [mem_range_kernelι_iff, mem_range_kernelι_iff]
      constructor
      · intro hx
        rw [← he, Grp.comp_hom_hom, ← Category.assoc, hx, MonObj.one_comp]
      · intro hx
        apply (cancel_mono e.hom.hom.hom).mp
        rw [Category.assoc, ← Grp.comp_hom_hom, he, hx, MonObj.one_comp]
    _ = _ := hq.2.2.2

/-- Recover a supplied monomorphic full kernel after the map has descended. -/
def sourceIso [Mono i.hom.hom] :
    (GroupScheme.baseChange b).obj (kernel r) ≅ U :=
  kernelBaseChangeIso b r ≪≫
    KernelRepresentative.iso ((GroupScheme.baseChange b).map r) i
      (kernel_range b r i q e he hq)

/-- Recovery preserves the actual inclusions into the extended ambient group. -/
theorem sourceIso_hom_comp [Mono i.hom.hom] :
    (sourceIso b r i q e he hq).hom ≫ i =
      (GroupScheme.baseChange b).map (kernelι r) := by
  change (kernelBaseChangeIso b r).hom ≫
    (KernelRepresentative.iso ((GroupScheme.baseChange b).map r) i
      (kernel_range b r i q e he hq)).hom ≫ i = _
  rw [KernelRepresentative.iso_hom_comp, kernelBaseChangeIso_hom_ι]

/-- The supplied quotient has precisely the extended ground-field kernel. -/
theorem isFppfQuotient_baseChange [Mono i.hom.hom] :
    RelativeRoot.IsFppfQuotient
      (SubgroupFunctor.range ((GroupScheme.baseChange b).map (kernelι r))) q := by
  rw [← sourceIso_hom_comp b r i q e he hq, SubgroupFunctor.range_iso_comp]
  exact hq

end Base

end DescendedQuotientKernel

section Field

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
    {G R : GroupScheme (Spec (CommRingCat.of k))}
    {U Q : GroupScheme (Spec (CommRingCat.of K))}

/-- Actual full-kernel recovery and geometric radical descent for a descended
torus quotient map, along an arbitrary field extension. -/
structure TorusQuotientKernelDescent
    (r : G ⟶ R)
    (i : U ⟶ (GroupScheme.baseChange (algebraBaseMap k K)).obj G)
    (q : (GroupScheme.baseChange (algebraBaseMap k K)).obj G ⟶ Q) where
  sourceIso : (GroupScheme.baseChange (algebraBaseMap k K)).obj (kernel r) ≅ U
  inclusion_comp :
    (GroupScheme.baseChange (algebraBaseMap k K)).map (kernelι r) =
      sourceIso.hom ≫ i
  targetIso : (GroupScheme.baseChange (algebraBaseMap k K)).obj R ≅ Q
  projection_comp :
    (GroupScheme.baseChange (algebraBaseMap k K)).map r ≫ targetIso.hom = q
  isTorus : IsTorus R
  isFppfQuotient : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (kernelι r)) r
  isGeometricUnipotentRadical : LeviSubgroup.IsGeometricUnipotentRadical (kernelι r)

/-- Descend the full smooth connected unipotent kernel and quotient geometry
once the actual torus-valued homomorphism has descended. -/
def torusQuotientKernelDescent [IsAffineHom G.X.hom]
    (r : G ⟶ R)
    (i : U ⟶ (GroupScheme.baseChange (algebraBaseMap k K)).obj G)
    (hi : IsClosedSubgroup i) (hs : Smooth U.X.hom)
    (hc : ConnectedSpace U.X.left) (hu : IsUnipotent U)
    (q : (GroupScheme.baseChange (algebraBaseMap k K)).obj G ⟶ Q)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q)
    (hQ : IsTorus Q)
    (e : (GroupScheme.baseChange (algebraBaseMap k K)).obj R ≅ Q)
    (he : (GroupScheme.baseChange (algebraBaseMap k K)).map r ≫ e.hom = q) :
    TorusQuotientKernelDescent r i q := by
  let b := algebraBaseMap k K
  let bc := GroupScheme.baseChange b
  have : IsAffineHom (bc.obj G).X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd G.X.hom b))
  have : IsClosedImmersion i.hom.hom.left := hi
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have hR : IsTorus R := IsTorus.of_baseChange (IsTorus.of_iso e hQ)
  have : IsAffine R.X.left := SplittingAssembly.isAffine_of_isTorus R hR
  have : IsAffineHom R.X.hom := inferInstance
  have hj : IsClosedSubgroup (kernelι r) :=
    inferInstanceAs (IsClosedImmersion (kernelι r).hom.hom.left)
  have : Surjective b := (fieldExtension_fpqc k K).1
  have : Flat b := (fieldExtension_fpqc k K).2.1
  have : QuasiCompact b := (fieldExtension_fpqc k K).2.2
  let a := DescendedQuotientKernel.sourceIso b r i q e he hq
  have ha : bc.map (kernelι r) = a.hom ≫ i :=
    (DescendedQuotientKernel.sourceIso_hom_comp b r i q e he hq).symm
  have hradK := IsUnipotentRadical.of_torus_quotient hi hs hc hu q hq hQ
  have hrad : IsUnipotentRadical (kernelι r) := by
    apply IsUnipotentRadical.of_baseChange (K := K) (hclosed := hj)
    change IsUnipotentRadical (bc.map (kernelι r))
    rw [ha]
    exact hradK.precomp_iso a
  have hr : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (kernelι r)) r :=
    RelativeRoot.IsFppfQuotient.of_baseChange_iso b (kernelι r) r q e he
      (DescendedQuotientKernel.isFppfQuotient_baseChange b r i q e he hq)
  exact {
    sourceIso := a
    inclusion_comp := ha
    targetIso := e
    projection_comp := he
    isTorus := hR
    isFppfQuotient := hr
    isGeometricUnipotentRadical :=
      LeviSubgroup.IsGeometricUnipotentRadical.of_torus_quotient
        hj hrad.smooth hrad.connectedSpace hrad.isUnipotent r hr hR
  }

end Field

end Langlands.GroupScheme
