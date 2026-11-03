import Langlands.GroupScheme.CentralIsogeny.Basic
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.Reductive.RootDatumHomLattices
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono

/-! # Detecting an isomorphism on a self-centralizing restriction -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section GeneralBase

variable {S : Scheme.{u}} {G H : GroupScheme S} {T T' : CommGroupScheme S}
  {i : T.toGrp ⟶ G} {i' : T'.toGrp ⟶ H} {φ : G ⟶ H} {t : T ⟶ T'}

/-- If the full kernel is contained in a subgroup on which the homomorphism is monic, the
ambient homomorphism is monic on all test schemes. -/
theorem mono_of_kernel_range_le_of_restriction
    [Mono (CommGroupScheme.groupHom t).hom.hom] [Mono i'.hom.hom]
    (ht : i ≫ φ = CommGroupScheme.groupHom t ≫ i')
    (hker : SubgroupFunctor.range (kernelι φ) ≤ SubgroupFunctor.range i) :
    Mono φ.hom.hom := by
  constructor
  intro U a b hab
  apply div_eq_one.mp
  have hk : (a / b) ≫ φ.hom.hom = 1 := by
    rw [GrpObj.div_comp, hab, div_self']
  obtain ⟨x, hx⟩ := SubgroupFunctor.mem_range.mp
    (hker U ((mem_range_kernelι_iff φ (a / b)).mpr hk))
  have hxt : x ≫ (CommGroupScheme.groupHom t).hom.hom = 1 := by
    apply (cancel_mono i'.hom.hom).mp
    rw [MonObj.one_comp]
    calc
      (x ≫ (CommGroupScheme.groupHom t).hom.hom) ≫ i'.hom.hom =
          x ≫ (i ≫ φ).hom.hom := by rw [ht]; rfl
      _ = (x ≫ i.hom.hom) ≫ φ.hom.hom := by
        rw [Grp.comp_hom_hom, Category.assoc]
      _ = 1 := by rw [hx, hk]
  have hx1 : x = 1 :=
    (cancel_mono (CommGroupScheme.groupHom t).hom.hom).mp
      (hxt.trans (MonObj.one_comp _).symm)
  rw [← hx, hx1, MonObj.one_comp]

/-- An isogeny is an isomorphism if its full kernel lies in a subgroup with monic restriction. -/
theorem IsIsogeny.isIso_of_kernel_range_le_of_restriction
    (hφ : IsIsogeny φ) [Mono (CommGroupScheme.groupHom t).hom.hom] [Mono i'.hom.hom]
    (ht : i ≫ φ = CommGroupScheme.groupHom t ≫ i')
    (hker : SubgroupFunctor.range (kernelι φ) ≤ SubgroupFunctor.range i) :
    IsIso φ := by
  have : Mono φ.hom.hom := mono_of_kernel_range_le_of_restriction ht hker
  have : Mono φ.hom.hom.left := Over.mono_left_of_mono _
  have : IsFinite φ.hom.hom.left := hφ.1
  have : Flat φ.hom.hom.left := hφ.2.1
  have : Surjective φ.hom.hom.left := hφ.2.2
  have : IsIso φ.hom.hom.left := Flat.isIso_of_surjective_of_mono _
  have : IsIso ((Over.forget S).map φ.hom.hom) := by
    change IsIso φ.hom.hom.left
    infer_instance
  have : IsIso φ.hom.hom := isIso_of_reflects_iso φ.hom.hom (Over.forget S)
  let e : G ≅ H := Grp.mkIso' (asIso φ.hom.hom)
  change IsIso e.hom
  infer_instance

/-- A central isogeny whose restriction to a self-centralizing commutative subgroup is an
isomorphism is an isomorphism. -/
theorem IsCentralIsogeny.isIso_of_selfCentralizing_restriction
    (hφ : IsCentralIsogeny φ) [IsIso t] [Mono i'.hom.hom]
    (ht : i ≫ φ = CommGroupScheme.groupHom t ≫ i')
    (hself : torusCentralizer i = SubgroupFunctor.range i) : IsIso φ := by
  have : IsIso (CommGroupScheme.groupHom t) := by
    refine ⟨⟨CommGroupScheme.groupHom (inv t), ?_, ?_⟩⟩
    · exact congrArg CommGroupScheme.groupHom (IsIso.hom_inv_id t)
    · exact congrArg CommGroupScheme.groupHom (IsIso.inv_hom_id t)
  apply hφ.isIsogeny.isIso_of_kernel_range_le_of_restriction ht
  rw [← hself]
  exact hφ.kernel_range_le_center.trans (center_le_torusCentralizer i)

/-- The actual ambient isomorphism constructed from an invertible self-centralizing
restriction of a central isogeny. -/
def IsCentralIsogeny.isoOfSelfCentralizingRestriction
    (hφ : IsCentralIsogeny φ) [IsIso t] [Mono i'.hom.hom]
    (ht : i ≫ φ = CommGroupScheme.groupHom t ≫ i')
    (hself : torusCentralizer i = SubgroupFunctor.range i) : G ≅ H :=
  haveI := hφ.isIso_of_selfCentralizing_restriction ht hself
  asIso φ

@[simp]
theorem IsCentralIsogeny.isoOfSelfCentralizingRestriction_hom
    (hφ : IsCentralIsogeny φ) [IsIso t] [Mono i'.hom.hom]
    (ht : i ≫ φ = CommGroupScheme.groupHom t ≫ i')
    (hself : torusCentralizer i = SubgroupFunctor.range i) :
    (hφ.isoOfSelfCentralizingRestriction ht hself).hom = φ :=
  rfl

end GeneralBase

variable {k : Type u} [Field k] {G H : GroupScheme (Spec (CommRingCat.of k))}
  {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
  {i : T.toGrp ⟶ G} {i' : T'.toGrp ⟶ H} {φ : G ⟶ H}

/-- For a maximal source torus which is self-centralizing, a central isogeny is invertible
exactly when its restriction to the supplied target torus is invertible. -/
theorem IsCentralIsogeny.isIso_iff_torusRestriction_of_selfCentralizing
    (hφ : IsCentralIsogeny φ) (hi : IsMaximalTorus i)
    (hT' : IsTorus T'.toGrp) (hi' : IsClosedSubgroup i') (t : T ⟶ T')
    (ht : i ≫ φ = CommGroupScheme.groupHom t ≫ i')
    (hself : torusCentralizer i = SubgroupFunctor.range i) : IsIso φ ↔ IsIso t := by
  constructor
  · intro h
    exact hi.isIso_factor_of_isIso hT' hi' φ t ht
  · intro h
    have : IsClosedImmersion i'.hom.hom.left := hi'
    have : Mono i'.hom.hom := Over.mono_of_mono_left _
    exact hφ.isIso_of_selfCentralizing_restriction ht hself

end Langlands.GroupScheme
