import Langlands.GroupScheme.Rational.SemigroupSmoothQuotientReduction
import Langlands.GroupScheme.Rational.SemigroupTransport
import Langlands.GroupScheme.Rational.RepresentedLieUniqueness
import Langlands.GroupScheme.Rational.RootSubgroupRepresentability
import Langlands.GroupScheme.Lie.SmoothOpenSubgroup
import Langlands.GroupScheme.SubgroupIntersection
import Langlands.GroupScheme.IdentityComponent

/-! # Smoothness and identity component of actual semigroup intersections -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SubgroupFunctor.IsRepresentedBy

variable {B : Scheme.{u}} {G H K : GroupScheme B} {F : SubgroupFunctor G}
    {l : K ⟶ G}

/-- Pulling a represented closed subgroup back along a homomorphism represents
its actual inverse image on every test. -/
theorem comap_subgroupIntersectionFst (hl : F.IsRepresentedBy l)
    (hc : IsClosedSubgroup l) (j : H ⟶ G) :
    (F.comap j).IsRepresentedBy (subgroupIntersectionFst j l) := by
  have hp : IsClosedImmersion (subgroupIntersectionFst j l).hom.hom.left :=
    MorphismProperty.of_isPullback
      (subgroupIntersection_isPullback_scheme j l).flip hc
  refine ⟨Over.mono_of_mono_left _, ?_⟩
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro x
  change (∃ y : T ⟶ (subgroupIntersection j l).X,
      y ≫ (subgroupIntersectionFst j l).hom.hom = x) ↔
    x ≫ j.hom.hom ∈ F.carrier T
  rw [← hl.2]
  let hpb := subgroupIntersection_isPullback j l
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨y ≫ (subgroupIntersectionSnd j l).hom.hom, ?_⟩
    change (y ≫ (subgroupIntersectionSnd j l).hom.hom) ≫ l.hom.hom =
      (y ≫ (subgroupIntersectionFst j l).hom.hom) ≫ j.hom.hom
    simp only [Category.assoc, hpb.w]
  · rintro ⟨z, hz⟩
    exact ⟨hpb.lift x z hz.symm, hpb.lift_fst _ _ _⟩

end SubgroupFunctor.IsRepresentedBy

namespace RelativeRoot

set_option backward.isDefEq.respectTransparency false

section FullLie

variable {k : Type u} [Field k]
    {G H K : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom]

/-- Included represented all-test subgroups with the same actual Lie image
have a full-Lie morphism between their representatives. -/
theorem fullLie_homOfLe_of_hasLieImage
    {F F' : SubgroupFunctor G} {p : H ⟶ G} {q : K ⟶ G}
    (hp : F.IsRepresentedBy p) (hq : F'.IsRepresentedBy q) (h : F ≤ F')
    {W : Submodule k (Additive (lieKernel G k))}
    (hLie : HasLieImage F W) (hLie' : HasLieImage F' W) :
    ∀ X : lieKernel K k, ∃ Y : lieKernel H k,
      Y.val ≫ (hp.homOfLe hq h).hom.hom = X.val := by
  have : Mono p.hom.hom := hp.1
  have : Mono q.hom.hom := hq.1
  intro X
  let XG : lieKernel G k := ⟨X.val ≫ q.hom.hom, by
    change Lie.reduction G (X.val ≫ q.hom.hom) = 1
    dsimp only [Lie.reduction, Lie.affineMap_apply]
    rw [← Category.assoc]
    change Lie.reduction K X.val ≫ q.hom.hom = 1
    rw [X.property, MonObj.one_comp]⟩
  have hXG : XG.val ∈ F'.carrier _ := by
    rw [← hq.2]
    exact SubgroupFunctor.mem_range.mpr ⟨X.val, rfl⟩
  have hXW : Additive.ofMul XG ∈ W := (hLie' _).mp hXG
  have hXF := (hLie (Additive.ofMul XG)).mpr hXW
  rw [← hp.2] at hXF
  obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp hXF
  have hy0 : Lie.reduction H y = 1 := by
    apply (cancel_mono p.hom.hom).mp
    rw [MonObj.one_comp]
    dsimp only [Lie.reduction, Lie.affineMap_apply]
    rw [Category.assoc, hy]
    exact XG.property
  refine ⟨⟨y, hy0⟩, ?_⟩
  apply (cancel_mono q.hom.hom).mp
  rw [Category.assoc, ← Grp.comp_hom_hom, hp.homOfLe_comp hq h]
  exact hy

/-- A connected smooth closed representative with the same Lie image as a
larger smooth closed representative is its identity component. -/
def identityComponentIsoOfLeOfHasLieImage
    [IsAffineHom K.X.hom] [LocallyOfFiniteType K.X.hom]
    [Smooth H.X.hom] [ConnectedSpace H.X.left] [Smooth K.X.hom]
    {F F' : SubgroupFunctor G} {p : H ⟶ G} {q : K ⟶ G}
    (hp : F.IsRepresentedBy p) (hq : F'.IsRepresentedBy q) (h : F ≤ F')
    (hpc : IsClosedSubgroup p) (hqc : IsClosedSubgroup q)
    {W : Submodule k (Additive (lieKernel G k))}
    (hLie : HasLieImage F W) (hLie' : HasLieImage F' W) :
    H ≅ identityComponent K := by
  let f := hp.homOfLe hq h
  have hfc : IsClosedSubgroup f := hp.homOfLe_isClosedSubgroup hq h hpc hqc
  have : IsClosedImmersion f.hom.hom.left := hfc
  have : IsOpenImmersion f.hom.hom.left := isOpenImmersion_of_fullLie f hfc
    (fullLie_homOfLe_of_hasLieImage hp hq h hLie hLie')
  exact IdentityComponent.isoOfIsOpenImmersion K f

/-- The identity-component identification commutes with the ambient inclusions. -/
theorem identityComponentIsoOfLeOfHasLieImage_fac
    [IsAffineHom K.X.hom] [LocallyOfFiniteType K.X.hom]
    [Smooth H.X.hom] [ConnectedSpace H.X.left] [Smooth K.X.hom]
    {F F' : SubgroupFunctor G} {p : H ⟶ G} {q : K ⟶ G}
    (hp : F.IsRepresentedBy p) (hq : F'.IsRepresentedBy q) (h : F ≤ F')
    (hpc : IsClosedSubgroup p) (hqc : IsClosedSubgroup q)
    {W : Submodule k (Additive (lieKernel G k))}
    (hLie : HasLieImage F W) (hLie' : HasLieImage F' W) :
    (identityComponentIsoOfLeOfHasLieImage hp hq h hpc hqc hLie hLie').hom ≫
      identityComponentι K ≫ q = p := by
  have hfc := hp.homOfLe_isClosedSubgroup hq h hpc hqc
  have : IsClosedImmersion (hp.homOfLe hq h).hom.hom.left := hfc
  have : IsOpenImmersion (hp.homOfLe hq h).hom.hom.left :=
    isOpenImmersion_of_fullLie _ hfc
      (fullLie_homOfLe_of_hasLieImage hp hq h hLie hLie')
  change (IdentityComponent.isoOfIsOpenImmersion K (hp.homOfLe hq h)).hom ≫
    identityComponentι K ≫ q = p
  rw [← Category.assoc,
    IdentityComponent.isoOfIsOpenImmersion_hom_identityComponentι]
  exact hp.homOfLe_comp hq h

end FullLie

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    (b : AutomorphicAction S.toGrp G) (c : AutomorphicAction S.toGrp H)
    (j : H ⟶ G)
    (heq : ∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X) (x : T ⟶ H.X),
      c.act s x ≫ j.hom.hom = b.act s (x ≫ j.hom.hom))

include heq

omit [IsAffineHom G.X.hom] [IsAffineHom H.X.hom] in
/-- Equivariant inverse images preserve actual stability under the action. -/
theorem isStable_comap_of_equivariant {F : SubgroupFunctor G} (hF : b.IsStable F) :
    c.IsStable (F.comap j) := by
  intro T s x hx
  change c.act s x ≫ j.hom.hom ∈ F.carrier T
  rw [heq]
  exact hF T s (x ≫ j.hom.hom) hx

/-- Exact ambient semigroup Lie image bounds the tangent weights in its
inverse image under an equivariant closed inclusion. -/
theorem actionWeightSupport_comap_semigroup_subset
    [LocallyOfFiniteType G.X.hom] [Mono j.hom.hom]
    (hS : IsSplitTorus S.toGrp) (A : AddSubsemigroup (characterLattice S))
    (hLie : HasLieImage (semigroupSubgroup b A) (semigroupWeightSpan b A)) :
    actionWeightSupport c ((semigroupSubgroup b A).comap j) ⊆ A := by
  rintro χ ⟨X, hX0, hXχ, hXF⟩
  by_contra hχ
  let Y := Lie.targetMapLinear j k X
  have hY0 : Y ≠ 0 := by
    intro h
    apply hX0
    apply Lie.targetMapLinear_injective j k
    simpa only [map_zero] using h
  have hYχ : Y ∈ actionWeightSpace b χ :=
    lieKernelTargetLinear_mem_actionWeightSpace b c j heq χ hXχ
  have hYA : Y ∈ semigroupWeightSpan b A := (hLie Y).mp hXF
  exact hY0 ((Submodule.disjoint_def.mp
    (disjoint_actionWeightSpace_semigroupWeightSpan b hS A χ hχ)) Y hYχ hYA)

/-- For an actual finite-type closed representative, exact Lie images for the
two semigroup functors identify the entire tangent image of the intersection. -/
theorem hasLieImage_comap_semigroup
    [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType H.X.hom]
    (hS : IsSplitTorus S.toGrp)
    (hjc : IsClosedSubgroup j) (A : AddSubsemigroup (characterLattice S))
    (hstable : b.IsStable (semigroupSubgroup b A))
    (hLieG : HasLieImage (semigroupSubgroup b A) (semigroupWeightSpan b A))
    (hLieH : HasLieImage (semigroupSubgroup c A) (semigroupWeightSpan c A))
    {K : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom K.X.hom]
    [LocallyOfFiniteType K.X.hom] (p : K ⟶ H)
    (hp : ((semigroupSubgroup b A).comap j).IsRepresentedBy p) :
    HasLieImage ((semigroupSubgroup b A).comap j) (semigroupWeightSpan c A) := by
  have : Mono j.hom.hom.left := hjc.mono
  have : Mono j.hom.hom := Over.mono_of_mono_left _
  apply (hasLieImage_iff_tangentSubmodule_eq _ _).mpr
  apply le_antisymm
  · exact (actionWeightSupport_subset_iff_tangentSubmodule_le c hS p hp
      (isStable_comap_of_equivariant b c j heq hstable) A).mp
      (actionWeightSupport_comap_semigroup_subset b c j heq hS A hLieG)
  · rw [← (hasLieImage_iff_tangentSubmodule_eq _ _).mp hLieH]
    exact tangentSubmodule_mono (SubgroupFunctor.map_le_iff_le_comap.mp
      (semigroupSubgroup_map_le j hjc c b heq A))

section Realization

variable [Smooth G.X.hom] [Smooth H.X.hom]
    (hReal : SemigroupRealizationStatement.{u})
    (hS : IsSplitTorus S.toGrp) (hjc : IsClosedSubgroup j)
    (A : AddSubsemigroup (characterLattice S))

include hReal hS hjc

/-- Assuming semigroup realization, every actual closed representative of the
inverse image of the ambient semigroup subgroup is smooth. Connectedness is
not assumed. -/
theorem smooth_semigroup_comap_representative
    {K : GroupScheme (Spec (CommRingCat.of k))} (p : K ⟶ H)
    (hp : ((semigroupSubgroup b A).comap j).IsRepresentedBy p)
    (hpc : IsClosedSubgroup p) : Smooth K.X.hom := by
  have : IsClosedImmersion p.hom.hom.left := hpc
  have : IsAffineHom K.X.hom := by
    rw [← p.hom.hom.w]
    infer_instance
  have : LocallyOfFiniteType K.X.hom := by
    rw [← p.hom.hom.w]
    infer_instance
  have hRG := hReal k G inferInstance inferInstance S hS b A
  have hRH := hReal k H inferInstance inferInstance S hS c A
  have hLie := hasLieImage_comap_semigroup b c j heq hS hjc A
    hRG.2.1 hRG.2.2.1 hRH.2.2.1 p hp
  obtain ⟨Hₐ, q, hq, hqc, hqs, _⟩ := hRH.1
  have : Smooth Hₐ.X.hom := hqs
  have hle : semigroupSubgroup c A ≤ (semigroupSubgroup b A).comap j :=
    SubgroupFunctor.map_le_iff_le_comap.mp (semigroupSubgroup_map_le j hjc c b heq A)
  exact smooth_of_fullLie_closed_subgroup K Hₐ (hq.homOfLe hp hle)
    (hq.homOfLe_isClosedSubgroup hp hle hqc hpc)
    (fullLie_homOfLe_of_hasLieImage hq hp hle hRH.2.2.1 hLie)

/-- The actual inverse image of an ambient semigroup subgroup under an
equivariant closed inclusion is smooth and closed, assuming realization. -/
theorem isSmoothClosed_semigroup_comap :
    IsSmoothClosed ((semigroupSubgroup b A).comap j) := by
  obtain ⟨Gₐ, l, hl, hlc, _, _⟩ :=
    (hReal k G inferInstance inferInstance S hS b A).1
  let p := subgroupIntersectionFst j l
  have hpc : IsClosedSubgroup p :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion)
      (subgroupIntersection_isPullback_scheme j l).flip hlc
  have hp := hl.comap_subgroupIntersectionFst hlc j
  exact ⟨subgroupIntersection j l, p, hp, hpc,
    smooth_semigroup_comap_representative b c j heq hReal hS hjc A p hp hpc⟩

/-- For a connected representative the three CGP connectedness alternatives
reduce the intersection comparison to the already established Lie image. -/
theorem semigroup_comap_eq_of_connected
    {K : GroupScheme (Spec (CommRingCat.of k))} (p : K ⟶ H)
    (hp : ((semigroupSubgroup b A).comap j).IsRepresentedBy p)
    (hpc : IsClosedSubgroup p) (hconn : ConnectedSpace K.X.left) :
    (semigroupSubgroup b A).comap j = semigroupSubgroup c A := by
  have : IsClosedImmersion p.hom.hom.left := hpc
  have : IsAffineHom K.X.hom := by
    rw [← p.hom.hom.w]
    infer_instance
  have : LocallyOfFiniteType K.X.hom := by
    rw [← p.hom.hom.w]
    infer_instance
  have hs := smooth_semigroup_comap_representative b c j heq hReal hS hjc A p hp hpc
  have hRG := hReal k G inferInstance inferInstance S hS b A
  have hRH := hReal k H inferInstance inferInstance S hS c A
  have hLie := hasLieImage_comap_semigroup b c j heq hS hjc A
    hRG.2.1 hRG.2.2.1 hRH.2.2.1 p hp
  exact (hRH.1.eq_of_le_of_hasLieImage ⟨K, p, hp, hpc, hs, hconn⟩
    (SubgroupFunctor.map_le_iff_le_comap.mp (semigroupSubgroup_map_le j hjc c b heq A))
    hRH.2.2.1 hLie).symm

end Realization

end RelativeRoot
end Langlands.GroupScheme
