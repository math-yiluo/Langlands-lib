import Langlands.Geometry.Building.Kottwitz.ReductiveMap
import Langlands.Geometry.Building.Kottwitz.TorusInertiaFunctoriality
import Langlands.GroupScheme.SubgroupIntersectionKernelComparison
import Langlands.GroupScheme.Torus.KernelCocharacters
import Langlands.GroupScheme.Torus.WeilRestrictionNormOneCocharacters
import Langlands.GroupScheme.FppfQuotientComparison
import Mathlib.LinearAlgebra.Isomorphisms

/-! # Integral cocharacter exactness for actual cocenters -/

noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme
open Langlands.GroupScheme.AlgebraicFundamentalGroup

namespace Langlands.Geometry.Building.Kottwitz

section KernelComparison

variable {S : Scheme.{u}} {C T G Q : GroupScheme S}
  (p : C ⟶ G) (t : T ⟶ G) (q : G ⟶ Q)
  (hp : IsClosedSubgroup p)
  (hker : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range p)

include hp hker

/-- Reversing the intersection presents the full kernel of a restricted quotient. -/
def cocenterIntersectionKernelIso :
    subgroupIntersection p t ≅ GroupScheme.kernel (t ≫ q) :=
  pullbackSymmetry p t ≪≫ (kernelCompositeIntersectionIso t p q hp hker).symm

@[reassoc]
theorem cocenterIntersectionKernelIso_hom_comp :
    (cocenterIntersectionKernelIso p t q hp hker).hom ≫ kernelι (t ≫ q) =
      subgroupIntersectionSnd p t := by
  change ((pullbackSymmetry p t).hom ≫
    (kernelCompositeIntersectionIso t p q hp hker).inv) ≫ kernelι (t ≫ q) = _
  rw [Category.assoc, ← kernelCompositeIntersectionIso_hom_comp t p q hp hker,
    Iso.inv_hom_id_assoc]
  exact pullbackSymmetry_hom_comp_fst p t

end KernelComparison

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (a : Choice k G) (hsc : HasSimplyConnectedDerivedGroup G) (c : Cocenter k G)

include hsc

/-- Every chosen cover of the derived group is an isomorphism when that group
is simply connected. -/
theorem cocenter_covering_isIso : IsIso a.covering := by
  obtain ⟨D, d, hd, hD⟩ := hsc
  let e : a.derived ≅ D :=
    a.isCover.isDerivedSubgroup.isRepresentedBy.isoOfIsRepresentedBy hd.isRepresentedBy
  have haD : IsSimplyConnected a.derived := hD.of_iso e
  exact haD.central_isogeny_isIso a.cover a.covering
    a.isCover.isSimplyConnectedCover.isSimplyConnected.isSemisimple
    a.isCover.isSimplyConnectedCover.isCentralIsogeny

/-- The ambient composite of the chosen cover presents the full derived subgroup. -/
theorem cocenter_cover_isDerivedSubgroup :
    IsDerivedSubgroup (a.covering ≫ a.derivedInclusion) := by
  let : IsIso a.covering := cocenter_covering_isIso a hsc
  have : IsClosedImmersion a.derivedInclusion.hom.hom.left :=
    a.isCover.isDerivedSubgroup.1
  refine ⟨?_, ?_⟩
  · change IsClosedImmersion
      (a.covering.hom.hom.left ≫ a.derivedInclusion.hom.hom.left)
    infer_instance
  · exact (SubgroupFunctor.range_iso_comp (asIso a.covering) a.derivedInclusion).trans
      a.isCover.isDerivedSubgroup.2

/-- The chosen preimage torus is the full actual kernel of the restriction
of any supplied cocenter quotient. -/
def scTorusCocenterKernelIso :
    a.scTorus ≅ CommGroupScheme.kernel
      (Additive.ofMul (a.inclusion ≫ c.quotient) : a.torus ⟶ c.torus) :=
  CommGroupScheme.isoOfGroupIso
    (cocenterIntersectionKernelIso (a.covering ≫ a.derivedInclusion)
      a.inclusion c.quotient (cocenter_cover_isDerivedSubgroup a hsc).1
      (c.isQuotient.2.2.2.trans (cocenter_cover_isDerivedSubgroup a hsc).2.symm))

@[reassoc]
theorem scTorusCocenterKernelIso_hom_comp :
    (scTorusCocenterKernelIso a hsc c).hom ≫
      CommGroupScheme.kernelι
        (Additive.ofMul (a.inclusion ≫ c.quotient) : a.torus ⟶ c.torus) =
      a.scToTorus := by
  apply Additive.toMul.injective
  exact cocenterIntersectionKernelIso_hom_comp _ _ _ _ _

variable (E : Type u) [Field E] [Algebra k E]

/-- The full-kernel comparison after any field extension. -/
def scTorusCocenterKernelBaseChangeIso :
    (CommGroupScheme.baseChange (algebraBaseMap k E)).obj a.scTorus ≅
      CommGroupScheme.kernel
        ((CommGroupScheme.baseChange (algebraBaseMap k E)).map
          (Additive.ofMul (a.inclusion ≫ c.quotient) : a.torus ⟶ c.torus)) :=
  (CommGroupScheme.baseChange (algebraBaseMap k E)).mapIso
      (scTorusCocenterKernelIso a hsc c) ≪≫
    CommGroupScheme.kernelBaseChangeIso (algebraBaseMap k E)
      (Additive.ofMul (a.inclusion ≫ c.quotient) : a.torus ⟶ c.torus)

@[reassoc]
theorem scTorusCocenterKernelBaseChangeIso_hom_comp :
    (scTorusCocenterKernelBaseChangeIso a hsc c E).hom ≫
      CommGroupScheme.kernelι
        ((CommGroupScheme.baseChange (algebraBaseMap k E)).map
          (Additive.ofMul (a.inclusion ≫ c.quotient) : a.torus ⟶ c.torus)) =
      (CommGroupScheme.baseChange (algebraBaseMap k E)).map a.scToTorus := by
  change ((CommGroupScheme.baseChange (algebraBaseMap k E)).map
      (scTorusCocenterKernelIso a hsc c).hom ≫
      (CommGroupScheme.kernelBaseChangeIso (algebraBaseMap k E)
        (Additive.ofMul (a.inclusion ≫ c.quotient) : a.torus ⟶ c.torus)).hom) ≫ _ = _
  rw [Category.assoc, CommGroupScheme.kernelBaseChangeIso_hom_ι, ← Functor.map_comp,
    scTorusCocenterKernelIso_hom_comp]

/-- Integral exactness: the actual cocenter restriction kills precisely the
cocharacters in the chosen coroot image. -/
theorem cocenter_cocharacter_eq_zero_iff (ν : a.lattice E) :
    geometricCocharacterMap k E
        (Additive.ofMul (a.inclusion ≫ c.quotient) : a.torus ⟶ c.torus) ν = 0 ↔
      ν ∈ a.corootImage E := by
  let f := (CommGroupScheme.baseChange (algebraBaseMap k E)).map
    (Additive.ofMul (a.inclusion ≫ c.quotient) : a.torus ⟶ c.torus)
  let e := scTorusCocenterKernelBaseChangeIso a hsc c E
  let l := (cocharacterLattice.congr e).trans (cocharacterLattice.kernelEquiv f)
  have hl : ∀ w : a.scLattice E, (l w).val = a.corootMap E w := by
    intro w
    change (w ≫ e.hom) ≫ CommGroupScheme.kernelι f =
      w ≫ (CommGroupScheme.baseChange (algebraBaseMap k E)).map a.scToTorus
    rw [Category.assoc, scTorusCocenterKernelBaseChangeIso_hom_comp]
  constructor
  · intro hν
    obtain ⟨w, hw⟩ := l.surjective ⟨ν, hν⟩
    exact ⟨w, (hl w).symm.trans (congrArg Subtype.val hw)⟩
  · rintro ⟨w, rfl⟩
    have hw := (l w).property
    change (l w).val ≫ f = 0 at hw
    rwa [hl w] at hw

omit hsc in
/-- Every supplied cocenter inherits integral cocharacter surjectivity from
the published quotient construction. -/
theorem cocenter_cocharacter_surjective
    (hTE : IsSplitTorus (GaloisPointComparison.baseChanged k E a.torus.toGrp)) :
    Function.Surjective (geometricCocharacterMap k E
      (Additive.ofMul (a.inclusion ≫ c.quotient) : a.torus ⟶ c.torus)) := by
  let hG := a.isCover.isConnectedReductive
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsAffine c.torus.X.left := torusIsAffine k c.torus c.isTorus
  obtain ⟨Q, q, hQa, hq, _, hT⟩ := cocenterQuotientExistence
    k G a.derived a.derivedInclusion hG a.isCover.isDerivedSubgroup
  let : IsAffine Q.X.left := hQa
  have hc : RelativeRoot.IsFppfQuotient
      (SubgroupFunctor.range a.derivedInclusion) c.quotient := by
    simpa only [a.isCover.isDerivedSubgroup.2] using c.isQuotient
  let e : Q.toGrp ≅ c.torus.toGrp := FppfQuotientComparison.iso hq hc
  have he : q ≫ e.hom = c.quotient := FppfQuotientComparison.iso_fac hq hc
  let ec : Q ≅ c.torus := CommGroupScheme.isoOfGroupIso e
  let B := CommGroupScheme.baseChange (algebraBaseMap k E)
  let eb := B.mapIso ec
  let f0 : a.torus ⟶ Q := Additive.ofMul (a.inclusion ≫ q)
  let f : a.torus ⟶ c.torus := Additive.ofMul (a.inclusion ≫ c.quotient)
  have hf : f0 ≫ ec.hom = f := by
    change (a.inclusion ≫ q) ≫ e.hom = a.inclusion ≫ c.quotient
    rw [Category.assoc, he]
  have hm : B.map f0 ≫ eb.hom = B.map f :=
    (B.map_comp f0 ec.hom).symm.trans (congrArg B.map hf)
  intro v
  obtain ⟨w, hw⟩ := (hT a.torus a.inclusion a.isMaximal E hTE).2 (v ≫ eb.inv)
  refine ⟨w, ?_⟩
  change w ≫ B.map f = v
  calc
    _ = w ≫ (B.map f0 ≫ eb.hom) := congrArg (fun j => w ≫ j) hm.symm
    _ = (w ≫ B.map f0) ≫ eb.hom := (Category.assoc _ _ _).symm
    _ = (v ≫ eb.inv) ≫ eb.hom := congrArg (fun j => j ≫ eb.hom) hw
    _ = v := by rw [Category.assoc, eb.inv_hom_id, Category.comp_id]

/-- The kernel submodule is exactly the chosen integral coroot image. -/
theorem cocenter_cocharacter_ker :
    (geometricCocharacterMap k E
      (Additive.ofMul (a.inclusion ≫ c.quotient) : a.torus ⟶ c.torus)).ker =
      a.corootImage E := by
  ext v
  exact cocenter_cocharacter_eq_zero_iff a hsc c E v

/-- The quotient by the chosen coroot image identifies integrally with the
actual cocenter cocharacter lattice. -/
def cocenterCocharacterEquiv
    (hTE : IsSplitTorus (GaloisPointComparison.baseChanged k E a.torus.toGrp)) :
    a.atChoice E ≃ₗ[ℤ] geometricCocharacters k E c.torus :=
  (Submodule.quotEquivOfEq _ _ (cocenter_cocharacter_ker a hsc c E).symm).trans
    (LinearMap.quotKerEquivOfSurjective
      (geometricCocharacterMap k E
        (Additive.ofMul (a.inclusion ≫ c.quotient) : a.torus ⟶ c.torus))
      (cocenter_cocharacter_surjective a c E hTE))

/-- The integral quotient comparison has the actual postcomposition law. -/
@[simp]
theorem cocenterCocharacterEquiv_projection
    (hTE : IsSplitTorus (GaloisPointComparison.baseChanged k E a.torus.toGrp))
    (v : a.lattice E) :
    cocenterCocharacterEquiv a hsc c E hTE (a.projection E v) =
      geometricCocharacterMap k E
        (Additive.ofMul (a.inclusion ≫ c.quotient) : a.torus ⟶ c.torus) v := by
  simp only [cocenterCocharacterEquiv, LinearEquiv.trans_apply, Choice.projection,
    Submodule.mkQ_apply, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk]

end Langlands.Geometry.Building.Kottwitz
