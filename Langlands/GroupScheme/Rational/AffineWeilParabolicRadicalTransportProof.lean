import Langlands.GroupScheme.AffineWeilDynamicTransport
import Langlands.GroupScheme.Rational.AffineWeilParabolicRadicalTransportStatement
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Dynamic.GeometricUnipotentRadicalProof
import Langlands.GroupScheme.Rational.AffineGeometricUnipotentRadical
import Langlands.GroupScheme.Dynamic.ParabolicLieCriterion
import Langlands.GroupScheme.Reductive.AffineWeilConnectedReductive

/-! # Parabolic and radical diagrams under finite separable Weil restriction: proof -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace AffineWeilParabolicRadicalTransport

/-- Composing with a fixed homomorphism preserves inclusions of ranges. -/
theorem range_comp_le_of_le {S : Scheme.{u}} {U U' P G : GroupScheme S}
    {r : U ⟶ P} {r' : U' ⟶ P} (h : SubgroupFunctor.range r ≤ SubgroupFunctor.range r')
    (p : P ⟶ G) : SubgroupFunctor.range (r ≫ p) ≤ SubgroupFunctor.range (r' ≫ p) := by
  intro T x hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.1 hx
  obtain ⟨z, hz⟩ := SubgroupFunctor.mem_range.1 (h T (SubgroupFunctor.mem_range.2 ⟨y, rfl⟩))
  refine SubgroupFunctor.mem_range.2 ⟨z, ?_⟩
  simp only [Grp.comp_hom_hom]
  rw [← Category.assoc, hz, Category.assoc]

variable {k : Type u} [Field k] {G P U : GroupScheme (Spec (CommRingCat.of k))}

/-- A parabolic subgroup of a connected reductive group represents a dynamic parabolic. -/
theorem exists_isRepresentedBy_parabolic (hG : IsConnectedReductive G) {p : P ⟶ G}
    (hp : IsParabolicSubgroup p) :
    ∃ χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G, (Dynamic.parabolic χ).IsRepresentedBy p := by
  obtain ⟨χ, hχ⟩ := (parabolicDynamic k G hG P p hp.isClosedSubgroup).1 hp
  have : IsClosedImmersion p.hom.hom.left := hp.isClosedSubgroup
  exact ⟨χ, Over.mono_of_mono_left _, hχ⟩

/-- A representative of a dynamic parabolic of a connected reductive group is parabolic. -/
theorem isParabolicSubgroup_of_isRepresentedBy (hG : IsConnectedReductive G)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) {p : P ⟶ G}
    (hp : (Dynamic.parabolic χ).IsRepresentedBy p) : IsParabolicSubgroup p :=
  haveI := hG.isAffineHom
  haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  (parabolicDynamic k G hG P p
    (Dynamic.Affine.isClosedSubgroup_of_isRepresentedBy_parabolic χ hp)).2 ⟨χ, hp.2⟩

/-- Inside a representative of a dynamic parabolic, a subgroup whose composite represents the
dynamic unipotent subgroup is a geometric unipotent radical. -/
theorem isGeometricUnipotentRadical_of_isRepresentedBy (hG : IsConnectedReductive G)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) {p : P ⟶ G}
    (hp : (Dynamic.parabolic χ).IsRepresentedBy p) {r : U ⟶ P}
    (hr : (Dynamic.unipotent χ).IsRepresentedBy (r ≫ p)) :
    LeviSubgroup.IsGeometricUnipotentRadical r := by
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsAffineHom P.X.hom :=
    (Dynamic.Affine.isClosedSubgroup_of_isRepresentedBy_parabolic χ hp).isAffineHom
  exact (dynamicGeometricUnipotentRadical k G hG χ P U p r hp hr).leviSubgroup

/-- In a representative of a dynamic parabolic, every unipotent radical composes to a
representative of the dynamic unipotent subgroup. -/
theorem isRepresentedBy_unipotent_of_isUnipotentRadical (hG : IsConnectedReductive G)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) {p : P ⟶ G}
    (hp : (Dynamic.parabolic χ).IsRepresentedBy p) {r : U ⟶ P} (hr : IsUnipotentRadical r) :
    (Dynamic.unipotent χ).IsRepresentedBy (r ≫ p) := by
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsAffineHom P.X.hom :=
    (Dynamic.Affine.isClosedSubgroup_of_isRepresentedBy_parabolic χ hp).isAffineHom
  have hle : SubgroupFunctor.range (Dynamic.Affine.unipotentHom χ) ≤ Dynamic.parabolic χ := by
    rw [(Dynamic.Affine.isRepresentedBy_unipotentHom χ).2]
    exact Dynamic.unipotent_le_parabolic χ
  have hrep₀ : (Dynamic.unipotent χ).IsRepresentedBy
      (hp.liftOfLE (Dynamic.Affine.unipotentHom χ) hle ≫ p) := by
    rw [hp.liftOfLE_comp]
    exact Dynamic.Affine.isRepresentedBy_unipotentHom χ
  have hr₀ : IsUnipotentRadical (hp.liftOfLE (Dynamic.Affine.unipotentHom χ) hle) :=
    (dynamicGeometricUnipotentRadical k G hG χ P _ p _ hp hrep₀).isUnipotentRadical
  have hrange := hr.range_eq hr₀
  refine ⟨?_, le_antisymm ?_ ?_⟩
  · have : IsClosedImmersion r.hom.hom.left := hr.isClosedSubgroup
    have : Mono r.hom.hom := Over.mono_of_mono_left _
    have : Mono p.hom.hom := hp.1
    rw [Grp.comp_hom_hom]
    infer_instance
  · rw [← hrep₀.2]
    exact range_comp_le_of_le hrange.le p
  · rw [← hrep₀.2]
    exact range_comp_le_of_le hrange.ge p

end AffineWeilParabolicRadicalTransport

open AffineWeilParabolicRadicalTransport in
/-- **Parabolic–radical diagrams under finite Weil restriction** (Borel–Tits 6.19 and
6.21(i)), assuming that finite separable affine Weil restriction preserves connected
reductivity. -/
theorem affineWeilParabolicRadicalTransport_of_connectedReductive
    (hR : ∀ (k K : Type u) [Field k] [Field K] [Algebra k K] [FiniteDimensional k K]
      [Algebra.IsSeparable k K] (G : GroupScheme (Spec (CommRingCat.of K)))
      (hG : IsConnectedReductive G),
      haveI := hG.isAffineHom
      haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
      haveI := hG.smooth
      IsConnectedReductive (AffineWeil.groupScheme k K G)) :
    AffineWeilParabolicRadicalTransportStatement.{u} := by
  intro k K _ _ _ _ _ G hG
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := hG.smooth
  have hRG := hR k K G hG
  refine ⟨?_, ?_⟩
  · intro P U _ _ _ _ p r hp hr
    obtain ⟨χ, hχ⟩ := exists_isRepresentedBy_parabolic hG hp
    have hu := isRepresentedBy_unipotent_of_isUnipotentRadical hG χ hχ hr.1
    have hχ' := AffineWeil.isRepresentedBy_map_parabolic (A := k) χ hχ
    have hu' := AffineWeil.isRepresentedBy_map_unipotent (A := k) χ hu
    rw [AffineWeil.map_comp] at hu'
    exact ⟨isParabolicSubgroup_of_isRepresentedBy hRG _ hχ',
      isGeometricUnipotentRadical_of_isRepresentedBy hRG _ hχ' hu'⟩
  · intro P U p r hp hr
    obtain ⟨ν, hν⟩ := exists_isRepresentedBy_parabolic hRG hp
    set χ := AffineWeil.descendCocharacter k ν
    rw [← AffineWeil.cocharacter_descendCocharacter ν] at hν
    have hrU := isRepresentedBy_unipotent_of_isUnipotentRadical hRG _ hν hr.1
    have hpc := Dynamic.Affine.isClosedSubgroup_parabolicHom χ
    have huc := Dynamic.Affine.isClosedSubgroup_unipotentHom χ
    have := hpc.isAffineHom
    have := huc.isAffineHom
    have aP : IsAffine (Dynamic.Affine.parabolicScheme χ).X.left :=
      isAffine_of_isAffineHom (Dynamic.Affine.parabolicScheme χ).X.hom
    have lP : LocallyOfFiniteType (Dynamic.Affine.parabolicScheme χ).X.hom :=
      hpc.locallyOfFiniteType
    have aU : IsAffine (Dynamic.Affine.unipotentScheme χ).X.left :=
      isAffine_of_isAffineHom (Dynamic.Affine.unipotentScheme χ).X.hom
    have lU : LocallyOfFiniteType (Dynamic.Affine.unipotentScheme χ).X.hom :=
      huc.locallyOfFiniteType
    have hp' := Dynamic.Affine.isRepresentedBy_parabolicHom χ
    have hle : SubgroupFunctor.range (Dynamic.Affine.unipotentHom χ) ≤ Dynamic.parabolic χ := by
      rw [(Dynamic.Affine.isRepresentedBy_unipotentHom χ).2]
      exact Dynamic.unipotent_le_parabolic χ
    have hr'p := hp'.liftOfLE_comp (Dynamic.Affine.unipotentHom χ) hle
    have hu' : (Dynamic.unipotent χ).IsRepresentedBy
        (hp'.liftOfLE (Dynamic.Affine.unipotentHom χ) hle ≫ Dynamic.Affine.parabolicHom χ) := by
      rw [hr'p]
      exact Dynamic.Affine.isRepresentedBy_unipotentHom χ
    have hmp := AffineWeil.isRepresentedBy_map_parabolic (A := k) χ hp'
    have hmu := AffineWeil.isRepresentedBy_map_unipotent (A := k) χ hu'
    refine ⟨Dynamic.Affine.parabolicScheme χ, Dynamic.Affine.unipotentScheme χ, aP, lP, aU, lU,
      Dynamic.Affine.parabolicHom χ, hp'.liftOfLE (Dynamic.Affine.unipotentHom χ) hle,
      isParabolicSubgroup_of_isRepresentedBy hG χ hp',
      isGeometricUnipotentRadical_of_isRepresentedBy hG χ hp' hu',
      hν.isoOfIsRepresentedBy hmp, hrU.isoOfIsRepresentedBy hmu,
      hν.isoOfIsRepresentedBy_hom_comp hmp, ?_⟩
    apply hmp.hom_ext
    rw [Category.assoc, ← AffineWeil.map_comp, hrU.isoOfIsRepresentedBy_hom_comp hmu,
      Category.assoc, hν.isoOfIsRepresentedBy_hom_comp hmp]

/-- **Parabolic–radical diagrams under finite separable Weil restriction** (Borel–Tits 6.19
and 6.21(i)): proof of the exact target. -/
theorem affineWeilParabolicRadicalTransport : AffineWeilParabolicRadicalTransportStatement.{u} :=
  affineWeilParabolicRadicalTransport_of_connectedReductive fun k K _ _ _ _ _ G hG =>
    AffineWeil.isConnectedReductive_restriction k K G hG

end Langlands.GroupScheme
