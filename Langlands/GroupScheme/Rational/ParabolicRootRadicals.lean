import Langlands.GroupScheme.Rational.ParabolicSplitComponentCocharacter
import Langlands.GroupScheme.Rational.DynamicSemistandardIntersectionModels
import Langlands.GroupScheme.Rational.GeometricUnipotentRadicalComparison
import Langlands.GroupScheme.Rational.SubgroupRelativeRoots
import Langlands.GroupScheme.Reductive.UnipotentFieldExtensionProof
import Langlands.GroupScheme.Dynamic.GeometricUnipotentRadicalReduction

/-! # Actual radicals of compatible parabolic root presentations -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace Dynamic

variable {k : Type u} [Field k]
  {G P Z U : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [Smooth G.X.hom]
  (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
  {p : P ⟶ G} (hP : (parabolic χ).IsRepresentedBy p)
  {z : Z ⟶ G} (hZ : (centralizer χ).IsRepresentedBy z)
  (hred : IsConnectedReductive Z)

include hP hZ hred in
/-- Identify a supplied geometric radical using reductivity of this actual
centralizer, without a universal centralizer or radical hypothesis. -/
theorem mem_range_radical_iff_of_reductive_centralizer {r : U ⟶ P}
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    {T : Over (Spec (CommRingCat.of k))} (x : T ⟶ P.X) :
    x ∈ (SubgroupFunctor.range r).carrier T ↔
      x ≫ p.hom.hom ∈ (unipotent χ).carrier T := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hpc := Affine.isClosedSubgroup_of_isRepresentedBy_parabolic χ hP
  let : IsAffineHom P.X.hom := hpc.isAffineHom
  let : Mono p.hom.hom := hP.1
  let hU := Affine.isRepresentedBy_unipotentHom χ
  let r' := unipotentToParabolic hP hU
  have hcomp : r' ≫ p = Affine.unipotentHom χ :=
    unipotentToParabolic_comp hP hU
  have hU' : (unipotent χ).IsRepresentedBy (r' ≫ p) := by
    rwa [hcomp]
  have hgeo := isGeometricUnipotentRadical_of_centralizer χ z p r' hP hU' hZ hred
  have hground := hgeo.isUnipotentRadical_of_unipotentFieldExtension
    unipotentFieldExtensionStatement
  have heq := hr.1.range_eq hground
  rw [heq, ← hU.2, SubgroupFunctor.mem_range, SubgroupFunctor.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, by rw [← hcomp, Grp.comp_hom_hom, Category.assoc]⟩
  · rintro ⟨y, hy⟩
    refine ⟨y, (cancel_mono p.hom.hom).mp ?_⟩
    rw [Category.assoc, ← Grp.comp_hom_hom, hcomp, hy]

include hP hZ hred in
/-- The ambient image of a supplied radical is the actual identity-limit
subgroup on every test scheme. -/
theorem range_comp_radical_eq_unipotent_of_reductive_centralizer {r : U ⟶ P}
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r) :
    SubgroupFunctor.range (r ≫ p) = unipotent χ := by
  let : Mono p.hom.hom := hP.1
  ext T x
  constructor
  · rintro ⟨y, rfl⟩
    change (y ≫ r.hom.hom) ≫ p.hom.hom ∈ (unipotent χ).carrier T
    exact (mem_range_radical_iff_of_reductive_centralizer χ hP hZ hred hr _).mp
      ⟨y, rfl⟩
  · intro hx
    obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp
      (show x ∈ (SubgroupFunctor.range p).carrier T by
        rw [hP.2]
        exact unipotent_le_parabolic χ T hx)
    have hyU := (mem_range_radical_iff_of_reductive_centralizer χ hP hZ hred hr y).mpr
      (by rwa [hy])
    obtain ⟨v, hv⟩ := SubgroupFunctor.mem_range.mp hyU
    refine ⟨v, ?_⟩
    change v ≫ (r ≫ p).hom.hom = x
    rw [Grp.comp_hom_hom, ← Category.assoc, hv, hy]

end Dynamic

namespace ParabolicRootPresentation

variable {k : Type u} [Field k]
  {A : CommGroupScheme (Spec (CommRingCat.of k))}
  {G M P : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation p l a)

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

/-- The actual affine identity-limit group of the chosen split-component
cocharacter, mapped into the specified parabolic. -/
def radicalHom :
    Dynamic.Affine.unipotentScheme
        (CommGroupScheme.groupHom r.splitComponentCocharacter ≫ a ≫ l ≫ p) ⟶ P := by
  let := r.isCompatible.parabolic.isClosedSubgroup.mono
  exact Dynamic.unipotentToParabolic
    ⟨Over.mono_of_mono_left _, r.parabolic_eq_splitComponentCocharacter⟩
    (Dynamic.Affine.isRepresentedBy_unipotentHom _)

theorem radicalHom_comp :
    r.radicalHom ≫ p = Dynamic.Affine.unipotentHom
      (CommGroupScheme.groupHom r.splitComponentCocharacter ≫ a ≫ l ≫ p) := by
  exact Dynamic.unipotentToParabolic_comp _ _

/-- The specified Levi and chosen actual radical give the Levi-first
multiplication isomorphism, already without a smoothness hypothesis. -/
theorem isIso_subgroupMultiplication_radicalHom :
    IsIso (subgroupMultiplication l r.radicalHom) := by
  let := r.isCompatible.parabolic.isClosedSubgroup.mono
  let := (r.isCompatible.levi.isClosedSubgroup.comp
    r.isCompatible.parabolic.isClosedSubgroup).mono
  exact Dynamic.isIso_subgroupMultiplication
    ⟨Over.mono_of_mono_left _, r.parabolic_eq_splitComponentCocharacter⟩
    ⟨Over.mono_of_mono_left _, r.levi_eq_splitComponentCocharacter⟩
    (Dynamic.Affine.isRepresentedBy_unipotentHom _) l r.radicalHom rfl r.radicalHom_comp

section Smooth

variable [Smooth G.X.hom]

/-- The chosen actual radical satisfies the full geometric greatestness
predicate, using reductivity of the specified Levi. -/
theorem isGeometricUnipotentRadical_radicalHom :
    IsGeometricUnipotentRadical r.radicalHom := by
  let := r.isCompatible.parabolic.isClosedSubgroup.mono
  let := (r.isCompatible.levi.isClosedSubgroup.comp
    r.isCompatible.parabolic.isClosedSubgroup).mono
  apply Dynamic.isGeometricUnipotentRadical_of_centralizer
    (CommGroupScheme.groupHom r.splitComponentCocharacter ≫ a ≫ l ≫ p) (l ≫ p) p
      r.radicalHom
    ⟨Over.mono_of_mono_left _, r.parabolic_eq_splitComponentCocharacter⟩
  · rw [r.radicalHom_comp]
    exact Dynamic.Affine.isRepresentedBy_unipotentHom _
  · exact ⟨Over.mono_of_mono_left _, r.levi_eq_splitComponentCocharacter⟩
  · exact r.isCompatible.levi.isConnectedReductive

/-- The same chosen radical is greatest both over the ground field and over
the algebraic closure, in the rational-Levi interface. -/
theorem leviSubgroup_isGeometricUnipotentRadical_radicalHom :
    LeviSubgroup.IsGeometricUnipotentRadical r.radicalHom := by
  let : IsAffineHom P.X.hom := r.isCompatible.levi.isAffineHom
  exact r.isGeometricUnipotentRadical_radicalHom.leviSubgroup_of_unipotentFieldExtension
    unipotentFieldExtensionStatement

/-- Every supplied geometric radical of the specified parabolic has the same
actual ambient image as the chosen dynamic identity-limit group. -/
theorem range_comp_radical_eq {U : GroupScheme (Spec (CommRingCat.of k))}
    {n : U ⟶ P} (hn : LeviSubgroup.IsGeometricUnipotentRadical n) :
    SubgroupFunctor.range (n ≫ p) =
      Dynamic.unipotent (CommGroupScheme.groupHom r.splitComponentCocharacter ≫
        a ≫ l ≫ p) := by
  let := r.isCompatible.parabolic.isClosedSubgroup.mono
  let := (r.isCompatible.levi.isClosedSubgroup.comp
    r.isCompatible.parabolic.isClosedSubgroup).mono
  exact Dynamic.range_comp_radical_eq_unipotent_of_reductive_centralizer
    _ ⟨Over.mono_of_mono_left _, r.parabolic_eq_splitComponentCocharacter⟩
    ⟨Over.mono_of_mono_left _, r.levi_eq_splitComponentCocharacter⟩
    r.isCompatible.levi.isConnectedReductive hn

/-- The complete actual split-component root support of any supplied radical,
including all multipliable roots. -/
theorem subgroupRelativeRoots_radical {U : GroupScheme (Spec (CommRingCat.of k))}
    {n : U ⟶ P} (hn : LeviSubgroup.IsGeometricUnipotentRadical n) :
    RelativeRoot.subgroupRelativeRoots (a ≫ l ≫ p) (SubgroupFunctor.range (n ≫ p)) =
      positiveRelativeRoots (a ≫ l ≫ p) r.splitComponentCocharacter := by
  rw [r.range_comp_radical_eq hn]
  exact RelativeRoot.subgroupRelativeRoots_dynamicUnipotent _
    r.isCompatible.splitComponent.1.isSplitSubtorus.1 _

end Smooth

end ParabolicRootPresentation

end Langlands.GroupScheme
