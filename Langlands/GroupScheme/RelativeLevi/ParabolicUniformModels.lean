import Langlands.GroupScheme.RelativeLevi.ParabolicUniformCocharacters
import Langlands.GroupScheme.RelativeLevi.ParabolicStandardFamilyClassification
import Langlands.GroupScheme.RelativeLevi.DynamicProof
import Langlands.GroupScheme.Reductive.AffineRegularBorel

/-! # Relative dynamic parabolic models for a uniform standard cocharacter family -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

namespace Langlands.GroupScheme.UniformStandardCocharacterFamily

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I]
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  (F : UniformStandardCocharacterFamily I G i)

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

/-- The actual affine dynamic parabolic for one fixed exponent vector. -/
abbrev parabolic (a : F.Index) : GroupScheme (Spec (CommRingCat.of R)) :=
  Dynamic.Affine.parabolicScheme (AffineRegularBorel.cocharacter i (F.exponents a))

/-- Its inclusion in the original group over the base ring. -/
def inclusion (a : F.Index) : F.parabolic a ⟶ G :=
  Dynamic.Affine.parabolicHom (AffineRegularBorel.cocharacter i (F.exponents a))

/-- Every model in the family is a relative parabolic subgroup. -/
theorem relativeParabolic (hG : IsReductive G) (a : F.Index) :
    IsRelativeParabolicSubgroup (F.inclusion a) := by
  let χ := AffineRegularBorel.cocharacter i (F.exponents a)
  exact (dynamicRelativeLevi _ G
    (Dynamic.Affine.parabolicScheme χ) (Dynamic.Affine.unipotentScheme χ)
    (Dynamic.Affine.centralizerScheme χ) χ
    (Dynamic.Affine.parabolicHom χ) (Dynamic.Affine.unipotentHom χ)
    (Dynamic.Affine.centralizerHom χ) hG
    (Dynamic.Affine.isRepresentedBy_parabolicHom χ)
    (Dynamic.Affine.isRepresentedBy_unipotentHom χ)
    (Dynamic.Affine.isRepresentedBy_centralizerHom χ)).1

/-- Field pullback of the actual inclusion represents the dynamic parabolic
of exactly the same exponent vector. -/
theorem range_field (k : Type u) [Field k] [Algebra R k] (a : F.Index) :
    SubgroupFunctor.range ((GroupScheme.baseChange (algebraBaseMap R k)).map
      (F.inclusion a)) =
      Dynamic.parabolic (CommGroupScheme.groupHom
        (splitTorus.exponentCocharacter (Spec (CommRingCat.of k)) I (F.exponents a)) ≫
          splitTorus.baseChangeHom (K := k) G I i) := by
  have h := (Dynamic.Affine.isRepresentedBy_parabolicHom
    (AffineRegularBorel.cocharacter i (F.exponents a))).baseChange (algebraBaseMap R k)
  rw [← Dynamic.parabolic_baseChange, AffineRegularBorel.cocharacter_baseChange] at h
  exact h.2

/-- The family classifies every rational parabolic on every field algebra,
with uniqueness of the index and equality on every scheme test. -/
theorem classifies_field (hG : IsReductive G)
    (hi : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (k : Type u) [Field k] [Algebra R k]
    (Q : GroupScheme (Spec (CommRingCat.of k)))
    (q : Q ⟶ (GroupScheme.baseChange (algebraBaseMap R k)).obj G)
    (hq : IsParabolicSubgroup q) :
    ∃! a : F.Index,
      ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
          ((GroupScheme.baseChange (algebraBaseMap R k)).obj G).X,
        SubgroupFunctor.range
            (q ≫ (((GroupScheme.baseChange (algebraBaseMap R k)).obj G).innerIso g).hom) =
          SubgroupFunctor.range ((GroupScheme.baseChange (algebraBaseMap R k)).map
            (F.inclusion a)) := by
  classical
  let : Smooth G.X.hom := hG.smooth
  let Gk := (GroupScheme.baseChange (algebraBaseMap R k)).obj G
  have hGk : IsConnectedReductive Gk := hG.isConnectedReductive_baseChange _
  let : IsAffineHom Gk.X.hom := hGk.isAffineHom
  let Tk := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I
  let ik := splitTorus.baseChangeHom (K := k) G I i
  have hik : IsMaximalSplitTorus (T := Tk) ik :=
    (splitTorus.isMaximalTorus_baseChangeHom_of_fibrewise I G i hi k).isMaximalSplitTorus
      (isSplitTorus_splitTorus (S := Spec (CommRingCat.of k)) I)
  obtain ⟨ν, hν, e, hζ⟩ := F.standard k
  let ζ := fun a => splitTorus.exponentCocharacter (Spec (CommRingCat.of k)) I (F.exponents a)
  let Pk := fun a => (GroupScheme.baseChange (algebraBaseMap R k)).obj (F.parabolic a)
  let jk := fun a => (GroupScheme.baseChange (algebraBaseMap R k)).map (F.inclusion a)
  have hjk : ∀ a, SubgroupFunctor.range (jk a) =
      Dynamic.parabolic (CommGroupScheme.groupHom (ζ a) ≫ ik) := F.range_field k
  let a := standardFamilyConjugacyIndex Gk hGk Tk ik hik ν hν e ζ hζ Pk jk hjk Q q hq
  exact ⟨a,
    standardFamilyConjugacyIndex_spec Gk hGk Tk ik hik ν hν e ζ hζ Pk jk hjk Q q hq,
    fun b hb => standardFamilyConjugacyIndex_unique
      Gk hGk Tk ik hik ν hν e ζ hζ Pk jk hjk Q q hq b hb⟩

end Langlands.GroupScheme.UniformStandardCocharacterFamily
