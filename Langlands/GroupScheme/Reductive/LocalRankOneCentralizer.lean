import Langlands.GroupScheme.Torus.RelativeCocharacterCentralizers
import Langlands.GroupScheme.Reductive.LocalRootGroupTorusCoordinate
import Langlands.GroupScheme.Reductive.LocalSplitRootBaseChange

/-! # Actual rank-one centralizers over a ring -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme

namespace LocalSplitCell

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I]
  {G C : GroupScheme (Spec (CommRingCat.of R))}

/-- A root parametrization which factors through a closed subgroup remains a
parametrization of the intrinsic root subgroup there. -/
theorem IsRootParametrization.of_comp
    {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
    {t : splitTorus (Spec (CommRingCat.of R)) I ⟶ C} {j : C ⟶ G}
    (hj : IsClosedSubgroup j) (ht : t ≫ j = i)
    {a : I → ℤ} {v : Ga R ⟶ C} {w : Ga R ⟶ G}
    (hw : IsRootParametrization i a w) (hv : v ≫ j = w) :
    IsRootParametrization t a v := by
  let : IsClosedImmersion j.hom.hom.left := hj
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  have hequiv : ∀ (Z : Over (Spec (CommRingCat.of R)))
      (s : Z ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X) (c : Γ(Z.left, ⊤)),
      (s ≫ t.hom.hom) * rootPoint v Z c * (s ≫ t.hom.hom)⁻¹ =
        rootPoint v Z (VectorGroup.charValue (S := splitTorus.commGroupScheme _ I)
          (splitTorus.exponentCharacter _ I a) Z s * c) := by
    intro Z s c
    apply (cancel_mono j.hom.hom).mp
    simpa only [MonObj.mul_comp, GrpObj.inv_comp, Category.assoc,
      ← Grp.comp_hom_hom, ht, hv, rootPoint] using hw.equivariant Z s c
  refine ⟨⟨?_, ?_⟩, IsClosedSubgroup.of_comp hj (hv.symm ▸ hw.isClosedSubgroup), hequiv⟩
  · have : IsClosedImmersion v.hom.hom.left :=
      IsClosedSubgroup.of_comp hj (hv.symm ▸ hw.isClosedSubgroup)
    exact Over.mono_of_mono_left _
  · apply le_antisymm
    · rintro Z g ⟨x, rfl⟩
      obtain ⟨c, rfl⟩ := (LocalRootGroup.scalarPoint_bijective _ Z).2 x
      exact LocalRootGroup.rootPoint_mem_subgroup t a hequiv c
    · intro Z g hg
      have hmem := RelativeRoot.comp_mem_subgroup (S := splitTorus.commGroupScheme _ I) t
        (splitTorus.exponentCharacter _ I a) j hg
      rw [ht] at hmem
      let x := (hw.represents.pointsEquiv Z).symm ⟨_, hmem⟩
      refine ⟨x, (cancel_mono j.hom.hom).mp ?_⟩
      change (x ≫ v.hom.hom) ≫ j.hom.hom = g ≫ j.hom.hom
      rw [Category.assoc, ← Grp.comp_hom_hom, hv]
      exact hw.represents.pointsEquiv_symm_comp ⟨_, hmem⟩

end LocalSplitCell

namespace splitTorus.RelativeCocharacterCentralizer

open LocalSplitCell

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I]
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G) (mu : I → ℤ)

/-- An actual relative cocharacter centralizer of a reductive group is reductive. -/
theorem isReductive (hG : IsReductive G) :
    IsReductive (groupScheme I G i mu) := by
  let : Smooth G.X.hom := hG.smooth
  refine ⟨inferInstance, inferInstance, fun s => ?_⟩
  have h := Dynamic.isRepresentedBy_centralizer_baseChange
    (geometricPoint (Spec (CommRingCat.of R)) s) (cocharacter I G i mu)
      (isRepresentedBy_inclusion I G i mu)
  exact (dynamicCentralizerReductive _ _ (hG.geometricFiber s).isConnectedReductive_of_isAlgClosed
    _ _ _ ((isClosedSubgroup_inclusion I G i mu).baseChange _) h).isPseudoReductive

/-- A fibrewise maximal torus remains fibrewise maximal inside the actual centralizer. -/
theorem isFibrewiseMaximalTorus
    (hmax : IsFibrewiseMaximalTorus (T := commGroupScheme _ I) i) :
    IsFibrewiseMaximalTorus (T := commGroupScheme _ I) (torusHom I G i mu) := by
  intro s
  apply IsMaximalTorus.of_comp ((isClosedSubgroup_inclusion I G i mu).baseChange _)
  rw [← Functor.map_comp, torusHom_comp]
  exact hmax s

/-- The root map factors through the actual centralizer when its exponent
annihilates the cocharacter. -/
def rootLift {a : I → ℤ} {w : Ga R ⟶ G}
    (hw : IsRootParametrization i a w) (ha : ∑ j, a j * mu j = 0) :
    Ga R ⟶ groupScheme I G i mu :=
  (isRepresentedBy_inclusion I G i mu).factorHom w (by
    rw [hw.represents.2]
    exact LocalRootGroup.subgroup_le_centralizer i mu a ha)

/-- The lifted root map recovers the supplied root map exactly. -/
theorem rootLift_comp {a : I → ℤ} {w : Ga R ⟶ G}
    (hw : IsRootParametrization i a w) (ha : ∑ j, a j * mu j = 0) :
    rootLift i mu hw ha ≫ inclusion I G i mu = w :=
  SubgroupFunctor.IsRepresentedBy.factorHom_comp _ _ _

/-- The lifted map parametrizes the intrinsic root subgroup of the centralizer. -/
theorem isRootParametrization_rootLift {a : I → ℤ} {w : Ga R ⟶ G}
    (hw : IsRootParametrization i a w) (ha : ∑ j, a j * mu j = 0) :
    IsRootParametrization (torusHom I G i mu) a (rootLift i mu hw ha) :=
  hw.of_comp (isClosedSubgroup_inclusion I G i mu) (torusHom_comp I G i mu)
    (rootLift_comp i mu hw ha)

section Field

variable (k : Type u) [Field k] [Algebra R k]

/-- On an actual field fibre, the roots of the centralizer are the ambient
roots whose exponent pairing with `mu` vanishes. -/
theorem mem_roots_baseChangeHom_iff (hG : IsReductive G)
    (m : I → ℤ) :
    exponentCharacter (Spec (CommRingCat.of k)) I m ∈
        roots (T := commGroupScheme _ I)
          (baseChangeHom (K := k) (groupScheme I G i mu) I (torusHom I G i mu)) ↔
      exponentCharacter (Spec (CommRingCat.of k)) I m ∈
        roots (T := commGroupScheme _ I) (baseChangeHom (K := k) G I i) ∧
          ∑ j, m j * mu j = 0 := by
  let : Smooth G.X.hom := hG.smooth
  let t := baseChangeHom (K := k) (groupScheme I G i mu) I (torusHom I G i mu)
  let z := (GroupScheme.baseChange (algebraBaseMap R k)).map (inclusion I G i mu)
  have htz : t ≫ z = baseChangeHom (K := k) G I i := by
    dsimp only [t, z, baseChangeHom]
    rw [Category.assoc, ← Functor.map_comp, torusHom_comp]
  have hrep : (Dynamic.centralizer
      (CommGroupScheme.groupHom (exponentCocharacter (Spec (CommRingCat.of k)) I mu) ≫
        baseChangeHom (K := k) G I i)).IsRepresentedBy z :=
    isRepresentedBy_baseChangeInclusion I G i mu (algebraBaseMap R k)
  have ht : t = Dynamic.torusFactor (T := commGroupScheme _ I)
      (baseChangeHom (K := k) G I i)
      (CommGroupScheme.groupHom (exponentCocharacter _ I mu)) hrep := by
    apply hrep.hom_ext
    exact htz.trans (Dynamic.torusFactor_comp (T := commGroupScheme _ I)
      (baseChangeHom (K := k) G I i)
      (CommGroupScheme.groupHom (exponentCocharacter _ I mu)) hrep).symm
  change exponentCharacter _ I m ∈ roots (T := commGroupScheme _ I) t ↔ _
  rw [ht]
  simpa only [latticePairing_exponentCharacter_exponentCocharacter] using
    Dynamic.mem_roots_torusFactor_iff (T := commGroupScheme _ I)
      (baseChangeHom (K := k) G I i) (exponentCocharacter _ I mu) hrep
      (exponentCharacter _ I m)

variable {J : Type u} {P : RootDatum J (I → ℤ) (I → ℤ)}

/-- A generic kernel exponent gives exactly the two specified opposite roots
on every actual field fibre of the relative centralizer. -/
theorem mem_roots_baseChangeHom_iff_eq_or_neg (hG : IsReductive G)
    (hP : IsFibrewiseRootDatumOf I G i P) (a : J)
    (ha : ∑ j, P.root a j * mu j = 0)
    (hmu : ∀ b : J, ∑ j, P.root b j * mu j = 0 →
      P.root b = P.root a ∨ P.root b = -P.root a) (m : I → ℤ) :
    exponentCharacter (Spec (CommRingCat.of k)) I m ∈
        roots (T := commGroupScheme _ I)
          (baseChangeHom (K := k) (groupScheme I G i mu) I (torusHom I G i mu)) ↔
      m = P.root a ∨ m = -P.root a := by
  rw [mem_roots_baseChangeHom_iff i mu k hG, hP.mem_roots_iff k]
  constructor
  · rintro ⟨⟨b, rfl⟩, hb⟩
    exact hmu b hb
  · rintro (rfl | rfl)
    · exact ⟨⟨a, rfl⟩, ha⟩
    · refine ⟨⟨P.reflectionPerm a a, ?_⟩, ?_⟩
      · rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self]
      · simpa only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, neg_zero] using
          congrArg Neg.neg ha

end Field

end splitTorus.RelativeCocharacterCentralizer

end Langlands.GroupScheme
