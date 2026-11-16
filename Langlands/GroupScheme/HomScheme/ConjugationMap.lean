import Langlands.GroupScheme.HomScheme.Universal
import Langlands.GroupScheme.RelativeLevi.ModuliConjugation
import Langlands.GroupScheme.Rational.TorusNormalizer
import Langlands.GroupScheme.Torus.MaximalBaseChangeForwardReduction

/-! # Actual conjugation families in relative Hom schemes -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.HomScheme
open TorusSubgroupModuli

variable {S : Scheme.{u}} {H G : GroupScheme S} {M T : Over S}

/-- Relative Hom evaluation commutes with the actual family point adjunction. -/
theorem familyPointsEquiv_comp_evaluate (a : T ⟶ M) (f : RelativeHom H G M)
    (V : Over T.left) (x : V ⟶ ((baseChange T.hom).obj H).X) :
    familyPointsEquiv (G := G) a V (x ≫ (evaluate a f).hom.hom) =
      familyPointsEquiv (G := H) a V x ≫ f.hom.hom := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [Over.comp_left, Category.assoc, familyPointsEquiv_original,
      evaluate_fst]
    have hx : x.left ≫ baseChangeProj H a =
        (familyPointsEquiv (G := H) a V x).left := by
      apply pullback.hom_ext
      · simp only [Category.assoc, baseChangeProj_fst, familyPointsEquiv_original]
      · rw [Category.assoc, baseChangeProj_snd, ← Category.assoc]
        change (x.left ≫ ((baseChange T.hom).obj H).X.hom) ≫ a.left =
          (familyPointsEquiv (G := H) a V x).left ≫ ((baseChange M.hom).obj H).X.hom
        rw [Over.w x, Over.w]
        rfl
    rw [← Category.assoc x.left, hx]
  · exact (Over.w _).trans (Over.w _).symm

/-- Pullback of a fixed homomorphism is the constant relative family. -/
@[simp]
theorem evaluate_baseChange (a : T ⟶ M) (f : H ⟶ G) :
    evaluate a ((baseChange M.hom).map f) = (baseChange T.hom).map f := by
  apply relativeHom_ext
  rw [evaluate_fst]
  change baseChangeProj H a ≫ ((Over.pullback M.hom).map f.hom.hom).left ≫
      pullback.fst G.X.hom M.hom =
    ((Over.pullback T.hom).map f.hom.hom).left ≫ pullback.fst G.X.hom T.hom
  simp only [Over.pullback_map_left, pullback.lift_fst,
    baseChangeProj_fst_assoc]

/-- Conjugating a fixed homomorphism by a test-valued point gives an actual
relative group homomorphism. -/
def conjugationFamily (f : H ⟶ G) (g : T ⟶ G.X) : RelativeHom H G T :=
  (baseChange T.hom).map f ≫
    (((baseChange T.hom).obj G).innerIso (RelativeLevi.pulledBackPoint G T g)).hom

/-- Conjugation families commute with arbitrary parameter restriction. -/
theorem evaluate_conjugationFamily (f : H ⟶ G) (g : M ⟶ G.X) (a : T ⟶ M) :
    evaluate a (conjugationFamily f g) = conjugationFamily f (a ≫ g) := by
  apply hom_ext_points
  intro V x
  apply (familyPointsEquiv (G := G) a V).injective
  rw [familyPointsEquiv_comp_evaluate]
  change familyPointsEquiv (G := H) a V x ≫
      ((baseChange M.hom).map f).hom.hom ≫
        ((((baseChange M.hom).obj G).innerIso
          (RelativeLevi.pulledBackPoint G M g)).hom).hom.hom =
    familyPointsEquiv (G := G) a V (x ≫ ((baseChange T.hom).map f).hom.hom ≫
      ((((baseChange T.hom).obj G).innerIso
        (RelativeLevi.pulledBackPoint G T (a ≫ g))).hom).hom.hom)
  rw [← Category.assoc, comp_innerIso_hom, ← Category.assoc, comp_innerIso_hom,
    map_mul, map_mul, map_inv, RelativeLevi.familyPointsEquiv_constantPoint]
  congr 2
  rw [← evaluate_baseChange a f, familyPointsEquiv_comp_evaluate]

/-- A parameter morphism for the conjugation family in a supplied universal
relative Hom scheme. -/
def conjugationParameter (f : H ⟶ G) {Y : Over S} (i : RelativeHom H G Y)
    (hi : IsUniversal i) (g : T ⟶ G.X) : T ⟶ Y :=
  Classical.choose (hi.existsUnique (conjugationFamily f g))

@[simp]
theorem evaluate_conjugationParameter (f : H ⟶ G) {Y : Over S}
    (i : RelativeHom H G Y) (hi : IsUniversal i) (g : T ⟶ G.X) :
    evaluate (conjugationParameter f i hi g) i = conjugationFamily f g :=
  (Classical.choose_spec (hi.existsUnique (conjugationFamily f g))).1

/-- Parameters of conjugation families are natural on all test schemes. -/
theorem conjugationParameter_comp (f : H ⟶ G) {Y : Over S}
    (i : RelativeHom H G Y) (hi : IsUniversal i) (g : M ⟶ G.X) (a : T ⟶ M) :
    a ≫ conjugationParameter f i hi g = conjugationParameter f i hi (a ≫ g) := by
  apply (hi T).injective
  change evaluate (a ≫ conjugationParameter f i hi g) i =
    evaluate (conjugationParameter f i hi (a ≫ g)) i
  rw [evaluate_comp, evaluate_conjugationParameter, evaluate_conjugationParameter,
    evaluate_conjugationFamily]

/-- The base-point pullback equivalence preserves the exact subgroup condition. -/
theorem mem_baseChange_basePoints_iff {B : Scheme.{u}} (b : B ⟶ S)
    (F : SubgroupFunctor G)
    (p : Over.mk (𝟙 B) ⟶ ((baseChange b).obj G).X) :
    p ∈ (F.baseChange b).carrier (Over.mk (𝟙 B)) ↔
      baseChangeBasePointsEquiv b G p ∈ F.carrier (Over.mk b) := by
  let e : Over.mk b ≅ (Over.map b).obj (Over.mk (𝟙 B)) :=
    Over.isoMk (Iso.refl B) (by simp)
  change baseChangePointsEquiv b G (Over.mk (𝟙 B)) p ∈ F.carrier _ ↔
    e.hom ≫ baseChangePointsEquiv b G (Over.mk (𝟙 B)) p ∈ F.carrier _
  constructor
  · exact F.comp_mem e.hom
  · intro hp
    simpa only [← Category.assoc, e.inv_hom_id, Category.id_comp] using F.comp_mem e.inv hp

/-- Fixing a homomorphism by relative conjugation is precisely membership in
its all-test centralizer. -/
theorem conjugationFamily_eq_baseChange_iff {A : CommGroupScheme S}
    (f : A.toGrp ⟶ G) (g : T ⟶ G.X) :
    conjugationFamily f g = (baseChange T.hom).map f ↔
      g ∈ (torusCentralizer f).carrier T := by
  have hp := mem_torusCentralizer_base_iff
    (T := (CommGroupScheme.baseChange T.hom).obj A)
    ((baseChange T.hom).map f) (RelativeLevi.pulledBackPoint G T g)
  rw [torusCentralizer_baseChange, mem_baseChange_basePoints_iff,
    RelativeLevi.baseChangeBasePointsEquiv_pulledBackPoint] at hp
  exact hp.symm

/-- The fibers of conjugation on all tests are exactly centralizer cosets. -/
theorem conjugationFamily_eq_iff {A : CommGroupScheme S}
    (f : A.toGrp ⟶ G) (g h : T ⟶ G.X) :
    conjugationFamily f g = conjugationFamily f h ↔
      g⁻¹ * h ∈ (torusCentralizer f).carrier T := by
  rw [← conjugationFamily_eq_baseChange_iff]
  change (baseChange T.hom).map f ≫
      (((baseChange T.hom).obj G).innerIso (RelativeLevi.pulledBackPointHom G T g)).hom =
    (baseChange T.hom).map f ≫
      (((baseChange T.hom).obj G).innerIso (RelativeLevi.pulledBackPointHom G T h)).hom ↔
    (baseChange T.hom).map f ≫
      (((baseChange T.hom).obj G).innerIso
        (RelativeLevi.pulledBackPointHom G T (g⁻¹ * h))).hom = (baseChange T.hom).map f
  rw [map_mul, map_inv, innerIso_mul_hom, innerIso_inv_hom]
  constructor
  · intro he
    rw [← Category.assoc, ← he, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · intro he
    apply (cancel_mono
      (((baseChange T.hom).obj G).innerIso
        (RelativeLevi.pulledBackPointHom G T g)).inv).mp
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using he.symm

/-- Two actual Hom parameters agree if and only if the original points differ
by an all-test centralizer point. -/
theorem conjugationParameter_eq_iff {A : CommGroupScheme S}
    (f : A.toGrp ⟶ G) {Y : Over S} (i : RelativeHom A.toGrp G Y)
    (hi : IsUniversal i) (g h : T ⟶ G.X) :
    conjugationParameter f i hi g = conjugationParameter f i hi h ↔
      g⁻¹ * h ∈ (torusCentralizer f).carrier T := by
  rw [← conjugationFamily_eq_iff f g h]
  constructor
  · intro he
    have hh := congrArg (fun a => evaluate a i) he
    simpa only [evaluate_conjugationParameter] using hh
  · intro he
    apply (hi T).injective
    change evaluate (conjugationParameter f i hi g) i =
      evaluate (conjugationParameter f i hi h) i
    simpa only [evaluate_conjugationParameter] using he

end Langlands.GroupScheme.HomScheme
