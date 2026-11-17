import Langlands.GroupScheme.OuterIsomorphismScheme
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.CategoryTheory.Yoneda

/-! # Orbits through global points of a supplied outer quotient -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.OuterIsomorphismScheme

variable {S : Scheme.{u}} {G H A : GroupScheme S}
  {I : GroupIsomorphismScheme G H} {a : AutomorphicAction A G}
  (O : OuterIsomorphismScheme I a) (p : Over.mk (𝟙 S) ⟶ I.parameter)

/-- The inverse-precomposition orbit through a global isomorphism point. -/
def pointOrbit (_O : OuterIsomorphismScheme I a)
    (p : Over.mk (𝟙 S) ⟶ I.parameter) : A.X ⟶ I.parameter :=
  lift (𝟙 A.X) (toUnit A.X ≫ p) ≫ I.actionHom a

theorem comp_pointOrbit {T : Over S} (d : T ⟶ A.X) :
    d ≫ O.pointOrbit p = lift d (toUnit T ≫ p) ≫ I.actionHom a := by
  simp only [pointOrbit, comp_lift_assoc, Category.comp_id, comp_toUnit_assoc]

@[reassoc] theorem pointOrbit_classMap :
    O.pointOrbit p ≫ O.classMap = toUnit A.X ≫ (p ≫ O.classMap) := by
  exact (O.invariant A.X (𝟙 A.X) (toUnit A.X ≫ p)).trans (Category.assoc _ _ _)

/-- The orbit lies in the actual outer fibre of the specified global point. -/
def pointOrbitLift : A.X ⟶ O.fibre (p ≫ O.classMap) :=
  O.fibrePoint (p ≫ O.classMap) (O.pointOrbit p) (O.pointOrbit_classMap p)

@[reassoc] theorem pointOrbitLift_projection :
    O.pointOrbitLift p ≫ O.fibreProjection (p ≫ O.classMap) = O.pointOrbit p :=
  ActionFibre.pointLift_projection O.classMap (p ≫ O.classMap)
    (O.pointOrbit p) (O.pointOrbit_classMap p)

/-- Unique all-test inner differences identify the acting scheme with the
outer fibre through any supplied global point. -/
instance pointOrbitLift_isIso : IsIso (O.pointOrbitLift p) := by
  apply isIso_of_yoneda_map_bijective
  intro T
  constructor
  · intro d e h
    have hde : d ≫ O.pointOrbit p = e ≫ O.pointOrbit p := by
      simpa only [Category.assoc, O.pointOrbitLift_projection] using
        congrArg (fun f => f ≫ O.fibreProjection (p ≫ O.classMap)) h
    have hc : (toUnit T ≫ p) ≫ O.classMap =
        (d ≫ O.pointOrbit p) ≫ O.classMap := by
      rw [Category.assoc, Category.assoc, O.pointOrbit_classMap,
        comp_toUnit_assoc]
    obtain ⟨r, _, hu⟩ := O.orbit T (toUnit T ≫ p) (d ≫ O.pointOrbit p) hc
    exact (hu d (O.comp_pointOrbit p d).symm).trans
      (hu e ((O.comp_pointOrbit p e).symm.trans hde.symm)).symm
  · intro y
    have hc : (toUnit T ≫ p) ≫ O.classMap =
        (y ≫ O.fibreProjection (p ≫ O.classMap)) ≫ O.classMap := by
      have hf := ActionFibre.projection_comp O.classMap (p ≫ O.classMap)
      change O.fibreProjection (p ≫ O.classMap) ≫ O.classMap =
        toUnit (O.fibre (p ≫ O.classMap)) ≫ (p ≫ O.classMap) at hf
      simpa only [Category.assoc, comp_toUnit_assoc] using
        (congrArg (fun f => y ≫ f) hf).symm
    obtain ⟨d, hd, _⟩ := O.orbit T (toUnit T ≫ p)
      (y ≫ O.fibreProjection (p ≫ O.classMap)) hc
    refine ⟨d, ?_⟩
    apply ActionFibre.hom_ext O.classMap (p ≫ O.classMap)
    change (d ≫ O.pointOrbitLift p) ≫ O.fibreProjection (p ≫ O.classMap) =
      y ≫ O.fibreProjection (p ≫ O.classMap)
    rw [Category.assoc, O.pointOrbitLift_projection, O.comp_pointOrbit]
    exact hd

theorem fibreProjection_isOpenImmersion [Etale O.parameter.hom] :
    IsOpenImmersion (O.fibreProjection (p ≫ O.classMap)).left := by
  let s : Over.mk (𝟙 S) ⟶ O.parameter := p ≫ O.classMap
  let : MorphismProperty.HasOfPostcompProperty @IsOpenImmersion @Etale :=
    MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr
      (fun _ _ f _ => inferInstanceAs (IsOpenImmersion (pullback.diagonal f)))
  have hs : s.left ≫ O.parameter.hom = 𝟙 S := Over.w s
  have : IsOpenImmersion (s.left ≫ O.parameter.hom) := by
    rw [hs]
    exact inferInstanceAs (IsOpenImmersion (𝟙 (S : Scheme.{u})))
  have : IsOpenImmersion s.left :=
    MorphismProperty.of_postcomp @IsOpenImmersion s.left O.parameter.hom ‹_› ‹_›
  change IsOpenImmersion (pullback.fst O.classMap.left s.left)
  infer_instance

theorem fibreProjection_isClosedImmersion [IsSeparated O.parameter.hom] :
    IsClosedImmersion (O.fibreProjection (p ≫ O.classMap)).left := by
  let s : Over.mk (𝟙 S) ⟶ O.parameter := p ≫ O.classMap
  have hs : s.left ≫ O.parameter.hom = 𝟙 S := Over.w s
  have : IsClosedImmersion (s.left ≫ O.parameter.hom) := by
    rw [hs]
    exact inferInstanceAs (IsClosedImmersion (𝟙 (S : Scheme.{u})))
  have : IsClosedImmersion s.left := IsClosedImmersion.of_comp s.left O.parameter.hom
  change IsClosedImmersion (pullback.fst O.classMap.left s.left)
  infer_instance

/-- An étale outer parameter makes each global inner orbit open. -/
theorem pointOrbit_isOpenImmersion [Etale O.parameter.hom] :
    IsOpenImmersion (O.pointOrbit p).left := by
  have : IsIso (O.pointOrbitLift p).left :=
    (Over.forget S).map_isIso (O.pointOrbitLift p)
  have := O.fibreProjection_isOpenImmersion p
  rw [← O.pointOrbitLift_projection p]
  change IsOpenImmersion ((O.pointOrbitLift p).left ≫
    (O.fibreProjection (p ≫ O.classMap)).left)
  infer_instance

/-- A separated outer parameter makes each global inner orbit closed. -/
theorem pointOrbit_isClosedImmersion [IsSeparated O.parameter.hom] :
    IsClosedImmersion (O.pointOrbit p).left := by
  have : IsIso (O.pointOrbitLift p).left :=
    (Over.forget S).map_isIso (O.pointOrbitLift p)
  have := O.fibreProjection_isClosedImmersion p
  rw [← O.pointOrbitLift_projection p]
  change IsClosedImmersion ((O.pointOrbitLift p).left ≫
    (O.fibreProjection (p ≫ O.classMap)).left)
  infer_instance

end Langlands.GroupScheme.OuterIsomorphismScheme
