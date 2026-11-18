import Langlands.GroupScheme.OuterIsomorphismSchemeOrbit
import Langlands.GroupScheme.RelativeInnerForm
import Langlands.AlgebraicGeometry.SchemeFlatPropertyDescent
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Geometry forced by the exact outer-isomorphism orbit condition -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.OuterIsomorphismScheme

variable {S : Scheme.{u}} {G H A : GroupScheme S}
  {I : GroupIsomorphismScheme G H} {a : AutomorphicAction A G}
  (O : OuterIsomorphismScheme I a)

/-- Over a family of represented classes, the outer map is the projection
from the product with the acting group. -/
theorem isPullback_of_point {U : Over S} (p : U ⟶ I.parameter) :
    IsPullback (lift (prod.fst : A.X ⨯ U ⟶ A.X) (prod.snd ≫ p) ≫ I.actionHom a)
      prod.snd O.classMap (p ≫ O.classMap) := by
  let := I.modObj a
  have hw : (lift (prod.fst : A.X ⨯ U ⟶ A.X) (prod.snd ≫ p) ≫ I.actionHom a) ≫
      O.classMap = prod.snd ≫ (p ≫ O.classMap) := by
    rw [O.invariant, Category.assoc]
  refine ⟨⟨hw⟩, ⟨PullbackCone.isLimitAux' _ (fun s => ?_)⟩⟩
  let h := O.orbit s.pt (s.snd ≫ p) s.fst
    (by simpa only [Category.assoc] using s.condition.symm)
  let d := h.choose
  have hd := h.choose_spec.1
  have hu := h.choose_spec.2
  refine ⟨prod.lift d s.snd, ?_, prod.lift_snd _ _, ?_⟩
  · change prod.lift d s.snd ≫
      (lift (prod.fst : A.X ⨯ U ⟶ A.X) (prod.snd ≫ p) ≫ I.actionHom a) = s.fst
    rw [← Category.assoc, comp_lift, prod.lift_fst, prod.lift_snd_assoc]
    exact hd
  · intro m hm₁ hm₂
    change s.pt ⟶ A.X ⨯ U at m
    apply prod.hom_ext (X := A.X) (Y := U)
    · rw [prod.lift_fst]
      apply hu
      change m ≫ prod.snd = s.snd at hm₂
      change m ≫ (lift (prod.fst : A.X ⨯ U ⟶ A.X) (prod.snd ≫ p) ≫
        I.actionHom a) = s.fst at hm₁
      rw [← Category.assoc, comp_lift, ← Category.assoc, hm₂] at hm₁
      exact hm₁
    · exact hm₂.trans (prod.lift_snd d s.snd).symm

/-- Every base-change-stable property satisfying fpqc target descent transfers
from the acting group to the outer class morphism. -/
theorem classMap_property (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange]
    [P.DescendsAlong (@Surjective.{u} ⊓ @Flat.{u} ⊓ @QuasiCompact.{u})]
    (hA : P A.X.hom) : P O.classMap.left := by
  have hpb := (O.isPullback_of_point (𝟙 I.parameter)).map (Over.forget S)
  simp only [Category.id_comp] at hpb
  apply MorphismProperty.of_isPullback_of_descendsAlong
    (P := P) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hpb.flip
    ⟨⟨O.surjective, O.flat⟩, O.quasiCompact⟩
  exact P.of_isPullback
    (Over.isPullback_of_binaryFan_isLimit
      (BinaryFan.mk (prod.fst : A.X ⨯ I.parameter ⟶ A.X) prod.snd)
      (prodIsProd A.X I.parameter)) hA

/-- An affine acting group makes the outer class map affine. -/
theorem affine [IsAffineHom A.X.hom] : IsAffineHom O.classMap.left :=
  O.classMap_property (@IsAffineHom.{u}) inferInstance

/-- A smooth acting group makes the outer class map smooth. -/
theorem smooth [Smooth A.X.hom] : Smooth O.classMap.left :=
  O.classMap_property (@Smooth.{u}) inferInstance

/-- Local finite presentation of the acting group passes to the class map. -/
theorem locallyOfFinitePresentation [LocallyOfFinitePresentation A.X.hom] :
    LocallyOfFinitePresentation O.classMap.left :=
  O.classMap_property (@LocallyOfFinitePresentation.{u}) inferInstance

/-- The inverse-precomposition orbit through a global isomorphism family. -/
abbrev orbitMap (O : OuterIsomorphismScheme I a)
    (p : Over.mk (𝟙 S) ⟶ I.parameter) : A.X ⟶ I.parameter :=
  O.pointOrbit p

/-- A global orbit is exactly the pullback over its outer-class section. -/
theorem orbitMap_isPullback (p : Over.mk (𝟙 S) ⟶ I.parameter) :
    IsPullback (O.orbitMap p) (toUnit A.X) O.classMap (p ≫ O.classMap) := by
  have hw : O.orbitMap p ≫ O.classMap = toUnit A.X ≫ (p ≫ O.classMap) := by
    rw [orbitMap, pointOrbit, O.invariant, Category.assoc]
  refine ⟨⟨hw⟩, ⟨PullbackCone.isLimitAux' _ (fun s => ?_)⟩⟩
  let h := O.orbit s.pt (s.snd ≫ p) s.fst
    (by simpa only [Category.assoc] using s.condition.symm)
  let d := h.choose
  have hd := h.choose_spec.1
  have hu := h.choose_spec.2
  refine ⟨d, ?_, toUnit_unique _ _, ?_⟩
  · change d ≫ O.orbitMap p = s.fst
    rw [orbitMap, pointOrbit, ← Category.assoc, comp_lift, Category.comp_id, comp_toUnit_assoc,
      toUnit_unique (toUnit s.pt) s.snd]
    exact hd
  · intro m hm₁ hm₂
    change s.pt ⟶ A.X at m
    apply hu
    change m ≫ O.orbitMap p = s.fst at hm₁
    rw [orbitMap, pointOrbit, ← Category.assoc, comp_lift, Category.comp_id, comp_toUnit_assoc,
      toUnit_unique (toUnit s.pt) s.snd] at hm₁
    exact hm₁

/-- Orbits through global sections are closed when the outer parameter is
separated over the base. -/
theorem orbitMap_isClosedImmersion [IsSeparated O.parameter.hom]
    (p : Over.mk (𝟙 S) ⟶ I.parameter) : IsClosedImmersion (O.orbitMap p).left :=
  O.pointOrbit_isClosedImmersion p

/-- The positive twist differs from inverse-precomposition by inversion in A. -/
theorem classify_twist_eq_inv_orbitMap (e : LocalGroupIso G H (Over.mk (𝟙 S))) :
    I.classify ((e.refine (toUnit A.X)).twist a (𝟙 A.X)) =
      ι[A.X] ≫ O.orbitMap (I.classify e) := by
  apply I.hom_ext
  intro W t g
  have he := congrArg
    (fun f : LocalGroupIso G H A.X => f.toFun t g)
    (I.refine_classify ((e.refine (toUnit A.X)).twist a (𝟙 A.X)))
  have hp := congrArg
    (fun f : LocalGroupIso G H (Over.mk (𝟙 S)) =>
      f.toFun (toUnit W) (a.act t g)) (I.refine_classify e)
  change I.universalIso.toFun (t ≫ I.classify _) g =
    e.toFun (t ≫ toUnit A.X) (a.act (t ≫ 𝟙 A.X) g) at he
  simp only [orbitMap, pointOrbit, ← Category.assoc, comp_lift, Category.comp_id]
  rw [I.actionHom_eval]
  simp only [Hom.inv_def, Category.assoc, GrpObj.inv_comp_inv, Category.comp_id,
    comp_toUnit_assoc]
  apply Eq.trans ?_ hp.symm
  simpa only [comp_toUnit, Category.comp_id] using he

/-- In particular, the positive inner-family inclusion is a closed immersion. -/
theorem classify_twist_isClosedImmersion [IsSeparated O.parameter.hom]
    (e : LocalGroupIso G H (Over.mk (𝟙 S))) :
    IsClosedImmersion
      (I.classify ((e.refine (toUnit A.X)).twist a (𝟙 A.X))).left := by
  rw [O.classify_twist_eq_inv_orbitMap, Over.comp_left]
  let : IsIso (ι[A.X]).left := (Over.forget S).map_isIso ι[A.X]
  let : IsClosedImmersion (O.orbitMap (I.classify e)).left :=
    O.orbitMap_isClosedImmersion _
  infer_instance

/-- The positive inner-automorphism map in the relative reductive geometry
statement is closed as soon as its outer parameter is separated. -/
theorem inner_isClosedImmersion {I : GroupIsomorphismScheme G G}
    (O : OuterIsomorphismScheme I a) [IsSeparated O.parameter.hom] :
    IsClosedImmersion (I.classify
      ((LocalGroupIso.ofIso (Iso.refl G) A.X).twist a (𝟙 A.X))).left :=
  O.classify_twist_isClosedImmersion (LocalGroupIso.ofIso (Iso.refl G) (Over.mk (𝟙 S)))

end Langlands.GroupScheme.OuterIsomorphismScheme
