import Langlands.GroupScheme.Cartier.RelativeHomFunctoriality
import Langlands.AbelianScheme.RelativeIntegralActionLocusGeometry

/-! # Finite equalities of actual relative homomorphisms -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u uI

namespace Langlands.GroupScheme.Cartier

variable {S : Scheme.{u}} [IsLocallyNoetherian S]
    (G H : CommGroupScheme S) {I : Type uI} [Finite I]
    (E : Over S)
    (e : (Langlands.AbelianScheme.locallyNoetherianTestInclusion S).op ⋙
        relativeHomFunctor G H ⋙ forget AddCommGrpCat.{u} ≅
      (Langlands.AbelianScheme.locallyNoetherianTestInclusion S).op ⋙ yoneda.obj E)

private abbrev identityTest :
    ObjectProperty.FullSubcategory (fun T : Over S => IsLocallyNoetherian T.left) :=
  ⟨Over.mk (𝟙 S), by change IsLocallyNoetherian S; infer_instance⟩

/-- Encode a finite family of global homomorphisms as a section of a relative Hom power. -/
def relativeHomEquationSection (p : I → (G ⟶ H)) :
    Over.mk (𝟙 S) ⟶ ∏ᶜ fun _ : I => E :=
  Pi.lift fun i => e.hom.app (op (identityTest (S := S)))
    ((CommGroupScheme.baseChange (𝟙 S)).map (p i))

/-- Decoding a restricted section gives the actual base change of each homomorphism. -/
theorem relativeHomEquationSection_decode (p : I → (G ⟶ H))
    (T : ObjectProperty.FullSubcategory (fun T : Over S => IsLocallyNoetherian T.left))
    (f : T.obj ⟶ Over.mk (𝟙 S)) (i : I) :
    e.inv.app (op T)
        ((f ≫ relativeHomEquationSection G H E e p) ≫ Pi.π (fun _ : I => E) i) =
      (CommGroupScheme.baseChange T.obj.hom).map (p i) := by
  simp only [relativeHomEquationSection, Category.assoc, Pi.lift_comp_π]
  have h := e.inv.naturality_apply (CD := fun X => X)
    (ObjectProperty.homMk (X := T) (Y := identityTest (S := S)) f).op
    (e.hom.app (op (identityTest (S := S)))
      ((CommGroupScheme.baseChange (𝟙 S)).map (p i)))
  change e.inv.app (op T)
      (f ≫ e.hom.app (op (identityTest (S := S)))
        ((CommGroupScheme.baseChange (𝟙 S)).map (p i))) =
    restrict G H f
      ((e.app (op (identityTest (S := S)))).toEquiv.symm
        ((e.app (op (identityTest (S := S)))).toEquiv
          ((CommGroupScheme.baseChange (𝟙 S)).map (p i)))) at h
  rw [Equiv.symm_apply_apply] at h
  exact h.trans (restrict_baseChange_map (p i) f)

/-- Equality of the finite section maps detects exactly the actual pullback equalities. -/
theorem relativeHomEquation_condition_iff (p q : I → (G ⟶ H))
    (T : ObjectProperty.FullSubcategory (fun T : Over S => IsLocallyNoetherian T.left))
    (f : T.obj ⟶ Over.mk (𝟙 S)) :
    f ≫ relativeHomEquationSection G H E e p =
        f ≫ relativeHomEquationSection G H E e q ↔
      ∀ i, (CommGroupScheme.baseChange T.obj.hom).map (p i) =
        (CommGroupScheme.baseChange T.obj.hom).map (q i) := by
  constructor
  · intro h i
    have hi := congrArg
      (fun k => e.inv.app (op T) (k ≫ Pi.π (fun _ : I => E) i)) h
    simpa only [relativeHomEquationSection_decode] using hi
  · intro h
    apply Pi.hom_ext
    intro i
    apply (e.app (op T)).toEquiv.symm.injective
    change e.inv.app (op T) ((f ≫ relativeHomEquationSection G H E e p) ≫
        Pi.π (fun _ : I => E) i) =
      e.inv.app (op T) ((f ≫ relativeHomEquationSection G H E e q) ≫
        Pi.π (fun _ : I => E) i)
    simpa only [relativeHomEquationSection_decode] using h i

/-- The actual equalizer in schemes over the base of two finite Hom sections. -/
abbrev relativeHomEquationLocus (p q : I → (G ⟶ H)) : Over S :=
  equalizer (relativeHomEquationSection G H E e p)
    (relativeHomEquationSection G H E e q)

/-- The equation locus inclusion into the base. -/
def relativeHomEquationLocusInclusion (p q : I → (G ⟶ H)) :
    relativeHomEquationLocus G H E e p q ⟶ Over.mk (𝟙 S) :=
  equalizer.ι _ _

instance relativeHomEquationLocusInclusion_isClosedImmersion
    (p q : I → (G ⟶ H)) [IsSeparated E.hom] :
    IsClosedImmersion (relativeHomEquationLocusInclusion G H E e p q).left := by
  have := Langlands.AbelianScheme.relativeEndomorphismPower_isSeparated (I := I) E
  exact isClosedImmersion_equalizer_ι_left _ _

/-- A separated Hom representative makes the equation locus a closed subscheme of the base. -/
instance relativeHomEquationLocus_isClosedImmersion
    (p q : I → (G ⟶ H)) [IsSeparated E.hom] :
    IsClosedImmersion (relativeHomEquationLocus G H E e p q).hom := by
  have h : (relativeHomEquationLocusInclusion G H E e p q).left =
      (relativeHomEquationLocus G H E e p q).hom := by
    exact (Category.comp_id (obj := Scheme.{u}) _).symm.trans
      (Over.w (relativeHomEquationLocusInclusion G H E e p q))
  rw [← h]
  infer_instance

instance relativeHomEquationLocus_isLocallyNoetherian
    (p q : I → (G ⟶ H)) [IsSeparated E.hom] :
    IsLocallyNoetherian (relativeHomEquationLocus G H E e p q).left :=
  LocallyOfFiniteType.isLocallyNoetherian (relativeHomEquationLocus G H E e p q).hom

/-- The equalizer classifies the actual finite equalities on every locally noetherian test. -/
def relativeHomEquationLocusHomEquiv (p q : I → (G ⟶ H))
    (T : ObjectProperty.FullSubcategory (fun T : Over S => IsLocallyNoetherian T.left)) :
    (T.obj ⟶ relativeHomEquationLocus G H E e p q) ≃
      {_f : T.obj ⟶ Over.mk (𝟙 S) //
        ∀ i, (CommGroupScheme.baseChange T.obj.hom).map (p i) =
          (CommGroupScheme.baseChange T.obj.hom).map (q i)} where
  toFun f := ⟨f ≫ equalizer.ι _ _,
    (relativeHomEquation_condition_iff G H E e p q T (f ≫ equalizer.ι _ _)).1 (by
      simpa only [Category.assoc] using
        congrArg (fun k => f ≫ k) (equalizer.condition
          (relativeHomEquationSection G H E e p) (relativeHomEquationSection G H E e q)))⟩
  invFun f := equalizer.lift f.val
    ((relativeHomEquation_condition_iff G H E e p q T f.val).2 f.property)
  left_inv f := by
    apply equalizer.hom_ext
    simp only [equalizer.lift_ι]
  right_inv f := by
    apply Subtype.ext
    simp only [equalizer.lift_ι]

/-- A map to the equation locus exists precisely when all pullback equalities hold. -/
theorem relativeHomEquationLocus_nonempty_iff (p q : I → (G ⟶ H))
    (T : ObjectProperty.FullSubcategory (fun T : Over S => IsLocallyNoetherian T.left)) :
    Nonempty (T.obj ⟶ relativeHomEquationLocus G H E e p q) ↔
      ∀ i, (CommGroupScheme.baseChange T.obj.hom).map (p i) =
        (CommGroupScheme.baseChange T.obj.hom).map (q i) := by
  constructor
  · rintro ⟨f⟩
    exact (relativeHomEquationLocusHomEquiv G H E e p q T f).property
  · intro h
    exact ⟨(relativeHomEquationLocusHomEquiv G H E e p q T).symm
      ⟨Over.mkIdTerminal.from T.obj, h⟩⟩

end Langlands.GroupScheme.Cartier
