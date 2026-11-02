import Langlands.AlgebraicGeometry.AlgebraicSpace.ExtensionProduct

/-! # The zero section and diagonal of a presheaf of abelian groups -/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.GroupIdentity

variable {S : Scheme.{u}} (G : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})

/-- The underlying full presheaf. -/
abbrev underlying : Presheaf S := G ⋙ forget AddCommGrpCat

/-- The terminal scheme over the base. -/
abbrev base : Over S := Over.mk (𝟙 S)

/-- The structure map of the full presheaf to the represented base. -/
def toBase : underlying G ⟶ (schemeYoneda S).obj (base (S := S)) where
  app T := TypeCat.ofHom fun _ ↦ ULift.up (Over.mkIdTerminal.from T.unop)
  naturality T T' f := by
    ext x
    apply ULift.ext
    exact Over.mkIdTerminal.hom_ext _ _

/-- The actual zero section over the represented base. -/
def zero : (schemeYoneda S).obj (base (S := S)) ⟶ underlying G where
  app T := TypeCat.ofHom fun _ ↦ (0 : G.obj T)
  naturality T T' f := by
    ext x
    change (0 : G.obj T') = G.map f (0 : G.obj T)
    rw [map_zero]

/-- Subtraction on the full presheaf, with elementwise product source. -/
def difference : FunctorToTypes.prod (underlying G) (underlying G) ⟶ underlying G where
  app T := TypeCat.ofHom fun z ↦ (show G.obj T from z.1) - (show G.obj T from z.2)
  naturality T T' f := by
    ext z
    change (show G.obj T' from G.map f z.1) - (show G.obj T' from G.map f z.2) =
      G.map f ((show G.obj T from z.1) - (show G.obj T from z.2))
    rw [map_sub]

/-- The diagonal is the pullback of the zero section along subtraction. -/
theorem isPullback_difference :
    IsPullback (toBase G) (diagPair (underlying G)) (zero G) (difference G) := by
  apply isPullback_of_elements
  · intro T x
    exact (sub_self (show G.obj T from x)).symm
  · intro T x y _ h
    exact congrArg Prod.fst h
  · intro T a z h
    refine ⟨z.1, ?_, ?_⟩
    · apply ULift.ext
      exact Over.mkIdTerminal.hom_ext _ _
    · change (0 : G.obj T) = (show G.obj T from z.1) - (show G.obj T from z.2) at h
      have hz : (show G.obj T from z.1) = z.2 := sub_eq_zero.mp h.symm
      exact Prod.ext rfl hz

/-- Pair a section with the zero section over the same test scheme. -/
def zeroGraph : underlying G ⟶ FunctorToTypes.prod (underlying G) (underlying G) :=
  FunctorToTypes.prod.lift (𝟙 _) (toBase G ≫ zero G)

/-- The zero section is the pullback of the diagonal along the zero graph. -/
theorem isPullback_zeroGraph :
    IsPullback (zero G) (zero G) (diagPair (underlying G)) (zeroGraph G) := by
  apply isPullback_of_elements
  · intro T a
    rfl
  · intro T a b _ _
    apply ULift.ext
    exact Over.mkIdTerminal.hom_ext _ _
  · intro T x y h
    have hxy : x = y := congrArg Prod.fst h
    have hx : x = (0 : G.obj T) := congrArg Prod.snd h
    refine ⟨ULift.up (Over.mkIdTerminal.from T.unop), hx.symm, ?_⟩
    exact hx.symm.trans hxy

attribute [local instance] MorphismProperty.relative_isStableUnderBaseChange

/-- Any relative scheme-morphism property of the diagonal is equivalent to the
same property of the zero section. The property need only respect isomorphisms. -/
theorem relative_diag_iff_zero (P : MorphismProperty Scheme.{u}) [P.RespectsIso] :
    (P.inverseImage (Over.forget S)).relative (schemeYoneda S) (diag (underlying G)) ↔
      (P.inverseImage (Over.forget S)).relative (schemeYoneda S) (zero G) := by
  let := MorphismProperty.RespectsIso.inverseImage P (Over.forget S)
  let Q := (P.inverseImage (Over.forget S)).relative (schemeYoneda S)
  have hd : Q (diag (underlying G)) ↔ Q (diagPair (underlying G)) := by
    rw [← diag_comp_binaryProductIso]
    exact (MorphismProperty.cancel_right_of_respectsIso Q _ _).symm
  change Q (diag (underlying G)) ↔ Q (zero G)
  rw [hd]
  exact ⟨fun h ↦ MorphismProperty.of_isPullback (isPullback_zeroGraph G) h,
    fun h ↦ MorphismProperty.of_isPullback (isPullback_difference G) h⟩

/-- The full presheaf diagonal is a closed immersion exactly when its zero
section is a closed immersion. -/
theorem isClosedImmersion_diag_iff_zero :
    IsClosedImmersion (diag (underlying G)) ↔ IsClosedImmersion (zero G) :=
  relative_diag_iff_zero G @_root_.AlgebraicGeometry.IsClosedImmersion.{u}

end Langlands.AlgebraicGeometry.AlgebraicSpace.GroupIdentity
