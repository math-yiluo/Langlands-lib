import Langlands.AlgebraicGeometry.AlgebraicSpace.Thickening
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Products of presheaves with represented schemes

For a presheaf `F` on schemes over `S` and a scheme `Λ` over `S`, the product
`F × Y(Λ)` is the base change of `F` to `Λ`, still as a presheaf on schemes over `S`.
For a presheaf of commutative groups, sections over `Λ` act on it by translations.
-/

universe u w

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- An elementwise criterion for pullback squares of type-valued presheaves. -/
theorem isPullback_of_elements {C : Type*} [Category C] {P X Y Z : C ⥤ Type w}
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (w : ∀ T p, f.app T (fst.app T p) = g.app T (snd.app T p))
    (inj : ∀ T p p', fst.app T p = fst.app T p' → snd.app T p = snd.app T p' → p = p')
    (surj : ∀ T x y, f.app T x = g.app T y → ∃ p, fst.app T p = x ∧ snd.app T p = y) :
    IsPullback fst snd f g := by
  refine IsPullback.of_forall_isPullback_app fun T => ?_
  refine (Types.isPullback_iff _ _ _ _).mpr ⟨?_, fun p p' h => inj T p p' h.1 h.2, surj T⟩
  ext p
  exact w T p

variable {S : Scheme.{u}}

/-- The product presheaf `F × Y(Λ)`. -/
abbrev extProd (F : Presheaf S) (Λ : Over S) : Presheaf S :=
  FunctorToTypes.prod F ((schemeYoneda S).obj Λ)

namespace extProd

variable {F F' : Presheaf S} {Λ Λ' : Over S}

/-- The projection to the presheaf factor. -/
abbrev fst : extProd F Λ ⟶ F := FunctorToTypes.prod.fst

/-- The projection to the represented factor. -/
abbrev snd : extProd F Λ ⟶ (schemeYoneda S).obj Λ := FunctorToTypes.prod.snd

/-- Change of the represented factor along `ρ : Λ' ⟶ Λ`. -/
def mapRight (ρ : Λ' ⟶ Λ) : extProd F Λ' ⟶ extProd F Λ :=
  FunctorToTypes.prod.lift fst (snd ≫ (schemeYoneda S).map ρ)

@[simp]
lemma mapRight_app (ρ : Λ' ⟶ Λ) (T : (Over S)ᵒᵖ) (z : (extProd F Λ').obj T) :
    (mapRight ρ).app T z = (z.1, ULift.up (z.2.down ≫ ρ)) := rfl

lemma mapRight_comp {Λ'' : Over S} (ρ' : Λ'' ⟶ Λ') (ρ : Λ' ⟶ Λ) :
    (mapRight (F := F) ρ' ≫ mapRight ρ) = mapRight (ρ' ≫ ρ) := by
  ext T z
  · rfl
  · change ULift.up ((z.2.down ≫ ρ') ≫ ρ) = ULift.up (z.2.down ≫ ρ' ≫ ρ)
    rw [Category.assoc]

lemma mapRight_id : mapRight (F := F) (𝟙 Λ) = 𝟙 _ := by
  ext T z
  · rfl
  · change ULift.up (z.2.down ≫ 𝟙 Λ) = z.2
    simp

/-- Change of the represented factor along an isomorphism. -/
def mapRightIso (ε : Λ' ≅ Λ) : extProd F Λ' ≅ extProd F Λ where
  hom := mapRight ε.hom
  inv := mapRight ε.inv
  hom_inv_id := by rw [mapRight_comp, ε.hom_inv_id, mapRight_id]
  inv_hom_id := by rw [mapRight_comp, ε.inv_hom_id, mapRight_id]

/-- Change of the presheaf factor along `φ : F ⟶ F'`. -/
def mapLeft (φ : F ⟶ F') : extProd F Λ ⟶ extProd F' Λ :=
  FunctorToTypes.prod.lift (fst ≫ φ) snd

@[simp]
lemma mapLeft_app (φ : F ⟶ F') (T : (Over S)ᵒᵖ) (z : (extProd F Λ).obj T) :
    (mapLeft (Λ := Λ) φ).app T z = (φ.app T z.1, z.2) := rfl

/-- Change of the represented factor is a base change of the represented map. -/
theorem isPullback_mapRight (ρ : Λ' ⟶ Λ) :
    IsPullback (mapRight (F := F) ρ) snd snd ((schemeYoneda S).map ρ) := by
  apply isPullback_of_elements
  · intro T p
    rfl
  · intro T p p' h1 h2
    have h1' := congrArg Prod.fst h1
    exact Prod.ext h1' h2
  · intro T x y h
    refine ⟨(x.1, y), ?_, rfl⟩
    exact Prod.ext rfl h.symm

/-- Change of the presheaf factor is a base change of the presheaf map. -/
theorem isPullback_mapLeft (φ : F ⟶ F') :
    IsPullback (mapLeft (Λ := Λ) φ) fst fst φ := by
  apply isPullback_of_elements
  · intro T p
    rfl
  · intro T p p' h1 h2
    have h1' := congrArg Prod.snd h1
    exact Prod.ext h2 h1'
  · intro T x y h
    exact ⟨(y, x.2), Prod.ext h.symm rfl, rfl⟩

/-- The map from the scheme product `T ⨯ Λ` determined by a section of `F` over `T`. -/
def fstPullbackMap {T : Over S} (x : F.obj (op T)) :
    (schemeYoneda S).obj (T ⨯ Λ) ⟶ extProd F Λ where
  app T' := TypeCat.ofHom fun f ↦ (F.map (f.down ≫ prod.fst).op x, ULift.up (f.down ≫ prod.snd))
  naturality T₁ T₂ g := by
    ext f
    · change F.map ((g.unop ≫ f.down) ≫ prod.fst).op x = F.map g (F.map (f.down ≫ prod.fst).op x)
      rw [Category.assoc, op_comp, F.map_comp]
      rfl
    · change ULift.up ((g.unop ≫ f.down) ≫ prod.snd) = ULift.up (g.unop ≫ f.down ≫ prod.snd)
      rw [Category.assoc]

/-- The projection `F × Y(Λ) ⟶ F` has the represented pullback `T ⨯ Λ` along every
section over `T`. -/
theorem isPullback_fst {T : Over S} (x : F.obj (op T)) :
    IsPullback (fstPullbackMap (Λ := Λ) x) ((schemeYoneda S).map prod.fst) fst
      (uliftYonedaEquiv.symm x) := by
  apply isPullback_of_elements
  · intro T' f
    change F.map (f.down ≫ prod.fst).op x = F.map (f.down ≫ prod.fst).op x
    rfl
  · intro T' f f' h1 h2
    apply ULift.ext
    apply prod.hom_ext
    · exact congrArg ULift.down h2
    · exact congrArg ULift.down (congrArg Prod.snd h1)
  · intro T' z g h
    refine ⟨ULift.up (prod.lift g.down z.2.down), ?_, ?_⟩
    · refine Prod.ext ?_ ?_
      · change F.map (prod.lift g.down z.2.down ≫ prod.fst).op x = z.1
        rw [prod.lift_fst]
        exact h.symm
      · change ULift.up (prod.lift g.down z.2.down ≫ prod.snd) = z.2
        rw [prod.lift_snd]
    · change ULift.up (prod.lift g.down z.2.down ≫ prod.fst) = g
      rw [prod.lift_fst]

/-- A base-change-stable scheme property of `Λ ⟶ S` holds for the projection `T ⨯ Λ ⟶ T`. -/
theorem prod_fst_left (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    {T : Over S} (hΛ : P Λ.hom) : P (prod.fst : T ⨯ Λ ⟶ T).left := by
  have : P.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
  rw [← Over.prodLeftIsoPullback_hom_fst]
  exact (MorphismProperty.cancel_left_of_respectsIso P _ _).mpr (P.pullback_fst _ _ hΛ)

/-- Scheme morphisms into `(T ⨯ Λ).left` are determined by their two projections. -/
theorem prod_left_hom_ext {T : Over S} {Z : Scheme.{u}} {g h : Z ⟶ (T ⨯ Λ).left}
    (h₁ : g ≫ (prod.fst : T ⨯ Λ ⟶ T).left = h ≫ (prod.fst : T ⨯ Λ ⟶ T).left)
    (h₂ : g ≫ (prod.snd : T ⨯ Λ ⟶ Λ).left = h ≫ (prod.snd : T ⨯ Λ ⟶ Λ).left) : g = h := by
  rw [← cancel_mono (Over.prodLeftIsoPullback T Λ).hom]
  apply pullback.hom_ext
  · simpa [Over.prodLeftIsoPullback_hom_fst] using h₁
  · simpa [Over.prodLeftIsoPullback_hom_snd] using h₂

/-- A base-change-stable scheme property of `Λ ⟶ S` holds relatively for the projection
`F × Y(Λ) ⟶ F`. -/
theorem relative_fst (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    (hΛ : P Λ.hom) :
    (P.inverseImage (Over.forget S)).relative (schemeYoneda S) (fst : extProd F Λ ⟶ F) := by
  have : P.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
  apply MorphismProperty.relative.of_exists
  intro T g
  refine ⟨T ⨯ Λ, fstPullbackMap (uliftYonedaEquiv g), prod.fst, ?_, ?_⟩
  · simpa using isPullback_fst (Λ := Λ) (uliftYonedaEquiv g)
  · exact prod_fst_left P hΛ

/-- The isomorphism `Y(U ⨯ Λ) ≅ Y(U) × Y(Λ)`. -/
def yonedaProdIso (U : Over S) :
    (schemeYoneda S).obj (U ⨯ Λ) ≅ extProd ((schemeYoneda S).obj U) Λ where
  hom := FunctorToTypes.prod.lift ((schemeYoneda S).map prod.fst) ((schemeYoneda S).map prod.snd)
  inv :=
    { app T := TypeCat.ofHom fun z ↦ ULift.up (prod.lift z.1.down z.2.down)
      naturality T₁ T₂ g := by
        ext z
        change ULift.up (prod.lift (g.unop ≫ z.1.down) (g.unop ≫ z.2.down)) =
          ULift.up (g.unop ≫ prod.lift z.1.down z.2.down)
        congr 1
        apply prod.hom_ext <;> simp }
  hom_inv_id := by
    ext T f
    change ULift.up (prod.lift (f.down ≫ prod.fst) (f.down ≫ prod.snd)) = f
    apply ULift.ext
    apply prod.hom_ext <;> simp
  inv_hom_id := by
    ext T z
    · change ULift.up (prod.lift z.1.down z.2.down ≫ prod.fst) = z.1
      simp
    · change ULift.up (prod.lift z.1.down z.2.down ≫ prod.snd) = z.2
      simp

@[simp]
lemma yonedaProdIso_hom_app (U : Over S) (T : (Over S)ᵒᵖ) (f : ULift (T.unop ⟶ U ⨯ Λ)) :
    (yonedaProdIso (Λ := Λ) U).hom.app T f =
      (ULift.up (f.down ≫ prod.fst), ULift.up (f.down ≫ prod.snd)) := rfl

/-- The product of an fppf sheaf with a represented scheme is an fppf sheaf. -/
theorem isSheaf (hF : CategoryTheory.Presheaf.IsSheaf (fppfTopology S) F) :
    CategoryTheory.Presheaf.IsSheaf (fppfTopology S) (extProd F Λ) :=
  Sheaf.tensorProd_isSheaf (fppfTopology S) ⟨F, hF⟩ ((schemeSheaf S).obj Λ)

end extProd

section Diagonal

attribute [local instance] MorphismProperty.relative_isStableUnderBaseChange

local instance : (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsClosedImmersion.{u})
    (Over.forget S)).RespectsIso :=
  MorphismProperty.RespectsIso.inverseImage _ _

local instance : (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsClosedImmersion.{u})
    (Over.forget S)).IsStableUnderComposition := by
  have h : MorphismProperty.IsMultiplicative (@_root_.AlgebraicGeometry.IsClosedImmersion.{u}) :=
    inferInstance
  have : MorphismProperty.IsStableUnderComposition
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u}) := h.toIsStableUnderComposition
  exact MorphismProperty.IsStableUnderComposition.inverseImage
    (P := @_root_.AlgebraicGeometry.IsClosedImmersion.{u}) (Over.forget S)

/-- The elementwise diagonal `z ↦ (z, z)`. -/
abbrev diagPair (X : Presheaf S) : X ⟶ FunctorToTypes.prod X X :=
  FunctorToTypes.prod.lift (𝟙 X) (𝟙 X)

lemma diag_comp_binaryProductIso (X : Presheaf S) :
    Limits.diag X ≫ (FunctorToTypes.binaryProductIso X X).hom = diagPair X := by
  ext T x
  · have h := congrArg (fun f : X ⟶ X ↦ f.app T x)
      (show Limits.diag X ≫ (FunctorToTypes.binaryProductIso X X).hom ≫
          FunctorToTypes.prod.fst = 𝟙 X by simp)
    exact h
  · have h := congrArg (fun f : X ⟶ X ↦ f.app T x)
      (show Limits.diag X ≫ (FunctorToTypes.binaryProductIso X X).hom ≫
          FunctorToTypes.prod.snd = 𝟙 X by simp)
    exact h

/-- Closedness of the diagonal can be tested on the elementwise diagonal. -/
theorem isClosedImmersion_diag_iff (X : Presheaf S) :
    IsClosedImmersion (Limits.diag X) ↔ IsClosedImmersion (diagPair X) := by
  rw [← diag_comp_binaryProductIso]
  exact (MorphismProperty.cancel_right_of_respectsIso
    ((MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsClosedImmersion.{u})
      (Over.forget S)).relative (schemeYoneda S)) _ _).symm

/-- The Yoneda image of a closed immersion of schemes is a representable closed immersion. -/
theorem isClosedImmersion_schemeYoneda_map {V W : Over S} (p : V ⟶ W)
    (hp : _root_.AlgebraicGeometry.IsClosedImmersion p.left) :
    IsClosedImmersion ((schemeYoneda S).map p) := by
  apply MorphismProperty.relative.of_exists
  intro T g
  obtain ⟨g, rfl⟩ := (schemeYoneda S).map_surjective g
  let h := IsPullback.of_hasPullback p g
  exact ⟨_, _, _, h.map (schemeYoneda S),
    MorphismProperty.of_isPullback (P := @_root_.AlgebraicGeometry.IsClosedImmersion.{u})
      (h.map (Over.forget S)) hp⟩

/-- A separated scheme over the base has a representable closed-immersion diagonal. -/
theorem isClosedImmersion_diag_schemeYoneda (Λ : Over S) [IsSeparated Λ.hom] :
    IsClosedImmersion (Limits.diag ((schemeYoneda S).obj Λ)) := by
  have heq : (Limits.diag Λ).left ≫ (Over.prodLeftIsoPullback Λ Λ).hom =
      pullback.diagonal Λ.hom := by
    apply pullback.hom_ext <;> simp [← Over.comp_left]
  have hc : _root_.AlgebraicGeometry.IsClosedImmersion (Limits.diag Λ).left := by
    have : _root_.AlgebraicGeometry.IsClosedImmersion
        ((Limits.diag Λ).left ≫ (Over.prodLeftIsoPullback Λ Λ).hom) := by
      rw [heq]; infer_instance
    exact (MorphismProperty.cancel_right_of_respectsIso
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u}) _ _).mp this
  have hd : Limits.diag ((schemeYoneda S).obj Λ) =
      (schemeYoneda S).map (Limits.diag Λ) ≫ prodComparison (schemeYoneda S) Λ Λ := by
    apply Limits.prod.hom_ext <;> simp [prodComparison, ← Functor.map_comp]
  rw [hd]
  exact (MorphismProperty.cancel_right_of_respectsIso
    ((MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsClosedImmersion.{u})
      (Over.forget S)).relative (schemeYoneda S)) _ _).mpr
    (isClosedImmersion_schemeYoneda_map _ hc)

/-- Closedness of the diagonal is invariant under isomorphism of presheaves. -/
theorem isClosedImmersion_diag_of_iso {X Y : Presheaf S} (e : X ≅ Y)
    (h : IsClosedImmersion (Limits.diag Y)) : IsClosedImmersion (Limits.diag X) := by
  have hw : Limits.diag X = e.hom ≫ Limits.diag Y ≫ (prod.mapIso e e).inv := by
    rw [← Category.assoc, ← Limits.prod.diag_map, Category.assoc, ← prod.mapIso_hom,
      Iso.hom_inv_id, Category.comp_id]
  rw [hw]
  let P := (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsClosedImmersion.{u})
      (Over.forget S)).relative (schemeYoneda S)
  exact (MorphismProperty.cancel_left_of_respectsIso P _ _).mpr
    ((MorphismProperty.cancel_right_of_respectsIso P _ _).mpr h)

namespace extProd

variable {F : Presheaf S} {Λ : Over S}

/-- `F × Y(Λ)` has closed diagonal when `F` does and `Λ` is separated over the base. -/
theorem isClosedImmersion_diag (hF : IsClosedImmersion (Limits.diag F))
    [IsSeparated Λ.hom] : IsClosedImmersion (Limits.diag (extProd F Λ)) := by
  let P := (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsClosedImmersion.{u})
      (Over.forget S)).relative (schemeYoneda S)
  rw [isClosedImmersion_diag_iff] at hF ⊢
  have hY := (isClosedImmersion_diag_iff _).mp (isClosedImmersion_diag_schemeYoneda Λ)
  let X := extProd F Λ
  let E := extProd X Λ
  let d1 : X ⟶ E := FunctorToTypes.prod.lift (𝟙 X) snd
  let d2 : E ⟶ FunctorToTypes.prod X X :=
    FunctorToTypes.prod.lift fst (FunctorToTypes.prod.lift (fst ≫ fst) snd)
  let e : E ⟶ FunctorToTypes.prod ((schemeYoneda S).obj Λ) ((schemeYoneda S).obj Λ) :=
    FunctorToTypes.prod.lift (fst ≫ snd) snd
  let h : FunctorToTypes.prod X X ⟶ FunctorToTypes.prod F F :=
    FunctorToTypes.prod.lift (FunctorToTypes.prod.fst ≫ fst) (FunctorToTypes.prod.snd ≫ fst)
  have h1 : IsPullback snd d1 (diagPair _) e := by
    apply isPullback_of_elements
    · intro T p; rfl
    · intro T p p' _ h2
      exact congrArg Prod.fst h2
    · intro T α z hz
      have ha := congrArg Prod.fst hz
      have hb := congrArg Prod.snd hz
      refine ⟨z.1, ha.symm, ?_⟩
      exact Prod.ext rfl (ha.symm.trans hb)
  have h2 : IsPullback (fst ≫ fst) d2 (diagPair F) h := by
    apply isPullback_of_elements
    · intro T p; rfl
    · intro T p p' _ h2
      have ha := congrArg Prod.fst h2
      have hb := congrArg Prod.snd (congrArg Prod.snd h2)
      exact Prod.ext ha hb
    · intro T x z hz
      refine ⟨(z.1, z.2.2), ?_, ?_⟩
      · exact (congrArg Prod.fst hz).symm
      · have ha := congrArg Prod.fst hz
        have hb := congrArg Prod.snd hz
        exact Prod.ext rfl (Prod.ext (ha.symm.trans hb) rfl)
  have hd1 : P d1 := MorphismProperty.of_isPullback h1 hY
  have hd2 : P d2 := MorphismProperty.of_isPullback h2 hF
  have : diagPair X = d1 ≫ d2 := rfl
  rw [this]
  exact MorphismProperty.comp_mem P _ _ hd1 hd2

end extProd

end Diagonal

section Translation

variable (G : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) {Λ : Over S}

/-- Translation of `G × Y(Λ)` by a section `c` of `G` over `Λ`:
`(x, α) ↦ (x + α^* c, α)`. -/
def translate (c : G.obj (op Λ)) :
    extProd (G ⋙ forget AddCommGrpCat) Λ ⟶ extProd (G ⋙ forget AddCommGrpCat) Λ where
  app T := TypeCat.ofHom fun z ↦ ((show G.obj T from z.1) + G.map z.2.down.op c, z.2)
  naturality T T' f := by
    ext z
    · change (show G.obj T' from G.map f z.1) + G.map (f.unop ≫ z.2.down).op c =
        G.map f ((show G.obj T from z.1) + G.map z.2.down.op c)
      rw [map_add, op_comp, G.map_comp, AddCommGrpCat.comp_apply]
      rfl
    · rfl

@[simp]
lemma translate_app (c : G.obj (op Λ)) (T : (Over S)ᵒᵖ)
    (z : (extProd (G ⋙ forget AddCommGrpCat) Λ).obj T) :
    (translate G c).app T z = ((show G.obj T from z.1) + G.map z.2.down.op c, z.2) := rfl

lemma translate_add (c d : G.obj (op Λ)) :
    translate G c ≫ translate G d = translate G (c + d) := by
  ext T z
  · change (show G.obj T from z.1) + G.map z.2.down.op c + G.map z.2.down.op d =
      (show G.obj T from z.1) + G.map z.2.down.op (c + d)
    rw [map_add, add_assoc]
  · rfl

lemma translate_zero : translate G (0 : G.obj (op Λ)) = 𝟙 _ := by
  ext T z
  · change (show G.obj T from z.1) + G.map z.2.down.op 0 = z.1
    rw [map_zero, add_zero]
  · rfl

/-- Translations are isomorphisms. -/
def translateIso (c : G.obj (op Λ)) :
    extProd (G ⋙ forget AddCommGrpCat) Λ ≅ extProd (G ⋙ forget AddCommGrpCat) Λ where
  hom := translate G c
  inv := translate G (-c)
  hom_inv_id := by rw [translate_add, add_neg_cancel, translate_zero]
  inv_hom_id := by rw [translate_add, neg_add_cancel, translate_zero]

end Translation

end Langlands.AlgebraicGeometry.AlgebraicSpace
