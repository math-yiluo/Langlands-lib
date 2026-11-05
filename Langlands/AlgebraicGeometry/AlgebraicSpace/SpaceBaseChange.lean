import Langlands.AlgebraicGeometry.AlgebraicSpace.SchemeBaseChange
import Langlands.AlgebraicGeometry.AlgebraicSpace.DiagonalEqualizer
import Langlands.AlgebraicGeometry.AlgebraicSpace.RingPoints
import Langlands.AlgebraicGeometry.AlgebraicSpace.StructuralAtlasGeometry
import Langlands.AlgebraicGeometry.PointTopology.RingPointBaseChange
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
# Base change of algebraic spaces

For a morphism of schemes `g : T ⟶ S`, restriction along `Over.map g` sends presheaves on
schemes over `S` to presheaves on schemes over `T`. Representable transformations stay
representable, with the same underlying scheme morphisms as represented projections.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {S T : Scheme.{u}} (g : T ⟶ S)

/-- Restriction of presheaves on schemes over `S` along `Over.map g`. -/
abbrev restrictPresheaf : Presheaf S ⥤ Presheaf T :=
  (Functor.whiskeringLeft _ _ _).obj (Over.map g).op

variable {g}

/-- Restriction keeps a relative property of a transformation, for any property of scheme
morphisms that respects isomorphisms: the represented projections over `T` are the
represented projections over `S`, viewed over `T`. -/
theorem relative_restrictPresheaf_map (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {F G : Presheaf S} {f : F ⟶ G}
    (hf : (MorphismProperty.inverseImage P (Over.forget S)).relative (schemeYoneda S) f) :
    (MorphismProperty.inverseImage P (Over.forget T)).relative (schemeYoneda T)
      ((restrictPresheaf g).map f) := by
  have : (MorphismProperty.inverseImage P (Over.forget T)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage P (Over.forget T)
  apply MorphismProperty.relative.of_exists
  intro U α
  let γ : G.obj (op ((Over.map g).obj U)) :=
    (uliftYonedaEquiv.{u + 1} α : ((restrictPresheaf g).obj G).obj (op U))
  let α' : (schemeYoneda S).obj ((Over.map g).obj U) ⟶ G := uliftYonedaEquiv.{u + 1}.symm γ
  have hsq := hf.rep.isPullback α'
  let sn := hf.rep.snd α'
  let fs := hf.rep.fst α'
  let W : Over T := Over.mk (sn.left ≫ U.hom)
  let snT : W ⟶ U := Over.homMk sn.left rfl
  let ι : (Over.map g).obj W ⟶ hf.rep.pullback α' := Over.homMk (𝟙 _) (by
    simp only [Over.map_obj_left, Over.map_obj_hom, Category.id_comp, W]
    rw [← Over.w sn]
    simp)
  let xV : F.obj (op (hf.rep.pullback α')) := uliftYonedaEquiv.{u + 1} fs
  let fsT : (schemeYoneda T).obj W ⟶ (restrictPresheaf g).obj F :=
    uliftYonedaEquiv.{u + 1}.symm (F.map ι.op xV)
  have hmap : ∀ {Z : Over T} (c : Z ⟶ W),
      (Over.map g).map c ≫ ι ≫ sn = (Over.map g).map (c ≫ snT) := by
    intro Z c
    ext
    simp [ι, snT]
  have hfs : ∀ {Z : Over T} (c : Z ⟶ W),
      fsT.app (op Z) (ULift.up c) = fs.app (op ((Over.map g).obj Z))
        (ULift.up ((Over.map g).map c ≫ ι)) := by
    intro Z c
    rw [schemeYoneda_app_up, schemeYoneda_app_up]
    simp only [fsT, Equiv.apply_symm_apply, xV]
    change F.map ((Over.map g).map c).op (F.map ι.op (uliftYonedaEquiv fs)) = _
    rw [op_comp, F.map_comp]
    rfl
  have hα : ∀ {Z : Over T} (a : Z ⟶ U),
      α.app (op Z) (ULift.up a) = α'.app (op ((Over.map g).obj Z))
        (ULift.up ((Over.map g).map a)) := by
    intro Z a
    rw [schemeYoneda_app_up, schemeYoneda_app_up]
    simp only [α', Equiv.apply_symm_apply]
    rfl
  refine ⟨W, fsT, snT, ?_, hf.property_snd α'⟩
  apply IsPullback.of_forall_isPullback_app
  intro Z
  obtain ⟨Z⟩ := Z
  have hS := hsq.app (op ((Over.map g).obj Z))
  rw [Types.isPullback_iff] at hS ⊢
  obtain ⟨wS, injS, surjS⟩ := hS
  refine ⟨?_, ?_, ?_⟩
  · ext ⟨c⟩
    have := ConcreteCategory.congr_hom wS
      (show ((schemeYoneda S).obj (hf.rep.pullback α')).obj (op ((Over.map g).obj Z)) from
        ULift.up ((Over.map g).map c ≫ ι))
    simp only at this ⊢
    change ((restrictPresheaf g).map f).app (op Z) (fsT.app (op Z) (ULift.up c)) =
      α.app (op Z) (ULift.up (c ≫ snT))
    rw [hfs, hα, ← hmap]
    exact this
  · rintro ⟨c₁⟩ ⟨c₂⟩ ⟨h₁, h₂⟩
    have e₂ : c₁ ≫ snT = c₂ ≫ snT := congrArg ULift.down h₂
    have hb : (Over.map g).map c₁ ≫ ι = (Over.map g).map c₂ ≫ ι := by
      have := injS (ULift.up ((Over.map g).map c₁ ≫ ι)) (ULift.up ((Over.map g).map c₂ ≫ ι))
        ⟨by
          change fs.app _ _ = fs.app _ _
          rw [← hfs, ← hfs]
          exact h₁,
         by
          change ULift.up (((Over.map g).map c₁ ≫ ι) ≫ sn) =
            ULift.up (((Over.map g).map c₂ ≫ ι) ≫ sn)
          rw [Category.assoc, Category.assoc, hmap, hmap, e₂]⟩
      exact congrArg ULift.down this
    have hl : c₁.left = c₂.left := by
      have := congrArg CommaMorphism.left hb
      simpa [ι] using this
    exact congrArg ULift.up (Over.OverMorphism.ext hl)
  · rintro x ⟨a⟩ hx
    obtain ⟨⟨b⟩, hb₁, hb₂⟩ := surjS x (ULift.up ((Over.map g).map a)) (by
      rw [← hα]
      exact hx)
    have hb₂' : b ≫ sn = (Over.map g).map a := congrArg ULift.down hb₂
    let c : Z ⟶ W := Over.homMk b.left (by
      have := congrArg CommaMorphism.left hb₂'
      simp only [Over.comp_left, Over.map_map_left] at this
      simp only [W, Over.mk_hom, ← Category.assoc, this]
      exact Over.w a)
    have hc : (Over.map g).map c ≫ ι = b := by
      ext
      simp [c, ι]
    refine ⟨ULift.up c, ?_, ?_⟩
    · rw [hfs, hc]
      exact hb₁
    · change ULift.up (c ≫ snT) = ULift.up a
      congr 1
      ext
      have := congrArg CommaMorphism.left hb₂'
      simpa [c, snT] using this

/-- Restriction keeps representability of a transformation. -/
theorem relativelyRepresentable_restrictPresheaf_map {F G : Presheaf S} {f : F ⟶ G}
    (hf : IsRepresentableMorphism f) :
    IsRepresentableMorphism ((restrictPresheaf g).map f) := by
  have h : (MorphismProperty.inverseImage (⊤ : MorphismProperty Scheme.{u})
      (Over.forget S)).relative (schemeYoneda S) f := ⟨hf, fun _ _ _ _ _ _ => trivial⟩
  exact (relative_restrictPresheaf_map (g := g) ⊤ h).rep

variable (g) in
/-- Restriction commutes with binary products of presheaves. -/
def restrictPresheafProdIso (F : Presheaf S) :
    (restrictPresheaf g).obj (F ⨯ F) ≅ (restrictPresheaf g).obj F ⨯ (restrictPresheaf g).obj F :=
  PreservesLimitPair.iso (restrictPresheaf g) F F

theorem restrictPresheaf_map_diag (F : Presheaf S) :
    (restrictPresheaf g).map (diag F) ≫ (restrictPresheafProdIso g F).hom =
      diag ((restrictPresheaf g).obj F) := by
  rw [restrictPresheafProdIso, PreservesLimitPair.iso_hom]
  apply prod.hom_ext
  · rw [Category.assoc, prodComparison_fst, ← Functor.map_comp]
    simp
  · rw [Category.assoc, prodComparison_snd, ← Functor.map_comp]
    simp

/-- Restriction keeps a relative property of the diagonal. -/
theorem relative_diag_restrictPresheaf (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {F : Presheaf S}
    (hF : (MorphismProperty.inverseImage P (Over.forget S)).relative (schemeYoneda S) (diag F)) :
    (MorphismProperty.inverseImage P (Over.forget T)).relative (schemeYoneda T)
      (diag ((restrictPresheaf g).obj F)) := by
  rw [← restrictPresheaf_map_diag]
  exact MorphismProperty.RespectsIso.postcomp _ _ _ (relative_restrictPresheaf_map P hF)

/-- Restriction keeps representability of the diagonal. -/
theorem hasRepresentableDiagonal_restrictPresheaf {F : Presheaf S}
    (hF : HasRepresentableDiagonal F) :
    HasRepresentableDiagonal ((restrictPresheaf g).obj F) := by
  unfold HasRepresentableDiagonal IsRepresentableMorphism
  rw [← restrictPresheaf_map_diag]
  exact MorphismProperty.RespectsIso.postcomp (schemeYoneda T).relativelyRepresentable _ _
    (relativelyRepresentable_restrictPresheaf_map hF)

variable (g) in
/-- The base change of a scheme atlas: the actual base-changed scheme with the restricted
transformation. -/
def restrictAtlas {F : Presheaf S} {U : Over S} (a : (schemeYoneda S).obj U ⟶ F) :
    (schemeYoneda T).obj ((Over.pullback g).obj U) ⟶ (restrictPresheaf g).obj F :=
  (schemeYonedaBaseChangeIso g U).hom ≫ (restrictPresheaf g).map a

/-- The base-changed atlas keeps a relative property of the atlas. -/
theorem relative_restrictAtlas (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {F : Presheaf S} {U : Over S} {a : (schemeYoneda S).obj U ⟶ F}
    (ha : (MorphismProperty.inverseImage P (Over.forget S)).relative (schemeYoneda S) a) :
    (MorphismProperty.inverseImage P (Over.forget T)).relative (schemeYoneda T)
      (restrictAtlas g a) :=
  MorphismProperty.RespectsIso.precomp _ _ _ (relative_restrictPresheaf_map P ha)

variable (g) in
/-- The restricted fppf sheaf of an algebraic space is an algebraic space. -/
theorem isAlgebraicSpace_restrict (X : AlgebraicSpace S) :
    IsAlgebraicSpace T ((Scheme.fppfTopology.overMapPullback (Type (u + 1)) g).obj X.toSheaf) := by
  have : MorphismProperty.RespectsIso (@Etale.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  obtain ⟨U, a, ha, hs⟩ := X.property.2
  exact ⟨hasRepresentableDiagonal_restrictPresheaf X.hasRepresentableDiagonal,
    (Over.pullback g).obj U, restrictAtlas g a, relative_restrictAtlas _ ha,
    relative_restrictAtlas _ hs⟩

variable (g) in
/-- The base change of an algebraic space over `S` along `g : T ⟶ S`: its fppf sheaf
restricted along `Over.map g`. -/
def baseChange (X : AlgebraicSpace S) : AlgebraicSpace T :=
  ⟨(Scheme.fppfTopology.overMapPullback (Type (u + 1)) g).obj X.toSheaf,
    isAlgebraicSpace_restrict g X⟩

/-- The presheaf of the base change is the restricted presheaf. -/
theorem baseChange_presheaf (X : AlgebraicSpace S) :
    (baseChange g X).presheaf = (restrictPresheaf g).obj X.presheaf := rfl

variable (g) in
/-- Base change of morphisms of algebraic spaces. -/
def baseChangeMap {X Y : AlgebraicSpace S} (f : X ⟶ Y) : baseChange g X ⟶ baseChange g Y :=
  homMk ((restrictPresheaf g).map (hom f))

variable (g) in
/-- Base change as a functor. -/
@[simps]
def baseChangeFunctor : AlgebraicSpace S ⥤ AlgebraicSpace T where
  obj := baseChange g
  map := baseChangeMap g
  map_id _ := rfl
  map_comp _ _ := rfl

variable (g) in
/-- The base change of the space of an actual scheme is the space of its actual base change. -/
def baseChangeSchemeIso (U : Over S) :
    (schemeToSpace T).obj ((Over.pullback g).obj U) ≅ baseChange g ((schemeToSpace S).obj U) where
  hom := homMk (schemeYonedaBaseChangeIso g U).hom
  inv := homMk (schemeYonedaBaseChangeIso g U).inv
  hom_inv_id := (homEquiv _ _).injective (schemeYonedaBaseChangeIso g U).hom_inv_id
  inv_hom_id := (homEquiv _ _).injective (schemeYonedaBaseChangeIso g U).inv_hom_id

/-- Base change keeps quasi-separatedness. -/
theorem IsQuasiSeparated.baseChange {X : AlgebraicSpace S} (hX : IsQuasiSeparated X) :
    IsQuasiSeparated (baseChange g X) :=
  have : MorphismProperty.RespectsIso (@QuasiCompact.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  relative_diag_restrictPresheaf (g := g) (@QuasiCompact.{u}) hX

/-- Base change keeps separatedness. -/
theorem IsSeparated.baseChange {X : AlgebraicSpace S} (hX : IsSeparated X) :
    IsSeparated (baseChange g X) :=
  relative_diag_restrictPresheaf (g := g) (@_root_.AlgebraicGeometry.IsClosedImmersion.{u}) hX

/-- Base change keeps an atlas property stable under base change of scheme morphisms. -/
theorem HasAtlasProperty.baseChange {P : MorphismProperty Scheme.{u}}
    [P.IsStableUnderBaseChange] {X : AlgebraicSpace S} (hX : HasAtlasProperty P X) :
    HasAtlasProperty P (baseChange g X) := by
  have : MorphismProperty.RespectsIso (@Etale.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  obtain ⟨U, a, ha, hs, hP⟩ := hX
  exact ⟨(Over.pullback g).obj U, restrictAtlas g a, relative_restrictAtlas _ ha,
    relative_restrictAtlas _ hs, P.pullback_snd _ _ hP⟩

section RingPoints

variable (C D : Type u) [CommRing C] [CommRing D] [Algebra C D]
variable (A : Type u) [CommRing A] [Algebra C A] [Algebra D A] [IsScalarTower C D A]

open Langlands.AlgebraicGeometry.PointTopology (ringTestRestrictScalarsIso)

/-- The `A`-valued points of the base change along `Spec D ⟶ Spec C` are the `A`-valued
points of the original space, for a `D`-algebra `A` with compatible `C`-algebra
structure. -/
def baseChangeRingPointsEquiv (X : AlgebraicSpace (Spec (CommRingCat.of C))) :
    RingPoints D (baseChange (Spec.algebraMap C D) X) A ≃ RingPoints C X A :=
  (X.presheaf.mapIso (ringTestRestrictScalarsIso C D A).op).toEquiv.symm

/-- The point identification is pullback along the restriction-of-scalars isomorphism. -/
theorem baseChangeRingPointsEquiv_apply (X : AlgebraicSpace (Spec (CommRingCat.of C)))
    (x : RingPoints D (baseChange (Spec.algebraMap C D) X) A) :
    baseChangeRingPointsEquiv C D A X x =
      X.pullback (ringTestRestrictScalarsIso C D A).inv x := rfl

/-- The point identification is natural in morphisms of algebraic spaces. -/
theorem baseChangeRingPointsEquiv_map {X Y : AlgebraicSpace (Spec (CommRingCat.of C))}
    (f : X ⟶ Y) (x : RingPoints D (baseChange (Spec.algebraMap C D) X) A) :
    baseChangeRingPointsEquiv C D A Y
        (RingPoints.map (baseChangeMap (Spec.algebraMap C D) f) x) =
      RingPoints.map f (baseChangeRingPointsEquiv C D A X x) :=
  mapSections_naturality f (ringTestRestrictScalarsIso C D A).inv x

end RingPoints

end Langlands.AlgebraicGeometry.AlgebraicSpace
