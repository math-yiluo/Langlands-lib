import Langlands.AlgebraicGeometry.AlgebraicSpace.BaseCompositionSheaf
import Langlands.AlgebraicGeometry.AlgebraicSpace.DiagonalEqualizer
import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-! # Geometry after composition of bases -/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.BaseComposition

open OriginalBaseTransport

variable {S T : Scheme.{u}} (g : S ⟶ T)

/-- A composed section of a represented presheaf is a map to the same scheme over `T`. -/
def schemeComparison (U : Over S) :
    presheaf g ((schemeYoneda S).obj U) ⟶ (schemeYoneda T).obj ((Over.map g).obj U) where
  app V := TypeCat.ofHom fun x => ULift.up (Over.homMk x.val.2.down.left (by
    change (x.val.2.down.left ≫ U.hom) ≫ g = V.unop.hom
    rw [x.val.2.down.w]
    exact congrArg ULift.down x.property))
  naturality {V W} a := by
    apply ConcreteCategory.hom_ext
    intro x
    apply ULift.ext
    apply Over.OverMorphism.ext
    rfl

lemma schemeComparison_bijective (U : Over S) (V : Over T) :
    Function.Bijective ((schemeComparison g U).app (op V)) := by
  constructor
  · rintro ⟨⟨s, ⟨a⟩⟩, hs⟩ ⟨⟨t, ⟨b⟩⟩, ht⟩ h
    have hab : a.left = b.left := congrArg (fun z => z.down.left) h
    have ha : a.left ≫ U.hom = s := a.w
    have hb : b.left ≫ U.hom = t := b.w
    have hst : s = t := ha.symm.trans ((congrArg (fun c => c ≫ U.hom) hab).trans hb)
    subst t
    apply Subtype.ext
    exact congrArg (Sigma.mk s) (congrArg ULift.up (Over.OverMorphism.ext hab))
  · rintro ⟨a⟩
    refine ⟨⟨⟨a.left ≫ U.hom, ULift.up (Over.homMk a.left rfl)⟩, ?_⟩, ?_⟩
    · change ULift.up ((a.left ≫ U.hom) ≫ g) = ULift.up V.hom
      exact congrArg ULift.up (by simpa only [Over.map_obj_hom, Category.assoc] using a.w)
    · apply ULift.ext
      apply Over.OverMorphism.ext
      rfl

/-- Composition of bases sends a represented presheaf to the same scheme over `T`. -/
def schemeIso (U : Over S) :
    (schemeYoneda T).obj ((Over.map g).obj U) ≅ presheaf g ((schemeYoneda S).obj U) := by
  letI : IsIso (schemeComparison g U) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro V
    rw [isIso_iff_bijective]
    exact schemeComparison_bijective g U V.unop
  exact (asIso (schemeComparison g U)).symm

/-- Composition of bases preserves pullback squares of relative presheaves. -/
theorem map_isPullback {A B C D : Presheaf S}
    {a : A ⟶ B} {b : A ⟶ C} {f : B ⟶ D} {h : C ⟶ D}
    (hsq : IsPullback a b f h) :
    IsPullback (map g a) (map g b) (map g f) (map g h) := by
  have hw : map g a ≫ map g f = map g b ≫ map g h := by
    exact ((presheafFunctor g).map_comp a f).symm.trans
      ((congrArg (fun k => (presheafFunctor g).map k) hsq.w).trans
        ((presheafFunctor g).map_comp b h))
  apply IsPullback.of_forall_isPullback_app
  intro V
  obtain ⟨V⟩ := V
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · exact congrArg (fun k => k.app (op V)) hw
  · rintro ⟨⟨s, x⟩, hs⟩ ⟨⟨t, y⟩, ht⟩ ⟨hx, hy⟩
    have hst : s = t := congrArg (fun z => z.val.1) hx
    subst t
    have hx' : a.app (op (Over.mk s)) x = a.app (op (Over.mk s)) y :=
      eq_of_heq (Sigma.mk.inj (congrArg Subtype.val hx)).2
    have hy' : b.app (op (Over.mk s)) x = b.app (op (Over.mk s)) y :=
      eq_of_heq (Sigma.mk.inj (congrArg Subtype.val hy)).2
    have hp := hsq.app (op (Over.mk s))
    rw [Types.isPullback_iff] at hp
    apply Subtype.ext
    exact congrArg (Sigma.mk s) (hp.2.1 x y ⟨hx', hy'⟩)
  · rintro ⟨⟨s, x⟩, hs⟩ ⟨⟨t, y⟩, ht⟩ hxy
    have hst : s = t := congrArg (fun z => z.val.1) hxy
    subst t
    have hxy' : f.app (op (Over.mk s)) x = h.app (op (Over.mk s)) y :=
      eq_of_heq (Sigma.mk.inj (congrArg Subtype.val hxy)).2
    have hp := hsq.app (op (Over.mk s))
    rw [Types.isPullback_iff] at hp
    obtain ⟨z, hz₁, hz₂⟩ := hp.2.2 x y hxy'
    refine ⟨⟨⟨s, z⟩, hs⟩, ?_, ?_⟩
    · apply Subtype.ext
      exact congrArg (Sigma.mk s) hz₁
    · apply Subtype.ext
      exact congrArg (Sigma.mk s) hz₂

/-- Scheme comparison commutes with morphisms of the representing schemes. -/
theorem schemeComparison_naturality {U V : Over S} (p : U ⟶ V) :
    map g ((schemeYoneda S).map p) ≫ schemeComparison g V =
      schemeComparison g U ≫ (schemeYoneda T).map ((Over.map g).map p) := by
  ext W x
  apply ULift.ext
  apply Over.OverMorphism.ext
  rfl

/-- The inverse scheme comparison is natural in the representing scheme. -/
theorem schemeIso_naturality {U V : Over S} (p : U ⟶ V) :
    (schemeIso g U).hom ≫ map g ((schemeYoneda S).map p) =
      (schemeYoneda T).map ((Over.map g).map p) ≫ (schemeIso g V).hom := by
  apply (cancel_mono (schemeIso g V).inv).mp
  change (schemeIso g U).hom ≫ map g ((schemeYoneda S).map p) ≫ schemeComparison g V = _
  rw [schemeComparison_naturality]
  change (schemeIso g U).hom ≫ (schemeIso g U).inv ≫ _ = _
  simp

/-- Compose a map from a scheme with the base morphism, using the same scheme over `T`. -/
def fromScheme {F : Presheaf S} {U : Over S} (a : (schemeYoneda S).obj U ⟶ F) :
    (schemeYoneda T).obj ((Over.map g).obj U) ⟶ presheaf g F :=
  (schemeIso g U).hom ≫ map g a

/-- The scheme comparison sends the identity section to the original lifted identity. -/
theorem schemeIso_hom_id (U : Over S) :
    uliftYonedaEquiv.{u + 1} ((schemeIso g U).hom) =
      liftSection g ((schemeYoneda S).obj U) U (ULift.up (𝟙 U)) := by
  apply (schemeComparison_bijective g U ((Over.map g).obj U)).injective
  change (schemeIso g U).inv.app _ ((schemeIso g U).hom.app _ (ULift.up (𝟙 _))) = _
  exact (schemeIso g U).hom_inv_id_app_apply (op ((Over.map g).obj U))
    (show ((schemeYoneda T).obj ((Over.map g).obj U)).obj (op ((Over.map g).obj U)) from
      ULift.up (𝟙 ((Over.map g).obj U)))

/-- Composing a scheme map lifts its corresponding original section. -/
theorem fromScheme_section {F : Presheaf S} {U : Over S}
    (a : (schemeYoneda S).obj U ⟶ F) :
    uliftYonedaEquiv.{u + 1} (fromScheme g a) = liftSection g F U (uliftYonedaEquiv.{u + 1} a) := by
  rw [fromScheme, uliftYonedaEquiv_comp, schemeIso_hom_id]
  exact map_liftSection g a U (ULift.up (𝟙 U))

/-- Composition of bases preserves every represented scheme-morphism property
that respects isomorphisms. The represented projection has the same underlying scheme map. -/
theorem relative_map (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {F G : Presheaf S} {f : F ⟶ G}
    (hf : (MorphismProperty.inverseImage P (Over.forget S)).relative (schemeYoneda S) f) :
    (MorphismProperty.inverseImage P (Over.forget T)).relative (schemeYoneda T) (map g f) := by
  let : (MorphismProperty.inverseImage P (Over.forget T)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage P (Over.forget T)
  apply MorphismProperty.relative.of_exists
  intro U α
  obtain ⟨V, t, rfl⟩ := U.mk_surjective
  generalize he : uliftYonedaEquiv.{u + 1} α = x
  rcases x with ⟨⟨s, y⟩, hs⟩
  change V ⟶ S at s
  have hst : s ≫ g = t := congrArg ULift.down hs
  subst t
  let US : Over S := Over.mk s
  let α' : (schemeYoneda S).obj US ⟶ G := uliftYonedaEquiv.{u + 1}.symm y
  have hα : α = fromScheme g α' := by
    apply uliftYonedaEquiv.{u + 1}.injective
    calc
      uliftYonedaEquiv.{u + 1} α = liftSection g G US y := he
      _ = uliftYonedaEquiv.{u + 1} (fromScheme g α') :=
        ((fromScheme_section g α').trans (congrArg (liftSection g G US)
          (uliftYonedaEquiv.{u + 1}.apply_symm_apply y))).symm
  let W := hf.rep.pullback α'
  let fst := hf.rep.fst α'
  let snd := hf.rep.snd α'
  refine ⟨(Over.map g).obj W, fromScheme g fst, (Over.map g).map snd, ?_,
    hf.property_snd α'⟩
  apply (map_isPullback g (hf.rep.isPullback α')).of_iso'
    (schemeIso g W) (Iso.refl _) (schemeIso g US) (Iso.refl _)
  · simp only [fromScheme, Iso.refl_hom, Category.comp_id]
    rfl
  · exact schemeIso_naturality g snd
  · simp
  · rw [hα]
    simp only [fromScheme, Iso.refl_hom, Category.comp_id]

/-- A representable transformation stays representable under composition of bases. -/
theorem representable_map {F G : Presheaf S} {f : F ⟶ G}
    (hf : IsRepresentableMorphism f) : IsRepresentableMorphism (map g f) := by
  have h : (MorphismProperty.inverseImage (⊤ : MorphismProperty Scheme.{u})
      (Over.forget S)).relative (schemeYoneda S) f := ⟨hf, fun _ _ _ _ _ _ => trivial⟩
  exact (relative_map g ⊤ h).rep

/-- A composed map from a scheme retains every represented projection property. -/
theorem relative_fromScheme (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {F : Presheaf S} {U : Over S} {a : (schemeYoneda S).obj U ⟶ F}
    (ha : (MorphismProperty.inverseImage P (Over.forget S)).relative (schemeYoneda S) a) :
    (MorphismProperty.inverseImage P (Over.forget T)).relative (schemeYoneda T)
      (fromScheme g a) :=
  MorphismProperty.RespectsIso.precomp _ _ _ (relative_map g P ha)

/-- The composed presheaf retains representability of its diagonal. -/
theorem hasRepresentableDiagonal_presheaf {F : Presheaf S} (hF : HasRepresentableDiagonal F) :
    HasRepresentableDiagonal (presheaf g F) := by
  apply Functor.relativelyRepresentable.diag_of_map_from_obj
  intro U α
  obtain ⟨V, t, rfl⟩ := U.mk_surjective
  generalize he : uliftYonedaEquiv.{u + 1} α = x
  rcases x with ⟨⟨s, y⟩, hs⟩
  change V ⟶ S at s
  have hst : s ≫ g = t := congrArg ULift.down hs
  subst t
  let US : Over S := Over.mk s
  let α' : (schemeYoneda S).obj US ⟶ F := uliftYonedaEquiv.{u + 1}.symm y
  have hα : α = fromScheme g α' := by
    apply uliftYonedaEquiv.{u + 1}.injective
    calc
      uliftYonedaEquiv.{u + 1} α = liftSection g F US y := he
      _ = uliftYonedaEquiv.{u + 1} (fromScheme g α') :=
        ((fromScheme_section g α').trans (congrArg (liftSection g F US)
          (uliftYonedaEquiv.{u + 1}.apply_symm_apply y))).symm
  rw [hα]
  exact MorphismProperty.RespectsIso.precomp _ _ _
    (representable_map g (Functor.relativelyRepresentable.of_diag hF α'))

/-- Composing the base of an algebraic space retains the defining geometric conditions. -/
theorem isAlgebraicSpace_sheaf (X : AlgebraicSpace S) : IsAlgebraicSpace T (sheaf g X.toSheaf) := by
  let : MorphismProperty.RespectsIso (@Etale.{u}) :=
    Etale.etale_isStableUnderBaseChange.respectsIso
  obtain ⟨U, a, ha, hs⟩ := X.property.2
  exact ⟨hasRepresentableDiagonal_presheaf g X.hasRepresentableDiagonal,
    (Over.map g).obj U, fromScheme g a, relative_fromScheme g _ ha,
    relative_fromScheme g _ hs⟩

/-- The actual algebraic space obtained by composing its base with `g`. -/
def space (X : AlgebraicSpace S) : AlgebraicSpace T :=
  ⟨sheaf g X.toSheaf, isAlgebraicSpace_sheaf g X⟩

/-- A morphism of spaces retains its original structure coordinate after base composition. -/
def spaceMap {X Y : AlgebraicSpace S} (f : X ⟶ Y) : space g X ⟶ space g Y :=
  homMk (map g (hom f))

/-- Composition of bases is a functor on actual algebraic spaces. -/
def spaceFunctor : AlgebraicSpace S ⥤ AlgebraicSpace T where
  obj := space g
  map := spaceMap g
  map_id X := by
    apply (homEquiv _ _).injective
    exact (presheafFunctor g).map_id X.presheaf
  map_comp f h := by
    apply (homEquiv _ _).injective
    exact (presheafFunctor g).map_comp (hom f) (hom h)

/-- A scheme viewed as a composed space is that same scheme over the composed base. -/
def spaceSchemeIso (U : Over S) :
    (schemeToSpace T).obj ((Over.map g).obj U) ≅ space g ((schemeToSpace S).obj U) where
  hom := homMk (schemeIso g U).hom
  inv := homMk (schemeIso g U).inv
  hom_inv_id := (homEquiv _ _).injective (schemeIso g U).hom_inv_id
  inv_hom_id := (homEquiv _ _).injective (schemeIso g U).inv_hom_id

end Langlands.AlgebraicGeometry.AlgebraicSpace.BaseComposition
