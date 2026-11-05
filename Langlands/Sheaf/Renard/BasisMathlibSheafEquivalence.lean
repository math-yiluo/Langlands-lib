import Langlands.Sheaf.Renard.AllOpenMathlibSheaf
import Langlands.Sheaf.Renard.BasisAllOpenEquivalence

/-!
# Chosen-basis sheaves and actual Mathlib sheaves

The reverse functor retains original groups and maps. The forward composition
uses the actual compatible-family equivalence at sufficient section size.
-/

open CategoryTheory Opposite TopologicalSpace

universe u v w

noncomputable section

namespace Langlands.Sheaf.Renard.BasisMathlib

variable {X : Type u} [TopologicalSpace X]

/-- Restrict actual Mathlib presheaves to the supplied chosen basis. -/
def rawFromMathlib (B : OpenBasis X) :
    TopCat.Presheaf AddCommGrpCat.{v} (TopCat.of X) ⥤ RawPresheaf.{u,v} B :=
  AllOpenMathlib.rawFromMathlib X ⋙ rawBasisRestriction B

/-- The composite is the original basis precomposition on underlying functors. -/
@[simp] theorem rawFromMathlib_obj (B : OpenBasis X)
    (G : TopCat.Presheaf AddCommGrpCat.{v} (TopCat.of X)) :
    (rawFromMathlib B).obj G = (basisInclusion B).op ⋙ G := rfl

/-- Restrict an actual Mathlib sheaf, using the published intrinsic gluing proof. -/
def fromMathlib (B : OpenBasis X) :
    TopCat.Sheaf AddCommGrpCat.{v} (TopCat.of X) ⥤ BasisSheaf.{u,v} B :=
  AllOpenMathlib.fromMathlib X ⋙ sheafBasisRestriction B

/-- Forgetting the two source predicates gives the original raw restriction. -/
theorem fromMathlib_forget (B : OpenBasis X) :
    fromMathlib.{u,v} B ⋙ sheafForget B ⋙ presheafInclusion B =
      TopCat.Sheaf.forget AddCommGrpCat (TopCat.of X) ⋙ rawFromMathlib B := rfl

/-- Every original Mathlib section group is preserved on the basis. -/
@[simp] theorem fromMathlib_sections (B : OpenBasis X)
    (G : TopCat.Sheaf AddCommGrpCat.{v} (TopCat.of X)) (U : BasisOpen B) :
    Sections ((fromMathlib B).obj G).obj.obj U = G.obj.obj (op U.obj) := rfl

/-- Restriction is the original Mathlib restriction map. -/
@[simp] theorem fromMathlib_restriction (B : OpenBasis X)
    (G : TopCat.Sheaf AddCommGrpCat.{v} (TopCat.of X))
    {U V : BasisOpen B} (h : U.obj ≤ V.obj) :
    restriction ((fromMathlib B).obj G).obj.obj h = G.obj.map (homOfLE h).op := rfl

/-- Each component is the original input natural transformation. -/
@[simp] theorem fromMathlib_map_app (B : OpenBasis X)
    {G H : TopCat.Sheaf AddCommGrpCat.{v} (TopCat.of X)} (φ : G ⟶ H) (U : BasisOpen B) :
    ((fromMathlib B).map φ).hom.hom.app (op U) = φ.hom.app (op U.obj) := rfl

/-- The restricted sheaf still glues families indexed in every universe. -/
theorem fromMathlib_unique_gluing (B : OpenBasis X)
    (G : TopCat.Sheaf AddCommGrpCat.{v} (TopCat.of X))
    {ι : Type w} (V : BasisOpen B) (U : ι → BasisOpen B)
    (hU : FamilyCovers V U) (s : ∀ i, G.obj.obj (op (U i).obj))
    (hs : Compatible ((fromMathlib B).obj G).obj.obj U s) :
    ∃! t : G.obj.obj (op V.obj), ∀ i, G.obj.map (homOfLE (hU.1 i)).op t = s i :=
  ((fromMathlib B).obj G).unique_gluing V U hU s hs

/-- The raw Mathlib presheaf of compatible families on the original basis. -/
def rawToMathlib (B : OpenBasis X) :
    RawPresheaf.{u,max u v} B ⥤
      TopCat.Presheaf AddCommGrpCat.{max u v} (TopCat.of X) :=
  BasisAllOpen.rawExtension.{u,v} B ⋙ AllOpenMathlib.rawToMathlib X

/-- Extend by actual compatible families, then apply the published Mathlib comparison. -/
def toMathlib (B : OpenBasis X) :
    BasisSheaf.{u,max u v} B ⥤ TopCat.Sheaf AddCommGrpCat.{max u v} (TopCat.of X) :=
  BasisAllOpen.extension.{u,v} B ⋙ AllOpenMathlib.toMathlib X

/-- The composition of the two actual equivalences, with all their comparison data. -/
def equivalence (B : OpenBasis X) :
    BasisSheaf.{u,max u v} B ≌ TopCat.Sheaf AddCommGrpCat.{max u v} (TopCat.of X) :=
  (BasisAllOpen.equivalence.{u,v} B).trans (AllOpenMathlib.equivalence.{u,max u v} X)

@[simp] theorem equivalence_functor (B : OpenBasis X) :
    (equivalence.{u,v} B).functor = toMathlib.{u,v} B := rfl

@[simp] theorem equivalence_inverse (B : OpenBasis X) :
    (equivalence.{u,v} B).inverse = fromMathlib.{u,max u v} B := rfl

/-- Forgetting the forward comparison gives the actual raw compatible-family functor. -/
theorem toMathlib_forget (B : OpenBasis X) :
    toMathlib.{u,v} B ⋙ TopCat.Sheaf.forget AddCommGrpCat (TopCat.of X) =
      sheafForget B ⋙ presheafInclusion B ⋙ rawToMathlib.{u,v} B := rfl

/-- Values on all actual opens are exactly the canonical compatible-family groups. -/
@[simp] theorem toMathlib_sections (B : OpenBasis X)
    (F : BasisSheaf.{u,max u v} B) (V : Opens X) :
    ((toMathlib.{u,v} B).obj F).obj.obj (op V) =
      AddCommGrpCat.of (BasisAllOpen.Families F.obj.obj V) := rfl

/-- Actual Mathlib restriction discards only the family components outside the smaller open. -/
@[simp] theorem toMathlib_restriction (B : OpenBasis X)
    (F : BasisSheaf.{u,max u v} B) {U V : Opens X} (h : U ≤ V) :
    (((toMathlib.{u,v} B).obj F).obj.map (homOfLE h).op).hom =
      BasisAllOpen.familyRestriction F.obj.obj h := rfl

/-- Actual morphisms act by the original basis components of the input transformation. -/
@[simp] theorem toMathlib_map_app (B : OpenBasis X)
    {F G : BasisSheaf.{u,max u v} B} (φ : F ⟶ G) (V : Opens X) :
    (((toMathlib.{u,v} B).map φ).hom.app (op V)).hom =
      BasisAllOpen.familyMap φ.hom.hom V := rfl

/-- Canonical additive comparison with each original basis section group. -/
def basisSectionIso (B : OpenBasis X) (F : BasisSheaf.{u,max u v} B) (U : BasisOpen B) :
    Sections F.obj.obj U ≃+ ((toMathlib.{u,v} B).obj F).obj.obj (op U.obj) :=
  BasisAllOpen.basisSectionIso F.obj.obj U

@[simp] theorem basisSectionIso_apply (B : OpenBasis X)
    (F : BasisSheaf.{u,max u v} B) (U : BasisOpen B) (s : Sections F.obj.obj U)
    (W : BasisAllOpen.Inside B U.obj) :
    (basisSectionIso B F U s).val W = restriction F.obj.obj W.property s := rfl

@[simp] theorem basisSectionIso_symm_apply (B : OpenBasis X)
    (F : BasisSheaf.{u,max u v} B) (U : BasisOpen B)
    (s : ((toMathlib.{u,v} B).obj F).obj.obj (op U.obj)) :
    (basisSectionIso B F U).symm s = s.val ⟨U, le_rfl⟩ := rfl

/-- The original basis restrictions are intertwined with the actual Mathlib maps. -/
theorem basisSectionIso_restriction (B : OpenBasis X)
    (F : BasisSheaf.{u,max u v} B) {U V : BasisOpen B} (h : U.obj ≤ V.obj)
    (s : Sections F.obj.obj V) :
    basisSectionIso B F U (restriction F.obj.obj h s) =
      ((toMathlib.{u,v} B).obj F).obj.map (homOfLE h).op (basisSectionIso B F V s) :=
  BasisAllOpen.basisSectionIso_restriction F.obj.obj h s

/-- The comparison preserves every actual original natural transformation. -/
theorem basisSectionIso_naturality (B : OpenBasis X)
    {F G : BasisSheaf.{u,max u v} B} (φ : F ⟶ G) (U : BasisOpen B)
    (s : Sections F.obj.obj U) :
    basisSectionIso B G U (φ.hom.hom.app (op U) s) =
      ((toMathlib.{u,v} B).map φ).hom.app (op U.obj) (basisSectionIso B F U s) :=
  BasisAllOpen.basisSectionIso_naturality φ.hom.hom U s

/-- The composed categorical unit has exactly the original basis comparison. -/
@[simp] theorem unit_hom_apply (B : OpenBasis X)
    (F : BasisSheaf.{u,max u v} B) (U : BasisOpen B) (s : Sections F.obj.obj U) :
    (((equivalence.{u,v} B).unitIso.hom.app F).hom.hom.app (op U)) s =
      basisSectionIso B F U s := rfl

@[simp] theorem unit_inv_apply (B : OpenBasis X)
    (F : BasisSheaf.{u,max u v} B) (U : BasisOpen B)
    (s : ((toMathlib.{u,v} B).obj F).obj.obj (op U.obj)) :
    (((equivalence.{u,v} B).unitIso.inv.app F).hom.hom.app (op U)) s =
      (basisSectionIso B F U).symm s := rfl

/-- On every actual Mathlib open the counit glues original chosen-basis restrictions. -/
def counitSectionIso (B : OpenBasis X)
    (G : TopCat.Sheaf AddCommGrpCat.{max u v} (TopCat.of X)) (V : Opens X) :
    ((toMathlib.{u,v} B).obj ((fromMathlib B).obj G)).obj.obj (op V) ≃+
      G.obj.obj (op V) :=
  BasisAllOpen.counitSectionIso B ((AllOpenMathlib.fromMathlib X).obj G) V

/-- Its inverse sends an original Mathlib section to its chosen-basis restrictions. -/
@[simp] theorem counitSectionIso_symm_apply (B : OpenBasis X)
    (G : TopCat.Sheaf AddCommGrpCat.{max u v} (TopCat.of X)) (V : Opens X)
    (s : G.obj.obj (op V)) (U : BasisAllOpen.Inside B V) :
    ((counitSectionIso.{u,v} B G V).symm s).val U =
      G.obj.map (homOfLE U.property).op s := rfl

/-- The counit section restricts to exactly the supplied component on every basis member. -/
theorem counitSectionIso_amalgamation (B : OpenBasis X)
    (G : TopCat.Sheaf AddCommGrpCat.{max u v} (TopCat.of X)) (V : Opens X)
    (s : ((toMathlib.{u,v} B).obj ((fromMathlib B).obj G)).obj.obj (op V))
    (U : BasisOpen B) (hU : U.obj ≤ V) :
    G.obj.map (homOfLE hU).op (counitSectionIso.{u,v} B G V s) = s.val ⟨U, hU⟩ :=
  BasisAllOpen.counitSectionIso_amalgamation B ((AllOpenMathlib.fromMathlib X).obj G)
    V s U hU

/-- The comparison uses the original Mathlib restriction maps on all opens. -/
theorem counitSectionIso_restriction (B : OpenBasis X)
    (G : TopCat.Sheaf AddCommGrpCat.{max u v} (TopCat.of X))
    {U V : Opens X} (h : U ≤ V)
    (s : ((toMathlib.{u,v} B).obj ((fromMathlib B).obj G)).obj.obj (op V)) :
    counitSectionIso.{u,v} B G U
        (((toMathlib.{u,v} B).obj ((fromMathlib B).obj G)).obj.map (homOfLE h).op s) =
      G.obj.map (homOfLE h).op (counitSectionIso.{u,v} B G V s) :=
  BasisAllOpen.counitSectionIso_restriction B ((AllOpenMathlib.fromMathlib X).obj G) h s

/-- Counit naturality is the original Mathlib natural-transformation equation. -/
theorem counitSectionIso_naturality (B : OpenBasis X)
    {G H : TopCat.Sheaf AddCommGrpCat.{max u v} (TopCat.of X)} (φ : G ⟶ H)
    (V : Opens X)
    (s : ((toMathlib.{u,v} B).obj ((fromMathlib B).obj G)).obj.obj (op V)) :
    counitSectionIso.{u,v} B H V
        (((toMathlib.{u,v} B).map ((fromMathlib B).map φ)).hom.app (op V) s) =
      φ.hom.app (op V) (counitSectionIso.{u,v} B G V s) :=
  BasisAllOpen.counitSectionIso_naturality B ((AllOpenMathlib.fromMathlib X).map φ) V s

/-- The composed categorical counit evaluates as the displayed actual gluing. -/
@[simp] theorem counit_hom_apply (B : OpenBasis X)
    (G : TopCat.Sheaf AddCommGrpCat.{max u v} (TopCat.of X)) (V : Opens X)
    (s : ((toMathlib.{u,v} B).obj ((fromMathlib B).obj G)).obj.obj (op V)) :
    (((equivalence.{u,v} B).counitIso.hom.app G).hom.app (op V)) s =
      counitSectionIso.{u,v} B G V s := rfl

@[simp] theorem counit_inv_apply (B : OpenBasis X)
    (G : TopCat.Sheaf AddCommGrpCat.{max u v} (TopCat.of X)) (V : Opens X)
    (s : G.obj.obj (op V)) :
    (((equivalence.{u,v} B).counitIso.inv.app G).hom.app (op V)) s =
      (counitSectionIso.{u,v} B G V).symm s := rfl

/-- The coherence law for the composed actual comparison functors. -/
@[simp] theorem functor_triangle (B : OpenBasis X) (F : BasisSheaf.{u,max u v} B) :
    (toMathlib.{u,v} B).map ((equivalence.{u,v} B).unitIso.hom.app F) ≫
      (equivalence.{u,v} B).counitIso.hom.app ((toMathlib.{u,v} B).obj F) =
        𝟙 ((toMathlib.{u,v} B).obj F) :=
  (equivalence.{u,v} B).functor_unitIso_comp F

@[simp] theorem inverse_triangle (B : OpenBasis X)
    (G : TopCat.Sheaf AddCommGrpCat.{max u v} (TopCat.of X)) :
    (equivalence.{u,v} B).unitIso.hom.app ((fromMathlib B).obj G) ≫
      (fromMathlib B).map ((equivalence.{u,v} B).counitIso.hom.app G) =
        𝟙 ((fromMathlib B).obj G) :=
  (equivalence.{u,v} B).unit_inverse_comp G

end Langlands.Sheaf.Renard.BasisMathlib
