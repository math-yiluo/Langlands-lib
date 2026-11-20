import Langlands.AbelianScheme.PolarizedFiniteLevel.ZariskiGluingScheme
import Langlands.AbelianScheme.AbelianSchemeStructureOfOpenCoverProof
import Langlands.AbelianScheme.PointedMorphismRigidityProof
import Langlands.AlgebraicGeometry.Picard.FamilyBaseChange

/-! # The glued abelian scheme of a rigid family of data -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj
open CategoryTheory.MonoidalCategory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open Langlands.AlgebraicGeometry.Picard

variable {P : Prerequisites.{u}} {g d n : ℕ} {T T' : Scheme.{u}}

/-- The unit section of an abelian scheme is the left component of its unit morphism. -/
theorem unitSection_eq_one_left (A : AbelianScheme T) : unitSection A = η[A.X].left := by
  change (SemiCartesianMonoidalCategory.toUnit (𝟙_ (Over T)) ≫ η[A.X]).left = _
  rw [SemiCartesianMonoidalCategory.toUnit_unit, Category.id_comp]

/-- Transition maps preserve unit sections. -/
theorem PolarizedIso.unitSection_overMap {c : Datum P T g d n} {c' : Datum P T' g d n}
    {b : T ⟶ T'} (θ : PolarizedIso c (c'.pullback b)) :
    unitSection c.abelian ≫ θ.overMap = b ≫ unitSection c'.abelian := by
  rw [PolarizedIso.overMap, ← Category.assoc, unitSection_hom]
  exact unitSection_baseChange_fst b c'.abelian

/-- An isomorphism of the underlying pointed schemes of two abelian schemes preserving the
unit sections is an isomorphism of abelian schemes (rigidity of pointed morphisms). -/
def abelianIsoOfUnit {A B : AbelianScheme T} (e : A.X ≅ B.X)
    (he : η[A.X] ≫ e.hom = η[B.X]) : A ≅ B :=
  have := A.smooth
  have := A.proper
  have := B.smooth
  have := B.proper
  have : IsMonHom e.hom := pointedMorphismRigidity T A.toGrp B.toGrp (AbelianScheme.isAbelian A)
    inferInstance inferInstance inferInstance e.hom he
  have : IsMonHom e.inv := pointedMorphismRigidity T B.toGrp A.toGrp (AbelianScheme.isAbelian B)
    inferInstance inferInstance inferInstance e.inv (by rw [← he, Category.assoc,
      e.hom_inv_id, Category.comp_id])
  { hom := Additive.ofMul (Grp.homMk e.hom)
    inv := Additive.ofMul (Grp.homMk e.inv)
    hom_inv_id := by
      apply congrArg Additive.ofMul
      ext1
      ext1
      change (e.hom ≫ e.inv).left = CommaMorphism.left (𝟙 A.X)
      rw [e.hom_inv_id]
    inv_hom_id := by
      apply congrArg Additive.ofMul
      ext1
      ext1
      change (e.inv ≫ e.hom).left = CommaMorphism.left (𝟙 B.X)
      rw [e.inv_hom_id] }

@[simp] theorem hom_abelianIsoOfUnit_hom {A B : AbelianScheme T} (e : A.X ≅ B.X)
    (he : η[A.X] ≫ e.hom = η[B.X]) : hom (abelianIsoOfUnit e he).hom = e.hom.left :=
  rfl

namespace ZariskiGluing

variable {S : Scheme.{u}} {J : Type*} {U : J → S.Opens}
  (hU : iSup U = ⊤) (c : ∀ W : SubOpens U, Datum P W.1.toScheme g d n)
  (hrig : ∀ (W : SubOpens U) (α : PolarizedIso (c W) (c W)), α = PolarizedIso.refl (c W))
  (θ : ∀ (W W' : SubOpens U) (h : W.1 ≤ W'.1),
    PolarizedIso (c W) ((c W').pullback (S.homOfLE h)))

/-- The glued scheme. -/
abbrev glued : Scheme.{u} := colimit (gluingData hU c hrig θ).functor

/-- The inclusion of a piece into the glued scheme. -/
abbrev gluedι (W : SubOpens U) : (c W).abelian.X.left ⟶ glued hU c hrig θ :=
  colimit.ι (gluingData hU c hrig θ).functor W

/-- The local unit sections are compatible with the transition maps. -/
theorem unitSection_compat {W W' : (subCover hU).I₀} (h : W ⟶ W') :
    (subCover hU).trans h ≫ unitSection (c W').abelian ≫ gluedι hU c hrig θ W' =
      unitSection (c W).abelian ≫ gluedι hU c hrig θ W := by
  rw [subCover_trans, ← Category.assoc,
    ← (θ W W' (leOfHom h)).unitSection_overMap, Category.assoc]
  congr 1
  exact colimit.w (gluingData hU c hrig θ).functor h

/-- The glued unit section. -/
def gluedUnit : S ⟶ glued hU c hrig θ :=
  (subCover hU).glueMorphismsOfLocallyDirected
    (fun W => unitSection (c W).abelian ≫ gluedι hU c hrig θ W)
    (unitSection_compat hU c hrig θ)

theorem gluedUnit_restrict (W : SubOpens U) :
    W.1.ι ≫ gluedUnit hU c hrig θ = unitSection (c W).abelian ≫ gluedι hU c hrig θ W :=
  (subCover hU).map_glueMorphismsOfLocallyDirected _ (unitSection_compat hU c hrig θ) W

theorem gluedUnit_toBase :
    gluedUnit hU c hrig θ ≫ (gluingData hU c hrig θ).toBase = 𝟙 S := by
  apply (subCover hU).hom_ext
  intro W
  change W.1.ι ≫ _ = W.1.ι ≫ _
  rw [← Category.assoc, gluedUnit_restrict, Category.assoc,
    Scheme.Cover.RelativeGluingData.ι_toBase, ← Category.assoc, Category.comp_id]
  change (unitSection (c W).abelian ≫ (c W).abelian.X.hom) ≫ W.1.ι = W.1.ι
  rw [unitSection_comp, Category.id_comp]

/-- The glued scheme over `S`. -/
abbrev gluedOver : Over S := Over.mk (gluingData hU c hrig θ).toBase

/-- The glued unit section, as a point of the glued scheme over `S`. -/
def gluedSection : 𝟙_ (Over S) ⟶ gluedOver hU c hrig θ :=
  Over.homMk (gluedUnit hU c hrig θ) (gluedUnit_toBase hU c hrig θ)

/-- The pullback of the glued scheme to a piece is the piece. -/
def localIso (W : SubOpens U) :
    (Over.pullback ((subCover hU).f W)).obj (gluedOver hU c hrig θ) ≅ (c W).abelian.X :=
  Over.isoMk (gluingData_isPullback hU c hrig θ W).flip.isoPullback.symm
    (IsPullback.isoPullback_inv_snd _)

theorem exists_gluedAbelian :
    ∃ (B : AbelianScheme S) (e : gluedOver hU c hrig θ ≅ B.X),
      gluedSection hU c hrig θ ≫ e.hom = η[B.X] :=
  abelianSchemeStructureOfOpenCover S (gluedOver hU c hrig θ) (gluedSection hU c hrig θ)
    (subCover hU) fun W => ⟨(c W).abelian, ⟨localIso hU c hrig θ W⟩⟩

/-- The glued abelian scheme. -/
def gluedAbelian : AbelianScheme S := (exists_gluedAbelian hU c hrig θ).choose

/-- The glued scheme over `S` is the underlying scheme of the glued abelian scheme. -/
def gluedIso : gluedOver hU c hrig θ ≅ (gluedAbelian hU c hrig θ).X :=
  (exists_gluedAbelian hU c hrig θ).choose_spec.choose

theorem gluedIso_unit :
    gluedSection hU c hrig θ ≫ (gluedIso hU c hrig θ).hom = η[(gluedAbelian hU c hrig θ).X] :=
  (exists_gluedAbelian hU c hrig θ).choose_spec.choose_spec

theorem unitSection_gluedIso_inv :
    unitSection (gluedAbelian hU c hrig θ) ≫ (gluedIso hU c hrig θ).inv.left =
      gluedUnit hU c hrig θ := by
  rw [unitSection_eq_one_left, ← gluedIso_unit]
  change (gluedSection hU c hrig θ ≫ (gluedIso hU c hrig θ).hom ≫
    (gluedIso hU c hrig θ).inv).left = _
  rw [Iso.hom_inv_id, Category.comp_id]
  rfl

/-- The restriction of the glued abelian scheme to a piece, as a scheme over the piece. -/
def restrictOverIso (W : SubOpens U) :
    ((baseChange W.1.ι).obj (gluedAbelian hU c hrig θ)).X ≅ (c W).abelian.X :=
  (Over.pullback W.1.ι).mapIso (gluedIso hU c hrig θ).symm ≪≫ localIso hU c hrig θ W

theorem restrictOverIso_hom_left_gluedι (W : SubOpens U) :
    (restrictOverIso hU c hrig θ W).hom.left ≫ gluedι hU c hrig θ W =
      pullback.fst (gluedAbelian hU c hrig θ).X.hom W.1.ι ≫ (gluedIso hU c hrig θ).inv.left := by
  have h1 : (localIso hU c hrig θ W).hom.left ≫ gluedι hU c hrig θ W =
      pullback.fst (gluingData hU c hrig θ).toBase W.1.ι :=
    IsPullback.isoPullback_inv_fst (gluingData_isPullback hU c hrig θ W).flip
  change ((Over.pullback W.1.ι).map (gluedIso hU c hrig θ).inv).left ≫
    (localIso hU c hrig θ W).hom.left ≫ gluedι hU c hrig θ W = _
  rw [h1]
  simp only [Over.pullback_map_left]
  exact pullback.lift_fst _ _ _

theorem restrictOverIso_unit (W : SubOpens U) :
    η[((baseChange W.1.ι).obj (gluedAbelian hU c hrig θ)).X] ≫
      (restrictOverIso hU c hrig θ W).hom = η[(c W).abelian.X] := by
  apply Over.OverMorphism.ext
  have hm : Mono (gluedι hU c hrig θ W) := inferInstance
  apply (cancel_mono (gluedι hU c hrig θ W)).mp
  change η[((baseChange W.1.ι).obj (gluedAbelian hU c hrig θ)).X].left ≫
      (restrictOverIso hU c hrig θ W).hom.left ≫ gluedι hU c hrig θ W =
    η[(c W).abelian.X].left ≫ gluedι hU c hrig θ W
  rw [restrictOverIso_hom_left_gluedι, ← unitSection_eq_one_left, ← unitSection_eq_one_left,
    ← gluedUnit_restrict, ← Category.assoc, unitSection_baseChange_fst, Category.assoc,
    unitSection_gluedIso_inv]

/-- The restriction of the glued abelian scheme to a piece is the piece. -/
def restrictIso (W : SubOpens U) :
    (baseChange W.1.ι).obj (gluedAbelian hU c hrig θ) ≅ (c W).abelian :=
  abelianIsoOfUnit (restrictOverIso hU c hrig θ W) (restrictOverIso_unit hU c hrig θ W)

theorem hom_restrictIso_gluedι (W : SubOpens U) :
    hom (restrictIso hU c hrig θ W).hom ≫ gluedι hU c hrig θ W =
      pullback.fst (gluedAbelian hU c hrig θ).X.hom W.1.ι ≫ (gluedIso hU c hrig θ).inv.left :=
  restrictOverIso_hom_left_gluedι hU c hrig θ W

end ZariskiGluing

end Langlands.AbelianScheme.PolarizedFiniteLevel
