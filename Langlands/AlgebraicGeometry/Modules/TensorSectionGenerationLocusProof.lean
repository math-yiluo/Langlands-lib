import Langlands.AlgebraicGeometry.Modules.TensorSectionGenerationLocusStatement
import Langlands.AlgebraicGeometry.Modules.PullbackTensorProof
import Langlands.AlgebraicGeometry.Modules.TensorUnitorLaws
import Langlands.AlgebraicGeometry.Picard.LineBundleTensor
import Langlands.AlgebraicGeometry.Picard.AffineGenerationLocusIntersectionProof

/-! # The generation locus of a tensor product of line-bundle sections -/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

set_option backward.isDefEq.respectTransparency false

namespace Langlands.SchemeModule

open Langlands.Scheme.Modules Langlands.AlgebraicGeometry.Picard

variable {X : Scheme.{u}}

/-- The stalk map of a morphism of module sheaves at a point is an isomorphism. -/
private abbrev StalkIso {N P : X.Modules} (φ : N ⟶ P) (x : X) : Prop :=
  IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map ((Scheme.Modules.toPresheaf X).map φ))

/-- Composing with isomorphisms on both sides does not change the stalk-isomorphism condition. -/
private lemma stalkIso_iso_comp_iff {N N' P P' : X.Modules} (a : N' ⟶ N) (φ : N ⟶ P)
    (b : P ⟶ P') [IsIso a] [IsIso b] (x : X) :
    StalkIso (a ≫ φ ≫ b) x ↔ StalkIso φ x := by
  simp only [StalkIso, Functor.map_comp, isIso_comp_left_iff, isIso_comp_right_iff]

/-- The coefficient of a composite of endomorphisms of the structure module is the product. -/
private lemma unitEndCoefficient_comp (α β : structureModule X ⟶ structureModule X)
    (U : X.Opens) :
    unitEndCoefficient (α ≫ β) U = unitEndCoefficient α U * unitEndCoefficient β U := by
  change β.app U (α.app U (1 : Γ(X, U))) = _
  rw [unitEndCoefficient_app]
  rfl

/-- A composite of endomorphisms of the structure module is a stalk isomorphism exactly
when both factors are. -/
private lemma stalkIso_unitEnd_comp_iff (α β : structureModule X ⟶ structureModule X)
    (x : X) : StalkIso (α ≫ β) x ↔ StalkIso α x ∧ StalkIso β x := by
  change IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map (α ≫ β).mapPresheaf) ↔
    IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map α.mapPresheaf) ∧
      IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map β.mapPresheaf)
  rw [unitEnd_stalkIso_iff_mem_basicOpen, unitEnd_stalkIso_iff_mem_basicOpen,
    unitEnd_stalkIso_iff_mem_basicOpen, unitEndCoefficient_comp, Scheme.basicOpen_mul]
  rfl

/-- Conjugating the tensor of two endomorphisms of the structure module by the left unitor
gives their composite. -/
private lemma tensorLeftUnitor_conj_tensorMap (α β : structureSheaf X ⟶ structureSheaf X) :
    (tensorLeftUnitor (structureSheaf X)).inv ≫ tensorMap α β ≫
        (tensorLeftUnitor (structureSheaf X)).hom = α ≫ β := by
  have hsplit : tensorMap α β =
      tensorMap α (𝟙 (structureSheaf X)) ≫ tensorMap (𝟙 (structureSheaf X)) β := by
    rw [tensorMap_comp, Category.comp_id, Category.id_comp]
  rw [hsplit, Category.assoc, tensorLeftUnitor_naturality, ← Category.assoc,
    ← Category.assoc, tensorUnitors_equal, Category.assoc (tensorLeftUnitor _).inv,
    tensorRightUnitor_naturality, ← tensorUnitors_equal, Iso.inv_hom_id_assoc]

/-- Tensoring two morphisms with isomorphisms on both sides does not change the
stalk-isomorphism condition. -/
private lemma stalkIso_tensorMap_iso_comp_iff {N₁ N₁' P₁ P₁' N₂ N₂' P₂ P₂' : X.Modules}
    (a₁ : N₁' ≅ N₁) (φ : N₁ ⟶ P₁) (b₁ : P₁' ≅ P₁)
    (a₂ : N₂' ≅ N₂) (ψ : N₂ ⟶ P₂) (b₂ : P₂' ≅ P₂) (x : X) :
    StalkIso (tensorMap (a₁.hom ≫ φ ≫ b₁.inv) (a₂.hom ≫ ψ ≫ b₂.inv)) x ↔
      StalkIso (tensorMap φ ψ) x := by
  rw [← tensorMap_comp, ← tensorMap_comp]
  change StalkIso (((tensorFunctor X).mapIso (a₁.prod a₂)).hom ≫ tensorMap φ ψ ≫
    ((tensorFunctor X).mapIso (b₁.prod b₂)).inv) x ↔ _
  exact stalkIso_iso_comp_iff _ _ _ x

/-- Restriction to an open subscheme, and the inverse image along its inclusion, have the
same stalk-isomorphism condition as the original morphism at the image point. -/
private lemma stalkIso_pullback_ι_iff {N P : X.Modules} (φ : N ⟶ P) (W : X.Opens)
    (y : W.toScheme) :
    StalkIso ((Scheme.Modules.pullback W.ι).map φ) y ↔ StalkIso φ (W.ι y) :=
  (NatIso.isIso_map_iff (Functor.isoWhiskerRight
    (Scheme.Modules.restrictFunctorIsoPullback W.ι)
      (Scheme.Modules.toPresheaf W.toScheme ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} y)) φ).symm.trans
    (isIso_stalk_restrict_iff φ W y)

/-- The product of two line-bundle sections is a stalk frame exactly where both factors are. -/
theorem isStalkFrame_tensorSection_iff (L M : LineBundle X)
    (s : GlobalSections L.obj) (t : GlobalSections M.obj) (x : X) :
    IsStalkFrame (tensorObj L.obj M.obj) (tensorSection L.obj M.obj s t) x ↔
      IsStalkFrame L.obj s x ∧ IsStalkFrame M.obj t x := by
  obtain ⟨U, hxU, ⟨eL⟩⟩ := L.property x
  obtain ⟨V, hxV, ⟨eM⟩⟩ := M.property x
  let W : X.Opens := U ⊓ V
  let y : W.toScheme := ⟨x, hxU, hxV⟩
  let P := Scheme.Modules.pullback W.ι
  let c := pullbackTensorComparison W.ι
  have : IsIso c := pullbackTensorComparisonIsIso W.ι
  let eL' := pullbackTrivializationOfLE (inf_le_left : W ≤ U) L.obj eL
  let eM' := pullbackTrivializationOfLE (inf_le_right : W ≤ V) M.obj eM
  let ι := pullbackUnitIso W.ι
  let fs := sectionHom L.obj s
  let ft := sectionHom M.obj t
  let α : structureModule W.toScheme ⟶ structureModule W.toScheme :=
    ι.inv ≫ P.map fs ≫ eL'.hom
  let β : structureModule W.toScheme ⟶ structureModule W.toScheme :=
    ι.inv ≫ P.map ft ≫ eM'.hom
  have hα : StalkIso α y ↔ IsStalkFrame L.obj s x :=
    (stalkIso_iso_comp_iff _ _ _ y).trans (stalkIso_pullback_ι_iff fs W y)
  have hβ : StalkIso β y ↔ IsStalkFrame M.obj t x :=
    (stalkIso_iso_comp_iff _ _ _ y).trans (stalkIso_pullback_ι_iff ft W y)
  have hfs : P.map fs = ι.hom ≫ α ≫ eL'.inv := by simp [α]
  have hft : P.map ft = ι.hom ≫ β ≫ eM'.inv := by simp [β]
  have hnat : P.map (tensorMap fs ft) ≫ c.app (L.obj, M.obj) =
      c.app (structureSheaf X, structureSheaf X) ≫ tensorMap (P.map fs) (P.map ft) :=
    c.naturality (X := (structureSheaf X, structureSheaf X)) (Y := (L.obj, M.obj)) (fs, ft)
  have htensor : P.map (sectionHom (tensorObj L.obj M.obj) (tensorSection L.obj M.obj s t)) =
      P.map (tensorLeftUnitor (structureSheaf X)).inv ≫ c.app (structureSheaf X, structureSheaf X) ≫
        tensorMap (P.map fs) (P.map ft) ≫ inv (c.app (L.obj, M.obj)) := by
    rw [sectionHom_tensorSection, Functor.map_comp, ← reassoc_of% hnat, IsIso.hom_inv_id,
      Category.comp_id]
  have key : StalkIso
      (P.map (sectionHom (tensorObj L.obj M.obj) (tensorSection L.obj M.obj s t))) y ↔
        StalkIso α y ∧ StalkIso β y :=
    calc _ ↔ StalkIso (tensorMap (P.map fs) (P.map ft)) y := by
          rw [htensor, ← Category.assoc]
          exact stalkIso_iso_comp_iff _ _ _ y
      _ ↔ StalkIso (tensorMap α β) y := by
          rw [hfs, hft]
          exact stalkIso_tensorMap_iso_comp_iff ι α eL' ι β eM' y
      _ ↔ StalkIso (α ≫ β) y := by
          have h := tensorLeftUnitor_conj_tensorMap (X := W.toScheme) α β
          refine (stalkIso_iso_comp_iff (tensorLeftUnitor (structureSheaf W.toScheme)).inv
            (tensorMap α β) (tensorLeftUnitor (structureSheaf W.toScheme)).hom y).symm.trans ?_
          rw [h]
      _ ↔ StalkIso α y ∧ StalkIso β y := stalkIso_unitEnd_comp_iff α β y
  exact (stalkIso_pullback_ι_iff _ W y).symm.trans (key.trans (and_congr hα hβ))

/-- For line bundles, the whole trivialization open of the product of two sections is the
intersection of the two whole trivialization opens. -/
theorem tensorSectionGenerationLocus : TensorSectionGenerationLocusStatement.{u} := by
  intro X L M s t
  apply SetLike.coe_injective
  rw [trivializationOpenInterior X, Opens.coe_inf, ← lineBundle_stalkFrame_set_eq L s,
    ← lineBundle_stalkFrame_set_eq M t]
  have hset : {x | IsStalkFrame (tensorObj L.obj M.obj) (tensorSection L.obj M.obj s t) x} =
      {x | IsStalkFrame L.obj s x} ∩ {x | IsStalkFrame M.obj t x} :=
    Set.ext fun x ↦ isStalkFrame_tensorSection_iff L M s t x
  rw [hset]
  exact ((isOpen_lineBundle_stalkFrame L s).inter (isOpen_lineBundle_stalkFrame M t)).interior_eq

end Langlands.SchemeModule
