/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationTensor
public import WeilConjectures.WeilSheaf.DerivedHom
public import WeilConjectures.WeilSheaf.TateTwistCohomology

/-!
# The tensor product of lisse Weil sheaves as a bifunctor

The tensor product `ℱ ⊗ 𝒢 = [ℱ^∨, 𝒢]` of a lisse Weil sheaf `ℱ` with a Weil sheaf `𝒢`
(`AlgebraicGeometry.WeilSheaf.tensorObj`) is functorial in both variables: the internal hom
`[A, B]` of pro-étale Weil sheaves is contravariant in `A`
(`AlgebraicGeometry.ProEtaleWeilSheaf.ihomMapLeft`) and covariant in `B`
(`AlgebraicGeometry.ProEtaleWeilSheaf.ihomMapRight`), so a morphism `f : ℱ ⟶ ℱ'` induces
`f^∨ : ℱ'^∨ ⟶ ℱ^∨` (`AlgebraicGeometry.WeilSheaf.dualMap`), and `f`, `g : 𝒢 ⟶ 𝒢'` induce
`f ⊗ g : ℱ ⊗ 𝒢 ⟶ ℱ' ⊗ 𝒢'` (`AlgebraicGeometry.WeilSheaf.tensorHom`).

## Main definitions

- `AlgebraicGeometry.LisseWeilSheaf.tensor`: the tensor product bifunctor on lisse Weil sheaves.
- `AlgebraicGeometry.LisseWeilSheaf.unit`: the constant lisse Weil sheaf `ℚ̄_ℓ`.
-/

@[expose] public section

universe u

open CategoryTheory Endofunctor

namespace AlgebraicGeometry

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

namespace ProEtaleWeilSheaf

/-- A morphism `g : B ⟶ B'` of pro-étale Weil sheaves induces `[A, B] ⟶ [A, B']`. -/
noncomputable def ihomMapRight (A : ProEtaleWeilSheaf k₀ l X) {B B' : ProEtaleWeilSheaf k₀ l X}
    (g : B ⟶ B') : ihom k₀ l X A B ⟶ ihom k₀ l X A B' :=
  ObjectProperty.homMk ⟨(AdicSheaf.ihom A.carrier).map g.hom.f, ihom_map_comm A g⟩

omit [Fact (ringChar k₀ ≠ l)] in
lemma ihomMapRight_hom_f (A : ProEtaleWeilSheaf k₀ l X) {B B' : ProEtaleWeilSheaf k₀ l X}
    (g : B ⟶ B') : (ihomMapRight A g).hom.f = (AdicSheaf.ihom A.carrier).map g.hom.f :=
  rfl

lemma ihomMapLeft_id (A B : ProEtaleWeilSheaf k₀ l X) : ihomMapLeft (𝟙 A) B = 𝟙 _ := by
  ext1
  rw [ihomMapLeft_hom_f]
  erw [Mod.ihomMap_id]
  rfl

lemma ihomMapLeft_comp {A A' A'' : ProEtaleWeilSheaf k₀ l X} (φ : A ⟶ A') (ψ : A' ⟶ A'')
    (B : ProEtaleWeilSheaf k₀ l X) :
    ihomMapLeft (φ ≫ ψ) B = ihomMapLeft ψ B ≫ ihomMapLeft φ B := by
  ext1
  rw [ihomMapLeft_hom_f]
  erw [Mod.ihomMap_comp]
  rfl

omit [Fact (ringChar k₀ ≠ l)] in
lemma ihomMapRight_id (A B : ProEtaleWeilSheaf k₀ l X) : ihomMapRight A (𝟙 B) = 𝟙 _ := by
  ext1
  rw [ihomMapRight_hom_f]
  exact (AdicSheaf.ihom A.carrier).map_id _

omit [Fact (ringChar k₀ ≠ l)] in
lemma ihomMapRight_comp (A : ProEtaleWeilSheaf k₀ l X) {B B' B'' : ProEtaleWeilSheaf k₀ l X}
    (g : B ⟶ B') (g' : B' ⟶ B'') :
    ihomMapRight A (g ≫ g') = ihomMapRight A g ≫ ihomMapRight A g' := by
  ext1
  rw [ihomMapRight_hom_f]
  exact (AdicSheaf.ihom A.carrier).map_comp _ _

/-- The internal hom is a bifunctor: the maps in the two variables commute. -/
@[reassoc]
lemma ihomMapRight_comp_ihomMapLeft {A A' : ProEtaleWeilSheaf k₀ l X} (φ : A ⟶ A')
    {B B' : ProEtaleWeilSheaf k₀ l X} (g : B ⟶ B') :
    ihomMapRight A' g ≫ ihomMapLeft φ B' = ihomMapLeft φ B ≫ ihomMapRight A g := by
  ext1
  exact (Mod.ihomMap φ.hom.f).naturality g.hom.f

end ProEtaleWeilSheaf

namespace WeilSheaf

/-- The dual `f^∨ : ℱ'^∨ ⟶ ℱ^∨` of a morphism `f : ℱ ⟶ ℱ'` of lisse Weil sheaves. -/
noncomputable def dualMap {F F' : WeilSheaf k₀ l X} (f : F ⟶ F') (hF : F.IsLisse)
    (hF' : F'.IsLisse) : F'.dual hF' ⟶ F.dual hF :=
  ObjectProperty.homMk (ProEtaleWeilSheaf.ihomMapLeft f.hom _)

lemma dualMap_id (F : WeilSheaf k₀ l X) (hF : F.IsLisse) : dualMap (𝟙 F) hF hF = 𝟙 _ :=
  ObjectProperty.hom_ext _ (ProEtaleWeilSheaf.ihomMapLeft_id _ _)

lemma dualMap_comp {F F' F'' : WeilSheaf k₀ l X} (f : F ⟶ F') (f' : F' ⟶ F'') (hF : F.IsLisse)
    (hF' : F'.IsLisse) (hF'' : F''.IsLisse) :
    dualMap (f ≫ f') hF hF'' = dualMap f' hF' hF'' ≫ dualMap f hF hF' :=
  ObjectProperty.hom_ext _ (ProEtaleWeilSheaf.ihomMapLeft_comp _ _ _)

lemma dualMap_comp_hom {F F' F'' : WeilSheaf k₀ l X} (f : F ⟶ F') (f' : F' ⟶ F'')
    (hF : F.IsLisse) (hF' : F'.IsLisse) (hF'' : F''.IsLisse) :
    (dualMap (f ≫ f') hF hF'').hom = (dualMap f' hF' hF'').hom ≫ (dualMap f hF hF').hom :=
  ProEtaleWeilSheaf.ihomMapLeft_comp _ _ _

/-- The tensor product `f ⊗ g : ℱ ⊗ 𝒢 ⟶ ℱ' ⊗ 𝒢'` of morphisms `f : ℱ ⟶ ℱ'` of lisse Weil sheaves
and `g : 𝒢 ⟶ 𝒢'` of Weil sheaves: the map `[ℱ^∨, 𝒢] ⟶ [ℱ'^∨, 𝒢']` induced by `f^∨` and `g`. -/
noncomputable def tensorHom {F F' G G' : WeilSheaf k₀ l X} (f : F ⟶ F') (g : G ⟶ G')
    (hF : F.IsLisse) (hF' : F'.IsLisse) : F.tensorObj G hF ⟶ F'.tensorObj G' hF' :=
  ObjectProperty.homMk (ProEtaleWeilSheaf.ihomMapRight (F.dual hF).obj g.hom ≫
    ProEtaleWeilSheaf.ihomMapLeft (dualMap f hF hF').hom G'.obj)

lemma tensorHom_id (F G : WeilSheaf k₀ l X) (hF : F.IsLisse) :
    tensorHom (𝟙 F) (𝟙 G) hF hF = 𝟙 _ := by
  refine ObjectProperty.hom_ext _ ?_
  rw [tensorHom, ObjectProperty.homMk_hom, dualMap_id]
  erw [ProEtaleWeilSheaf.ihomMapRight_id, ProEtaleWeilSheaf.ihomMapLeft_id]
  exact Category.comp_id _

lemma tensorHom_comp {F F' F'' G G' G'' : WeilSheaf k₀ l X} (f : F ⟶ F') (f' : F' ⟶ F'')
    (g : G ⟶ G') (g' : G' ⟶ G'') (hF : F.IsLisse) (hF' : F'.IsLisse) (hF'' : F''.IsLisse) :
    tensorHom (f ≫ f') (g ≫ g') hF hF'' = tensorHom f g hF hF' ≫ tensorHom f' g' hF' hF'' := by
  refine ObjectProperty.hom_ext _ ?_
  rw [ObjectProperty.FullSubcategory.comp_hom]
  simp only [tensorHom, ObjectProperty.homMk_hom]
  rw [dualMap_comp_hom f f' hF hF' hF'', ProEtaleWeilSheaf.ihomMapLeft_comp]
  erw [ProEtaleWeilSheaf.ihomMapRight_comp _ g.hom g'.hom]
  rw [Category.assoc, Category.assoc, ← ProEtaleWeilSheaf.ihomMapRight_comp_ihomMapLeft_assoc]

end WeilSheaf

namespace LisseWeilSheaf

variable (k₀ l X) in
/-- Blueprint `definition-weil-representation--1` (subsection
`definition-weil-representation--1`): the tensor product `(ℱ, 𝒢) ↦ ℱ ⊗ 𝒢 = [ℱ^∨, 𝒢]` of
lisse Weil sheaves, as a bifunctor (`AlgebraicGeometry.WeilSheaf.tensorObj`,
`AlgebraicGeometry.WeilSheaf.tensorHom`). -/
noncomputable def tensor :
    LisseWeilSheaf k₀ l X × LisseWeilSheaf k₀ l X ⥤ LisseWeilSheaf k₀ l X where
  obj F := ⟨F.1.obj.tensorObj F.2.obj F.1.property, F.1.property.tensorObj F.2.property⟩
  map f := ObjectProperty.homMk (WeilSheaf.tensorHom f.1.hom f.2.hom _ _)
  map_id _ := ObjectProperty.hom_ext _ (WeilSheaf.tensorHom_id _ _ _)
  map_comp _ _ := ObjectProperty.hom_ext _ (WeilSheaf.tensorHom_comp _ _ _ _ _ _ _)

variable (k₀ l X) in
/-- Blueprint `definition-weil-representation--1` (subsection
`definition-weil-representation--1`): the constant lisse Weil sheaf `ℚ̄_ℓ`, the unit for
the tensor product. -/
noncomputable def unit : LisseWeilSheaf k₀ l X :=
  ⟨WeilSheaf.adicConstant k₀ l X, WeilSheaf.isLisse_adicConstant k₀ l X⟩

end LisseWeilSheaf

end AlgebraicGeometry
