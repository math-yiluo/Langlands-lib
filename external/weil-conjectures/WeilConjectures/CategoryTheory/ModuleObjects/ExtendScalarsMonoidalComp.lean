/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.ChangeOfScalarsSquare
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsMonoidal
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.NaturalTransformationOplax

/-!
# The compatibilities of extension of scalars are monoidal

Let `C` be a braided monoidal category with coequalizers preserved by tensoring on either side,
and `φ : R ⟶ S`, `ψ : S ⟶ T` morphisms of commutative algebra objects of `C`. For the strong
monoidal structures `Mod.extendScalarsMonoidal` of the extensions of scalars, the transitivity
isomorphism `Mod.extendScalarsComp φ ψ : T ⊗_R - ≅ T ⊗_S (S ⊗_R -)` and the isomorphism
`Mod.extendScalarsIsoOfEq` between the extensions of scalars along equal morphisms are monoidal
natural isomorphisms (`Mod.isMonoidal_extendScalarsComp_hom`,
`Mod.isMonoidal_extendScalarsIsoOfEq_hom`).

Both are comparison isomorphisms `Adjunction.leftAdjointUniq` of left adjoints of the
restrictions of scalars, which are lax monoidal (`Mod.comapLaxMonoidal`), and the corresponding
isomorphisms `Mod.comapComp` and `Mod.comapCongr` of restrictions of scalars, whose components
are identities, are monoidal (`Mod.isMonoidal_comapComp_hom`, `Mod.isMonoidal_comapCongr_hom`).
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonObj Limits

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  {R S T : C} [MonObj R] [MonObj S] [MonObj T] [IsCommMonObj R] [IsCommMonObj S]
  [IsCommMonObj T]

section Comap

variable (φ : R ⟶ S) (ψ : S ⟶ T) [IsMonHom φ] [IsMonHom ψ]

/-- The isomorphism `(φ ≫ ψ)^* ≅ ψ^* ⋙ φ^*` of restrictions of scalars is monoidal for the lax
monoidal structures `Mod.comapLaxMonoidal`. -/
lemma isMonoidal_comapComp_hom :
    letI := comapLaxMonoidal φ
    letI := comapLaxMonoidal ψ
    letI := comapLaxMonoidal (φ ≫ ψ)
    NatTrans.IsMonoidal (comapComp φ ψ).hom := by
  let := comapLaxMonoidal φ
  let := comapLaxMonoidal ψ
  let := comapLaxMonoidal (φ ≫ ψ)
  constructor
  · apply Mod.hom_ext
    simp only [Mod.comp_hom', Functor.LaxMonoidal.comp_ε]
    simp only [Functor.comp_obj, comapComp_hom_app_hom, comap_map_hom]
    exact Category.comp_id _
  · intro M N
    apply Mod.hom_ext
    rw [← cancel_epi (tensorObjπ ((comap (φ ≫ ψ)).obj M) ((comap (φ ≫ ψ)).obj N))]
    simp only [Mod.comp_hom', Functor.LaxMonoidal.comp_μ]
    erw [tensorObjπ_comapTensorHom_hom_assoc, tensorObjπ_tensorHom_hom_whisker_assoc,
      tensorObjπ_comapTensorHom_hom_assoc]
    simp only [Functor.comp_obj, comapComp_hom_app_hom, comap_map_hom]
    erw [Category.comp_id, id_whiskerRight, Category.id_comp, MonoidalCategory.whiskerLeft_id,
      Category.id_comp]
    exact (tensorObjπ_comapTensorHom_hom ψ M N).symm

/-- The isomorphism `φ^* ≅ φ'^*` of restrictions of scalars along equal morphisms is monoidal
for the lax monoidal structures `Mod.comapLaxMonoidal`. -/
lemma isMonoidal_comapCongr_hom {φ φ' : R ⟶ S} [IsMonHom φ] [IsMonHom φ'] (h : φ = φ') :
    letI := comapLaxMonoidal φ
    letI := comapLaxMonoidal φ'
    NatTrans.IsMonoidal (comapCongr h).hom := by
  subst h
  let := comapLaxMonoidal φ
  have e : comapCongr (rfl : φ = φ) = Iso.refl _ :=
    Iso.ext (NatTrans.ext (funext fun M ↦ Mod.hom_ext _ _ (comapCongr_hom_app_hom rfl M)))
  rw [e]
  exact NatTrans.IsMonoidal.id

end Comap
section ExtendScalars

variable (φ : R ⟶ S) (ψ : S ⟶ T) [IsMonHom φ] [IsMonHom ψ]

/-- The adjunction `S ⊗_R - ⊣ φ^*` is monoidal for the strong monoidal structure
`Mod.extendScalarsMonoidal` and the lax monoidal structure `Mod.comapLaxMonoidal`. -/
lemma isMonoidal_extendRestrictAdjunction :
    letI := comapLaxMonoidal φ
    letI := extendScalarsMonoidal φ
    (extendRestrictAdjunction φ).IsMonoidal := by
  let := comapLaxMonoidal φ
  let := (extendRestrictAdjunction φ).leftAdjointOplaxMonoidal
  exact (inferInstance : (extendRestrictAdjunction φ).IsMonoidal)

set_option synthInstance.maxHeartbeats 100000 in
-- the search for `(extendScalars φ ⋙ extendScalars ψ).LaxMonoidal` first explores braidings
/-- The transitivity isomorphism `T ⊗_R - ≅ T ⊗_S (S ⊗_R -)` of extension of scalars is a
monoidal natural isomorphism, for the strong monoidal structures `Mod.extendScalarsMonoidal`. -/
lemma isMonoidal_extendScalarsComp_hom :
    letI := extendScalarsMonoidal φ
    letI := extendScalarsMonoidal ψ
    letI := extendScalarsMonoidal (φ ≫ ψ)
    NatTrans.IsMonoidal (extendScalarsComp φ ψ).hom := by
  let := comapLaxMonoidal φ
  let := comapLaxMonoidal ψ
  let := comapLaxMonoidal (φ ≫ ψ)
  let := extendScalarsMonoidal φ
  let := extendScalarsMonoidal ψ
  let := extendScalarsMonoidal (φ ≫ ψ)
  have := isMonoidal_extendRestrictAdjunction φ
  have := isMonoidal_extendRestrictAdjunction ψ
  have := isMonoidal_extendRestrictAdjunction (φ ≫ ψ)
  have := isMonoidal_comapComp_hom φ ψ
  have : NatTrans.IsMonoidal (comapComp φ ψ).symm.hom :=
    inferInstanceAs (NatTrans.IsMonoidal (comapComp φ ψ).inv)
  have := Adjunction.isMonoidal_ofNatIsoRight
    ((extendRestrictAdjunction φ).comp (extendRestrictAdjunction ψ)) (comapComp φ ψ).symm
  exact Adjunction.isMonoidal_leftAdjointUniq_hom _ _

/-- The isomorphism `S ⊗_{R,φ} - ≅ S ⊗_{R,φ'} -` between the extensions of scalars along equal
morphisms is a monoidal natural isomorphism, for the strong monoidal structures
`Mod.extendScalarsMonoidal`. -/
lemma isMonoidal_extendScalarsIsoOfEq_hom {φ φ' : R ⟶ S} [IsMonHom φ] [IsMonHom φ']
    (h : φ = φ') :
    letI := extendScalarsMonoidal φ
    letI := extendScalarsMonoidal φ'
    NatTrans.IsMonoidal (extendScalarsIsoOfEq h).hom := by
  let := comapLaxMonoidal φ
  let := comapLaxMonoidal φ'
  let := extendScalarsMonoidal φ
  let := extendScalarsMonoidal φ'
  have := isMonoidal_extendRestrictAdjunction φ
  have := isMonoidal_extendRestrictAdjunction φ'
  have := isMonoidal_comapCongr_hom h
  have : NatTrans.IsMonoidal (comapCongr h).symm.hom :=
    inferInstanceAs (NatTrans.IsMonoidal (comapCongr h).inv)
  have := Adjunction.isMonoidal_ofNatIsoRight (extendRestrictAdjunction φ') (comapCongr h).symm
  exact Adjunction.isMonoidal_leftAdjointUniq_hom _ _

end ExtendScalars

end CategoryTheory.Mod
