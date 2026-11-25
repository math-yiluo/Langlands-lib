/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHomUnit
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomOver
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Opposite

/-!
# The internal hom out of free sheaves of modules

Let `R` be a sheaf of commutative rings on a site `(C, J)`. For a sheaf of modules `N` over `R`:

* `SheafOfModules.homObjUnitIso`: the internal hom `homObj R N` out of the unit is `N`;
* the internal hom is additive in its first variable, so that it sends finite biproducts to
  finite biproducts;
* `SheafOfModules.homObjFreeIso`: for a finite type `I`, `homObj (free I) N ≅ ⨁_I N`;
* `SheafOfModules.IsFiniteLocallyFree.homObj_unit`: the dual `homObj M R` of a finite locally
  free sheaf of modules `M` is finite locally free.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace SheafOfModules

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})] {R : Sheaf J CommRingCat.{u}}

-- The underlying sheaf of rings of the sheaf of commutative rings `R`.
set_option hygiene false in
local notation "𝓡" => (sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R

variable (N : SheafOfModules.{u} 𝓡)

/-- **The internal hom out of the unit.** `homObj R N ≅ N`. -/
noncomputable def homObjUnitIso : homObj (unit 𝓡) N ≅ N :=
  (fullyFaithfulForget _).preimageIso (PresheafOfModules.homObjUnitIso (R := R.obj) N.val)

variable {N} in
lemma homObjMap_add_left {M M' N' : SheafOfModules.{u} 𝓡} (f f' : M' ⟶ M) (g : N ⟶ N') :
    homObjMap (f + f') g = homObjMap f g + homObjMap f' g :=
  hom_ext (PresheafOfModules.homObjMap_add_left f.val f'.val g.val)

instance : ((homFunctor R).flip.obj N).Additive where
  map_add {_ _ f g} := by
    change homObjMap (f + g).unop (𝟙 N) = homObjMap f.unop (𝟙 N) + homObjMap g.unop (𝟙 N)
    rw [unop_add]
    exact homObjMap_add_left _ _ _

variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The internal hom out of a finite free module.** For a finite type `I`,
`homObj (free I) N ≅ ⨁_I N`. -/
noncomputable def homObjFreeIso (I : Type u) [Fintype I] :
    homObj (free I) N ≅ ⨁ fun _ : I ↦ N :=
  ((homFunctor R).flip.obj N).mapIso (biproduct.isoCoproduct fun _ : I ↦ unit 𝓡).op ≪≫
    ((homFunctor R).flip.obj N).opMapBiproductIso (fun _ : I ↦ unit 𝓡) ≪≫
      biproduct.mapIso fun _ ↦ homObjUnitIso N

variable {N} in
/-- **The dual of a finite free module.** For a finite type `I`, `homObj (free I) R ≅ free I`. -/
noncomputable def homObjFreeUnitIso (I : Type u) [Fintype I] :
    homObj (free I) (unit 𝓡) ≅ free I :=
  homObjFreeIso (unit 𝓡) I ≪≫ biproduct.isoCoproduct _

omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The dual of a finite locally free module is finite locally free.** Over each `X` on which
`M` is free on a finite type `I`, the dual `homObj M R` is `homObj (free I) R ≅ free I`. -/
theorem IsFiniteLocallyFree.homObj_unit [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}] (M : SheafOfModules.{u} 𝓡)
    [M.IsFiniteLocallyFree] : (homObj M (unit 𝓡)).IsFiniteLocallyFree := by
  obtain ⟨q, hq, hf⟩ := IsFiniteLocallyFree.exists_localGeneratorsData (M := M)
  have (i : q.I) : Finite (q.generators i).I := (hf.isFiniteType i).finite
  refine isFiniteLocallyFree_of_exists_over_iso_free q.X q.coversTop (fun i ↦ (q.generators i).I)
    fun i ↦ ⟨?_⟩
  let := Fintype.ofFinite (q.generators i).I
  exact overHomObjIso M (unit 𝓡) (q.X i) ≪≫
    ((homFunctor (R.over (q.X i))).flip.obj (unit _)).mapIso (asIso (q.generators i).π).op ≪≫
      homObjFreeUnitIso _

end SheafOfModules
