import Langlands.Cohomology.HyperextAbutmentNaturality
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

/-!
# The hyperext abutment filtration as a functor

Let `t` be a t-structure on a pretriangulated category `C`. The published module
`Langlands.Cohomology.HyperextAbutmentNaturality` shows that the abutment filtration
`F^p = filtration t K B n p` on `Hom(K, B⟦n⟧)` and its graded pieces `gr^p = F^p / F^{p+1}` are
natural in `K` (by precomposition) and in `B` (by postcomposition with `ψ⟦n⟧'`). This module
packages these maps as functors to abelian groups.

## Main definitions

* `filtrationFunctor t K n p`, `gradedFunctor t K n p : C ⥤ AddCommGrpCat`: `B ↦ F^p(K, B)` and
  `B ↦ gr^p(K, B)`, by postcomposition.
* `filtrationPrecompFunctor t B n p`, `gradedPrecompFunctor t B n p : Cᵒᵖ ⥤ AddCommGrpCat`:
  `K ↦ F^p(K, B)` and `K ↦ gr^p(K, B)`, by precomposition.
* `filtrationBifunctor t n p`, `gradedBifunctor t n p : Cᵒᵖ ⥤ C ⥤ AddCommGrpCat`: both
  variables at once.
* `filtrationι t K n p`: the inclusion of `F^p(K, -)` into the abutment functor
  `B ↦ Hom(K, B⟦n⟧)`, written `shiftFunctor C n ⋙ preadditiveCoyoneda.obj (op K)`.
* `filtrationMapOfLE t K n hpq`: the inclusion `F^q(K, -) ⟶ F^p(K, -)` for `p ≤ q`.
* `gradedπ t K n p`: the projection `F^p(K, -) ⟶ gr^p(K, -)`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated CategoryTheory.Triangulated
  Opposite

namespace Langlands.Cohomology

namespace HyperextAbutment

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] (t : TStructure C)

/-- The step `F^p` of the abutment filtration on `Hom(K, B⟦n⟧)`, as a functor of `B` by
postcomposition (`filtrationPostcomp`). -/
def filtrationFunctor (K : C) (n p : ℤ) : C ⥤ AddCommGrpCat.{v} where
  obj B := AddCommGrpCat.of (filtration t K B n p)
  map ψ := AddCommGrpCat.ofHom (filtrationPostcomp t K ψ n p)
  map_id B := AddCommGrpCat.hom_ext (filtrationPostcomp_id t K B n p)
  map_comp ψ ψ' := AddCommGrpCat.hom_ext (filtrationPostcomp_comp t K ψ ψ' n p)

@[simp]
lemma filtrationFunctor_map_hom (K : C) (n p : ℤ) {B B' : C} (ψ : B ⟶ B') :
    ((filtrationFunctor t K n p).map ψ).hom = filtrationPostcomp t K ψ n p :=
  rfl

/-- The graded piece `gr^p = F^p / F^{p+1}` of the abutment filtration on `Hom(K, B⟦n⟧)`, as a
functor of `B` by postcomposition (`gradedPostcomp`). -/
def gradedFunctor (K : C) (n p : ℤ) : C ⥤ AddCommGrpCat.{v} where
  obj B := AddCommGrpCat.of (graded t K B n p)
  map ψ := AddCommGrpCat.ofHom (gradedPostcomp t K ψ n p)
  map_id B := AddCommGrpCat.hom_ext (gradedPostcomp_id t K B n p)
  map_comp ψ ψ' := AddCommGrpCat.hom_ext (gradedPostcomp_comp t K ψ ψ' n p)

@[simp]
lemma gradedFunctor_map_hom (K : C) (n p : ℤ) {B B' : C} (ψ : B ⟶ B') :
    ((gradedFunctor t K n p).map ψ).hom = gradedPostcomp t K ψ n p :=
  rfl

/-- The step `F^p` of the abutment filtration on `Hom(K, B⟦n⟧)`, as a contravariant functor of
`K` by precomposition (`filtrationPrecomp`). -/
def filtrationPrecompFunctor (B : C) (n p : ℤ) : Cᵒᵖ ⥤ AddCommGrpCat.{v} where
  obj K := AddCommGrpCat.of (filtration t K.unop B n p)
  map φ := AddCommGrpCat.ofHom (filtrationPrecomp t φ.unop B n p)
  map_id K := AddCommGrpCat.hom_ext (filtrationPrecomp_id t K.unop B n p)
  map_comp φ φ' := AddCommGrpCat.hom_ext (filtrationPrecomp_comp t φ'.unop φ.unop B n p)

@[simp]
lemma filtrationPrecompFunctor_map_hom (B : C) (n p : ℤ) {K K' : Cᵒᵖ} (φ : K ⟶ K') :
    ((filtrationPrecompFunctor t B n p).map φ).hom = filtrationPrecomp t φ.unop B n p :=
  rfl

/-- The graded piece `gr^p` of the abutment filtration on `Hom(K, B⟦n⟧)`, as a contravariant
functor of `K` by precomposition (`gradedPrecomp`). -/
def gradedPrecompFunctor (B : C) (n p : ℤ) : Cᵒᵖ ⥤ AddCommGrpCat.{v} where
  obj K := AddCommGrpCat.of (graded t K.unop B n p)
  map φ := AddCommGrpCat.ofHom (gradedPrecomp t φ.unop B n p)
  map_id K := AddCommGrpCat.hom_ext (gradedPrecomp_id t K.unop B n p)
  map_comp φ φ' := AddCommGrpCat.hom_ext (gradedPrecomp_comp t φ'.unop φ.unop B n p)

@[simp]
lemma gradedPrecompFunctor_map_hom (B : C) (n p : ℤ) {K K' : Cᵒᵖ} (φ : K ⟶ K') :
    ((gradedPrecompFunctor t B n p).map φ).hom = gradedPrecomp t φ.unop B n p :=
  rfl

/-- The step `F^p` of the abutment filtration on `Hom(K, B⟦n⟧)` as a functor of both variables:
contravariant in `K` by precomposition, covariant in `B` by postcomposition. The two actions
commute by `filtrationPrecomp_comp_filtrationPostcomp`. -/
def filtrationBifunctor (n p : ℤ) : Cᵒᵖ ⥤ C ⥤ AddCommGrpCat.{v} where
  obj K := filtrationFunctor t K.unop n p
  map φ :=
    { app := fun B => (filtrationPrecompFunctor t B n p).map φ
      naturality := fun _ _ ψ => AddCommGrpCat.hom_ext
        (filtrationPrecomp_comp_filtrationPostcomp t φ.unop ψ n p) }
  map_id K := NatTrans.ext (funext fun B => (filtrationPrecompFunctor t B n p).map_id K)
  map_comp φ φ' := NatTrans.ext (funext fun B => (filtrationPrecompFunctor t B n p).map_comp φ φ')

/-- The graded piece `gr^p` of the abutment filtration on `Hom(K, B⟦n⟧)` as a functor of both
variables. The two actions commute by `gradedPrecomp_comp_gradedPostcomp`. -/
def gradedBifunctor (n p : ℤ) : Cᵒᵖ ⥤ C ⥤ AddCommGrpCat.{v} where
  obj K := gradedFunctor t K.unop n p
  map φ :=
    { app := fun B => (gradedPrecompFunctor t B n p).map φ
      naturality := fun _ _ ψ => AddCommGrpCat.hom_ext
        (gradedPrecomp_comp_gradedPostcomp t φ.unop ψ n p) }
  map_id K := NatTrans.ext (funext fun B => (gradedPrecompFunctor t B n p).map_id K)
  map_comp φ φ' := NatTrans.ext (funext fun B => (gradedPrecompFunctor t B n p).map_comp φ φ')

/-- The inclusion of `F^p(K, B)` into `Hom(K, B⟦n⟧)`, natural in `B`. -/
def filtrationι (K : C) (n p : ℤ) :
    filtrationFunctor t K n p ⟶ shiftFunctor C n ⋙ preadditiveCoyoneda.obj (op K) where
  app B := AddCommGrpCat.ofHom (filtration t K B n p).subtype
  naturality _ _ _ := rfl

@[simp]
lemma filtrationι_app_hom_apply (K : C) (n p : ℤ) (B : C) (f : filtration t K B n p) :
    ((filtrationι t K n p).app B).hom f = (f : ShiftedHom K B n) :=
  rfl

/-- The inclusion `F^q(K, B) ⟶ F^p(K, B)` for `p ≤ q`, natural in `B`. -/
def filtrationMapOfLE (K : C) (n : ℤ) {p q : ℤ} (hpq : p ≤ q) :
    filtrationFunctor t K n q ⟶ filtrationFunctor t K n p where
  app _ := AddCommGrpCat.ofHom (AddSubgroup.inclusion (filtration_le_of_le hpq))
  naturality _ _ _ := rfl

@[simp]
lemma filtrationMapOfLE_app_hom_apply (K : C) (n : ℤ) {p q : ℤ} (hpq : p ≤ q) (B : C)
    (f : filtration t K B n q) :
    ((filtrationMapOfLE t K n hpq).app B).hom f =
      AddSubgroup.inclusion (filtration_le_of_le hpq) f :=
  rfl

/-- The projection `F^p(K, B) ⟶ gr^p(K, B)`, natural in `B`. -/
def gradedπ (K : C) (n p : ℤ) : filtrationFunctor t K n p ⟶ gradedFunctor t K n p where
  app _ := AddCommGrpCat.ofHom (QuotientAddGroup.mk' _)
  naturality _ _ _ := rfl

@[simp]
lemma gradedπ_app_hom_apply (K : C) (n p : ℤ) (B : C) (f : filtration t K B n p) :
    ((gradedπ t K n p).app B).hom f = QuotientAddGroup.mk f :=
  rfl

end HyperextAbutment

end Langlands.Cohomology
