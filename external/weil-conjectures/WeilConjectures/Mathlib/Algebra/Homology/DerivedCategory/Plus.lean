/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.CategoryTheory.Triangulated.TStructure.ETrunc
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# Truncations and homology in the bounded below derived category

Let `C` be an abelian category. For the canonical t-structure
`DerivedCategory.Plus.TStructure.t` on `DerivedCategory.Plus C`, we show that the truncation
morphisms induce isomorphisms in homology in the expected range of degrees, and that
`τ_{≥ q} τ_{< q + 1} X` is isomorphic to the single complex on `H^q(X)` in degree `q`.

## Main statements

- `DerivedCategory.Plus.isIso_homologyFunctor_map_truncLTι_app`: `H^n(τ_{<a} X) ≅ H^n(X)`
  for `n < a`.
- `DerivedCategory.Plus.isIso_homologyFunctor_map_truncGEπ_app`: `H^n(X) ≅ H^n(τ_{≥a} X)`
  for `a ≤ n`.
- `DerivedCategory.Plus.nonempty_eTruncGE_eTruncLT_iso_singleFunctor`:
  `τ_{≥ q} τ_{< q + 1} X ≅ H^q(X)[-q]`.
- `DerivedCategory.Plus.eTruncLTCompETruncGEIso`: the same isomorphism, natural in `X`.

-/

@[expose] public section

open CategoryTheory Category Limits Triangulated Pretriangulated

open DerivedCategory.Plus.TStructure (t)

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

namespace DerivedCategory.Plus

/-- `H^n(τ_{<a} X) ⟶ H^n(X)` is an isomorphism for `n < a`. -/
lemma isIso_homologyFunctor_map_truncLTι_app (X : Plus C) (a n : ℤ) (h : n < a) :
    IsIso ((homologyFunctor C n).map ((t.truncLTι a).app X)) := by
  have hT := ι.map_distinguished _ (t.triangleLTGE_distinguished a X)
  have : (ι.mapTriangle.obj ((t.triangleLTGE a).obj X)).obj₁.IsLE (a - 1) :=
    inferInstanceAs ((ι.obj ((t.truncLT a).obj X)).IsLE (a - 1))
  have : (ι.mapTriangle.obj ((t.triangleLTGE a).obj X)).obj₃.IsGE a :=
    inferInstanceAs ((ι.obj ((t.truncGE a).obj X)).IsGE a)
  exact DerivedCategory.isIso_homologyFunctor_map_mor₁_of_isLE_of_isGE _ hT a n h

/-- `H^n(X) ⟶ H^n(τ_{≥a} X)` is an isomorphism for `a ≤ n`. -/
lemma isIso_homologyFunctor_map_truncGEπ_app (X : Plus C) (a n : ℤ) (h : a ≤ n) :
    IsIso ((homologyFunctor C n).map ((t.truncGEπ a).app X)) := by
  have hT := ι.map_distinguished _ (t.triangleLTGE_distinguished a X)
  have : (ι.mapTriangle.obj ((t.triangleLTGE a).obj X)).obj₁.IsLE (a - 1) :=
    inferInstanceAs ((ι.obj ((t.truncLT a).obj X)).IsLE (a - 1))
  have : (ι.mapTriangle.obj ((t.triangleLTGE a).obj X)).obj₃.IsGE a :=
    inferInstanceAs ((ι.obj ((t.truncGE a).obj X)).IsGE a)
  exact DerivedCategory.isIso_homologyFunctor_map_mor₂_of_isLE_of_isGE _ hT a n h

/-- For `q : ℤ`, the object `τ_{≥ q} τ_{< q + 1} X` (written with the `EInt`-indexed
truncations, as in `t.spectralObject X`) is isomorphic to the single complex
`(singleFunctor C q).obj (H^q X)`. -/
lemma nonempty_eTruncGE_eTruncLT_iso_singleFunctor (X : Plus C) (q : ℤ) :
    Nonempty ((t.eTruncGE.obj (q : EInt)).obj ((t.eTruncLT.obj ((q + 1 : ℤ) : EInt)).obj X) ≅
      (singleFunctor C q).obj ((homologyFunctor C q).obj X)) := by
  let Y := (t.truncGE q).obj ((t.truncLT (q + 1)).obj X)
  obtain ⟨A, ⟨e⟩⟩ :=
    DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE (ι.obj Y) q
  let e' : Y ≅ (singleFunctor C q).obj A := ι.preimageIso e
  have := isIso_homologyFunctor_map_truncGEπ_app ((t.truncLT (q + 1)).obj X) q q le_rfl
  have := isIso_homologyFunctor_map_truncLTι_app X (q + 1) q (by lia)
  exact ⟨e' ≪≫ (singleFunctor C q).mapIso
    (((singleFunctorCompHomologyFunctorIso C q).app A).symm ≪≫
      (homologyFunctor C q).mapIso e'.symm ≪≫
      (asIso ((homologyFunctor C q).map ((t.truncGEπ q).app _))).symm ≪≫
      asIso ((homologyFunctor C q).map ((t.truncLTι (q + 1)).app X)))⟩

instance (n : ℤ) : (singleFunctor C n).Faithful :=
  Functor.Faithful.of_comp_iso (singleFunctorιIso C n)

instance (n : ℤ) : (singleFunctor C n).Full :=
  Functor.Full.of_comp_faithful_iso (singleFunctorιIso C n)

/-- The single functor `C ⥤ DerivedCategory.Plus C` in degree `n` followed by the homology
in degree `n` is isomorphic to the identity. -/
noncomputable def singleFunctorCompHomologyFunctorIso (n : ℤ) :
    singleFunctor C n ⋙ homologyFunctor C n ≅ 𝟭 C :=
  DerivedCategory.singleFunctorCompHomologyFunctorIso C n

/-- The truncation `τ_{≥ q} τ_{< q + 1}` on `DerivedCategory.Plus C`, written with the
`EInt`-indexed truncations as in `t.spectralObject`, is isomorphic to `X ↦ H^q(X)[-q]`,
naturally in `X`.

Since the single functor in degree `q` is fully faithful and `τ_{≥ q} τ_{< q + 1}` lands in its
essential image (`DerivedCategory.Plus.nonempty_eTruncGE_eTruncLT_iso_singleFunctor`), this
truncation factors through the single functor, and the factorization is identified with `H^q`
using that the truncation maps induce isomorphisms on `H^q`. -/
noncomputable def eTruncLTCompETruncGEIso (q : ℤ) :
    (t (C := C)).eTruncLT.obj ((q + 1 : ℤ) : EInt) ⋙ (t (C := C)).eTruncGE.obj (q : EInt) ≅
      homologyFunctor C q ⋙ singleFunctor C q :=
  let Φ := (t (C := C)).eTruncLT.obj ((q + 1 : ℤ) : EInt) ⋙ (t (C := C)).eTruncGE.obj (q : EInt)
  let S := singleFunctor C q
  have hΦ : ∀ X, S.essImage (Φ.obj X) := fun X ↦
    ⟨_, ⟨(nonempty_eTruncGE_eTruncLT_iso_singleFunctor X q).some.symm⟩⟩
  let L := S.essImage.lift Φ hΦ
  let Φ' := L ⋙ S.toEssImage.inv
  let e₁ : Φ' ⋙ S ≅ Φ :=
    Functor.isoWhiskerLeft L (Functor.isoWhiskerLeft S.toEssImage.inv S.toEssImageCompι.symm ≪≫
      Functor.isoWhiskerRight S.toEssImage.asEquivalence.counitIso S.essImage.ι ≪≫
      Functor.leftUnitor _) ≪≫ S.essImage.liftCompιIso Φ hΦ
  let e₂ : Φ ⋙ homologyFunctor C q ≅ Φ' :=
    Functor.isoWhiskerRight e₁.symm _ ≪≫
      Functor.isoWhiskerLeft Φ' (singleFunctorCompHomologyFunctorIso q) ≪≫ Functor.rightUnitor _
  let α : (t (C := C)).eTruncLT.obj ((q + 1 : ℤ) : EInt) ⋙ homologyFunctor C q ⟶
      homologyFunctor C q :=
    Functor.whiskerRight ((t (C := C)).eTruncLTι ((q + 1 : ℤ) : EInt)) (homologyFunctor C q)
  let β : (t (C := C)).eTruncLT.obj ((q + 1 : ℤ) : EInt) ⋙ homologyFunctor C q ⟶
      Φ ⋙ homologyFunctor C q :=
    Functor.whiskerLeft ((t (C := C)).eTruncLT.obj ((q + 1 : ℤ) : EInt))
      (Functor.whiskerRight ((t (C := C)).eTruncGEπ (q : EInt)) (homologyFunctor C q))
  have (X : Plus C) : IsIso (α.app X) :=
    isIso_homologyFunctor_map_truncLTι_app X (q + 1) q (by lia)
  have (X : Plus C) : IsIso (β.app X) :=
    isIso_homologyFunctor_map_truncGEπ_app _ q q le_rfl
  have : IsIso α := NatIso.isIso_of_isIso_app _
  have : IsIso β := NatIso.isIso_of_isIso_app _
  e₁.symm ≪≫ Functor.isoWhiskerRight (e₂.symm ≪≫ (asIso β).symm ≪≫ asIso α) S

instance (q : ℤ) (X : Plus C) : IsIso ((homologyFunctor C q).map ((t.eTruncGEπ (q : EInt)).app
    ((t.eTruncLT.obj ((q + 1 : ℤ) : EInt)).obj X))) :=
  isIso_homologyFunctor_map_truncGEπ_app ((t.truncLT (q + 1)).obj X) q q le_rfl

/-- The isomorphism `τ_{≥ q} τ_{< q + 1} X ≅ H^q(X)[-q]` induces on `H^q` the inverse of the map
induced by the projection `τ_{< q + 1} X ⟶ τ_{≥ q} τ_{< q + 1} X` followed by the map induced by
the inclusion `τ_{< q + 1} X ⟶ X`. -/
lemma homologyFunctor_map_eTruncLTCompETruncGEIso_hom_app (q : ℤ) (X : Plus C) :
    (homologyFunctor C q).map ((eTruncLTCompETruncGEIso q).hom.app X) ≫
        (singleFunctorCompHomologyFunctorIso q).hom.app ((homologyFunctor C q).obj X) =
      inv ((homologyFunctor C q).map ((t.eTruncGEπ (q : EInt)).app
          ((t.eTruncLT.obj ((q + 1 : ℤ) : EInt)).obj X))) ≫
        (homologyFunctor C q).map ((t.eTruncLTι ((q + 1 : ℤ) : EInt)).app X) := by
  have hS {a b : C} (u : a ⟶ b) : (homologyFunctor C q).map ((singleFunctor C q).map u) ≫
      (singleFunctorCompHomologyFunctorIso q).hom.app b =
      (singleFunctorCompHomologyFunctorIso q).hom.app a ≫ u :=
    (singleFunctorCompHomologyFunctorIso (C := C) q).hom.naturality u
  have hS' {a b : C} (u : a ⟶ b) {Z : C} (w : b ⟶ Z) :
      (homologyFunctor C q).map ((singleFunctor C q).map u) ≫
      (singleFunctorCompHomologyFunctorIso q).hom.app b ≫ w =
      (singleFunctorCompHomologyFunctorIso q).hom.app a ≫ u ≫ w := by
    rw [reassoc_of% (hS u)]
  simp [eTruncLTCompETruncGEIso, -Functor.map_inv, hS, hS']

/-- Morphisms to `H^q(M)[-q]` from an object concentrated in degree `q` are determined by the
morphisms they induce on `H^q`. -/
lemma singleFunctor_hom_ext_of_isGE_of_isLE {W : Plus C} (q : ℤ) [W.IsGE q] [W.IsLE q] {M : C}
    {f g : W ⟶ (singleFunctor C q).obj M}
    (h : (homologyFunctor C q).map f = (homologyFunctor C q).map g) : f = g := by
  obtain ⟨A, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE (ι.obj W) q
  let e' : W ≅ (singleFunctor C q).obj A := ι.preimageIso e
  rw [← cancel_epi e'.inv]
  suffices (singleFunctor C q).preimage (e'.inv ≫ f) =
      (singleFunctor C q).preimage (e'.inv ≫ g) by
    simpa using congrArg (singleFunctor C q).map this
  have hu (u : A ⟶ M) : u = (singleFunctorCompHomologyFunctorIso q).inv.app A ≫
      (homologyFunctor C q).map ((singleFunctor C q).map u) ≫
      (singleFunctorCompHomologyFunctorIso q).hom.app M := by
    have := (singleFunctorCompHomologyFunctorIso (C := C) q).hom.naturality u
    simp only [Functor.comp_obj, Functor.comp_map, Functor.id_map] at this
    rw [this, Iso.inv_hom_id_app_assoc]
  rw [hu ((singleFunctor C q).preimage (e'.inv ≫ f)),
    hu ((singleFunctor C q).preimage (e'.inv ≫ g))]
  simp [h]

end DerivedCategory.Plus

namespace CochainComplex.IsKInjective

open CategoryTheory

/-- **Morphisms into a K-injective complex are computed in the homotopy category.** For a
K-injective complex `I`, the localization functor `Qh : K(C) ⥤ D(C)` induces bijections
`Hom_K(N, I) ≃ Hom_D(N, I)` for every complex `N`; the same holds in the bounded below derived
category for bounded below `N` and `I`; and a quasi-isomorphism between K-injective complexes is
a homotopy equivalence. (blueprint: `lem-weil-pbc-kinjective-hom-derived`) -/
theorem Qh_map_bijective_and_plus {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C] :
    (∀ (N : HomotopyCategory C (ComplexShape.up ℤ)) (I : CochainComplex C ℤ) [I.IsKInjective],
      Function.Bijective (DerivedCategory.Qh.map :
        (N ⟶ (HomotopyCategory.quotient _ _).obj I) → _)) ∧
    (∀ (N I : HomotopyCategory.Plus C), CochainComplex.IsKInjective I.1.as →
      Function.Bijective (DerivedCategory.Plus.Qh.map : (N ⟶ I) → _)) ∧
    (∀ {K L : CochainComplex C ℤ} [K.IsKInjective] [L.IsKInjective] (f : K ⟶ L),
      QuasiIso f ↔ HomologicalComplex.homotopyEquivalences C (.up ℤ) f) :=
  ⟨fun N I _ ↦ Qh_map_bijective N I,
    fun N I hI ↦ DerivedCategory.Plus.Qh_map_bijective_of_isKInjective N I hI,
    fun f ↦ quasiIso_iff f⟩


end CochainComplex.IsKInjective
