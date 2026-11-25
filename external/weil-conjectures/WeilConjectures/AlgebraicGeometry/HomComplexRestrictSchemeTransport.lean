/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Homology.Additive
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Algebra.Homology.HomComplexRestrictOpen
import WeilConjectures.Algebra.Homology.HomComplexProjections
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Transport of Hom complexes through the open-subscheme equivalence

Source: Stacks Project, Cohomology, Tag 08DL and Cohomology on Sites, Tag 0A8X.
(blueprint: lem-sc-hom-complex-restrict-scheme-transport). -/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry
open CategoryTheory.Limits Opposite

private theorem fan_iso {C : Type*} [Category C] {ι : Type*}
    {A B : C} {f g : ι → C} (π : ∀ i, A ⟶ f i) (τ : ∀ i, B ⟶ g i)
    (hπ : Limits.IsLimit (Limits.Fan.mk A π)) (hτ : Limits.IsLimit (Limits.Fan.mk B τ))
    (e : ∀ i, f i ≅ g i) :
    ∃ a : A ≅ B, ∀ i, a.hom ≫ τ i = π i ≫ (e i).hom := by
  let a := Limits.Fan.IsLimit.lift hτ (fun i ↦ π i ≫ (e i).hom)
  let b := Limits.Fan.IsLimit.lift hπ (fun i ↦ τ i ≫ (e i).inv)
  have ha (i) : a ≫ τ i = π i ≫ (e i).hom := Limits.Fan.IsLimit.fac hτ _ i
  have hb (i) : b ≫ π i = τ i ≫ (e i).inv := Limits.Fan.IsLimit.fac hπ _ i
  refine ⟨⟨a, b, ?_, ?_⟩, ha⟩
  · apply Limits.Fan.IsLimit.hom_ext hπ
    intro i
    change (a ≫ b) ≫ π i = (𝟙 A) ≫ π i
    rw [Category.assoc, hb, ← Category.assoc, ha, Category.assoc,
      Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  · apply Limits.Fan.IsLimit.hom_ext hτ
    intro i
    change (b ≫ a) ≫ τ i = (𝟙 B) ≫ τ i
    rw [Category.assoc, ha, ← Category.assoc, hb, Category.assoc,
      Iso.inv_hom_id, Category.comp_id, Category.id_comp]

private theorem factor_differential
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    (F : C ⥤ D) [F.Additive]
    {Hn Hm A B E : C} {Kn Km A' B' E' : D}
    (dH : Hn ⟶ Hm) (dK : Kn ⟶ Km)
    (a : Hn ⟶ A) (b : Hn ⟶ B) (c : Hm ⟶ E)
    (α : A ⟶ E) (β : B ⟶ E)
    (a' : Kn ⟶ A') (b' : Kn ⟶ B') (c' : Km ⟶ E')
    (α' : A' ⟶ E') (β' : B' ⟶ E')
    (en : F.obj Hn ⟶ Kn) (em : F.obj Hm ⟶ Km)
    (sa : F.obj A ⟶ A') (sb : F.obj B ⟶ B') (sc : F.obj E ⟶ E') (t : ℤ)
    (hH : dH ≫ c = a ≫ α - t • (b ≫ β))
    (hK : dK ≫ c' = a' ≫ α' - t • (b' ≫ β'))
    (ha : en ≫ a' = F.map a ≫ sa) (hb : en ≫ b' = F.map b ≫ sb)
    (hc : em ≫ c' = F.map c ≫ sc)
    (hα : F.map α ≫ sc = sa ≫ α') (hβ : F.map β ≫ sc = sb ≫ β') :
    (en ≫ dK) ≫ c' = (F.map dH ≫ em) ≫ c' := by
  simp only [Category.assoc, hK, Preadditive.comp_sub,
    Preadditive.comp_zsmul]
  rw [← Category.assoc en a', ha, Category.assoc,
    ← Category.assoc en b', hb, Category.assoc]
  rw [hc, ← Category.assoc (F.map dH), ← F.map_comp, hH]
  simp only [Functor.map_sub, Functor.map_zsmul, Functor.map_comp,
    Preadditive.sub_comp, Preadditive.zsmul_comp, Category.assoc, hα, hβ]


-- Specializing both chosen projection families unfolds their product interfaces.
set_option backward.isDefEq.respectTransparency false in
/-- Given the natural internal-Hom comparisons for the over-open equivalence, the
product construction and the differential compatibility produce the Hom-complex comparison.

Source: Stacks Project, Cohomology, Tag 08DL and Cohomology on Sites, Tag 0A8X.
(blueprint: lem-sc-hom-complex-restrict-scheme-transport).

Proof: Apply `homComplex_restrict_open` and transport its componentwise product
projections through the supplied internal-Hom isomorphisms. Preservation of products
by the over-open equivalence gives the component isomorphisms. The naturality equation
for the supplied comparisons identifies both summands in the Hom differential, so
`HomologicalComplex.Hom.isoOfComponents` gives the chain isomorphism. Finally compose
with `overFunctorEquiv U` on each complex. All constructions are valid for arbitrary
integer-indexed complexes, including zero and empty cases. -/
theorem homComplex_restrict_scheme_of_homIso {Y : Scheme.{u}} (U : Y.Opens)
    (L M : CochainComplex Y.Modules ℤ)
    (e : ∀ (A B : SheafOfModules.{u} (Y.ringCatSheaf.over U)),
      (Scheme.Modules.overEquiv U).functor.obj
        (SheafOfModules.homObj (R := Y.toRingedSpace.sheaf.over U) A B) ≅
      SheafOfModules.homObj (R := U.toScheme.toRingedSpace.sheaf)
        ((Scheme.Modules.overEquiv U).functor.obj A)
        ((Scheme.Modules.overEquiv U).functor.obj B))
    (he : ∀ (A A' B B' : SheafOfModules.{u} (Y.ringCatSheaf.over U))
      (f : A' ⟶ A) (g : B ⟶ B'),
      (Scheme.Modules.overEquiv U).functor.map
          (SheafOfModules.homObjMap (R := Y.toRingedSpace.sheaf.over U) f g) ≫
        (e A' B').hom =
      (e A B).hom ≫ SheafOfModules.homObjMap
        (R := U.toScheme.toRingedSpace.sheaf)
        ((Scheme.Modules.overEquiv U).functor.map f)
        ((Scheme.Modules.overEquiv U).functor.map g)) :
    Nonempty (
      ((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex (.up ℤ)).obj
        (homComplex (R := Y.toRingedSpace.sheaf) L M) ≅
      homComplex (R := U.toScheme.toRingedSpace.sheaf)
        (((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex (.up ℤ)).obj L)
        (((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex (.up ℤ)).obj M)) := by
  classical
  let O := SheafOfModules.overFunctor.{u} Y.ringCatSheaf U
  let F := (Scheme.Modules.overEquiv U).functor
  let : F.Additive := Functor.additive_of_preserves_binary_products F
  let LO := (O.mapHomologicalComplex (.up ℤ)).obj L
  let MO := (O.mapHomologicalComplex (.up ℤ)).obj M
  let LF := (F.mapHomologicalComplex (.up ℤ)).obj LO
  let MF := (F.mapHomologicalComplex (.up ℤ)).obj MO
  let H := homComplex (R := Y.toRingedSpace.sheaf.over U) LO MO
  let K := homComplex (R := U.toScheme.toRingedSpace.sheaf) LF MF
  let π := Classical.choose (homComplex_projections_exists
    (R := Y.toRingedSpace.sheaf.over U))
  let τ := Classical.choose (homComplex_projections_exists
    (R := U.toScheme.toRingedSpace.sheaf))
  have hπ := Classical.choose_spec (homComplex_projections_exists
    (R := Y.toRingedSpace.sheaf.over U))
  have hτ := Classical.choose_spec (homComplex_projections_exists
    (R := U.toScheme.toRingedSpace.sheaf))
  have hp (n : ℤ) : IsLimit (Fan.mk (F.obj (H.X n))
      (fun p : ℤ ↦ F.map (π LO MO n p (p + n) rfl))) :=
    isLimitFanMkObjOfIsLimit F _ _ (Classical.choice (hπ.1 LO MO n))
  have ht (n : ℤ) : IsLimit (Fan.mk (K.X n)
      (fun p : ℤ ↦ τ LF MF n p (p + n) rfl)) := Classical.choice (hτ.1 LF MF n)
  have hi (n : ℤ) := fan_iso _ _ (hp n) (ht n)
    (fun p : ℤ ↦ e (LO.X p) (MO.X (p + n)))
  choose a ha using hi
  have ha' (n p q : ℤ) (hpq : p + n = q) :
      (a n).hom ≫ τ LF MF n p q hpq =
        F.map (π LO MO n p q hpq) ≫ (e (LO.X p) (MO.X q)).hom := by
    subst q
    exact ha n p
  have comm (n m : ℤ) (hnm : n + 1 = m) :
      (a n).hom ≫ K.d n m = F.map (H.d n m) ≫ (a m).hom := by
    apply (hτ.1 LF MF m).some.hom_ext
    intro j
    obtain ⟨p⟩ := j
    change ((a n).hom ≫ K.d n m) ≫ τ LF MF m p (p + m) rfl =
      (F.map (H.d n m) ≫ (a m).hom) ≫ τ LF MF m p (p + m) rfl
    have hH := hπ.2.1 LO MO n m p (p + m) (p + n) (p + 1)
      hnm rfl rfl (by omega)
    have hK := hτ.2.1 LF MF n m p (p + m) (p + n) (p + 1)
      hnm rfl rfl (by omega)
    change H.d n m ≫ π LO MO m p (p + m) rfl = _ at hH
    change K.d n m ≫ τ LF MF m p (p + m) rfl = _ at hK
    simp only [Units.smul_def] at hH hK
    have hα := he (LO.X p) (LO.X p) (MO.X (p + n)) (MO.X (p + m))
      (𝟙 _) (MO.d (p + n) (p + m))
    have hβ := he (LO.X (p + 1)) (LO.X p) (MO.X (p + m)) (MO.X (p + m))
      (LO.d p (p + 1)) (𝟙 _)
    rw [F.map_id] at hα hβ
    exact factor_differential F (H.d n m) (K.d n m)
      (π LO MO n p (p + n) rfl) (π LO MO n (p + 1) (p + m) (by omega))
      (π LO MO m p (p + m) rfl)
      (SheafOfModules.homObjMap (R := Y.toRingedSpace.sheaf.over U)
        (𝟙 (LO.X p)) (MO.d (p + n) (p + m)))
      (SheafOfModules.homObjMap (R := Y.toRingedSpace.sheaf.over U)
        (LO.d p (p + 1)) (𝟙 (MO.X (p + m))))
      (τ LF MF n p (p + n) rfl) (τ LF MF n (p + 1) (p + m) (by omega))
      (τ LF MF m p (p + m) rfl)
      (SheafOfModules.homObjMap (R := U.toScheme.toRingedSpace.sheaf)
        (𝟙 (LF.X p)) (MF.d (p + n) (p + m)))
      (SheafOfModules.homObjMap (R := U.toScheme.toRingedSpace.sheaf)
        (LF.d p (p + 1)) (𝟙 (MF.X (p + m))))
      (a n).hom (a m).hom
      (e (LO.X p) (MO.X (p + n))).hom
      (e (LO.X (p + 1)) (MO.X (p + m))).hom
      (e (LO.X p) (MO.X (p + m))).hom (n.negOnePow : ℤ)
      hH hK (ha' n p (p + n) rfl) (ha' n (p + 1) (p + m) (by omega))
      (ha' m p (p + m) rfl) hα hβ
  let c : (F.mapHomologicalComplex (.up ℤ)).obj H ≅ K :=
    HomologicalComplex.Hom.isoOfComponents a comm
  let : (Scheme.Modules.restrictFunctor U.ι).Additive :=
    (Scheme.Modules.restrictAdjunction U.ι).left_adjoint_additive
  let s := NatIso.mapHomologicalComplex (Scheme.Modules.overFunctorEquiv U) (.up ℤ)
  obtain ⟨b⟩ := homComplex_restrict_open Y.toRingedSpace U L M
  exact ⟨(s.app (homComplex (R := Y.toRingedSpace.sheaf) L M)).symm ≪≫
    (F.mapHomologicalComplex (.up ℤ)).mapIso b.symm ≪≫ c ≪≫
    ((homComplexFunctor (R := U.toScheme.toRingedSpace.sheaf)).mapIso
      (s.app L).symm.op).app MF ≪≫
    ((homComplexFunctor (R := U.toScheme.toRingedSpace.sheaf)).obj
      (op (((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex (.up ℤ)).obj L))).mapIso
        (s.app M)⟩


end AlgebraicGeometry
