/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomOver
import WeilConjectures.Algebra.Homology.InternalHomOverNaturality

/-!
# Differential compatibility for the product comparison under open restriction

Source: Stacks Project, Cohomology, Tag 08DL, and Cohomology on Sites, Tag 0A8X.
(blueprint: lem-sc-hom-complex-restrict-open-differential).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry

universe u

namespace CategoryTheory

private theorem overHom_post
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
    {R : Sheaf J CommRingCat.{u}} (U : C)
    (A : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R))
    {B B' : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R)} (g : B ⟶ B') :
    (SheafOfModules.overFunctor _ U).map
        (SheafOfModules.homObjMap (R := R) (𝟙 A) g) ≫
          (SheafOfModules.overHomObjIso A B' U).hom =
      (SheafOfModules.overHomObjIso A B U).hom ≫
        SheafOfModules.homObjMap (R := R.over U) (𝟙 (A.over U))
          ((SheafOfModules.overFunctor _ U).map g) := by
  simpa only [Functor.map_id] using overHomObjIso_naturality U (𝟙 A) g

private theorem overHom_pre
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
    {R : Sheaf J CommRingCat.{u}} (U : C)
    {A A' : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R)} (f : A' ⟶ A)
    (B : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R)) :
    (SheafOfModules.overFunctor _ U).map
        (SheafOfModules.homObjMap (R := R) f (𝟙 B)) ≫
          (SheafOfModules.overHomObjIso A' B U).hom =
      (SheafOfModules.overHomObjIso A B U).hom ≫
        SheafOfModules.homObjMap (R := R.over U)
          ((SheafOfModules.overFunctor _ U).map f) (𝟙 (B.over U)) := by
  simpa only [Functor.map_id] using overHomObjIso_naturality U f (𝟙 B)

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

set_option backward.isDefEq.respectTransparency true in
-- Specializing the projection families unfolds the chosen Hom-complex interfaces.
/-- A degreewise comparison satisfying the factorwise product projection equations
intertwines the Hom-complex differential. This statement supplies no degreewise
isomorphisms: those must already have been constructed.

Source: Stacks Project, Cohomology, Tag 08DL, construction of internal Hom;
Cohomology on Sites, Tag 0A8X, the displayed Hom-complex differential.

Proof: Fix adjacent degrees n and m and postcompose both sides with each chosen
product projection in degree m on the localized site. These projections are jointly
monic by the limit assertion in `homComplex_projections_exists`. Expand the localized
differential using the second assertion of that theorem. Distribute composition over
subtraction and multiplication by the integer unit n.negOnePow, and apply the assumed
projection equation to both summands, with indices (p,p+n) and (p+m-n,p+m).
On the other side use the projection equation in degree m, functoriality of
restriction, and the global differential formula. Restriction is additive, so it
preserves subtraction and this integer-unit multiplication. The two summands now
agree by naturality of `SheafOfModules.overHomObjIso` in both arguments: on an object
W over U, its forward map precomposes a local module morphism by
`Over.iteratedSliceForward W`. Precomposition preserves identity and composition,
so restricting the pre- and post-compositions gives precisely the pre- and
post-compositions of the restricted maps. Thus both summands, with the same sign,
agree after every product projection, proving the asserted equality. The argument
uses all integer-indexed factors, and applies unchanged to zero complexes, the
empty open, and unbounded complexes.
(blueprint: lem-sc-hom-complex-restrict-open-differential). -/
theorem homComplex_restrict_open_differential (X : RingedSpace.{u}) (U : Opens X)
    (L M : CochainComplex (SheafOfModules.{u} (moduleRings X)) ℤ) :
    let F := SheafOfModules.overFunctor.{u} (moduleRings X) U
    let LF := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L
    let MF := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj M
    let H := homComplex (R := X.sheaf) L M
    let K := homComplex (R := X.sheaf.over U) LF MF
    let π := Classical.choose (homComplex_projections_exists (R := X.sheaf))
    let τ := Classical.choose (homComplex_projections_exists (R := X.sheaf.over U))
    ∀ (e : ∀ n : ℤ, F.obj (H.X n) ≅ K.X n),
      (∀ (n p q : ℤ) (hpq : p + n = q),
        (e n).hom ≫ τ LF MF n p q hpq =
          F.map (π L M n p q hpq) ≫
            (SheafOfModules.overHomObjIso (L.X p) (M.X q) U).hom) →
      ∀ (n m : ℤ), n + 1 = m →
        (e n).hom ≫ K.d n m = F.map (H.d n m) ≫ (e m).hom := by
  classical
  intro F LF MF H K π τ e he n m hnm
  have hπ := Classical.choose_spec
    (homComplex_projections_exists.{u, u, u, u} (R := X.sheaf))
  have hτ := Classical.choose_spec
    (homComplex_projections_exists.{u, u, u, u} (R := X.sheaf.over U))
  apply (hτ.1 LF MF m).some.hom_ext
  intro j
  obtain ⟨p⟩ := j
  change ((e n).hom ≫ K.d n m) ≫ τ LF MF m p (p + m) rfl =
    (F.map (H.d n m) ≫ (e m).hom) ≫ τ LF MF m p (p + m) rfl
  have ha := he n p (p + n) rfl
  have hb := he n (p + 1) (p + m) (by omega)
  have hc := he m p (p + m) rfl
  have hH := hπ.2.1 L M n m p (p + m) (p + n) (p + 1)
    hnm rfl rfl (by omega)
  have hK := hτ.2.1 LF MF n m p (p + m) (p + n) (p + 1)
    hnm rfl rfl (by omega)
  have hα := overHom_post (C := Opens X) (J := Opens.grothendieckTopology X) U
    (R := X.sheaf) (L.X p) (M.d (p + n) (p + m))
  have hβ := overHom_pre (C := Opens X) (J := Opens.grothendieckTopology X) U
    (R := X.sheaf) (L.d p (p + 1)) (M.X (p + m))
  change H.d n m ≫ π L M m p (p + m) rfl = _ at hH
  change K.d n m ≫ τ LF MF m p (p + m) rfl = _ at hK
  simp only [Units.smul_def] at hH hK
  refine factor_differential
    (C := SheafOfModules.{u} (moduleRings X))
    (D := SheafOfModules.{u} ((moduleRings X).over U)) F
    (H.d n m)
    (K.d n m)
    (π L M n p (p + n) rfl) (π L M n (p + 1) (p + m) (by omega))
    (π L M m p (p + m) rfl)
    (SheafOfModules.homObjMap (R := X.sheaf) (𝟙 (L.X p)) (M.d (p + n) (p + m)))
    (SheafOfModules.homObjMap (R := X.sheaf) (L.d p (p + 1)) (𝟙 (M.X (p + m))))
    (τ LF MF n p (p + n) rfl) (τ LF MF n (p + 1) (p + m) (by omega))
    (τ LF MF m p (p + m) rfl)
    (SheafOfModules.homObjMap (R := X.sheaf.over U)
      (𝟙 (LF.X p)) (MF.d (p + n) (p + m)))
    (SheafOfModules.homObjMap (R := X.sheaf.over U) (LF.d p (p + 1)) (𝟙 (MF.X (p + m))))
    (e n).hom (e m).hom
    (SheafOfModules.overHomObjIso (L.X p) (M.X (p + n)) U).hom
    (SheafOfModules.overHomObjIso (L.X (p + 1)) (M.X (p + m)) U).hom
    (SheafOfModules.overHomObjIso (L.X p) (M.X (p + m)) U).hom (n.negOnePow : ℤ)
    hH hK ha hb hc hα hβ

end CategoryTheory
