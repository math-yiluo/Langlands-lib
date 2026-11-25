/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import WeilConjectures.Algebra.Homology.HomComplexProjections
import WeilConjectures.Algebra.Homology.HomComplexMappingConeDifferential

/-! # Internal Hom complexes and mapping cones

Source: Stacks Project, sites-cohomology.tex, Section 0A8X (Hom complexes), and
sites-cohomology.tex, Section 08J7, proof of Lemma 21.35.4.
(blueprint: lem-sc-hom-complex-mapping-cone).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

private lemma homObjMap_add_right
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R : Sheaf J CommRingCat.{u}}
    {A A' B B' : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (f : A' ⟶ A) (g h : B ⟶ B') :
    SheafOfModules.homObjMap (R := R) f (g + h) =
      SheafOfModules.homObjMap f g + SheafOfModules.homObjMap f h := by
  apply SheafOfModules.hom_ext
  ext X φ
  rfl

private lemma homObjMap_zero_right
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R : Sheaf J CommRingCat.{u}}
    {A A' B B' : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (f : A' ⟶ A) : SheafOfModules.homObjMap (R := R) f (0 : B ⟶ B') = 0 := by
  apply SheafOfModules.hom_ext
  ext X φ
  rfl

-- The product comparison unfolds the chosen Hom-complex functor repeatedly.
set_option backward.isDefEq.respectTransparency false in
/-- Internal Hom in the second variable commutes with mapping cones.

Source: Stacks Project, sites-cohomology.tex, Section 0A8X (the differential of the
Hom complex), and Section 08J7, the proof of Lemma 21.35.4.
(blueprint: lem-sc-hom-complex-mapping-cone).

Proof: in degree `n`, the cone of `Hom(E,f)` is
`Hom(E,G)^(n+1) ⊞ Hom(E,I)^n`. Its product components are pairs of local maps
`E^p → G^(p+n+1)` and `E^p → I^(p+n)`. Internal Hom preserves binary
biproducts in its second variable, so the product universal property identifies
these pairs with the degree `n` product of maps
`E^p → G^(p+n+1) ⊞ I^(p+n)`, which is `Hom(E,cone(f))^n`.
The inverse separates the two components by the biproduct projections.
The cone differential sends a pair `(a,b)` to `(-d_Hom a, f a + d_Hom b)`.
Expanding the Hom differential gives in the first component
`-d_G a + (-1)^(n+1) a d_E`, and in the second
`f a + d_I b - (-1)^n b d_E`. These are exactly the two components of
the differential on `Hom(E,cone(f))`, since the cone differential has matrix
`(-d_G, 0; f, d_I)`. Thus the degreewise maps and their inverses are chain maps.
Their compositions are identities by the biproduct and product universal
properties. This argument uses no boundedness or projectivity. -/
theorem homComplex_mappingCone_iso
    {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u})
    (E G I : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (f : G ⟶ I) :
    Nonempty (CochainComplex.mappingCone
        (((homComplexFunctor (R := R)).obj (op E)).map f) ≅
      homComplex (R := R) E (CochainComplex.mappingCone f)) := by
  rw [CochainComplex.mappingCone, CochainComplex.mappingCone]
  classical
  let A := SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
  let HG := ((homComplexFunctor (R := R)).obj (op E)).obj G
  let HI := ((homComplexFunctor (R := R)).obj (op E)).obj I
  let cf := HomologicalComplex.homotopyCofiber f
  let H := ((homComplexFunctor (R := R)).obj (op E)).obj cf
  let hf := ((homComplexFunctor (R := R)).obj (op E)).map f
  let K := HomologicalComplex.homotopyCofiber hf
  let π := Classical.choose (homComplex_projections_exists (R := R))
  have hπ := Classical.choose_spec (homComplex_projections_exists (R := R))
  let pg (n : ℤ) := HomologicalComplex.homotopyCofiber.fstX hf n (n + 1) rfl
  let pi (n : ℤ) := HomologicalComplex.homotopyCofiber.sndX hf n
  let ig (n p : ℤ) := HomologicalComplex.homotopyCofiber.inlX f
    (p + (n + 1)) (p + n) (by change (p + n) + 1 = p + (n + 1); omega)
  let ii (n p : ℤ) := HomologicalComplex.homotopyCofiber.inrX f (p + n)
  let fg (n p : ℤ) := HomologicalComplex.homotopyCofiber.fstX f
    (p + n) (p + (n + 1)) (by change (p + n) + 1 = p + (n + 1); omega)
  let fi (n p : ℤ) := HomologicalComplex.homotopyCofiber.sndX f (p + n)
  let proj (T : CochainComplex A ℤ) (n p : ℤ) := π E T n p (p + n) rfl
  have hp (T : CochainComplex A ℤ) (n : ℤ) :
      IsLimit (Fan.mk ((((homComplexFunctor (R := R)).obj (op E)).obj T).X n) (proj T n)) :=
    Classical.choice (hπ.1 E T n)
  let a (n : ℤ) : K.X n ⟶ H.X n := Fan.IsLimit.lift (hp cf n) (fun p ↦
    pg n ≫ proj G (n + 1) p ≫ SheafOfModules.homObjMap (R := R) (𝟙 (E.X p)) (ig n p) +
    pi n ≫ proj I n p ≫ SheafOfModules.homObjMap (R := R) (𝟙 (E.X p)) (ii n p))
  have ha (n p : ℤ) : a n ≫ proj cf n p =
      pg n ≫ proj G (n + 1) p ≫ SheafOfModules.homObjMap (R := R) (𝟙 (E.X p)) (ig n p) +
      pi n ≫ proj I n p ≫ SheafOfModules.homObjMap (R := R) (𝟙 (E.X p)) (ii n p) :=
    Fan.IsLimit.fac (hp cf n) _ p
  let bg (n : ℤ) : H.X n ⟶ HG.X (n + 1) := Fan.IsLimit.lift (hp G (n + 1))
    (fun p ↦ proj cf n p ≫ SheafOfModules.homObjMap (R := R) (𝟙 (E.X p)) (fg n p))
  let bi (n : ℤ) : H.X n ⟶ HI.X n := Fan.IsLimit.lift (hp I n)
    (fun p ↦ proj cf n p ≫ SheafOfModules.homObjMap (R := R) (𝟙 (E.X p)) (fi n p))
  have hbg (n p : ℤ) : bg n ≫ proj G (n + 1) p =
      proj cf n p ≫ SheafOfModules.homObjMap (R := R) (𝟙 (E.X p)) (fg n p) :=
    Fan.IsLimit.fac (hp G (n + 1)) _ p
  have hbi (n p : ℤ) : bi n ≫ proj I n p =
      proj cf n p ≫ SheafOfModules.homObjMap (R := R) (𝟙 (E.X p)) (fi n p) :=
    Fan.IsLimit.fac (hp I n) _ p
  let b (n : ℤ) : H.X n ⟶ K.X n :=
    bg n ≫ HomologicalComplex.homotopyCofiber.inlX hf (n + 1) n rfl +
      bi n ≫ HomologicalComplex.homotopyCofiber.inrX hf n
  have hb₁ (n : ℤ) : b n ≫ pg n = bg n := by
    dsimp only [b, pg]
    simp only [Preadditive.add_comp, Category.assoc,
      HomologicalComplex.homotopyCofiber.inlX_fstX,
      HomologicalComplex.homotopyCofiber.inrX_fstX, comp_zero, add_zero]
    exact Category.comp_id _
  have hb₂ (n : ℤ) : b n ≫ pi n = bi n := by
    dsimp only [b, pi]
    simp only [Preadditive.add_comp, Category.assoc,
      HomologicalComplex.homotopyCofiber.inlX_sndX,
      HomologicalComplex.homotopyCofiber.inrX_sndX, comp_zero, zero_add]
    exact Category.comp_id _
  have habg (n : ℤ) : a n ≫ bg n = pg n := by
    apply Fan.IsLimit.hom_ext (hp G (n + 1))
    intro p
    change (a n ≫ bg n) ≫ proj G (n + 1) p = pg n ≫ proj G (n + 1) p
    rw [Category.assoc, hbg n p, ← Category.assoc, ha n p]
    simp only [Preadditive.add_comp, Category.assoc,
      SheafOfModules.homObjMap_comp_homObjMap, Category.id_comp]
    dsimp only [ig, ii, fg]
    simp only [HomologicalComplex.homotopyCofiber.inlX_fstX,
      HomologicalComplex.homotopyCofiber.inrX_fstX,
      SheafOfModules.homObjMap_id, homObjMap_zero_right,
      Category.comp_id, comp_zero, add_zero]
  have habi (n : ℤ) : a n ≫ bi n = pi n := by
    apply Fan.IsLimit.hom_ext (hp I n)
    intro p
    change (a n ≫ bi n) ≫ proj I n p = pi n ≫ proj I n p
    rw [Category.assoc, hbi n p, ← Category.assoc, ha n p]
    simp only [Preadditive.add_comp, Category.assoc,
      SheafOfModules.homObjMap_comp_homObjMap, Category.id_comp]
    dsimp only [ig, ii, fi]
    simp only [HomologicalComplex.homotopyCofiber.inlX_sndX,
      HomologicalComplex.homotopyCofiber.inrX_sndX,
      SheafOfModules.homObjMap_id, homObjMap_zero_right,
      Category.comp_id, comp_zero, zero_add]
  have hab (n : ℤ) : a n ≫ b n = 𝟙 (K.X n) := by
    apply HomologicalComplex.homotopyCofiber.ext_to_X hf n (n + 1) rfl
    · change (a n ≫ b n) ≫ pg n = (𝟙 _) ≫ pg n
      simp only [Category.assoc, hb₁ n, habg n, Category.id_comp]
    · change (a n ≫ b n) ≫ pi n = (𝟙 _) ≫ pi n
      simp only [Category.assoc, hb₂ n, habi n, Category.id_comp]
  have hba (n : ℤ) : b n ≫ a n = 𝟙 (H.X n) := by
    apply Fan.IsLimit.hom_ext (hp cf n)
    intro p
    change (b n ≫ a n) ≫ proj cf n p = (𝟙 _) ≫ proj cf n p
    rw [Category.assoc, ha n p, Preadditive.comp_add]
    simp only [← Category.assoc, hb₁, hb₂, hbg, hbi]
    simp only [Category.assoc, SheafOfModules.homObjMap_comp_homObjMap,
      Category.id_comp, ← Preadditive.comp_add, ← homObjMap_add_right]
    have hid : fg n p ≫ ig n p + fi n p ≫ ii n p = 𝟙 (cf.X (p + n)) := by
      apply HomologicalComplex.homotopyCofiber.ext_to_X f (p + n)
        (p + (n + 1)) (by change (p + n) + 1 = p + (n + 1); omega)
      · dsimp only [fg, ig, fi, ii]
        simp only [Preadditive.add_comp, Category.assoc,
          HomologicalComplex.homotopyCofiber.inlX_fstX,
          HomologicalComplex.homotopyCofiber.inrX_fstX,
          Category.comp_id, comp_zero, add_zero]
        exact (Category.id_comp _).symm
      · dsimp only [fg, ig, fi, ii]
        simp only [Preadditive.add_comp, Category.assoc,
          HomologicalComplex.homotopyCofiber.inlX_sndX,
          HomologicalComplex.homotopyCofiber.inrX_sndX,
          Category.comp_id, comp_zero, zero_add]
        exact (Category.id_comp _).symm
    rw [hid]
    have hi := SheafOfModules.homObjMap_id (R := R) (M := E.X p)
      (N := cf.X (p + n))
    rw [hi, Category.comp_id]
  let e (n : ℤ) : K.X n ≅ H.X n := ⟨a n, b n, hab n, hba n⟩
  have comm := homComplex_mappingCone_differential J R E G I f e
    (fun n p ↦ ha n p)
  exact ⟨HomologicalComplex.Hom.isoOfComponents e comm⟩

end CategoryTheory
