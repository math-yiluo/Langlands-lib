/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Ring.NegOnePow
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits

/-!
# Hom complexes of sheaves of modules

Source: Stacks Project, sites-cohomology.tex, Section 0A8X
(section-hom-complexes) (blueprint: def-pur-hom-complex).

The chosen bifunctor has product terms, differential `d_M f - (-1)^n f d_L`,
and componentwise pre- and post-composition. Its existence proof is postponed;
its data are selected from that named theorem, constructed explicitly.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w r

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  {R : Sheaf J CommRingCat.{r}}

private lemma homMap_zero_left {A A' B B' : SheafOfModules.{w} ((sheafCompose J (forget₂
    CommRingCat.{r} RingCat.{r})).obj R)} (g : B ⟶ B') :
    SheafOfModules.homObjMap (0 : A' ⟶ A) g = 0 := by
  apply SheafOfModules.hom_ext
  ext X φ : 3
  change (PresheafOfModules.restrictOver R.obj X.unop).map 0 ≫ φ ≫
    (PresheafOfModules.restrictOver R.obj X.unop).map g.val = 0
  ext W x
  change ((g.val.app _).hom) ((φ.app W).hom (0)) = 0
  rw [map_zero, map_zero]

private lemma homMap_zero_right {A A' B B' : SheafOfModules.{w} ((sheafCompose J (forget₂
    CommRingCat.{r} RingCat.{r})).obj R)} (f : A' ⟶ A) :
    SheafOfModules.homObjMap f (0 : B ⟶ B') = 0 := by
  apply SheafOfModules.hom_ext
  ext X φ : 3
  change (PresheafOfModules.restrictOver R.obj X.unop).map f.val ≫ φ ≫
    (PresheafOfModules.restrictOver R.obj X.unop).map 0 = 0
  ext W x
  rfl

private noncomputable def homTerm (L M : CochainComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ) (n : ℤ) :
    SheafOfModules.{max u v w} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R) :=
  ∏ᶜ fun p : ℤ ↦ SheafOfModules.homObj (L.X p) (M.X (p + n))

private noncomputable def homProj (L M : CochainComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ) (n p q : ℤ) (hpq : p + n =
    q) :
    homTerm L M n ⟶ SheafOfModules.homObj (L.X p) (M.X q) := by
  subst q
  exact Pi.π _ p

private noncomputable def homDiff (L M : CochainComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ) (n m : ℤ) :
    homTerm L M n ⟶ homTerm L M m :=
  Pi.lift fun p : ℤ ↦
    homProj L M n p (p + n) rfl ≫
      SheafOfModules.homObjMap (𝟙 _) (M.d (p + n) (p + m)) -
    n.negOnePow • (homProj L M n (p + m - n) (p + m) (by omega) ≫
      SheafOfModules.homObjMap (L.d p (p + m - n)) (𝟙 _))

private lemma homDiff_proj (L M : CochainComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ) (n m p q q' p' : ℤ) (hpq :
    p + m = q)
    (hq' : p + n = q') (hp' : p' + n = q) :
    homDiff L M n m ≫ homProj L M m p q hpq =
      homProj L M n p q' hq' ≫ SheafOfModules.homObjMap (𝟙 _) (M.d q' q) -
      n.negOnePow • (homProj L M n p' q hp' ≫
        SheafOfModules.homObjMap (L.d p p') (𝟙 _)) := by
  subst q q'
  obtain rfl : p' = p + m - n := by omega
  exact Pi.lift_comp_π _ _

private lemma homDiff_shape (L M : CochainComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ) (n m : ℤ) (h : ¬ n + 1 =
    m) :
    homDiff L M n m = 0 := by
  apply Pi.hom_ext
  intro p
  change homDiff L M n m ≫ homProj L M m p (p + m) rfl = _
  rw [homDiff_proj L M n m p (p + m) (p + n) (p + m - n) rfl rfl (by omega)]
  rw [M.shape, L.shape, homMap_zero_left, homMap_zero_right]
  · simp
  all_goals simp only [ComplexShape.up_Rel]; omega

private lemma homDiff_sq (L M : CochainComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ) (n m k : ℤ) :
    homDiff L M n m ≫ homDiff L M m k = 0 := by
  by_cases hnm : n + 1 = m
  · by_cases hmk : m + 1 = k
    · apply Pi.hom_ext
      intro p
      change (homDiff L M n m ≫ homDiff L M m k) ≫
        homProj L M k p (p + k) rfl = _
      rw [Category.assoc,
        homDiff_proj L M m k p (p + k) (p + m) (p + 1) rfl rfl (by omega),
        Preadditive.comp_sub, Linear.comp_units_smul,
        ← Category.assoc,
        homDiff_proj L M n m p (p + m) (p + n) (p + 1) rfl rfl (by omega),
        ← Category.assoc,
        homDiff_proj L M n m (p + 1) (p + k) (p + m) (p + 2)
          (by omega) (by omega) (by omega)]
      simp only [Preadditive.sub_comp, Linear.units_smul_comp, Category.assoc,
        SheafOfModules.homObjMap_comp_homObjMap, Category.id_comp, Category.comp_id,
        HomologicalComplex.d_comp_d, homMap_zero_left, homMap_zero_right,
        comp_zero, zero_comp, smul_zero, smul_sub, zero_sub]
      subst m
      simp only [Int.negOnePow_succ, Units.neg_smul]
      abel
    · rw [homDiff_shape L M m k hmk, comp_zero]
  · rw [homDiff_shape L M n m hnm, zero_comp]

private noncomputable def homObjComplex (L M : CochainComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ) :
    CochainComplex (SheafOfModules.{max u v w} ((sheafCompose J (forget₂ CommRingCat.{r}
    RingCat.{r})).obj R)) ℤ where
  X := homTerm L M
  d := homDiff L M
  shape := homDiff_shape L M
  d_comp_d' _ _ _ _ _ := homDiff_sq L M _ _ _

private noncomputable def homTermMap {L L' M M' : CochainComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ} (f : L' ⟶ L) (g : M ⟶ M')
    (n : ℤ) : homTerm L M n ⟶ homTerm L' M' n :=
  Pi.lift fun p : ℤ ↦ homProj L M n p (p + n) rfl ≫
    SheafOfModules.homObjMap (f.f p) (g.f (p + n))

private lemma homTermMap_proj {L L' M M' : CochainComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ} (f : L' ⟶ L) (g : M ⟶ M')
    (n p q : ℤ) (hpq : p + n = q) :
    homTermMap f g n ≫ homProj L' M' n p q hpq =
      homProj L M n p q hpq ≫ SheafOfModules.homObjMap (f.f p) (g.f q) := by
  subst q
  exact Pi.lift_comp_π _ _

private lemma homTermMap_comm {L L' M M' : CochainComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ} (f : L' ⟶ L) (g : M ⟶ M')
    (n m : ℤ) :
    homTermMap f g n ≫ homDiff L' M' n m =
      homDiff L M n m ≫ homTermMap f g m := by
  apply Pi.hom_ext
  intro p
  change (homTermMap f g n ≫ homDiff L' M' n m) ≫
    homProj L' M' m p (p + m) rfl =
    (homDiff L M n m ≫ homTermMap f g m) ≫ homProj L' M' m p (p + m) rfl
  rw [Category.assoc, Category.assoc,
    homDiff_proj L' M' n m p (p + m) (p + n) (p + m - n) rfl rfl (by omega),
    homTermMap_proj, Preadditive.comp_sub, Linear.comp_units_smul,
    ← Category.assoc, homTermMap_proj, ← Category.assoc, homTermMap_proj,
    ← Category.assoc, homDiff_proj L M n m p (p + m) (p + n) (p + m - n)
      rfl rfl (by omega)]
  simp only [Preadditive.sub_comp, Linear.units_smul_comp, Category.assoc,
    SheafOfModules.homObjMap_comp_homObjMap, Category.id_comp, Category.comp_id]
  rw [g.comm, f.comm]

private noncomputable def homComplexMap {L L' M M' : CochainComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ} (f : L' ⟶ L) (g : M ⟶ M') :
    homObjComplex L M ⟶ homObjComplex L' M' where
  f := homTermMap f g
  comm' n m _ := homTermMap_comm f g n m

private lemma homComplexMap_id (L M : CochainComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ) : homComplexMap (𝟙 L) (𝟙
    M) = 𝟙 _ := by
  apply HomologicalComplex.hom_ext
  intro n
  apply Pi.hom_ext
  intro p
  change homTermMap (𝟙 L) (𝟙 M) n ≫ homProj L M n p (p + n) rfl = _
  rw [homTermMap_proj]
  simp [homProj]

private lemma homComplexMap_comp {L L' L'' M M' M'' : CochainComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ}
    (f : L' ⟶ L) (f' : L'' ⟶ L') (g : M ⟶ M') (g' : M' ⟶ M'') :
    homComplexMap f g ≫ homComplexMap f' g' = homComplexMap (f' ≫ f) (g ≫ g') := by
  apply HomologicalComplex.hom_ext
  intro n
  apply Pi.hom_ext
  intro p
  change (homTermMap f g n ≫ homTermMap f' g' n) ≫
    homProj L'' M'' n p (p + n) rfl =
    homTermMap (f' ≫ f) (g ≫ g') n ≫ homProj L'' M'' n p (p + n) rfl
  rw [Category.assoc, homTermMap_proj, ← Category.assoc, homTermMap_proj,
    homTermMap_proj, Category.assoc, SheafOfModules.homObjMap_comp_homObjMap]
  rfl

private noncomputable def homBifunctor :
    (CochainComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ)ᵒᵖ ⥤
      CochainComplex (SheafOfModules.{w}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ ⥤ CochainComplex
    (SheafOfModules.{max u v w} ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ
    where
  obj L :=
    { obj M := homObjComplex L.unop M
      map g := homComplexMap (𝟙 L.unop) g
      map_id M := homComplexMap_id L.unop M
      map_comp g g' := by rw [homComplexMap_comp]; simp }
  map f :=
    { app M := homComplexMap f.unop (𝟙 M)
      naturality {M M'} g := by
        dsimp
        rw [homComplexMap_comp, homComplexMap_comp]
        simp }
  map_id L := by
    apply NatTrans.ext
    funext M
    exact homComplexMap_id L.unop M
  map_comp f f' := by
    apply NatTrans.ext
    funext M
    dsimp
    rw [homComplexMap_comp]
    simp

/-- Existence of the Hom-complex bifunctor with its product projections and exact sign.
Source: Stacks Project, sites-cohomology.tex, Section 0A8X
(section-hom-complexes) (blueprint: def-pur-hom-complex).

Proof: take in degree `n` the product of the internal sheaf Homs from `L^p` to
`M^(p+n)`. Products are computed sectionwise, so sections are families of maps
on the localized site. Define the differential on these families by
`d_M f - (-1)^n f d_L`. Both composition maps are linear and commute with
restriction. Expanding its square gives the two zero terms `d_M^2 f` and
`f d_L^2`, while the mixed terms cancel because the signs in consecutive
integer degrees are opposite. Thus these products form a cochain complex.
Pre- and post-compose each component with chain maps. Their chain-map
identities show this commutes with the differential; associativity and identity
of composition give the bifunctor laws. Use the product universal property
for the projections and their formulas below. No extra boundedness is used. -/
theorem homComplex_exists :
    ∃ F : (CochainComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ)ᵒᵖ ⥤ CochainComplex
        (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ ⥤ CochainComplex
        (SheafOfModules.{max u v w}
          ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ,
      ∃ π : ∀ (L M : CochainComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ) (n p q : ℤ), p + n = q →
        (((F.obj (op L)).obj M).X n ⟶ SheafOfModules.homObj (L.X p) (M.X q)),
        (∀ (L M : CochainComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ) (n : ℤ),
          Nonempty (IsLimit (Fan.mk (((F.obj (op L)).obj M).X n)
            (fun p : ℤ ↦ π L M n p (p + n) rfl)))) ∧
        (∀ (L M : CochainComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ) (n m p q q' p' : ℤ)
          (_hnm : n + 1 = m) (hpq : p + m = q)
          (hq' : p + n = q') (hp' : p' + n = q),
          ((F.obj (op L)).obj M).d n m ≫ π L M m p q hpq =
            π L M n p q' hq' ≫ SheafOfModules.homObjMap (𝟙 (L.X p)) (M.d q' q) -
              n.negOnePow • (π L M n p' q hp' ≫
                SheafOfModules.homObjMap (L.d p p') (𝟙 (M.X q)))) ∧
        (∀ (L L' M M' : CochainComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ) (f : L' ⟶ L) (g : M ⟶ M')
          (n p q : ℤ) (hpq : p + n = q),
          (((F.map f.op).app M) ≫ (F.obj (op L')).map g).f n ≫ π L' M' n p q hpq =
            π L M n p q hpq ≫ SheafOfModules.homObjMap (f.f p) (g.f q)) := by
  refine ⟨homBifunctor, homProj, ?_, ?_, ?_⟩
  · intro L M n
    exact ⟨productIsProduct _⟩
  · intro L M n m p q q' p' hnm hpq hq' hp'
    exact homDiff_proj L M n m p q q' p' hpq hq' hp'
  · intro L L' M M' f g n p q hpq
    change (homTermMap f (𝟙 M) n ≫ homTermMap (𝟙 L') g n) ≫
      homProj L' M' n p q hpq = _
    rw [Category.assoc, homTermMap_proj, ← Category.assoc, homTermMap_proj,
      Category.assoc, SheafOfModules.homObjMap_comp_homObjMap]
    simp

/-- The sheaf-valued Hom-complex bifunctor, contravariant in the first complex.
Source: Stacks Project, sites-cohomology.tex, Section 0A8X
(section-hom-complexes) (blueprint: def-pur-hom-complex).
Its projections, differential and componentwise action are specified together
by `homComplex_exists`, from which this definition selects its data. The comparison with the
internal hom complex `CochainComplex.internalHomObj` is `homComplexIsoInternalHomObj`
(`homComplexFunctorObjIsoInternalHom`). -/
noncomputable def homComplexFunctor :
    (CochainComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ)ᵒᵖ ⥤ CochainComplex
        (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ ⥤ CochainComplex
        (SheafOfModules.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ :=
  Classical.choose (homComplex_exists (C := C) (J := J) (R := R))

/-- The Hom complex of two cochain complexes of sheaves of modules.
Source: Stacks Project, sites-cohomology.tex, Section 0A8X
(section-hom-complexes) (blueprint: def-pur-hom-complex).
In degree `n` its product projections identify sections with families of
localized linear maps `L^p → M^(p+n)`, and its differential is
`d_M f - (-1)^n f d_L`. Functoriality is supplied by `homComplexFunctor`. -/
noncomputable def homComplex
    (L M : CochainComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ) : CochainComplex
        (SheafOfModules.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ :=
  (homComplexFunctor.obj (op L)).obj M

end CategoryTheory
