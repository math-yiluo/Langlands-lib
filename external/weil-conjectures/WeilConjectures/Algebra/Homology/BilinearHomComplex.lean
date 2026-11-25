/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.CategoryTheory.Preadditive.Opposite
import Mathlib.Algebra.Module.Basic
import Mathlib.CategoryTheory.Linear.Basic
/-! # Product Hom complexes for a separately additive coefficient bifunctor
Source: Stacks Project, sites-cohomology.tex, Section 0A8X, and Algebraization, Tag 099I
(auxiliary; not a blueprint node).
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory
variable {A B D : Type u} [Category.{v} A] [Category.{v} B] [Category.{v} D]
  [Preadditive A] [Preadditive B] [Preadditive D] [HasProducts.{0} D]
  (H : Aᵒᵖ ⥤ B ⥤ D) [H.Additive] [∀ a, (H.obj a).Additive]

private abbrev hObj (a : A) (b : B) := (H.obj (op a)).obj b

private def hMap {a a' : A} {b b' : B} (f : a' ⟶ a) (g : b ⟶ b') :
    hObj H a b ⟶ hObj H a' b' :=
  (Functor.uncurry.obj H).map (X := (op a, b)) (Y := (op a', b')) (f.op, g)

omit [Preadditive A] [Preadditive B] [Preadditive D] [HasProducts D]
    [H.Additive] [∀ a, (H.obj a).Additive] in
private lemma hMap_comp {a a' a'' : A} {b b' b'' : B}
    (f : a' ⟶ a) (f' : a'' ⟶ a') (g : b ⟶ b') (g' : b' ⟶ b'') :
    hMap H f g ≫ hMap H f' g' = hMap H (f' ≫ f) (g ≫ g') := by
  exact ((Functor.uncurry.obj H).map_comp
    (show (op a, b) ⟶ (op a', b') from (f.op, g))
    (show (op a', b') ⟶ (op a'', b'') from (f'.op, g'))).symm

omit [Preadditive A] [Preadditive B] [Preadditive D] [HasProducts D]
    [H.Additive] [∀ a, (H.obj a).Additive] in
@[simp] private lemma hMap_id (a : A) (b : B) :
    hMap H (𝟙 a) (𝟙 b) = 𝟙 (hObj H a b) := by
  exact (Functor.uncurry.obj H).map_id (op a, b)

omit [Preadditive B] [HasProducts D] [∀ a, (H.obj a).Additive] in
private lemma hMap_zero_left {a a' : A} {b b' : B} (g : b ⟶ b') :
    hMap H (0 : a' ⟶ a) g = 0 := by
  simp [hMap, Functor.uncurry_obj_map]

omit [Preadditive A] [HasProducts D] [H.Additive] in
private lemma hMap_zero_right {a a' : A} {b b' : B} (f : a' ⟶ a) :
    hMap H f (0 : b ⟶ b') = 0 := by
  simp [hMap, Functor.uncurry_obj_map]

private noncomputable def homTerm (L : CochainComplex A ℤ) (M : CochainComplex B ℤ) (n : ℤ) :
    D :=
  ∏ᶜ fun p : ℤ ↦ hObj H (L.X p) (M.X (p + n))

private noncomputable def homProj (L : CochainComplex A ℤ)
    (M : CochainComplex B ℤ) (n p q : ℤ) (hpq : p + n =
    q) :
    homTerm H L M n ⟶ hObj H (L.X p) (M.X q) := by
  subst q
  exact Pi.π _ p

private noncomputable def homDiff (L : CochainComplex A ℤ) (M : CochainComplex B ℤ) (n m : ℤ) :
    homTerm H L M n ⟶ homTerm H L M m :=
  Pi.lift fun p : ℤ ↦
    homProj H L M n p (p + n) rfl ≫
      hMap H (𝟙 _) (M.d (p + n) (p + m)) -
    n.negOnePow • (homProj H L M n (p + m - n) (p + m) (by omega) ≫
      hMap H (L.d p (p + m - n)) (𝟙 _))

omit [H.Additive] [∀ a, (H.obj a).Additive] in
private lemma homDiff_proj (L : CochainComplex A ℤ)
    (M : CochainComplex B ℤ) (n m p q q' p' : ℤ) (hpq :
    p + m = q)
    (hq' : p + n = q') (hp' : p' + n = q) :
    homDiff H L M n m ≫ homProj H L M m p q hpq =
      homProj H L M n p q' hq' ≫ hMap H (𝟙 _) (M.d q' q) -
      n.negOnePow • (homProj H L M n p' q hp' ≫
        hMap H (L.d p p') (𝟙 _)) := by
  subst q q'
  obtain rfl : p' = p + m - n := by omega
  exact Pi.lift_comp_π _ _

private lemma homDiff_shape (L : CochainComplex A ℤ)
    (M : CochainComplex B ℤ) (n m : ℤ) (h : ¬ n + 1 =
    m) :
    homDiff H L M n m = 0 := by
  apply Pi.hom_ext
  intro p
  change homDiff H L M n m ≫ homProj H L M m p (p + m) rfl = _
  rw [homDiff_proj H L M n m p (p + m) (p + n) (p + m - n) rfl rfl (by omega)]
  rw [M.shape, L.shape, hMap_zero_left H, hMap_zero_right H]
  · simp
  all_goals simp only [ComplexShape.up_Rel]; omega

private lemma homDiff_sq (L : CochainComplex A ℤ) (M : CochainComplex B ℤ) (n m k : ℤ) :
    homDiff H L M n m ≫ homDiff H L M m k = 0 := by
  by_cases hnm : n + 1 = m
  · by_cases hmk : m + 1 = k
    · apply Pi.hom_ext
      intro p
      change (homDiff H L M n m ≫ homDiff H L M m k) ≫
        homProj H L M k p (p + k) rfl = _
      rw [Category.assoc,
        homDiff_proj H L M m k p (p + k) (p + m) (p + 1) rfl rfl (by omega),
        Preadditive.comp_sub, Linear.comp_units_smul,
        ← Category.assoc,
        homDiff_proj H L M n m p (p + m) (p + n) (p + 1) rfl rfl (by omega),
        ← Category.assoc,
        homDiff_proj H L M n m (p + 1) (p + k) (p + m) (p + 2)
          (by omega) (by omega) (by omega)]
      simp only [Preadditive.sub_comp, Linear.units_smul_comp, Category.assoc,
        hMap_comp H, Category.id_comp, Category.comp_id,
        HomologicalComplex.d_comp_d, hMap_zero_left H, hMap_zero_right H,
        comp_zero, zero_comp, smul_zero, smul_sub, zero_sub]
      subst m
      simp only [Int.negOnePow_succ, Units.neg_smul]
      abel
    · rw [homDiff_shape H L M m k hmk, comp_zero]
  · rw [homDiff_shape H L M n m hnm, zero_comp]

private noncomputable def homObjComplex (L : CochainComplex A ℤ) (M : CochainComplex B ℤ) :
    CochainComplex (D) ℤ where
  X := homTerm H L M
  d := homDiff H L M
  shape := homDiff_shape H L M
  d_comp_d' _ _ _ _ _ := homDiff_sq H L M _ _ _

private noncomputable def homTermMap {L L' : CochainComplex A ℤ} {M M' : CochainComplex B ℤ}
    (f : L' ⟶ L) (g : M ⟶ M')
    (n : ℤ) : homTerm H L M n ⟶ homTerm H L' M' n :=
  Pi.lift fun p : ℤ ↦ homProj H L M n p (p + n) rfl ≫
    hMap H (f.f p) (g.f (p + n))

omit [Preadditive D] [H.Additive] [∀ a, (H.obj a).Additive] in
private lemma homTermMap_proj {L L' : CochainComplex A ℤ} {M M' : CochainComplex B ℤ}
    (f : L' ⟶ L) (g : M ⟶ M')
    (n p q : ℤ) (hpq : p + n = q) :
    homTermMap H f g n ≫ homProj H L' M' n p q hpq =
      homProj H L M n p q hpq ≫ hMap H (f.f p) (g.f q) := by
  subst q
  exact Pi.lift_comp_π _ _

omit [H.Additive] [∀ a, (H.obj a).Additive] in
private lemma homTermMap_comm {L L' : CochainComplex A ℤ} {M M' : CochainComplex B ℤ}
    (f : L' ⟶ L) (g : M ⟶ M')
    (n m : ℤ) :
    homTermMap H f g n ≫ homDiff H L' M' n m =
      homDiff H L M n m ≫ homTermMap H f g m := by
  apply Pi.hom_ext
  intro p
  change (homTermMap H f g n ≫ homDiff H L' M' n m) ≫
    homProj H L' M' m p (p + m) rfl =
    (homDiff H L M n m ≫ homTermMap H f g m) ≫ homProj H L' M' m p (p + m) rfl
  rw [Category.assoc, Category.assoc,
    homDiff_proj H L' M' n m p (p + m) (p + n) (p + m - n) rfl rfl (by omega),
    homTermMap_proj H, Preadditive.comp_sub, Linear.comp_units_smul,
    ← Category.assoc, homTermMap_proj H, ← Category.assoc, homTermMap_proj H,
    ← Category.assoc, homDiff_proj H L M n m p (p + m) (p + n) (p + m - n)
      rfl rfl (by omega)]
  simp only [Preadditive.sub_comp, Linear.units_smul_comp, Category.assoc,
    hMap_comp H, Category.id_comp, Category.comp_id]
  rw [g.comm, f.comm]

private noncomputable def homComplexMap {L L' : CochainComplex A ℤ} {M M' : CochainComplex B ℤ}
    (f : L' ⟶ L) (g : M ⟶ M') :
    homObjComplex H L M ⟶ homObjComplex H L' M' where
  f := homTermMap H f g
  comm' n m _ := homTermMap_comm H f g n m

private lemma homComplexMap_id (L : CochainComplex A ℤ)
    (M : CochainComplex B ℤ) : homComplexMap H (𝟙 L) (𝟙
    M) = 𝟙 _ := by
  apply HomologicalComplex.hom_ext
  intro n
  apply Pi.hom_ext
  intro p
  change homTermMap H (𝟙 L) (𝟙 M) n ≫ homProj H L M n p (p + n) rfl = _
  rw [homTermMap_proj H]
  simp [homProj, hMap_id]

private lemma homComplexMap_comp {L L' L'' : CochainComplex A ℤ} {M M' M'' : CochainComplex B ℤ}
    (f : L' ⟶ L) (f' : L'' ⟶ L') (g : M ⟶ M') (g' : M' ⟶ M'') :
    homComplexMap H f g ≫ homComplexMap H f' g' = homComplexMap H (f' ≫ f) (g ≫ g') := by
  apply HomologicalComplex.hom_ext
  intro n
  apply Pi.hom_ext
  intro p
  change (homTermMap H f g n ≫ homTermMap H f' g' n) ≫
    homProj H L'' M'' n p (p + n) rfl =
    homTermMap H (f' ≫ f) (g ≫ g') n ≫ homProj H L'' M'' n p (p + n) rfl
  rw [Category.assoc, homTermMap_proj H, ← Category.assoc, homTermMap_proj H,
    homTermMap_proj H, Category.assoc, hMap_comp H]
  rfl

private noncomputable def homBifunctor :
    (CochainComplex (A) ℤ)ᵒᵖ ⥤ CochainComplex B ℤ ⥤ CochainComplex
    (D) ℤ
    where
  obj L :=
    { obj M := homObjComplex H L.unop M
      map g := homComplexMap H (𝟙 L.unop) g
      map_id M := homComplexMap_id H L.unop M
      map_comp g g' := by rw [homComplexMap_comp H]; simp }
  map f :=
    { app M := homComplexMap H f.unop (𝟙 M)
      naturality {M M'} g := by
        dsimp
        rw [homComplexMap_comp H, homComplexMap_comp H]
        simp }
  map_id L := by
    apply NatTrans.ext
    funext M
    exact homComplexMap_id H L.unop M
  map_comp f f' := by
    apply NatTrans.ext
    funext M
    dsimp
    rw [homComplexMap_comp H]
    simp
omit [Preadditive A] [Preadditive B] [HasProducts D]
    [H.Additive] [∀ a, (H.obj a).Additive] in
/-- The projection data of a product Hom complex, with each law stored separately.
Source: Stacks Project, Algebraization, Tag 099I; sites-cohomology.tex, Section 0A8X.
(auxiliary; not a blueprint node). -/
structure ProductHomComplexData [HasZeroMorphisms A] [HasZeroMorphisms B]
    (F : (CochainComplex A ℤ)ᵒᵖ ⥤ CochainComplex B ℤ ⥤ CochainComplex D ℤ) where
  π : ∀ (L : CochainComplex A ℤ) (M : CochainComplex B ℤ) (n p q : ℤ), p + n = q →
    (((F.obj (op L)).obj M).X n ⟶ (H.obj (op (L.X p))).obj (M.X q))
  isLimit : ∀ (L : CochainComplex A ℤ) (M : CochainComplex B ℤ) (n : ℤ),
    Nonempty (IsLimit (Fan.mk (((F.obj (op L)).obj M).X n)
      (fun p : ℤ ↦ π L M n p (p + n) rfl)))
  differential : ∀ (L : CochainComplex A ℤ) (M : CochainComplex B ℤ)
    (n m p q q' p' : ℤ) (_hnm : n + 1 = m) (hpq : p + m = q)
    (hq' : p + n = q') (hp' : p' + n = q),
    ((F.obj (op L)).obj M).d n m ≫ π L M m p q hpq =
      π L M n p q' hq' ≫ (Functor.uncurry.obj H).map
        (X := (op (L.X p), M.X q')) (Y := (op (L.X p), M.X q))
        ((𝟙 (L.X p)).op, M.d q' q) -
      n.negOnePow • (π L M n p' q hp' ≫ (Functor.uncurry.obj H).map
        (X := (op (L.X p'), M.X q)) (Y := (op (L.X p), M.X q))
        ((L.d p p').op, 𝟙 (M.X q)))
  naturality : ∀ (L L' : CochainComplex A ℤ) (M M' : CochainComplex B ℤ)
    (f : L' ⟶ L) (g : M ⟶ M') (n p q : ℤ) (hpq : p + n = q),
    (((F.map f.op).app M) ≫ (F.obj (op L')).map g).f n ≫ π L' M' n p q hpq =
      π L M n p q hpq ≫ (Functor.uncurry.obj H).map
        (X := (op (L.X p), M.X q)) (Y := (op (L'.X p), M'.X q))
        ((f.f p).op, g.f q)

omit [Preadditive A] [Preadditive B] [HasProducts D]
    [H.Additive] [∀ a, (H.obj a).Additive] in
/-- Product projections, differential, and functoriality specifying a product Hom complex.
Source: Stacks Project, Algebraization, Tag 099I; sites-cohomology.tex, Section 0A8X
(auxiliary; not a blueprint node).
This proposition packages the full formulas so coefficient specializations can use the
abstract preadditive hom structures without re-elaborating them after substitution. -/
def ProductHomComplexSpecification [HasZeroMorphisms A] [HasZeroMorphisms B]
    (F : (CochainComplex A ℤ)ᵒᵖ ⥤ CochainComplex B ℤ ⥤ CochainComplex D ℤ) : Prop :=
  Nonempty (ProductHomComplexData H F)

/-- Existence of the Hom-complex bifunctor with its product projections and exact sign.
Source: Stacks Project, sites-cohomology.tex, Section 0A8X, and Algebraization, Tag 099I
(auxiliary; not a blueprint node).
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
theorem exists_bilinearHomComplexFunctor :
    ∃ F : (CochainComplex A ℤ)ᵒᵖ ⥤ CochainComplex B ℤ ⥤ CochainComplex D ℤ,
      ProductHomComplexSpecification H F := by
  refine ⟨homBifunctor H, ⟨⟨homProj H, ?_, ?_, ?_⟩⟩⟩
  · intro L M n
    exact ⟨productIsProduct _⟩
  · intro L M n m p q q' p' hnm hpq hq' hp'
    exact homDiff_proj H L M n m p q q' p' hpq hq' hp'
  · intro L L' M M' f g n p q hpq
    change (homTermMap H f (𝟙 M) n ≫ homTermMap H (𝟙 L') g n) ≫
      homProj H L' M' n p q hpq = _
    rw [Category.assoc, homTermMap_proj H, ← Category.assoc, homTermMap_proj H,
      Category.assoc, hMap_comp H]
    simp only [HomologicalComplex.id_f, Category.id_comp]
    rfl
end CategoryTheory
