/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-!
# The Čech complex of a family of morphisms with a common target

Let `C` be a category, `V` an object of `C` such that `Over V` has finite products, and
`U : ι → Over V` a family of objects over `V`. For a presheaf `P` of abelian groups on `C`, the
(ordered) Čech complex `Č(U, P)` has in degree `k` the cochains `c = (c y)_y`, indexed by the
tuples `y : Fin (k + 1) → ι`, with `c y ∈ P(U (y 0) ×_V ⋯ ×_V U (y k))`; the differential is the
alternating sum of the restrictions along the projections that forget one factor.

The main result is that `Č(U, P)` is exact in positive degrees when `P` is an injective
presheaf, for *every* family `U`. An injective presheaf is a direct summand of the presheaf
`Y ↦ ∏_{Z, g : Z ⟶ Y} P(Z)` (`CategoryTheory.Presheaf.cofree`), whose Čech complex is
contracted by inserting, in front of a tuple of morphisms `g : Z ⟶ U (y 0) ×_V ⋯ ×_V U (y k)`,
a morphism `Z ⟶ U j` over `V` chosen depending only on `Z ⟶ V`.

## Main definitions

- `CategoryTheory.Presheaf.cechComplex`: the Čech complex `Č(U, P)`, as a functor of `P`.
- `CategoryTheory.Presheaf.cofree`: the presheaf `Y ↦ ∏_{Z, g : Z ⟶ Y} P(Z)`.

## Main statements

- `CategoryTheory.Presheaf.exactAt_cechComplex_of_injective`: the Čech complex of an injective
  presheaf of abelian groups is exact in positive degrees.
- `CategoryTheory.Presheaf.exactAt_cechComplex_of_sectionwise`: exactness of Čech complexes
  passes to the cokernel of a sectionwise short exact sequence of presheaves.

## Implementation notes

As in `WeilConjectures.Topology.Sheaves.Cech`, the cochains are dependent functions and the
complex is the alternating coface map complex of an explicit cosimplicial abelian group, rather
than Mathlib's `CategoryTheory.cechComplexFunctor`, whose cochains are elements of categorical
products.
-/

@[expose] public section

universe s t v w

open CategoryTheory Limits Opposite

namespace CategoryTheory.Presheaf

variable {C : Type w} [Category.{v} C] {V : C} [HasFiniteProducts (Over V)] {ι : Type t}
  (U : ι → Over V)

/-- The member `U (y 0) ×_V ⋯ ×_V U (y k)` of the Čech nerve of the family `U`, indexed by the
tuple `y`: the product in `Over V`. -/
noncomputable abbrev cechNerveObj {k : ℕ} (y : Fin (k + 1) → ι) : Over V :=
  ∏ᶜ fun l ↦ U (y l)

/-- The map `U (y 0) ×_V ⋯ ×_V U (y m) ⟶ U (y (θ 0)) ×_V ⋯ ×_V U (y (θ k))` of the Čech nerve
induced by `θ : Fin (k + 1) → Fin (m + 1)`. -/
noncomputable abbrev cechNerveMap {k m : ℕ} (y : Fin (m + 1) → ι)
    (θ : Fin (k + 1) → Fin (m + 1)) : cechNerveObj U y ⟶ cechNerveObj U (y ∘ θ) :=
  Pi.lift fun l ↦ Pi.π (fun l ↦ U (y l)) (θ l)

@[reassoc (attr := simp)]
lemma cechNerveMap_π {k m : ℕ} (y : Fin (m + 1) → ι) (θ : Fin (k + 1) → Fin (m + 1))
    (l : Fin (k + 1)) :
    cechNerveMap U y θ ≫ Pi.π (fun l ↦ U (y (θ l))) l = Pi.π (fun l ↦ U (y l)) (θ l) :=
  Pi.lift_comp_π _ _

lemma cechNerveMap_id {k : ℕ} (y : Fin (k + 1) → ι) : cechNerveMap U y id = 𝟙 _ :=
  Pi.hom_ext _ _ fun l ↦ by erw [Pi.lift_comp_π, Category.id_comp]; rfl

lemma cechNerveMap_comp {k m p : ℕ} (y : Fin (p + 1) → ι) (θ : Fin (k + 1) → Fin (m + 1))
    (θ' : Fin (m + 1) → Fin (p + 1)) :
    cechNerveMap U y θ' ≫ cechNerveMap U (y ∘ θ') θ = cechNerveMap U y (θ' ∘ θ) :=
  Pi.hom_ext _ _ fun l ↦ by
    erw [Category.assoc, Pi.lift_comp_π, Pi.lift_comp_π, Pi.lift_comp_π]; rfl

/-- Transport along an equality of tuples commutes with the projections. -/
lemma eqToHom_cechNerveObj_π {k : ℕ} {y y' : Fin (k + 1) → ι} (h : y = y') (l : Fin (k + 1)) :
    eqToHom (congrArg (cechNerveObj U) h) ≫ Pi.π (fun l ↦ U (y' l)) l =
      Pi.π (fun l ↦ U (y l)) l ≫ eqToHom (congrArg U (congrFun h l)) := by
  subst h
  simp

/-- The morphism `W ⟶ U a ×_V U (y 0) ×_V ⋯ ×_V U (y k)` with components `λ : W ⟶ U a` and
`g : W ⟶ U (y 0) ×_V ⋯ ×_V U (y k)`. -/
noncomputable def cechNerveCons {k : ℕ} {W : Over V} {a : ι} (lam : W ⟶ U a)
    {y : Fin (k + 1) → ι} (g : W ⟶ cechNerveObj U y) :
    W ⟶ cechNerveObj U (Fin.cons a y : Fin (k + 2) → ι) :=
  Pi.lift (Fin.cons (α := fun l ↦ W ⟶ U ((Fin.cons a y : Fin (k + 2) → ι) l)) lam
    fun l ↦ g ≫ Pi.π _ l)

@[reassoc]
lemma cechNerveCons_π_zero {k : ℕ} {W : Over V} {a : ι} (lam : W ⟶ U a)
    {y : Fin (k + 1) → ι} (g : W ⟶ cechNerveObj U y) :
    cechNerveCons U lam g ≫ Pi.π (fun l ↦ U ((Fin.cons a y : Fin (k + 2) → ι) l)) 0 = lam :=
  Pi.lift_comp_π _ _

@[reassoc]
lemma cechNerveCons_π_succ {k : ℕ} {W : Over V} {a : ι} (lam : W ⟶ U a)
    {y : Fin (k + 1) → ι} (g : W ⟶ cechNerveObj U y) (l : Fin (k + 1)) :
    cechNerveCons U lam g ≫ Pi.π (fun l ↦ U ((Fin.cons a y : Fin (k + 2) → ι) l)) l.succ =
      g ≫ Pi.π _ l :=
  Pi.lift_comp_π _ _

lemma cechNerveCons_π_of_eq_zero {k : ℕ} {W : Over V} {a : ι} (lam : W ⟶ U a)
    {y : Fin (k + 1) → ι} (g : W ⟶ cechNerveObj U y) (m : Fin (k + 2)) (hm : m = 0)
    (h : U ((Fin.cons a y : Fin (k + 2) → ι) m) = U a) :
    cechNerveCons U lam g ≫ Pi.π _ m ≫ eqToHom h = lam := by
  subst hm
  rw [cechNerveCons, Pi.lift_comp_π_assoc]
  exact Category.comp_id _

lemma cechNerveCons_π_of_eq_succ {k : ℕ} {W : Over V} {a : ι} (lam : W ⟶ U a)
    {y : Fin (k + 1) → ι} (g : W ⟶ cechNerveObj U y) (m : Fin (k + 2)) (l : Fin (k + 1))
    (hm : m = l.succ) (h : U ((Fin.cons a y : Fin (k + 2) → ι) m) = U (y l)) :
    cechNerveCons U lam g ≫ Pi.π _ m ≫ eqToHom h = g ≫ Pi.π _ l := by
  subst hm
  rw [cechNerveCons, Pi.lift_comp_π_assoc]
  exact Category.comp_id _

/-- Forgetting the first factor of `U a ×_V U (y 0) ×_V ⋯ ×_V U (y k)` undoes
`CategoryTheory.Presheaf.cechNerveCons`. -/
lemma cechNerveCons_cechNerveMap_succ {k : ℕ} {W : Over V} {a : ι} (lam : W ⟶ U a)
    {y : Fin (k + 1) → ι} (g : W ⟶ cechNerveObj U y) :
    cechNerveCons U lam g ≫ cechNerveMap U (Fin.cons a y : Fin (k + 2) → ι) Fin.succ = g :=
  Pi.hom_ext _ _ fun l ↦ by
    erw [Category.assoc, Pi.lift_comp_π]
    exact cechNerveCons_π_succ U lam g l


variable (P : Cᵒᵖ ⥤ AddCommGrpCat.{max w v})

/-- The Čech cochains of degree `k` of the family `U` with values in `P`: the families of
sections `c y ∈ P(U (y 0) ×_V ⋯ ×_V U (y k))` indexed by the tuples `y : Fin (k + 1) → ι`. -/
abbrev CechCochain (k : ℕ) : Type (max w v t) :=
  ∀ y : Fin (k + 1) → ι, P.obj (op (cechNerveObj U y).left)

/-- The Čech cosimplicial abelian group of the family `U` with values in a presheaf `P`, as a
functor of `P`. In degree `k` it is the group `CechCochain U P k`, and a map `θ` of the simplex
category acts by `c ↦ (y ↦ c (y ∘ θ))`, restricted along `CategoryTheory.Presheaf.cechNerveMap`.
-/
@[simps]
noncomputable def cechCosimplicialObject :
    (Cᵒᵖ ⥤ AddCommGrpCat.{max w v}) ⥤ CosimplicialObject AddCommGrpCat.{max w v t} where
  obj P :=
    { obj k := AddCommGrpCat.of (CechCochain U P k.len)
      map {k m} θ := AddCommGrpCat.ofHom (AddMonoidHom.pi fun y ↦
        (P.map (cechNerveMap U y θ.toOrderHom).left.op).hom.comp
          (Pi.evalAddMonoidHom _ (y ∘ θ.toOrderHom)))
      map_id k := by
        refine AddCommGrpCat.ext fun c ↦ funext fun y ↦ ?_
        change P.map (cechNerveMap U y id).left.op (c y) = c y
        rw [cechNerveMap_id]
        exact ConcreteCategory.congr_hom (P.map_id _) (c y)
      map_comp {k m p} θ θ' := by
        refine AddCommGrpCat.ext fun c ↦ funext fun y ↦ ?_
        change P.map (cechNerveMap U y (θ'.toOrderHom ∘ θ.toOrderHom)).left.op _ =
          P.map (cechNerveMap U y θ'.toOrderHom).left.op
            (P.map (cechNerveMap U (y ∘ θ'.toOrderHom) θ.toOrderHom).left.op _)
        rw [← cechNerveMap_comp, Over.comp_left, op_comp, P.map_comp]
        rfl }
  map φ :=
    { app k := AddCommGrpCat.ofHom (AddMonoidHom.pi fun y ↦
        (φ.app _).hom.comp (Pi.evalAddMonoidHom _ y))
      naturality k m θ := by
        refine AddCommGrpCat.ext fun c ↦ funext fun y ↦ ?_
        exact NatTrans.naturality_apply φ _ (c _) }
  map_id P := rfl
  map_comp φ ψ := rfl

/-- The Čech complex `Č(U, P)` of the family `U` with values in a presheaf `P`, as a functor
of `P`: the alternating coface map complex of `CategoryTheory.Presheaf.cechCosimplicialObject`.
-/
noncomputable def cechComplex :
    (Cᵒᵖ ⥤ AddCommGrpCat.{max w v}) ⥤ CochainComplex AddCommGrpCat.{max w v t} ℕ :=
  cechCosimplicialObject U ⋙ AlgebraicTopology.alternatingCofaceMapComplex _

instance : (cechComplex U).Additive where
  map_add := rfl

/-- A finite sum of morphisms of abelian groups is computed pointwise. -/
private lemma sum_apply' {M N : AddCommGrpCat.{s}} {κ : Type*} (f : κ → (M ⟶ N))
    (s : Finset κ) (x : M) : (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  rw [← AddMonoidHom.finsetSum_apply]
  exact congr($(map_sum AddCommGrpCat.homAddEquiv f s) x)

/-- The Čech differential is the alternating sum of the restrictions of the faces. -/
lemma cechComplex_d_apply (k : ℕ) (c : ((cechComplex U).obj P).X k)
    (y : Fin (k + 2) → ι) :
    ((cechComplex U).obj P).d k (k + 1) c y =
      ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) •
        P.map (cechNerveMap U y i.succAbove).left.op (c (y ∘ i.succAbove)) := by
  have h : ((cechComplex U).obj P).d k (k + 1) =
      ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) • ((cechCosimplicialObject U).obj P).δ i :=
    CochainComplex.of_d (fun m ↦ ((cechCosimplicialObject U).obj P).obj (SimplexCategory.mk m))
      (AlgebraicTopology.AlternatingCofaceMapComplex.objD _) k
  rw [h]
  refine (congrFun (sum_apply' (fun i : Fin (k + 2) ↦
    (-1 : ℤ) ^ (i : ℕ) • ((cechCosimplicialObject U).obj P).δ i) Finset.univ c) y).trans ?_
  refine (Finset.sum_apply _ _ _).trans ?_
  rfl

@[simp]
lemma cechComplex_map_f_apply {P Q : Cᵒᵖ ⥤ AddCommGrpCat.{max w v}} (φ : P ⟶ Q) (k : ℕ)
    (c : ((cechComplex U).obj P).X k) (y : Fin (k + 1) → ι) :
    ((cechComplex U).map φ).f k c y = φ.app _ (c y) :=
  rfl

/-- The zero Čech cochain vanishes termwise. -/
@[simp]
lemma cechComplex_zero_apply (k : ℕ) (y : Fin (k + 1) → ι) :
    (0 : ((cechComplex U).obj P).X k) y = 0 :=
  rfl

/-- Subtraction of Čech cochains is termwise. -/
@[simp]
lemma cechComplex_sub_apply (k : ℕ) (a b : ((cechComplex U).obj P).X k)
    (y : Fin (k + 1) → ι) : (a - b) y = a y - b y :=
  rfl

/-- Exactness of the Čech complex in degree `q + 1`, in terms of cochains: every cocycle is a
coboundary. -/
lemma exactAt_cechComplex_iff (q : ℕ) :
    ((cechComplex U).obj P).ExactAt (q + 1) ↔
      ∀ c : ((cechComplex U).obj P).X (q + 1), ((cechComplex U).obj P).d (q + 1) (q + 2) c = 0 →
        ∃ b : ((cechComplex U).obj P).X q, ((cechComplex U).obj P).d q (q + 1) b = c := by
  rw [HomologicalComplex.exactAt_iff' _ q (q + 1) (q + 2) (by simp) (by simp),
    ShortComplex.ab_exact_iff]
  rfl

/-- A morphism of presheaves commutes with the Čech differentials. -/
lemma cechComplex_map_f_d_apply {P Q : Cᵒᵖ ⥤ AddCommGrpCat.{max w v}} (φ : P ⟶ Q) (k : ℕ)
    (c : ((cechComplex U).obj P).X k) :
    ((cechComplex U).map φ).f (k + 1) (((cechComplex U).obj P).d k (k + 1) c) =
      ((cechComplex U).obj Q).d k (k + 1) (((cechComplex U).map φ).f k c) :=
  (ConcreteCategory.congr_hom (((cechComplex U).map φ).comm k (k + 1)) c).symm

/-- The composite of two Čech differentials vanishes. -/
lemma cechComplex_d_d_apply (k : ℕ) (c : ((cechComplex U).obj P).X k) :
    ((cechComplex U).obj P).d (k + 1) (k + 2) (((cechComplex U).obj P).d k (k + 1) c) = 0 :=
  ConcreteCategory.congr_hom (((cechComplex U).obj P).d_comp_d k (k + 1) (k + 2)) c

/-- A sectionwise injective morphism of presheaves induces injections on Čech cochains. -/
lemma cechComplex_map_f_injective {P Q : Cᵒᵖ ⥤ AddCommGrpCat.{max w v}} (f : P ⟶ Q)
    (hf : ∀ W, Function.Injective (f.app W)) (k : ℕ) :
    Function.Injective (((cechComplex U).map f).f k) := fun a b h ↦ by
  funext y
  exact hf _ (by simpa only [cechComplex_map_f_apply] using congr_fun h y)

/-- If `P₁ → P₂ → P₃` is sectionwise exact at `P₂`, then so are the Čech cochains. -/
lemma exists_cechComplex_map_f_eq {P₁ P₂ P₃ : Cᵒᵖ ⥤ AddCommGrpCat.{max w v}}
    (f : P₁ ⟶ P₂) (g : P₂ ⟶ P₃) (hfg : ∀ W x, g.app W x = 0 → ∃ y, f.app W y = x) (k : ℕ)
    (a : ((cechComplex U).obj P₂).X k) (ha : ((cechComplex U).map g).f k a = 0) :
    ∃ e, ((cechComplex U).map f).f k e = a := by
  have (y : Fin (k + 1) → ι) := hfg _ (a y) (by
    simpa only [cechComplex_map_f_apply, cechComplex_zero_apply] using congr_fun ha y)
  choose e he using this
  exact ⟨e, funext fun y ↦ (cechComplex_map_f_apply U f k e y).trans (he y)⟩

/-- If the composite `P₁ → P₂ → P₃` vanishes sectionwise, then it vanishes on Čech cochains. -/
lemma cechComplex_map_f_map_f_eq_zero {P₁ P₂ P₃ : Cᵒᵖ ⥤ AddCommGrpCat.{max w v}}
    (f : P₁ ⟶ P₂) (g : P₂ ⟶ P₃) (hfg : ∀ W x, g.app W (f.app W x) = 0) (k : ℕ)
    (b : ((cechComplex U).obj P₁).X k) :
    ((cechComplex U).map g).f k (((cechComplex U).map f).f k b) = 0 := by
  funext y
  rw [cechComplex_map_f_apply, cechComplex_map_f_apply, cechComplex_zero_apply]
  exact hfg _ _

/-- Let `P₁ → P₂ → P₃` be morphisms of presheaves which are sectionwise left exact, and such
that `P₂ → P₃` is surjective on the sections over the members of the Čech nerve of `U`. If the
Čech complexes of `P₁` and `P₂` are exact in degrees `q + 2` and `q + 1`, then the Čech complex
of `P₃` is exact in degree `q + 1`. -/
theorem exactAt_cechComplex_of_sectionwise {P₁ P₂ P₃ : Cᵒᵖ ⥤ AddCommGrpCat.{max w v}}
    (f : P₁ ⟶ P₂) (g : P₂ ⟶ P₃) (hfg : ∀ W x, g.app W (f.app W x) = 0)
    (hf : ∀ W, Function.Injective (f.app W))
    (hfg' : ∀ W x, g.app W x = 0 → ∃ y, f.app W y = x)
    (hg : ∀ (k : ℕ) (y : Fin (k + 1) → ι),
      Function.Surjective (g.app (op (cechNerveObj U y).left)))
    (q : ℕ) (h₁ : ((cechComplex U).obj P₁).ExactAt (q + 2))
    (h₂ : ((cechComplex U).obj P₂).ExactAt (q + 1)) :
    ((cechComplex U).obj P₃).ExactAt (q + 1) := by
  have hinj := cechComplex_map_f_injective U f hf
  have hker := exists_cechComplex_map_f_eq U f g hfg'
  have hzero := cechComplex_map_f_map_f_eq_zero U f g hfg
  rw [exactAt_cechComplex_iff] at h₁ h₂ ⊢
  intro c hc
  obtain ⟨a, hac⟩ : ∃ a : ((cechComplex U).obj P₂).X (q + 1),
      ((cechComplex U).map g).f (q + 1) a = c := by
    choose a ha using fun y ↦ hg (q + 1) y (c y)
    exact ⟨a, funext fun y ↦ (cechComplex_map_f_apply U g _ a y).trans (ha y)⟩
  obtain ⟨e, he⟩ := hker _ (((cechComplex U).obj P₂).d (q + 1) (q + 2) a) (by
    rw [cechComplex_map_f_d_apply, hac, hc])
  obtain ⟨b, hb⟩ := h₁ e (hinj _ (by
    rw [cechComplex_map_f_d_apply, he, map_zero, cechComplex_d_d_apply]))
  obtain ⟨a', ha'⟩ := h₂ (a - ((cechComplex U).map f).f (q + 1) b) (by
    rw [map_sub, ← cechComplex_map_f_d_apply, hb, he, sub_self])
  refine ⟨((cechComplex U).map g).f q a', ?_⟩
  rw [← cechComplex_map_f_d_apply, ha', map_sub, hzero, sub_zero, hac]

/-! ### The cofree presheaf -/

/-- The presheaf `Y ↦ ∏_{Z, g : Z ⟶ Y} P(Z)` of families of sections of `P` indexed by all the
morphisms into `Y`, with restriction by precomposition. It is the product over all objects `Z`
of the right adjoints of the evaluation functors at `Z`. -/
@[simps]
noncomputable def cofree : Cᵒᵖ ⥤ AddCommGrpCat.{max w v} where
  obj Y := AddCommGrpCat.of (∀ (Z : C) (_ : Z ⟶ Y.unop), P.obj (op Z))
  map {Y Y'} h := AddCommGrpCat.ofHom
    { toFun c Z g := c Z (g ≫ h.unop)
      map_zero' := rfl
      map_add' _ _ := rfl }
  map_id _ := by
    refine AddCommGrpCat.ext fun c ↦ funext fun Z ↦ funext fun g ↦ ?_
    simp
  map_comp _ _ := by
    refine AddCommGrpCat.ext fun c ↦ funext fun Z ↦ funext fun g ↦ ?_
    simp

/-- The embedding of a presheaf into its cofree presheaf, `p ↦ (g ↦ P(g) p)`. -/
@[simps]
noncomputable def toCofree : P ⟶ cofree P where
  app Y := AddCommGrpCat.ofHom
    { toFun p Z g := P.map g.op p
      map_zero' := funext fun _ ↦ funext fun _ ↦ map_zero _
      map_add' _ _ := funext fun _ ↦ funext fun _ ↦ map_add _ _ _ }
  naturality Y Y' h := by
    refine AddCommGrpCat.ext fun p ↦ funext fun Z ↦ funext fun g ↦ ?_
    change P.map g.op (P.map h p) = P.map (g ≫ h.unop).op p
    rw [op_comp, P.map_comp]
    rfl

instance : Mono (toCofree P) := by
  have (Y : Cᵒᵖ) : Mono ((toCofree P).app Y) :=
    (AddCommGrpCat.mono_iff_injective _).2 fun p p' h ↦ by
      have := congrFun (congrFun h Y.unop) (𝟙 _)
      change P.map (𝟙 _).op p = P.map (𝟙 _).op p' at this
      simpa using this
  exact NatTrans.mono_of_mono_app _

/-- Two components of a Čech cochain of the cofree presheaf indexed by equal tuples agree, after
transport of the morphism along the equality. -/
lemma cofree_cochain_congr {k : ℕ} (c : ((cechComplex U).obj (cofree P)).X k)
    {y y' : Fin (k + 1) → ι} (h : y = y') (Z : C) (g : Z ⟶ (cechNerveObj U y).left) :
    c y Z g = c y' Z (g ≫ (eqToHom (congrArg (cechNerveObj U) h)).left) := by
  subst h
  simp

/-- The Čech differential of a cochain of the cofree presheaf, evaluated at `g : Z ⟶ U_y`. -/
lemma cechComplex_cofree_d_apply (k : ℕ) (c : ((cechComplex U).obj (cofree P)).X k)
    (y : Fin (k + 2) → ι) (Z : C) (g : Z ⟶ (cechNerveObj U y).left) :
    ((cechComplex U).obj (cofree P)).d k (k + 1) c y Z g =
      ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) •
        c (y ∘ i.succAbove) Z (g ≫ (cechNerveMap U y i.succAbove).left) := by
  rw [cechComplex_d_apply]
  erw [Finset.sum_apply, Finset.sum_apply]
  rfl

/-- A component of a Čech cochain of the cofree presheaf, along a face of the Čech nerve,
followed by a transport along an equality of tuples. -/
lemma cofree_cochain_face_eq {k : ℕ} (c : ((cechComplex U).obj (cofree P)).X k) {Z : C}
    {f : Z ⟶ V} {m : ℕ} {y : Fin (m + 1) → ι} (G : Over.mk f ⟶ cechNerveObj U y)
    (θ : Fin (k + 1) → Fin (m + 1)) {y' : Fin (k + 1) → ι} (h : y ∘ θ = y')
    (G' : Over.mk f ⟶ cechNerveObj U y')
    (hG : ∀ l, G ≫ Pi.π _ (θ l) ≫ eqToHom (congrArg U (congrFun h l)) = G' ≫ Pi.π _ l) :
    c (y ∘ θ) Z (G.left ≫ (cechNerveMap U y θ).left) = c y' Z G'.left := by
  rw [cofree_cochain_congr U P c h]
  congr 1
  rw [← Over.comp_left, ← Over.comp_left]
  congr 1
  refine Pi.hom_ext _ _ fun l ↦ ?_
  rw [Category.assoc, Category.assoc, eqToHom_cechNerveObj_π U h, ← hG]
  erw [Pi.lift_comp_π_assoc]

/-- The Čech complex of the cofree presheaf is exact in positive degrees. -/
theorem exactAt_cechComplex_cofree (q : ℕ) :
    ((cechComplex U).obj (cofree P)).ExactAt (q + 1) := by
  classical
  rw [exactAt_cechComplex_iff]
  intro c hc
  -- for a morphism `f : Z ⟶ V`, a lift of `f` to some member of the family, if there is one
  let j (Z : C) (f : Z ⟶ V) (h : ∃ a, Nonempty (Over.mk f ⟶ U a)) : ι := h.choose
  let lam (Z : C) (f : Z ⟶ V) (h : ∃ a, Nonempty (Over.mk f ⟶ U a)) :
      Over.mk f ⟶ U (j Z f h) := h.choose_spec.some
  have hex {k : ℕ} (y : Fin (k + 1) → ι) (Z : C) (g : Z ⟶ (cechNerveObj U y).left) :
      ∃ a, Nonempty (Over.mk (g ≫ (cechNerveObj U y).hom) ⟶ U a) :=
    ⟨y 0, ⟨Over.homMk g ≫ Pi.π _ 0⟩⟩
  let b : ((cechComplex U).obj (cofree P)).X q := fun y Z g ↦
    c (Fin.cons (j Z _ (hex y Z g)) y) Z
      (cechNerveCons U (lam Z _ (hex y Z g)) (Over.homMk g)).left
  have hb (y : Fin (q + 1) → ι) (Z : C) (g : Z ⟶ (cechNerveObj U y).left) (f : Z ⟶ V)
      (hf : g ≫ (cechNerveObj U y).hom = f) (h : ∃ a, Nonempty (Over.mk f ⟶ U a)) :
      b y Z g = c (Fin.cons (j Z f h) y) Z
        (cechNerveCons U (lam Z f h) (Over.homMk g hf : Over.mk f ⟶ _)).left := by
    subst hf
    rfl
  refine ⟨b, ?_⟩
  funext (y : Fin (q + 2) → ι)
  funext Z g
  set f := g ≫ (cechNerveObj U y).hom with hf
  have hex' : ∃ a, Nonempty (Over.mk f ⟶ U a) := hex y Z g
  set J := j Z f hex'
  set Λ := lam Z f hex'
  let G : Over.mk f ⟶ cechNerveObj U (Fin.cons J y : Fin (q + 3) → ι) :=
    cechNerveCons U Λ (Over.homMk g)
  -- the cocycle condition at the tuple `Fin.cons J y`
  have h₀ := congrArg (fun c' ↦ c' (Fin.cons J y) Z G.left) hc
  simp only at h₀
  rw [cechComplex_cofree_d_apply, Fin.sum_univ_succ] at h₀
  change _ = (0 : P.obj (op Z)) at h₀
  -- the first face of the cocycle condition is `c y`
  have e₀ : c ((Fin.cons J y : Fin (q + 3) → ι) ∘ (0 : Fin (q + 3)).succAbove) Z
      (G.left ≫ (cechNerveMap U (Fin.cons J y : Fin (q + 3) → ι)
        (0 : Fin (q + 3)).succAbove).left) = c y Z g :=
    cofree_cochain_face_eq U P c G _ (by funext l; simp) (Over.homMk g) fun l ↦
      cechNerveCons_π_of_eq_succ U Λ _ _ l (by simp) _
  -- the other faces are the terms of the differential of `b`
  have e (i : Fin (q + 2)) : c ((Fin.cons J y : Fin (q + 3) → ι) ∘ i.succ.succAbove) Z
      (G.left ≫ (cechNerveMap U (Fin.cons J y : Fin (q + 3) → ι) i.succ.succAbove).left) =
      b (y ∘ i.succAbove) Z (g ≫ (cechNerveMap U y i.succAbove).left) := by
    rw [hb _ _ _ f (by simp [hf]) hex']
    refine cofree_cochain_face_eq U P c G _
      (by funext l; cases l using Fin.cases with | zero => rfl | succ l => simp) _ fun l ↦ ?_
    cases l using Fin.cases with
    | zero =>
      exact (cechNerveCons_π_of_eq_zero U Λ _ _ (by simp) _).trans
        (cechNerveCons_π_zero U _ _).symm
    | succ l =>
      refine (cechNerveCons_π_of_eq_succ U Λ _ _ (i.succAbove l) (by simp) _).trans ?_
      rw [cechNerveCons_π_succ]
      ext1
      simp only [Over.comp_left, Over.homMk_left, Category.assoc]
      rw [← Over.comp_left]
      erw [Pi.lift_comp_π]
  rw [e₀] at h₀
  simp only [e, Fin.val_succ, pow_succ, mul_neg_one, neg_smul, Finset.sum_neg_distrib,
    Fin.val_zero, pow_zero, one_smul] at h₀
  rw [cechComplex_cofree_d_apply]
  exact (add_neg_eq_zero.mp h₀).symm

/-- The Čech complex of an injective presheaf of abelian groups is exact in positive degrees:
the presheaf is a direct summand of its cofree presheaf, whose Čech complex is exact. -/
theorem exactAt_cechComplex_of_injective [Injective P] (q : ℕ) :
    ((cechComplex U).obj P).ExactAt (q + 1) := by
  have hr := Injective.comp_factorThru (𝟙 P) (toCofree P)
  set ι' := (cechComplex U).map (toCofree P)
  set ρ := (cechComplex U).map (Injective.factorThru (𝟙 P) (toCofree P))
  have hιρ (k : ℕ) (c : ((cechComplex U).obj P).X k) : ρ.f k (ι'.f k c) = c := by
    rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f, ← Functor.map_comp, hr,
      CategoryTheory.Functor.map_id, HomologicalComplex.id_f, ConcreteCategory.id_apply]
  rw [exactAt_cechComplex_iff]
  intro c hc
  obtain ⟨b, hb⟩ := (exactAt_cechComplex_iff U _ q).1 (exactAt_cechComplex_cofree U P q)
    (ι'.f (q + 1) c) (by
      exact (ConcreteCategory.congr_hom (ι'.comm (q + 1) (q + 2)) c).trans
        ((congrArg (ι'.f (q + 2)) hc).trans (map_zero _)))
  exact ⟨ρ.f q b, (ConcreteCategory.congr_hom (ρ.comm q (q + 1)) b).trans
    ((congrArg (ρ.f (q + 1)) hb).trans (hιρ _ c))⟩

end CategoryTheory.Presheaf
