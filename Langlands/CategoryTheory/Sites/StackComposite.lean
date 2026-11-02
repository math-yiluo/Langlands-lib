import Mathlib.CategoryTheory.Sites.Descent.Precoverage
import Mathlib.CategoryTheory.Sites.Hypercover.Zero

/-! # Effective descent along composite families -/

universe w t t' v' v u' u

open CategoryTheory Opposite Limits Bicategory
open CategoryTheory.Pseudofunctor CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Langlands.StackComposite

variable {C : Type u} [Category.{v} C] {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}

lemma toLoc_comp {X Y Z : C} {x : Y ⟶ X} {g : Z ⟶ Y} {gx : Z ⟶ X} (h : g ≫ x = gx) :
    x.op.toLoc ≫ g.op.toLoc = gx.op.toLoc := by
  subst h
  rfl

section Assoc

variable {X Y Z W : C} (x : Y ⟶ X) (g : Z ⟶ Y) (h : W ⟶ Z) (gx : Z ⟶ X) (hg : W ⟶ Y)
  (hgx : W ⟶ X) (e₁ : g ≫ x = gx) (e₂ : h ≫ g = hg) (e₃ : h ≫ gx = hgx)

include e₁ e₂ e₃

lemma map_mapComp'_inv_comp_mapComp'_inv (A : F.obj (.mk (op X))) :
    (F.map h.op.toLoc).toFunctor.map
        ((F.mapComp' x.op.toLoc g.op.toLoc gx.op.toLoc (toLoc_comp e₁)).inv.toNatTrans.app A) ≫
      (F.mapComp' gx.op.toLoc h.op.toLoc hgx.op.toLoc (toLoc_comp e₃)).inv.toNatTrans.app A =
    (F.mapComp' g.op.toLoc h.op.toLoc hg.op.toLoc (toLoc_comp e₂)).inv.toNatTrans.app
        ((F.map x.op.toLoc).toFunctor.obj A) ≫
      (F.mapComp' x.op.toLoc hg.op.toLoc hgx.op.toLoc
        (toLoc_comp (by rw [← e₂, ← e₃, ← e₁, Category.assoc]))).inv.toNatTrans.app A := by
  simpa using F.mapComp'_inv_whiskerRight_mapComp'₀₂₃_inv_app x.op.toLoc g.op.toLoc
    h.op.toLoc gx.op.toLoc hg.op.toLoc hgx.op.toLoc (toLoc_comp e₁) (toLoc_comp e₂)
    (toLoc_comp e₃) A

lemma mapComp'_hom_comp_map_mapComp'_hom (A : F.obj (.mk (op X))) :
    (F.mapComp' gx.op.toLoc h.op.toLoc hgx.op.toLoc (toLoc_comp e₃)).hom.toNatTrans.app A ≫
      (F.map h.op.toLoc).toFunctor.map
        ((F.mapComp' x.op.toLoc g.op.toLoc gx.op.toLoc (toLoc_comp e₁)).hom.toNatTrans.app A) =
    (F.mapComp' x.op.toLoc hg.op.toLoc hgx.op.toLoc
        (toLoc_comp (by rw [← e₂, ← e₃, ← e₁, Category.assoc]))).hom.toNatTrans.app A ≫
      (F.mapComp' g.op.toLoc h.op.toLoc hg.op.toLoc (toLoc_comp e₂)).hom.toNatTrans.app
        ((F.map x.op.toLoc).toFunctor.obj A) := by
  simpa using F.mapComp'₀₂₃_hom_comp_mapComp'_hom_whiskerRight_app x.op.toLoc g.op.toLoc
    h.op.toLoc gx.op.toLoc hg.op.toLoc hgx.op.toLoc (toLoc_comp e₁) (toLoc_comp e₂)
    (toLoc_comp e₃) A

end Assoc

section PullHom

variable {X₁ X₂ X₃ : C} {M₁ : F.obj (.mk (op X₁))} {M₂ : F.obj (.mk (op X₂))}
  {M₃ : F.obj (.mk (op X₃))} {Y : C} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂} {f₃ : Y ⟶ X₃}

/-- `pullHom` is compatible with composition. -/
@[reassoc]
lemma pullHom_comp
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂)
    (ψ : (F.map f₂.op.toLoc).toFunctor.obj M₂ ⟶ (F.map f₃.op.toLoc).toFunctor.obj M₃)
    {Y' : C} (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (gf₃ : Y' ⟶ X₃)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) (hgf₃ : g ≫ f₃ = gf₃) :
    pullHom (φ ≫ ψ) g gf₁ gf₃ hgf₁ hgf₃ =
      pullHom φ g gf₁ gf₂ hgf₁ hgf₂ ≫ pullHom ψ g gf₂ gf₃ hgf₂ hgf₃ := by
  simp [pullHom]

/-- `pullHom` of an identity is an identity. -/
@[simp]
lemma pullHom_id_hom {Y' : C} (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (hgf₁ : g ≫ f₁ = gf₁) :
    pullHom (𝟙 ((F.map f₁.op.toLoc).toFunctor.obj M₁)) g gf₁ gf₁ hgf₁ hgf₁ = 𝟙 _ := by
  simp [pullHom]

/-- Pulling back a morphism conjugated by composition comparisons. -/
lemma map_conj {Y X₁ X₂ Z W : C} {A : F.obj (.mk (op X₁))} {B : F.obj (.mk (op X₂))}
    (x₁ : Y ⟶ X₁) (x₂ : Y ⟶ X₂) (g : Z ⟶ Y) (h : W ⟶ Z) (q : W ⟶ Y) (e : h ≫ g = q)
    (τ : (F.map (g ≫ x₁).op.toLoc).toFunctor.obj A ⟶ (F.map (g ≫ x₂).op.toLoc).toFunctor.obj B) :
    (F.map h.op.toLoc).toFunctor.map
      ((F.mapComp' x₁.op.toLoc g.op.toLoc (g ≫ x₁).op.toLoc rfl).inv.toNatTrans.app A ≫ τ ≫
        (F.mapComp' x₂.op.toLoc g.op.toLoc (g ≫ x₂).op.toLoc rfl).hom.toNatTrans.app B) =
    (F.mapComp' g.op.toLoc h.op.toLoc q.op.toLoc (toLoc_comp e)).inv.toNatTrans.app _ ≫
      (F.mapComp' x₁.op.toLoc q.op.toLoc (q ≫ x₁).op.toLoc rfl).inv.toNatTrans.app A ≫
      pullHom τ h (q ≫ x₁) (q ≫ x₂) (by rw [← e]; simp) (by rw [← e]; simp) ≫
      (F.mapComp' x₂.op.toLoc q.op.toLoc (q ≫ x₂).op.toLoc rfl).hom.toNatTrans.app B ≫
      (F.mapComp' g.op.toLoc h.op.toLoc q.op.toLoc (toLoc_comp e)).hom.toNatTrans.app _ := by
  subst e
  rw [Functor.map_comp, Functor.map_comp,
    map_eq_pullHom τ h ((h ≫ g) ≫ x₁) ((h ≫ g) ≫ x₂) (by simp) (by simp)]
  simp only [Category.assoc]
  rw [reassoc_of% (map_mapComp'_inv_comp_mapComp'_inv x₁ g h (g ≫ x₁) (h ≫ g) ((h ≫ g) ≫ x₁)
      rfl rfl (Category.assoc _ _ _).symm A),
    mapComp'_hom_comp_map_mapComp'_hom x₂ g h (g ≫ x₂) (h ≫ g) ((h ≫ g) ≫ x₂)
      rfl rfl (Category.assoc _ _ _).symm B]

end PullHom

section Small

variable (F) in
/-- Small variant of `IsPrestack.of_precoverage`. -/
lemma isPrestack_of_small {K : Precoverage C} [HasPullbacks C] [K.IsStableUnderBaseChange]
    [Precoverage.Small.{w} K]
    (hF : ∀ (S : C) (E : Precoverage.ZeroHypercover.{w} K S), F.IsPrestackFor E.presieve₀) :
    F.IsPrestack K.toGrothendieck where
  isSheaf {S} M N := by
    rw [isSheaf_iff_isSheaf_of_type, over_toGrothendieck_eq_toGrothendieck_comap_forget,
      Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange_of_small.{w}]
    intro X E
    rw [Presieve.isSheafFor_iff_generate]
    apply Pseudofunctor.IsPrestackFor.isSheafFor'
    have := hF _ (E.map (Over.forget S) le_rfl)
    rw [Precoverage.ZeroHypercover.map_toPreZeroHypercover,
      PreZeroHypercover.presieve₀_map] at this
    simpa [Sieve.overEquiv_generate, ← Sieve.arrows_generate_map_eq_functorPushforward]
      using this

end Small

section Glue

variable (J : GrothendieckTopology C) [F.IsPrestack J]
  {Y X₁ X₂ : C} {A : F.obj (.mk (op X₁))} {B : F.obj (.mk (op X₂))} (x₁ : Y ⟶ X₁) (x₂ : Y ⟶ X₂)

/-- The family of all arrows of a sieve. -/
abbrev sieveFamily (T : Sieve Y) : (i : Σ Z : C, {g : Z ⟶ Y // T g}) → i.1 ⟶ Y :=
  fun i ↦ i.2.1

lemma sieveFamily_mem {T : Sieve Y} (hT : T ∈ J Y) :
    Sieve.ofArrows _ (sieveFamily T) ∈ J Y := by
  refine J.superset_covering ?_ hT
  intro Z g hg
  exact ⟨Z, 𝟙 Z, g,
    Presieve.ofArrows.mk (Y := fun i : Σ Z : C, {g : Z ⟶ Y // T g} ↦ i.1) ⟨Z, g, hg⟩,
    Category.id_comp g⟩

include J in
/-- Morphisms between pullbacks are determined by their pullbacks along the arrows of a
covering sieve. -/
lemma hom_ext_of_sieve {T : Sieve Y} (hT : T ∈ J Y)
    {ψ ψ' : (F.map x₁.op.toLoc).toFunctor.obj A ⟶ (F.map x₂.op.toLoc).toFunctor.obj B}
    (h : ∀ ⦃Z : C⦄ (g : Z ⟶ Y), T g →
      pullHom ψ g (g ≫ x₁) (g ≫ x₂) = pullHom ψ' g (g ≫ x₁) (g ≫ x₂)) : ψ = ψ' := by
  have hF := F.fullyFaithfulToDescentData (J := J) (sieveFamily T) (sieveFamily_mem J hT)
  apply hF.map_injective
  ext i
  obtain ⟨Z, g, hg⟩ := i
  change (F.map g.op.toLoc).toFunctor.map ψ = (F.map g.op.toLoc).toFunctor.map ψ'
  rw [map_eq_pullHom ψ g (g ≫ x₁) (g ≫ x₂) rfl rfl,
    map_eq_pullHom ψ' g (g ≫ x₁) (g ≫ x₂) rfl rfl, h g hg]

include J in
/-- Compatible pullbacks along the arrows of a covering sieve glue to a morphism. -/
lemma exists_glue {T : Sieve Y} (hT : T ∈ J Y)
    (σ : ∀ ⦃Z : C⦄ (g : Z ⟶ Y), T g →
      ((F.map (g ≫ x₁).op.toLoc).toFunctor.obj A ⟶ (F.map (g ≫ x₂).op.toLoc).toFunctor.obj B))
    (hσ : ∀ ⦃Z Z' : C⦄ (g : Z ⟶ Y) (hg : T g) (h : Z' ⟶ Z),
      pullHom (σ g hg) h ((h ≫ g) ≫ x₁) ((h ≫ g) ≫ x₂) (by simp) (by simp) =
        σ (h ≫ g) (T.downward_closed hg h)) :
    ∃ ψ : (F.map x₁.op.toLoc).toFunctor.obj A ⟶ (F.map x₂.op.toLoc).toFunctor.obj B,
      ∀ ⦃Z : C⦄ (g : Z ⟶ Y) (hg : T g), pullHom ψ g (g ≫ x₁) (g ≫ x₂) = σ g hg := by
  have hF := F.fullyFaithfulToDescentData (J := J) (sieveFamily T) (sieveFamily_mem J hT)
  let φ : (F.toDescentData (sieveFamily T)).obj ((F.map x₁.op.toLoc).toFunctor.obj A) ⟶
      (F.toDescentData (sieveFamily T)).obj ((F.map x₂.op.toLoc).toFunctor.obj B) :=
    { hom i := (F.mapComp' x₁.op.toLoc i.2.1.op.toLoc (i.2.1 ≫ x₁).op.toLoc rfl).inv.toNatTrans.app A ≫
        σ i.2.1 i.2.2 ≫
        (F.mapComp' x₂.op.toLoc i.2.1.op.toLoc (i.2.1 ≫ x₂).op.toLoc rfl).hom.toNatTrans.app B
      comm := by
        rintro W q ⟨Z₁, g₁, hg₁⟩ ⟨Z₂, g₂, hg₂⟩ h₁ h₂ hq₁ hq₂
        have hσ' : ∀ ⦃Z : C⦄ (g : Z ⟶ Y) (hg : T g) (h : W ⟶ Z) (e : h ≫ g = q),
            pullHom (σ g hg) h (q ≫ x₁) (q ≫ x₂) (by rw [← e]; simp) (by rw [← e]; simp) =
              σ q (e ▸ T.downward_closed hg h) := by
          intro Z g hg h e
          subst e
          exact hσ g hg h
        rw [map_conj x₁ x₂ g₁ h₁ q hq₁, map_conj x₁ x₂ g₂ h₂ q hq₂, hσ' g₁ hg₁ h₁ hq₁,
          hσ' g₂ hg₂ h₂ hq₂]
        erw [Pseudofunctor.DescentData.ofObj_hom, Pseudofunctor.DescentData.ofObj_hom]
        simp }
  refine ⟨hF.preimage φ, fun Z g hg ↦ ?_⟩
  have := congrArg (fun φ ↦ φ.hom ⟨Z, g, hg⟩) (hF.map_preimage φ)
  change (F.map g.op.toLoc).toFunctor.map (hF.preimage φ) = _ at this
  rw [map_eq_pullHom (hF.preimage φ) g (g ≫ x₁) (g ≫ x₂) rfl rfl] at this
  simpa [φ, cancel_epi, cancel_mono] using this

end Glue

section Composite

variable {S : C} {ι : Type t} {U : ι → C} {r : ∀ i, U i ⟶ S}
  {κ : ι → Type t'} {V : ∀ i, κ i → C} {s : ∀ i k, V i k ⟶ U i}

/-- The composite family `s i k ≫ r i`, indexed by pairs `⟨i, k⟩`. -/
abbrev compFamily (r : ∀ i, U i ⟶ S) (s : ∀ i k, V i k ⟶ U i) (x : Σ i, κ i) :
    V x.1 x.2 ⟶ S :=
  s x.1 x.2 ≫ r x.1

lemma hom_congr {ι : Type*} {X : ι → C} {f : ∀ i, X i ⟶ S} (D : F.DescentData f) {Y : C}
    {q q' : Y ⟶ S} (hq : q = q') {i₁ i₂ : ι} (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
    D.hom q f₁ f₂ hf₁ hf₂ = D.hom q' f₁ f₂ (hf₁.trans hq) (hf₂.trans hq) := by
  subst hq
  rfl

lemma hom_congr' (D : F.DescentData (compFamily r s)) {Z : C} {q q' : Z ⟶ S} (hq : q = q')
    {i₁ i₂ : ι} {k₁ : κ i₁} {k₂ : κ i₂} (f₁ : Z ⟶ V i₁ k₁) (f₂ : Z ⟶ V i₂ k₂)
    (hf₁ : f₁ ≫ compFamily r s ⟨i₁, k₁⟩ = q) (hf₂ : f₂ ≫ compFamily r s ⟨i₂, k₂⟩ = q) :
    D.hom q (i₁ := ⟨i₁, k₁⟩) (i₂ := ⟨i₂, k₂⟩) f₁ f₂ hf₁ hf₂ =
      D.hom q' (i₁ := ⟨i₁, k₁⟩) (i₂ := ⟨i₂, k₂⟩) f₁ f₂ (hf₁.trans hq) (hf₂.trans hq) := by
  subst hq
  rfl

/-- Restriction of descent data relative to the composite family to the family `s i`. -/
def restrict (D : F.DescentData (compFamily r s)) (i : ι) : F.DescentData (s i) where
  obj k := D.obj ⟨i, k⟩
  hom Y q k₁ k₂ f₁ f₂ hf₁ hf₂ := D.hom (q ≫ r i) (i₁ := ⟨i, k₁⟩) (i₂ := ⟨i, k₂⟩) f₁ f₂
    (by rw [← hf₁, Category.assoc]) (by rw [← hf₂, Category.assoc])
  pullHom_hom Y' Y g q q' hq k₁ k₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ :=
    D.pullHom_hom g (q ≫ r i) (q' ≫ r i) (by rw [← hq, Category.assoc])
      (i₁ := ⟨i, k₁⟩) (i₂ := ⟨i, k₂⟩) f₁ f₂ (by rw [← hf₁, Category.assoc])
      (by rw [← hf₂, Category.assoc]) gf₁ gf₂ hgf₁ hgf₂
  hom_self Y q k g hg := D.hom_self _ (i := ⟨i, k⟩) g (by rw [← hg, Category.assoc])
  hom_comp Y q k₁ k₂ k₃ f₁ f₂ f₃ hf₁ hf₂ hf₃ :=
    D.hom_comp _ (i₁ := ⟨i, k₁⟩) (i₂ := ⟨i, k₂⟩) (i₃ := ⟨i, k₃⟩) f₁ f₂ f₃
      (by rw [← hf₁, Category.assoc]) (by rw [← hf₂, Category.assoc])
      (by rw [← hf₃, Category.assoc])

/-- The components of an isomorphism to a restriction, with their actual types. -/
def eHom {D : F.DescentData (compFamily r s)} {i : ι} {M : F.obj (.mk (op (U i)))}
    (e : (F.toDescentData (s i)).obj M ≅ restrict D i) (k : κ i) :
    (F.map (s i k).op.toLoc).toFunctor.obj M ⟶ D.obj ⟨i, k⟩ :=
  e.hom.hom k

/-- The inverse components of an isomorphism to a restriction. -/
def eInv {D : F.DescentData (compFamily r s)} {i : ι} {M : F.obj (.mk (op (U i)))}
    (e : (F.toDescentData (s i)).obj M ≅ restrict D i) (k : κ i) :
    D.obj ⟨i, k⟩ ⟶ (F.map (s i k).op.toLoc).toFunctor.obj M :=
  e.inv.hom k

@[reassoc (attr := simp)]
lemma eHom_eInv {D : F.DescentData (compFamily r s)} {i : ι} {M : F.obj (.mk (op (U i)))}
    (e : (F.toDescentData (s i)).obj M ≅ restrict D i) (k : κ i) :
    eHom e k ≫ eInv e k = 𝟙 _ := by
  simp only [eHom, eInv, ← Pseudofunctor.DescentData.comp_hom, Iso.hom_inv_id]
  rfl

@[reassoc (attr := simp)]
lemma eInv_eHom {D : F.DescentData (compFamily r s)} {i : ι} {M : F.obj (.mk (op (U i)))}
    (e : (F.toDescentData (s i)).obj M ≅ restrict D i) (k : κ i) :
    eInv e k ≫ eHom e k = 𝟙 _ := by
  simp only [eHom, eInv, ← Pseudofunctor.DescentData.comp_hom, Iso.inv_hom_id]
  rfl

variable (D : F.DescentData (compFamily r s)) {M : ∀ i, F.obj (.mk (op (U i)))}
  (e : ∀ i, (F.toDescentData (s i)).obj (M i) ≅ restrict D i)
include e

/-- The comparison `x^* M_i ⟶ a^* D_{i,k}` for a factorization `a ≫ s i k = x`. -/
def β {i : ι} {Z : C} (x : Z ⟶ U i) {k : κ i} (a : Z ⟶ V i k) (ha : a ≫ s i k = x) :
    (F.map x.op.toLoc).toFunctor.obj (M i) ⟶ (F.map a.op.toLoc).toFunctor.obj (D.obj ⟨i, k⟩) :=
  (F.mapComp' (s i k).op.toLoc a.op.toLoc x.op.toLoc (toLoc_comp ha)).hom.toNatTrans.app (M i) ≫
    (F.map a.op.toLoc).toFunctor.map (eHom (e i) k)

/-- The inverse comparison `a^* D_{i,k} ⟶ x^* M_i`. -/
def β' {i : ι} {Z : C} (x : Z ⟶ U i) {k : κ i} (a : Z ⟶ V i k) (ha : a ≫ s i k = x) :
    (F.map a.op.toLoc).toFunctor.obj (D.obj ⟨i, k⟩) ⟶ (F.map x.op.toLoc).toFunctor.obj (M i) :=
  (F.map a.op.toLoc).toFunctor.map (eInv (e i) k) ≫
    (F.mapComp' (s i k).op.toLoc a.op.toLoc x.op.toLoc (toLoc_comp ha)).inv.toNatTrans.app (M i)

@[reassoc (attr := simp)]
lemma β_β' {i : ι} {Z : C} (x : Z ⟶ U i) {k : κ i} (a : Z ⟶ V i k) (ha : a ≫ s i k = x) :
    β D e x a ha ≫ β' D e x a ha = 𝟙 _ := by
  simp [β, β', ← Functor.map_comp_assoc]

@[reassoc (attr := simp)]
lemma β'_β {i : ι} {Z : C} (x : Z ⟶ U i) {k : κ i} (a : Z ⟶ V i k) (ha : a ≫ s i k = x) :
    β' D e x a ha ≫ β D e x a ha = 𝟙 _ := by
  simp [β, β', ← Functor.map_comp]

instance {i : ι} {Z : C} (x : Z ⟶ U i) {k : κ i} (a : Z ⟶ V i k) (ha : a ≫ s i k = x) :
    IsIso (β D e x a ha) :=
  ⟨⟨β' D e x a ha, β_β' D e x a ha, β'_β D e x a ha⟩⟩

lemma β_comp_hom {i : ι} {Z : C} (x : Z ⟶ U i) {k k' : κ i} (a : Z ⟶ V i k)
    (a' : Z ⟶ V i k') (ha : a ≫ s i k = x) (ha' : a' ≫ s i k' = x) :
    β D e x a ha ≫ D.hom (x ≫ r i) (i₁ := ⟨i, k⟩) (i₂ := ⟨i, k'⟩) a a'
        (by rw [← ha, Category.assoc]) (by rw [← ha', Category.assoc]) =
      β D e x a' ha' := by
  have h : (F.map a.op.toLoc).toFunctor.map (eHom (e i) k) ≫
      D.hom (x ≫ r i) (i₁ := ⟨i, k⟩) (i₂ := ⟨i, k'⟩) a a'
        (by rw [← ha, Category.assoc]) (by rw [← ha', Category.assoc]) =
      (F.mapComp' (s i k).op.toLoc a.op.toLoc x.op.toLoc (toLoc_comp ha)).inv.toNatTrans.app
          (M i) ≫
        (F.mapComp' (s i k').op.toLoc a'.op.toLoc x.op.toLoc (toLoc_comp ha')).hom.toNatTrans.app
          (M i) ≫ (F.map a'.op.toLoc).toFunctor.map (eHom (e i) k') := by
    have := (e i).hom.comm x a a' ha ha'
    erw [Pseudofunctor.DescentData.ofObj_hom] at this
    rw [Category.assoc] at this
    exact this
  simp only [β, Category.assoc, h]
  simp

lemma hom_comp_β' {i : ι} {Z : C} (x : Z ⟶ U i) {k k' : κ i} (a : Z ⟶ V i k)
    (a' : Z ⟶ V i k') (ha : a ≫ s i k = x) (ha' : a' ≫ s i k' = x) :
    D.hom (x ≫ r i) (i₁ := ⟨i, k'⟩) (i₂ := ⟨i, k⟩) a' a
        (by rw [← ha', Category.assoc]) (by rw [← ha, Category.assoc]) ≫ β' D e x a ha =
      β' D e x a' ha' := by
  rw [← cancel_epi (β D e x a' ha'), reassoc_of% (β_comp_hom D e x a' a ha' ha)]
  simp

lemma pullHom_β {i : ι} {Z : C} (x : Z ⟶ U i) {k : κ i} (a : Z ⟶ V i k) (ha : a ≫ s i k = x)
    {Z' : C} (h : Z' ⟶ Z) (y : Z' ⟶ U i) (b : Z' ⟶ V i k) (hy : h ≫ x = y) (hb : h ≫ a = b) :
    pullHom (β D e x a ha) h y b hy hb =
      β D e y b (by rw [← hy, ← hb, Category.assoc, ha]) := by
  subst hy hb
  simp only [pullHom, β, Functor.map_comp, Category.assoc]
  rw [reassoc_of% (mapComp'_hom_comp_map_mapComp'_hom (s i k) a h x (h ≫ a) (h ≫ x)
    ha rfl rfl (M i))]
  rw [F.mapComp'_naturality_2]

lemma pullHom_β' {i : ι} {Z : C} (x : Z ⟶ U i) {k : κ i} (a : Z ⟶ V i k) (ha : a ≫ s i k = x)
    {Z' : C} (h : Z' ⟶ Z) (y : Z' ⟶ U i) (b : Z' ⟶ V i k) (hy : h ≫ x = y) (hb : h ≫ a = b) :
    pullHom (β' D e x a ha) h b y hb hy =
      β' D e y b (by rw [← hy, ← hb, Category.assoc, ha]) := by
  subst hy hb
  simp only [pullHom, β', Functor.map_comp, Category.assoc]
  rw [map_mapComp'_inv_comp_mapComp'_inv (s i k) a h x (h ≫ a) (h ≫ x) ha rfl rfl (M i)]
  rw [← Category.assoc, ← Category.assoc, Category.assoc _ _
    ((F.mapComp' a.op.toLoc h.op.toLoc (h ≫ a).op.toLoc _).inv.toNatTrans.app _),
    F.mapComp'_naturality_2]

/-- The local sections used to glue the descent isomorphisms over `r`. -/
def Φ {i₁ i₂ : ι} {Z : C} (y₁ : Z ⟶ U i₁) {k₁ : κ i₁} (a₁ : Z ⟶ V i₁ k₁)
    (ha₁ : a₁ ≫ s i₁ k₁ = y₁) (y₂ : Z ⟶ U i₂) {k₂ : κ i₂} (a₂ : Z ⟶ V i₂ k₂)
    (ha₂ : a₂ ≫ s i₂ k₂ = y₂) (hy : y₂ ≫ r i₂ = y₁ ≫ r i₁) :
    (F.map y₁.op.toLoc).toFunctor.obj (M i₁) ⟶ (F.map y₂.op.toLoc).toFunctor.obj (M i₂) :=
  β D e y₁ a₁ ha₁ ≫
    D.hom (y₁ ≫ r i₁) (i₁ := ⟨i₁, k₁⟩) (i₂ := ⟨i₂, k₂⟩) a₁ a₂ (by rw [← ha₁, Category.assoc])
      (by rw [← hy, ← ha₂, Category.assoc]) ≫
    β' D e y₂ a₂ ha₂

lemma Φ_indep {i₁ i₂ : ι} {Z : C} (y₁ : Z ⟶ U i₁) {k₁ k₁' : κ i₁} (a₁ : Z ⟶ V i₁ k₁)
    (a₁' : Z ⟶ V i₁ k₁') (ha₁ : a₁ ≫ s i₁ k₁ = y₁) (ha₁' : a₁' ≫ s i₁ k₁' = y₁)
    (y₂ : Z ⟶ U i₂) {k₂ k₂' : κ i₂} (a₂ : Z ⟶ V i₂ k₂) (a₂' : Z ⟶ V i₂ k₂')
    (ha₂ : a₂ ≫ s i₂ k₂ = y₂) (ha₂' : a₂' ≫ s i₂ k₂' = y₂) (hy : y₂ ≫ r i₂ = y₁ ≫ r i₁) :
    Φ D e y₁ a₁ ha₁ y₂ a₂ ha₂ hy = Φ D e y₁ a₁' ha₁' y₂ a₂' ha₂' hy := by
  simp only [Φ]
  rw [← β_comp_hom D e y₁ a₁ a₁' ha₁ ha₁', ← hom_comp_β' D e y₂ a₂ a₂' ha₂ ha₂',
    hom_congr' D hy a₂' a₂]
  simp

lemma pullHom_Φ {i₁ i₂ : ι} {Z : C} (y₁ : Z ⟶ U i₁) {k₁ : κ i₁} (a₁ : Z ⟶ V i₁ k₁)
    (ha₁ : a₁ ≫ s i₁ k₁ = y₁) (y₂ : Z ⟶ U i₂) {k₂ : κ i₂} (a₂ : Z ⟶ V i₂ k₂)
    (ha₂ : a₂ ≫ s i₂ k₂ = y₂) (hy : y₂ ≫ r i₂ = y₁ ≫ r i₁) {Z' : C} (h : Z' ⟶ Z)
    (z₁ : Z' ⟶ U i₁) (z₂ : Z' ⟶ U i₂) (hz₁ : h ≫ y₁ = z₁) (hz₂ : h ≫ y₂ = z₂) :
    pullHom (Φ D e y₁ a₁ ha₁ y₂ a₂ ha₂ hy) h z₁ z₂ hz₁ hz₂ =
      Φ D e z₁ (h ≫ a₁) (by rw [Category.assoc, ha₁, hz₁]) z₂ (h ≫ a₂)
        (by rw [Category.assoc, ha₂, hz₂]) (by rw [← hz₁, ← hz₂, Category.assoc, hy,
          Category.assoc]) := by
  simp only [Φ]
  rw [pullHom_comp _ _ h z₁ (h ≫ a₁) z₂ hz₁ rfl hz₂,
    pullHom_comp _ _ h (h ≫ a₁) (h ≫ a₂) z₂ rfl rfl hz₂,
    pullHom_β D e y₁ a₁ ha₁ h z₁ (h ≫ a₁) hz₁ rfl,
    pullHom_β' D e y₂ a₂ ha₂ h z₂ (h ≫ a₂) hz₂ rfl,
    D.pullHom_hom h (y₁ ≫ r i₁) (z₁ ≫ r i₁) (by rw [← hz₁, Category.assoc])
      (i₁ := ⟨i₁, k₁⟩) (i₂ := ⟨i₂, k₂⟩) a₁ a₂ (by rw [← ha₁, Category.assoc])
      (by rw [← hy, ← ha₂, Category.assoc]) (h ≫ a₁) (h ≫ a₂) rfl rfl]

lemma Φ_self {i : ι} {Z : C} (y : Z ⟶ U i) {k k' : κ i} (a : Z ⟶ V i k) (a' : Z ⟶ V i k')
    (ha : a ≫ s i k = y) (ha' : a' ≫ s i k' = y) :
    Φ D e y a ha y a' ha' rfl = 𝟙 _ := by
  rw [Φ_indep D e y a a ha ha y a' a ha' ha rfl]
  simp only [Φ]
  rw [D.hom_self (y ≫ r i) (i := ⟨i, k⟩) a (by rw [← ha, Category.assoc])]
  simp

lemma Φ_comp {i₁ i₂ i₃ : ι} {Z : C} (y₁ : Z ⟶ U i₁) {k₁ : κ i₁} (a₁ : Z ⟶ V i₁ k₁)
    (ha₁ : a₁ ≫ s i₁ k₁ = y₁) (y₂ : Z ⟶ U i₂) {k₂ : κ i₂} (a₂ : Z ⟶ V i₂ k₂)
    (ha₂ : a₂ ≫ s i₂ k₂ = y₂) (y₃ : Z ⟶ U i₃) {k₃ : κ i₃} (a₃ : Z ⟶ V i₃ k₃)
    (ha₃ : a₃ ≫ s i₃ k₃ = y₃) (hy₁₂ : y₂ ≫ r i₂ = y₁ ≫ r i₁)
    (hy₂₃ : y₃ ≫ r i₃ = y₂ ≫ r i₂) :
    Φ D e y₁ a₁ ha₁ y₂ a₂ ha₂ hy₁₂ ≫ Φ D e y₂ a₂ ha₂ y₃ a₃ ha₃ hy₂₃ =
      Φ D e y₁ a₁ ha₁ y₃ a₃ ha₃ (hy₂₃.trans hy₁₂) := by
  simp only [Φ, Category.assoc, β'_β_assoc]
  rw [hom_congr' D hy₁₂ a₂ a₃]
  simp

end Composite

section Glued

variable {S : C} {ι : Type t} {U : ι → C} {κ : ι → Type t'} {V : ∀ i, κ i → C}
  (s : ∀ i k, V i k ⟶ U i)

/-- The sieve of maps along which two given maps both factor through the families `s`. -/
def sieveT {Y : C} {i₁ i₂ : ι} (f₁ : Y ⟶ U i₁) (f₂ : Y ⟶ U i₂) : Sieve Y :=
  Sieve.pullback f₁ (Sieve.ofArrows _ (s i₁)) ⊓ Sieve.pullback f₂ (Sieve.ofArrows _ (s i₂))

variable {s}

lemma exists_fac {i : ι} {Z : C} {y : Z ⟶ U i} (h : Sieve.ofArrows _ (s i) y) :
    ∃ (k : κ i) (a : Z ⟶ V i k), a ≫ s i k = y := by
  obtain ⟨k, a, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ y).1 h
  exact ⟨k, a, rfl⟩

/-- A chosen index of a factorization through the family `s i`. -/
def idx {i : ι} {Z : C} {y : Z ⟶ U i} (h : Sieve.ofArrows _ (s i) y) : κ i :=
  (exists_fac h).choose

/-- A chosen factorization through the family `s i`. -/
def lift {i : ι} {Z : C} {y : Z ⟶ U i} (h : Sieve.ofArrows _ (s i) y) : Z ⟶ V i (idx h) :=
  (exists_fac h).choose_spec.choose

@[reassoc]
lemma lift_fac {i : ι} {Z : C} {y : Z ⟶ U i} (h : Sieve.ofArrows _ (s i) y) :
    lift h ≫ s i (idx h) = y :=
  (exists_fac h).choose_spec.choose_spec

lemma mem_sieveT {Y Z : C} {i₁ i₂ : ι} {f₁ : Y ⟶ U i₁} {f₂ : Y ⟶ U i₂} (g : Z ⟶ Y)
    {k₁ : κ i₁} (a₁ : Z ⟶ V i₁ k₁) (ha₁ : a₁ ≫ s i₁ k₁ = g ≫ f₁) {k₂ : κ i₂}
    (a₂ : Z ⟶ V i₂ k₂) (ha₂ : a₂ ≫ s i₂ k₂ = g ≫ f₂) : sieveT s f₁ f₂ g :=
  ⟨(Sieve.mem_ofArrows_iff _ _ _).2 ⟨k₁, a₁, ha₁.symm⟩,
    (Sieve.mem_ofArrows_iff _ _ _).2 ⟨k₂, a₂, ha₂.symm⟩⟩

variable (J : GrothendieckTopology C) [F.IsPrestack J]
  (hs : ∀ i, Sieve.ofArrows _ (s i) ∈ J (U i)) {r : ∀ i, U i ⟶ S}
  (D : F.DescentData (compFamily r s)) {M : ∀ i, F.obj (.mk (op (U i)))}
  (e : ∀ i, (F.toDescentData (s i)).obj (M i) ≅ restrict D i)

include hs in
lemma sieveT_mem {Y : C} {i₁ i₂ : ι} (f₁ : Y ⟶ U i₁) (f₂ : Y ⟶ U i₂) :
    sieveT s f₁ f₂ ∈ J Y :=
  J.intersection_covering (J.pullback_stable f₁ (hs i₁)) (J.pullback_stable f₂ (hs i₂))

/-- The local sections whose gluing is the descent isomorphism over `r`. -/
def σ {Y : C} {i₁ i₂ : ι} (f₁ : Y ⟶ U i₁) (f₂ : Y ⟶ U i₂) (hf : f₂ ≫ r i₂ = f₁ ≫ r i₁)
    ⦃Z : C⦄ (g : Z ⟶ Y) (hg : sieveT s f₁ f₂ g) :
    (F.map (g ≫ f₁).op.toLoc).toFunctor.obj (M i₁) ⟶
      (F.map (g ≫ f₂).op.toLoc).toFunctor.obj (M i₂) :=
  Φ D e (g ≫ f₁) (lift hg.1) (lift_fac hg.1) (g ≫ f₂) (lift hg.2) (lift_fac hg.2)
    (by rw [Category.assoc, hf, Category.assoc])

lemma σ_eq {Y : C} {i₁ i₂ : ι} (f₁ : Y ⟶ U i₁) (f₂ : Y ⟶ U i₂) (hf : f₂ ≫ r i₂ = f₁ ≫ r i₁)
    ⦃Z : C⦄ (g : Z ⟶ Y) (hg : sieveT s f₁ f₂ g) {k₁ : κ i₁} (a₁ : Z ⟶ V i₁ k₁)
    (ha₁ : a₁ ≫ s i₁ k₁ = g ≫ f₁) {k₂ : κ i₂} (a₂ : Z ⟶ V i₂ k₂)
    (ha₂ : a₂ ≫ s i₂ k₂ = g ≫ f₂) :
    σ D e f₁ f₂ hf g hg = Φ D e (g ≫ f₁) a₁ ha₁ (g ≫ f₂) a₂ ha₂
      (by rw [Category.assoc, hf, Category.assoc]) :=
  Φ_indep _ _ _ _ _ _ _ _ _ _ _ _ _

lemma σ_compat {Y : C} {i₁ i₂ : ι} (f₁ : Y ⟶ U i₁) (f₂ : Y ⟶ U i₂)
    (hf : f₂ ≫ r i₂ = f₁ ≫ r i₁) ⦃Z Z' : C⦄ (g : Z ⟶ Y) (hg : sieveT s f₁ f₂ g) (h : Z' ⟶ Z) :
    pullHom (σ D e f₁ f₂ hf g hg) h ((h ≫ g) ≫ f₁) ((h ≫ g) ≫ f₂) (by simp) (by simp) =
      σ D e f₁ f₂ hf (h ≫ g) ((sieveT s f₁ f₂).downward_closed hg h) := by
  rw [σ, pullHom_Φ]
  exact Φ_indep _ _ _ _ _ _ _ _ _ _ _ _ _

/-- The glued descent morphism over `r`. -/
def ehom {Y : C} (q : Y ⟶ S) {i₁ i₂ : ι} (f₁ : Y ⟶ U i₁) (f₂ : Y ⟶ U i₂)
    (hf₁ : f₁ ≫ r i₁ = q) (hf₂ : f₂ ≫ r i₂ = q) :
    (F.map f₁.op.toLoc).toFunctor.obj (M i₁) ⟶ (F.map f₂.op.toLoc).toFunctor.obj (M i₂) :=
  (exists_glue J f₁ f₂ (sieveT_mem J hs f₁ f₂) (σ D e f₁ f₂ (hf₂.trans hf₁.symm))
    (σ_compat D e f₁ f₂ (hf₂.trans hf₁.symm))).choose

lemma pullHom_ehom {Y : C} (q : Y ⟶ S) {i₁ i₂ : ι} (f₁ : Y ⟶ U i₁) (f₂ : Y ⟶ U i₂)
    (hf₁ : f₁ ≫ r i₁ = q) (hf₂ : f₂ ≫ r i₂ = q) {Z : C} (g : Z ⟶ Y) (y₁ : Z ⟶ U i₁)
    (y₂ : Z ⟶ U i₂) (hy₁ : g ≫ f₁ = y₁) (hy₂ : g ≫ f₂ = y₂) {k₁ : κ i₁} (a₁ : Z ⟶ V i₁ k₁)
    (ha₁ : a₁ ≫ s i₁ k₁ = y₁) {k₂ : κ i₂} (a₂ : Z ⟶ V i₂ k₂) (ha₂ : a₂ ≫ s i₂ k₂ = y₂) :
    pullHom (ehom J hs D e q f₁ f₂ hf₁ hf₂) g y₁ y₂ hy₁ hy₂ =
      Φ D e y₁ a₁ ha₁ y₂ a₂ ha₂ (by rw [← hy₁, ← hy₂, Category.assoc, Category.assoc, hf₁, hf₂]) := by
  subst hy₁ hy₂
  rw [ehom, (exists_glue J f₁ f₂ (sieveT_mem J hs f₁ f₂) (σ D e f₁ f₂ (hf₂.trans hf₁.symm))
    (σ_compat D e f₁ f₂ (hf₂.trans hf₁.symm))).choose_spec g (mem_sieveT g a₁ ha₁ a₂ ha₂)]
  exact σ_eq D e f₁ f₂ _ g _ a₁ ha₁ a₂ ha₂

/-- The descent data over `r` obtained by gluing. -/
def glued : F.DescentData r where
  obj := M
  hom Y q i₁ i₂ f₁ f₂ hf₁ hf₂ := ehom J hs D e q f₁ f₂ hf₁ hf₂
  pullHom_hom Y' Y g q q' hq i₁ i₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ := by
    apply hom_ext_of_sieve J gf₁ gf₂ (sieveT_mem J hs gf₁ gf₂)
    rintro Z g' ⟨h₁, h₂⟩
    obtain ⟨k₁, a₁, ha₁⟩ := exists_fac h₁
    obtain ⟨k₂, a₂, ha₂⟩ := exists_fac h₂
    rw [pullHom_pullHom, pullHom_ehom J hs D e q f₁ f₂ hf₁ hf₂ (g' ≫ g) (g' ≫ gf₁) (g' ≫ gf₂)
      (by rw [Category.assoc, hgf₁]) (by rw [Category.assoc, hgf₂]) a₁ ha₁ a₂ ha₂,
      pullHom_ehom J hs D e q' gf₁ gf₂ _ _ g' (g' ≫ gf₁) (g' ≫ gf₂) rfl rfl a₁ ha₁ a₂ ha₂]
  hom_self Y q i g hg := by
    apply hom_ext_of_sieve J g g (sieveT_mem J hs g g)
    rintro Z g' ⟨h₁, -⟩
    obtain ⟨k, a, ha⟩ := exists_fac h₁
    rw [pullHom_ehom J hs D e q g g hg hg g' (g' ≫ g) (g' ≫ g) rfl rfl a ha a ha, Φ_self,
      pullHom_id_hom]
  hom_comp Y q i₁ i₂ i₃ f₁ f₂ f₃ hf₁ hf₂ hf₃ := by
    apply hom_ext_of_sieve J f₁ f₃ (J.intersection_covering (sieveT_mem J hs f₁ f₂)
      (J.pullback_stable f₃ (hs i₃)))
    rintro Z g ⟨⟨h₁, h₂⟩, h₃⟩
    obtain ⟨k₁, a₁, ha₁⟩ := exists_fac h₁
    obtain ⟨k₂, a₂, ha₂⟩ := exists_fac h₂
    obtain ⟨k₃, a₃, ha₃⟩ := exists_fac h₃
    rw [pullHom_comp _ _ g (g ≫ f₁) (g ≫ f₂) (g ≫ f₃) rfl rfl rfl,
      pullHom_ehom J hs D e q f₁ f₂ hf₁ hf₂ g _ _ rfl rfl a₁ ha₁ a₂ ha₂,
      pullHom_ehom J hs D e q f₂ f₃ hf₂ hf₃ g _ _ rfl rfl a₂ ha₂ a₃ ha₃,
      pullHom_ehom J hs D e q f₁ f₃ hf₁ hf₃ g _ _ rfl rfl a₁ ha₁ a₃ ha₃, Φ_comp]

lemma ehom_eq_Φ {Y : C} (q : Y ⟶ S) {i₁ i₂ : ι} (f₁ : Y ⟶ U i₁) (f₂ : Y ⟶ U i₂)
    (hf₁ : f₁ ≫ r i₁ = q) (hf₂ : f₂ ≫ r i₂ = q) {k₁ : κ i₁} (a₁ : Y ⟶ V i₁ k₁)
    (ha₁ : a₁ ≫ s i₁ k₁ = f₁) {k₂ : κ i₂} (a₂ : Y ⟶ V i₂ k₂) (ha₂ : a₂ ≫ s i₂ k₂ = f₂) :
    ehom J hs D e q f₁ f₂ hf₁ hf₂ = Φ D e f₁ a₁ ha₁ f₂ a₂ ha₂ (hf₂.trans hf₁.symm) := by
  rw [← pullHom_id (ehom J hs D e q f₁ f₂ hf₁ hf₂)]
  exact pullHom_ehom J hs D e q f₁ f₂ hf₁ hf₂ (𝟙 Y) f₁ f₂ (Category.id_comp _)
    (Category.id_comp _) a₁ ha₁ a₂ ha₂

lemma compFamily_w (x : Σ i, κ i) : s x.1 x.2 ≫ r x.1 = compFamily r s x ≫ 𝟙 S :=
  (Category.comp_id _).symm

/-- Pulling the glued descent data back to the composite family recovers `D`. -/
def pullGluedIso :
    (Pseudofunctor.DescentData.pullFunctor F (f := r) (p := 𝟙 S) (f' := compFamily r s) (α := Sigma.fst)
      (p' := fun x ↦ s x.1 x.2) compFamily_w).obj (glued J hs D e) ≅ D :=
  Pseudofunctor.DescentData.isoMk
    (fun x ↦ ⟨eHom (e x.1) x.2, eInv (e x.1) x.2, eHom_eInv _ _, eInv_eHom _ _⟩) (by
      rintro Y q ⟨i₁, k₁⟩ ⟨i₂, k₂⟩ f₁ f₂ hf₁ hf₂
      have hq₁ : (f₁ ≫ s i₁ k₁) ≫ r i₁ = q ≫ 𝟙 S := by
        rw [Category.assoc, Category.comp_id]; exact hf₁
      have hq₂ : (f₂ ≫ s i₂ k₂) ≫ r i₂ = q ≫ 𝟙 S := by
        rw [Category.assoc, Category.comp_id]; exact hf₂
      have h : ((Pseudofunctor.DescentData.pullFunctor F (f := r) (p := 𝟙 S)
          (f' := compFamily r s) (α := Sigma.fst) (p' := fun x ↦ s x.1 x.2)
          compFamily_w).obj (glued J hs D e)).hom q f₁ f₂ hf₁ hf₂ =
          (F.mapComp' (s i₁ k₁).op.toLoc f₁.op.toLoc (f₁ ≫ s i₁ k₁).op.toLoc
            rfl).inv.toNatTrans.app (M i₁) ≫
          ehom J hs D e (q ≫ 𝟙 S) (f₁ ≫ s i₁ k₁) (f₂ ≫ s i₂ k₂) hq₁ hq₂ ≫
          (F.mapComp' (s i₂ k₂).op.toLoc f₂.op.toLoc (f₂ ≫ s i₂ k₂).op.toLoc
            rfl).hom.toNatTrans.app (M i₂) :=
        Pseudofunctor.DescentData.pullFunctorObjHom_eq (compFamily_w (r := r) (s := s))
          (glued J hs D e) q f₁ f₂ (q ≫ 𝟙 S) (f₁ ≫ s i₁ k₁)
          (f₂ ≫ s i₂ k₂) hf₁ hf₂ rfl rfl rfl
      rw [h, ehom_eq_Φ J hs D e _ _ _ hq₁ hq₂ f₁ rfl f₂ rfl,
        hom_congr' D (hf₁.symm.trans (Category.assoc _ _ _).symm) f₁ f₂ hf₁ hf₂]
      simp [Φ, β, β', ← Functor.map_comp])

end Glued

section Main

variable (F) (J : GrothendieckTopology C) [F.IsPrestack J]

/-- **Effective descent along composite families.** Let `F` be a prestack for `J`, let
`r i : U i ⟶ S` be a family of morphisms along which descent is effective, and for each `i`
let `s i k : V i k ⟶ U i` be a covering family along which descent is effective. Then
descent is effective along the composite family `s i k ≫ r i`. -/
theorem essSurj_toDescentData_comp {S : C} {ι : Type t} {U : ι → C} (r : ∀ i, U i ⟶ S)
    {κ : ι → Type t'} {V : ∀ i, κ i → C} (s : ∀ i k, V i k ⟶ U i)
    (hs : ∀ i, Sieve.ofArrows _ (s i) ∈ J (U i))
    (hr' : (F.toDescentData r).EssSurj) (hs' : ∀ i, (F.toDescentData (s i)).EssSurj) :
    (F.toDescentData (fun x : Σ i, κ i ↦ s x.1 x.2 ≫ r x.1)).EssSurj := by
  refine ⟨fun D ↦ ?_⟩
  let M : ∀ i, F.obj (.mk (op (U i))) := fun i ↦
    haveI := hs' i
    (F.toDescentData (s i)).objPreimage (restrict D i)
  let e : ∀ i, (F.toDescentData (s i)).obj (M i) ≅ restrict D i := fun i ↦
    haveI := hs' i
    (F.toDescentData (s i)).objObjPreimageIso (restrict D i)
  let E := glued J hs D e
  let N := (F.toDescentData r).objPreimage E
  let eN : (F.toDescentData r).obj N ≅ E := (F.toDescentData r).objObjPreimageIso E
  let iso₁ := Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso F
      (compFamily_w (r := r) (s := s)) ≪≫
    Functor.isoWhiskerRight (Cat.Hom.toNatIso (F.mapId _)) _ ≪≫ Functor.leftUnitor _
  exact ⟨N, ⟨(iso₁.app N).symm ≪≫
    (Pseudofunctor.DescentData.pullFunctor F (compFamily_w (r := r) (s := s))).mapIso eN ≪≫
      pullGluedIso J hs D e⟩⟩

end Main

end Langlands.StackComposite
