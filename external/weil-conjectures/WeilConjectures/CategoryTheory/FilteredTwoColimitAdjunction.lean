/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.FilteredTwoColimit
public import Mathlib.CategoryTheory.Adjunction.Comma
public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Left adjoints between filtered 2-colimits of categories

Let `c : CategoryCocone C D` and `c' : CategoryCocone C' D'` be cocones of categories on two
directed systems indexed by the same directed preorder `I`, and let `F : D ⥤ D'` be a functor
which is induced by levelwise left adjoints `L i ⊣ R i`, `L i : C i ⥤ C' i`, in the following
sense (`CategoryTheory.CategoryCocone.LevelwiseLeftAdjoint`):

* isomorphisms `α i : L i ⋙ c'.Φ i ≅ c.Φ i ⋙ F` say that `F` restricts to `L i` at stage `i`;
* natural transformations `β h : c.T h ⋙ L j ⟶ L i ⋙ c'.T h` (for `h : i ≤ j`) compare the
  left adjoints with the transition functors, compatibly with `α`, `c.iso` and `c'.iso`;
* the mates `R i ⋙ c.T h ⟶ c'.T h ⋙ R j` of the `β h` are isomorphisms: the right adjoints
  commute with the transition functors.

If `c` and `c'` are filtered 2-colimits, then `F` is a left adjoint
(`CategoryTheory.CategoryCocone.LevelwiseLeftAdjoint.isLeftAdjoint`). Only (Obj) and the
surjectivity half of (Hom) are needed for `c`.

The proof shows that for `y : C' k`, the morphism
`ε : F (c.Φ k (R k y)) ⟶ c'.Φ k (L k (R k y)) ⟶ c'.Φ k y` (given by `α k` and the counit of
`L k ⊣ R k`) is a terminal object of `CostructuredArrow F (c'.Φ k y)`, i.e. that
`f ↦ F.map f ≫ ε` is bijective on morphisms from any `X : D`. Writing `X ≅ c.Φ j x` and
moving to a common stage `n ≥ j, k` (the object `c.Φ k (R k y)` becomes `c.Φ n (R n (T y))`
thanks to the invertibility of the mates), one reduces to source and target at the same stage,
where the bijectivity follows from the adjunctions at the finite stages and the (Hom)
properties of `c` and `c'`. No coherence between the transition functors is used.
-/

@[expose] public section

universe w v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory

open Category

namespace Functor

variable {D : Type u₃} [Category.{v₃} D] {D' : Type u₄} [Category.{v₄} D'] (F : D ⥤ D')

/-- Bijectivity of `f ↦ F.map f ≫ ε` on morphisms `X ⟶ R` is invariant under isomorphisms of
the source `X`, of the object `R` and of the target of `ε`. -/
lemma bijective_map_comp_of_iso {X X' R R' : D} {Y Y' : D'} (σ : X ≅ X') (ρ : R ≅ R')
    (ι : Y' ≅ Y) (ε : F.obj R ⟶ Y) (ε' : F.obj R' ⟶ Y') (hε : ε = F.map ρ.hom ≫ ε' ≫ ι.hom)
    (h : Function.Bijective fun f : X' ⟶ R' ↦ F.map f ≫ ε') :
    Function.Bijective fun f : X ⟶ R ↦ F.map f ≫ ε := by
  have : (fun f : X ⟶ R ↦ F.map f ≫ ε) = (Iso.homCongr (F.mapIso σ.symm) ι) ∘
      (fun f : X' ⟶ R' ↦ F.map f ≫ ε') ∘ (Iso.homCongr σ ρ) := by
    funext f
    simp [hε]
  rw [this]
  exact (Iso.homCongr _ _).bijective.comp (h.comp (Iso.homCongr _ _).bijective)

/-- If `f ↦ F.map f ≫ ε` is bijective on morphisms `X ⟶ R` for every `X`, then `ε` is a terminal
object of the category of costructured arrows `F.obj _ ⟶ Y`. -/
noncomputable def isTerminalCostructuredArrowMkOfBijective {R : D} {Y : D'} (ε : F.obj R ⟶ Y)
    (h : ∀ X : D, Function.Bijective fun f : X ⟶ R ↦ F.map f ≫ ε) :
    Limits.IsTerminal (CostructuredArrow.mk ε) :=
  Limits.IsTerminal.ofUniqueHom
    (fun Z ↦ CostructuredArrow.homMk ((h Z.left).2 Z.hom).choose ((h Z.left).2 Z.hom).choose_spec)
    (fun Z m ↦ by
      ext
      apply (h Z.left).1
      simpa using (CostructuredArrow.w m).trans ((h Z.left).2 Z.hom).choose_spec.symm)

end Functor

namespace CategoryCocone

variable {I : Type w} [Preorder I] {C : I → Type u₁} [∀ i, Category.{v₁} (C i)]
  {C' : I → Type u₂} [∀ i, Category.{v₂} (C' i)] {D : Type u₃} [Category.{v₃} D]
  {D' : Type u₄} [Category.{v₄} D']

/-- A functor `F : D ⥤ D'` between the vertices of two cocones of categories `c` and `c'`,
induced by levelwise left adjoints `L i ⊣ R i` whose right adjoints commute with the transition
functors:

* `α i : L i ⋙ c'.Φ i ≅ c.Φ i ⋙ F` identifies `F` at stage `i` with `L i`;
* `β h : c.T h ⋙ L j ⟶ L i ⋙ c'.T h` compares `L` with the transition functors;
* `comm` is the compatibility of `α i`, `α j`, `β h`, `c.iso h` and `c'.iso h`: the two
  natural transformations `c.T h ⋙ L j ⋙ c'.Φ j ⟶ c.Φ i ⋙ F` obtained by pasting are equal,
  i.e. `α i` is obtained from `α j` by pasting with `β h`, `c.iso h` and `c'.iso h`;
* `isIso_mate` says that the mate `R i ⋙ c.T h ⟶ c'.T h ⋙ R j` of `β h` (under the adjunctions
  `adj i` and `adj j`) is an isomorphism, i.e. the right adjoints commute with the transition
  functors.

The transformations `β h` need not be isomorphisms. -/
structure LevelwiseLeftAdjoint (c : CategoryCocone C D) (c' : CategoryCocone C' D')
    (F : D ⥤ D') where
  /-- The levelwise left adjoints. -/
  L : ∀ i, C i ⥤ C' i
  /-- The levelwise right adjoints. -/
  R : ∀ i, C' i ⥤ C i
  /-- The levelwise adjunctions. -/
  adj : ∀ i, L i ⊣ R i
  /-- The identification of `F` at stage `i` with `L i`. -/
  α : ∀ i, L i ⋙ c'.Φ i ≅ c.Φ i ⋙ F
  /-- The comparison of the left adjoints with the transition functors. -/
  β : ∀ {i j : I} (h : i ≤ j), c.T h ⋙ L j ⟶ L i ⋙ c'.T h
  /-- The compatibility of `α`, `β` and the structure isomorphisms of the cocones. -/
  comm : ∀ {i j : I} (h : i ≤ j) (x : C i),
    (c'.Φ j).map ((β h).app x) ≫ (c'.iso h).hom.app ((L i).obj x) ≫ (α i).hom.app x =
      (α j).hom.app ((c.T h).obj x) ≫ F.map ((c.iso h).hom.app x)
  /-- The mates of the `β h`, comparing the right adjoints with the transition functors, are
  isomorphisms. -/
  isIso_mate : ∀ {i j : I} (h : i ≤ j) (y : C' i),
    IsIso ((mateEquiv (adj i) (adj j) (β h)).app y)

namespace LevelwiseLeftAdjoint

variable {c : CategoryCocone C D} {c' : CategoryCocone C' D'} {F : D ⥤ D'}

/-- A `LevelwiseLeftAdjoint` from isomorphisms `γ h : L i ⋙ c'.T h ≅ c.T h ⋙ L j` (taking
`β h = (γ h).inv`), with the compatibility in the form
`α i = (c'.iso h)⁻¹ ≫ c'.Φ j (γ h) ≫ α j ≫ F (c.iso h)`. -/
def ofIso (L : ∀ i, C i ⥤ C' i) (R : ∀ i, C' i ⥤ C i) (adj : ∀ i, L i ⊣ R i)
    (α : ∀ i, L i ⋙ c'.Φ i ≅ c.Φ i ⋙ F)
    (γ : ∀ {i j : I} (h : i ≤ j), L i ⋙ c'.T h ≅ c.T h ⋙ L j)
    (hcocycle : ∀ {i j : I} (h : i ≤ j) (x : C i),
      (α i).hom.app x = (c'.iso h).inv.app ((L i).obj x) ≫ (c'.Φ j).map ((γ h).hom.app x) ≫
        (α j).hom.app ((c.T h).obj x) ≫ F.map ((c.iso h).hom.app x))
    (hmate : ∀ {i j : I} (h : i ≤ j),
      IsIso (mateEquiv (adj i) (adj j) (TwoSquare.mk _ _ _ _ (γ h).inv))) :
    LevelwiseLeftAdjoint c c' F where
  L := L
  R := R
  adj := adj
  α := α
  β h := (γ h).inv
  comm h x := by
    rw [hcocycle h x, Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app,
      Functor.map_id, Category.id_comp]
  isIso_mate h y := by
    have := hmate h
    exact NatIso.isIso_app_of_isIso _ y

variable (A : LevelwiseLeftAdjoint c c' F)

/-- The mate `R i ⋙ c.T h ⟶ c'.T h ⋙ R j` of `β h`. -/
abbrev mate {i j : I} (h : i ≤ j) : A.R i ⋙ c.T h ⟶ c'.T h ⋙ A.R j :=
  mateEquiv (A.adj i) (A.adj j) (A.β h)

/-- The components of the mates of the `β h` are isomorphisms. -/
instance {i j : I} (h : i ≤ j) (y : C' i) : IsIso ((A.mate h).app y) := A.isIso_mate h y

/-- The compatibility `comm`, rewritten with the inverses of the isomorphisms. -/
@[reassoc]
lemma map_inv_comp_inv_comp_map {i j : I} (h : i ≤ j) (x : C i) :
    F.map ((c.iso h).inv.app x) ≫ (A.α j).inv.app ((c.T h).obj x) ≫
        (c'.Φ j).map ((A.β h).app x) =
      (A.α i).inv.app x ≫ (c'.iso h).inv.app ((A.L i).obj x) := by
  rw [← cancel_mono ((c'.iso h).hom.app _), ← cancel_mono ((A.α i).hom.app x)]
  simp only [assoc, A.comm, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app, comp_id,
    ← F.map_comp, Functor.comp_obj]
  simp

/-- The candidate counit at stage `k`: the morphism `F (c.Φ k (R k y)) ⟶ c'.Φ k y` given by `α k`
and the counit of `L k ⊣ R k`. -/
def counitObj (k : I) (y : C' k) : F.obj ((c.Φ k).obj ((A.R k).obj y)) ⟶ (c'.Φ k).obj y :=
  (A.α k).inv.app _ ≫ (c'.Φ k).map ((A.adj k).counit.app y)

/-- Composing the image of a morphism `g : x ⟶ R k y` of stage `k` with the candidate counit
gives the image of the transpose of `g`. -/
@[reassoc]
lemma map_map_comp_counitObj {k : I} {x : C k} {y : C' k} (g : x ⟶ (A.R k).obj y) :
    F.map ((c.Φ k).map g) ≫ A.counitObj k y =
      (A.α k).inv.app x ≫ (c'.Φ k).map ((A.L k).map g ≫ (A.adj k).counit.app y) := by
  rw [counitObj, ← Functor.comp_map, (A.α k).inv.naturality_assoc, Functor.comp_map,
    Functor.map_comp]

/-- The transpose of the transition of `g : x ⟶ R k y` followed by the mate is `β` followed by
the transition of the transpose of `g`. -/
lemma map_map_mate_comp_counit {k n : I} (h : k ≤ n) {x : C k} {y : C' k}
    (g : x ⟶ (A.R k).obj y) :
    (A.L n).map ((c.T h).map g ≫ (A.mate h).app y) ≫ (A.adj n).counit.app _ =
      (A.β h).app x ≫ (c'.T h).map ((A.L k).map g ≫ (A.adj k).counit.app y) := by
  rw [Functor.map_comp, assoc, mateEquiv_counit, ← Functor.comp_map,
    (A.β h).naturality_assoc, Functor.map_comp]
  rfl

/-- The candidate counits at stages `k ≤ n` are compatible. -/
lemma map_hom_comp_counitObj {k n : I} (h : k ≤ n) (y : C' k) :
    F.map ((c.iso h).hom.app ((A.R k).obj y)) ≫ A.counitObj k y =
      F.map ((c.Φ n).map ((A.mate h).app y)) ≫ A.counitObj n ((c'.T h).obj y) ≫
        (c'.iso h).hom.app y := by
  have key := A.map_map_mate_comp_counit h (𝟙 ((A.R k).obj y))
  simp only [Functor.map_id, id_comp] at key
  rw [← cancel_epi (F.map ((c.iso h).inv.app _)), map_map_comp_counitObj_assoc, key,
    Functor.map_comp, assoc]
  dsimp only [Functor.comp_obj]
  rw [map_inv_comp_inv_comp_map_assoc]
  have := NatIso.naturality_1 (c'.iso h) ((A.adj k).counit.app y)
  rw [Functor.comp_map] at this
  simp only [counitObj, ← F.map_comp_assoc, Iso.inv_hom_id_app, F.map_id, id_comp]
  exact congrArg _ this.symm

/-- Change of stage for `f ↦ F.map f ≫ ε`: a morphism `c.Φ k x ⟶ c.Φ k (R k y)` written at
stage `n ≥ k` through the structure isomorphisms. -/
lemma map_comp_counitObj_eq {k n : I} (h : k ≤ n) {x : C k} {y : C' k}
    (f : (c.Φ n).obj ((c.T h).obj x) ⟶ (c.Φ n).obj ((c.T h).obj ((A.R k).obj y))) :
    F.map ((c.iso h).inv.app x ≫ f ≫ (c.iso h).hom.app _) ≫ A.counitObj k y =
      F.map ((c.iso h).inv.app x) ≫
        (F.map (f ≫ (c.Φ n).map ((A.mate h).app y)) ≫ A.counitObj n ((c'.T h).obj y)) ≫
          (c'.iso h).hom.app y := by
  simp only [Functor.map_comp, assoc, A.map_hom_comp_counitObj]

/-- Injectivity of `f ↦ F.map f ≫ ε` on images of morphisms of stage `k`. -/
lemma map_eq_map_of_map_map_comp_counitObj_eq (hc' : c'.HomInj) {k : I} {x : C k} {y : C' k}
    (g₁ g₂ : x ⟶ (A.R k).obj y)
    (hg : F.map ((c.Φ k).map g₁) ≫ A.counitObj k y = F.map ((c.Φ k).map g₂) ≫ A.counitObj k y) :
    (c.Φ k).map g₁ = (c.Φ k).map g₂ := by
  rw [map_map_comp_counitObj, map_map_comp_counitObj, cancel_epi] at hg
  obtain ⟨n, h, hn⟩ := hc' k _ _ _ _ hg
  have hT : (c.T h).map g₁ = (c.T h).map g₂ := by
    rw [← cancel_mono ((A.mate h).app y), ← ((A.adj n).homEquiv _ _).symm.injective.eq_iff,
      Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, A.map_map_mate_comp_counit,
      A.map_map_mate_comp_counit, hn]
  rw [← NatIso.naturality_1 (c.iso h) g₁, ← NatIso.naturality_1 (c.iso h) g₂, Functor.comp_map,
    Functor.comp_map, hT]

/-- If the image of a morphism `g` of stage `k` and an arbitrary `f` have the same composite with
the candidate counit, they are equal. -/
lemma map_eq_of_map_map_comp_counitObj_eq (hc : c.HomSurj) (hc' : c'.HomInj) {k : I} {x : C k}
    {y : C' k} (g : x ⟶ (A.R k).obj y) (f : (c.Φ k).obj x ⟶ (c.Φ k).obj ((A.R k).obj y))
    (hf : F.map ((c.Φ k).map g) ≫ A.counitObj k y = F.map f ≫ A.counitObj k y) :
    (c.Φ k).map g = f := by
  obtain ⟨n, h, h', g', rfl⟩ := hc k k x _ f
  obtain rfl : h = h' := rfl
  rw [← NatIso.naturality_1 (c.iso h) g, Functor.comp_map, A.map_comp_counitObj_eq,
    A.map_comp_counitObj_eq, cancel_epi, cancel_mono, ← Functor.map_comp,
    ← Functor.map_comp] at hf
  have := A.map_eq_map_of_map_map_comp_counitObj_eq hc' _ _ hf
  rw [Functor.map_comp, Functor.map_comp, cancel_mono] at this
  rw [← NatIso.naturality_1 (c.iso h) g, Functor.comp_map, this]

/-- Injectivity of `f ↦ F.map f ≫ ε` on morphisms `c.Φ k x ⟶ c.Φ k (R k y)`. -/
lemma injective_map_comp_counitObj (hc : c.HomSurj) (hc' : c'.HomInj) {k : I} (x : C k)
    (y : C' k) :
    Function.Injective fun f : (c.Φ k).obj x ⟶ (c.Φ k).obj ((A.R k).obj y) ↦
      F.map f ≫ A.counitObj k y := by
  intro f₁ f₂ hf
  obtain ⟨n, h, h', g₁, rfl⟩ := hc k k x _ f₁
  obtain rfl : h = h' := rfl
  obtain ⟨f₂', rfl⟩ : ∃ f₂', f₂ = (c.iso h).inv.app x ≫ f₂' ≫ (c.iso h).hom.app _ :=
    ⟨(c.iso h).hom.app x ≫ f₂ ≫ (c.iso h).inv.app _, by simp⟩
  dsimp only at hf
  rw [A.map_comp_counitObj_eq, A.map_comp_counitObj_eq, cancel_epi, cancel_mono,
    ← Functor.map_comp] at hf
  have := A.map_eq_of_map_map_comp_counitObj_eq hc hc' _ _ hf
  rw [Functor.map_comp, cancel_mono] at this
  rw [this]

/-- Surjectivity of `f ↦ F.map f ≫ ε` on morphisms `c.Φ k x ⟶ c.Φ k (R k y)`. -/
lemma surjective_map_comp_counitObj (hc' : c'.HomSurj) {k : I} (x : C k) (y : C' k) :
    Function.Surjective fun f : (c.Φ k).obj x ⟶ (c.Φ k).obj ((A.R k).obj y) ↦
      F.map f ≫ A.counitObj k y := by
  intro φ
  obtain ⟨n, h, h', u, hu⟩ := hc' k k _ y ((A.α k).hom.app x ≫ φ)
  obtain rfl : h = h' := rfl
  refine ⟨(c.iso h).inv.app x ≫ (c.Φ n).map
    ((A.adj n).homEquiv _ _ ((A.β h).app x ≫ u) ≫ inv ((A.mate h).app y)) ≫
      (c.iso h).hom.app _, ?_⟩
  dsimp only
  rw [A.map_comp_counitObj_eq]
  simp only [Functor.map_comp, assoc, Functor.map_inv, IsIso.inv_hom_id_assoc]
  rw [map_map_comp_counitObj_assoc,
    ← Adjunction.homEquiv_counit, Equiv.symm_apply_apply, Functor.map_comp, assoc,
    map_inv_comp_inv_comp_map_assoc, ← hu]
  simp

/-- `f ↦ F.map f ≫ ε` is bijective on morphisms `c.Φ k x ⟶ c.Φ k (R k y)`. -/
lemma bijective_map_comp_counitObj (hc : c.HomSurj) (hc' : c'.HomSurj) (hc'' : c'.HomInj)
    {k : I} (x : C k) (y : C' k) :
    Function.Bijective fun f : (c.Φ k).obj x ⟶ (c.Φ k).obj ((A.R k).obj y) ↦
      F.map f ≫ A.counitObj k y :=
  ⟨A.injective_map_comp_counitObj hc hc'' x y, A.surjective_map_comp_counitObj hc' x y⟩

/-- `f ↦ F.map f ≫ ε` is bijective on morphisms `X ⟶ c.Φ k (R k y)`, for every object `X`. -/
lemma bijective_map_comp_counitObj_of_obj [IsDirected I (· ≤ ·)] (hc₁ : c.EssSurjObj)
    (hc : c.HomSurj) (hc' : c'.HomSurj) (hc'' : c'.HomInj) (X : D) {k : I} (y : C' k) :
    Function.Bijective fun f : X ⟶ (c.Φ k).obj ((A.R k).obj y) ↦ F.map f ≫ A.counitObj k y := by
  obtain ⟨j, x, ⟨e⟩⟩ := hc₁ X
  obtain ⟨n, hjn, hkn⟩ := directed_of (· ≤ ·) j k
  refine F.bijective_map_comp_of_iso (e.symm ≪≫ ((c.iso hjn).app x).symm)
    (((c.iso hkn).app _).symm ≪≫ (c.Φ n).mapIso (asIso ((A.mate hkn).app y)))
    ((c'.iso hkn).app y) _ _ ?_ (A.bijective_map_comp_counitObj hc hc' hc'' _ _)
  rw [← cancel_epi (F.map ((c.iso hkn).hom.app _)), A.map_hom_comp_counitObj, Iso.trans_hom,
    Iso.symm_hom, Iso.app_inv, Functor.mapIso_hom, asIso_hom, F.map_comp, assoc,
    ← F.map_comp_assoc, Iso.hom_inv_id_app, F.map_id, id_comp, Iso.app_hom]

/-- A functor between filtered 2-colimits of categories induced by levelwise left adjoints whose
right adjoints commute with the transition functors is a left adjoint. Only (Obj) and the
surjectivity half of (Hom) are used for the source cocone `c`. -/
theorem isLeftAdjoint (A : LevelwiseLeftAdjoint c c' F) [IsDirected I (· ≤ ·)]
    (hc₁ : c.EssSurjObj) (hc : c.HomSurj)
    (hc'₁ : c'.EssSurjObj) (hc' : c'.HomSurj) (hc'' : c'.HomInj) : F.IsLeftAdjoint := by
  have (Y : D') : Limits.HasTerminal (CostructuredArrow F Y) := by
    obtain ⟨k, y, ⟨e⟩⟩ := hc'₁ Y
    refine Limits.IsTerminal.hasTerminal (F.isTerminalCostructuredArrowMkOfBijective
      (A.counitObj k y ≫ e.hom) fun X ↦ ?_)
    exact F.bijective_map_comp_of_iso (Iso.refl X) (Iso.refl _) e _ _ (by simp)
      (A.bijective_map_comp_counitObj_of_obj hc₁ hc hc' hc'' X y)
  exact isLeftAdjoint_of_costructuredArrowTerminals F

/-- A functor between filtered 2-colimits of categories induced by levelwise left adjoints whose
right adjoints commute with the transition functors is a left adjoint. -/
theorem isLeftAdjoint_of_isFilteredTwoColimit (A : LevelwiseLeftAdjoint c c' F)
    [IsDirected I (· ≤ ·)]
    (hc : c.IsFilteredTwoColimit) (hc' : c'.IsFilteredTwoColimit) : F.IsLeftAdjoint :=
  A.isLeftAdjoint hc.essSurjObj hc.homSurj hc'.essSurjObj hc'.homSurj hc'.homInj

end LevelwiseLeftAdjoint

end CategoryCocone

end CategoryTheory
