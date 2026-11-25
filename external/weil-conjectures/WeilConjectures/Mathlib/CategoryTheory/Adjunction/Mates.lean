/-
Copyright (c) 2026 Christian Merten, Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Equivalence

/-!
# Coherence of the conjugation bijection, in isomorphism form

Mathlib records the compatibility of `CategoryTheory.conjugateEquiv` with composition, the
unitors, the associator and whiskering as statements about natural *transformations*. Since
`CategoryTheory.conjugateIsoEquiv` is built from `CategoryTheory.conjugateEquiv` on the
`hom` and the `inv`, each of these statements has a counterpart for natural *isomorphisms*,
and it is the latter that one wants when transporting the coherence of a pseudofunctor
`X ↦ F X` from the right adjoints to the left adjoints.

## Main results

- `CategoryTheory.conjugateIsoEquiv_trans`: conjugation turns a composite of natural
  isomorphisms into the composite in the opposite order.
- `CategoryTheory.conjugateIsoEquiv_leftUnitor`,
  `CategoryTheory.conjugateIsoEquiv_rightUnitor`,
  `CategoryTheory.conjugateIsoEquiv_associator`: conjugation carries the unitors and the
  associator of the left adjoints to those of the right adjoints.
- `CategoryTheory.conjugateIsoEquiv_isoWhiskerLeft` and
  `CategoryTheory.conjugateIsoEquiv_isoWhiskerRight`: conjugation exchanges left and right
  whiskering.
- `CategoryTheory.Adjunction.map_unit_app_comp_liftAlgebraStr`: the unit `K ⟶ R (L K)` of an
  adjunction intertwines a structure map `G K ⟶ K` with its lift
  `CategoryTheory.Adjunction.liftAlgebraStr : G (R (L K)) ⟶ R (L K)` along a lift of `G`.
- `CategoryTheory.mateEquiv_whiskerBottom`: the mate of a 2-square whiskered at the bottom is
  the mate whiskered on the left.
- `CategoryTheory.mateEquiv_whiskerTop_conjugateEquiv`: conjugates of morphisms of left
  adjoints compatible with 2-squares are compatible with the mates of these 2-squares.
- `CategoryTheory.Adjunction.whiskerRight_comp_conjugateIsoEquiv_hom`: for an adjoint triple
  `L ⊣ M ⊣ R`, the comparison `L ⟶ R` commutes with the exchange isomorphisms obtained by
  conjugating an isomorphism `ED ⋙ M ≅ M ⋙ EC` for self-equivalences `EC` and `ED`.
- `CategoryTheory.mateEquiv_eq_of_unit`, `CategoryTheory.conjugateEquiv_eq_of_unit`: a mate, resp. a
  conjugate, is determined by its compatibility with the units.
- `CategoryTheory.isIso_mateEquiv_of_isEquivalence`: for adjunctions `L₁ ⊣ R₁` and `L₂ ⊣ R₂` and
  equivalences `G` and `H`, the mate `R₁ ⋙ G ⟶ H ⋙ R₂` of an isomorphism
  `G ⋙ L₂ ≅ L₁ ⋙ H` is an isomorphism.
-/

@[expose] public section

namespace CategoryTheory


universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄}
variable [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} D]

section

variable {L₁ L₂ L₃ : A ⥤ B} {R₁ R₂ R₃ : B ⥤ A}
variable (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃)

/-- Conjugating the inverse of a natural isomorphism gives the inverse of the conjugate. -/
lemma conjugateIsoEquiv_iso_symm (e : L₂ ≅ L₁) :
    conjugateIsoEquiv adj₂ adj₁ e.symm = (conjugateIsoEquiv adj₁ adj₂ e).symm :=
  rfl

/-- Conjugation turns a composite of natural isomorphisms of left adjoints into the
composite, in the opposite order, of the conjugate natural isomorphisms. -/
lemma conjugateIsoEquiv_trans (e : L₂ ≅ L₁) (e' : L₃ ≅ L₂) :
    conjugateIsoEquiv adj₁ adj₃ (e' ≪≫ e) =
      conjugateIsoEquiv adj₁ adj₂ e ≪≫ conjugateIsoEquiv adj₂ adj₃ e' := by
  ext : 1
  exact (conjugateEquiv_comp adj₁ adj₂ adj₃ e.hom e'.hom).symm

/-- **The mate of an isomorphism of left adjoints carries the pasted unit and counit.**
Transporting the adjunction `L₁ ⊣ R₁` along an isomorphism `e : L₁ ≅ L₂` of left adjoints and
along its conjugate `R₁ ≅ R₂` gives back the adjunction `L₂ ⊣ R₂`: the unit and counit of
`adj₂` are those of `adj₁` pasted with `e` and with the conjugate of `e`:
```
  𝟭 --η₁--> L₁ ⋙ R₁ --e ◫ ẽ--> L₂ ⋙ R₂        R₂ ⋙ L₂ --ẽ⁻¹ ◫ e⁻¹--> R₁ ⋙ L₁ --ε₁--> 𝟭
```
where `ẽ : R₁ ≅ R₂` is the inverse of the conjugate `R₂ ≅ R₁` of `e`; the left composite is the
unit `η₂` of `adj₂` and the right composite is its counit `ε₂`. -/
lemma Adjunction.ofNatIsoLeft_ofNatIsoRight_conjugateIsoEquiv (e : L₁ ≅ L₂) :
    (adj₁.ofNatIsoLeft e).ofNatIsoRight (conjugateIsoEquiv adj₂ adj₁ e).symm = adj₂ := by
  ext c
  have h := unit_conjugateEquiv adj₁ adj₂ e.inv c
  have hn := (conjugateEquiv adj₁ adj₂ e.inv).naturality (e.hom.app c)
  simp only [Functor.comp_obj, Functor.id_obj] at h hn
  simp only [Adjunction.ofNatIsoRight_unit, Adjunction.ofNatIsoLeft_unit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.symm_hom, conjugateIsoEquiv_apply_inv,
    Category.assoc, Functor.comp_obj, Functor.id_obj]
  rw [hn, reassoc_of% h, ← R₂.map_comp, Iso.inv_hom_id_app, R₂.map_id, Category.comp_id]

end

/-- Conjugation carries the left unitor of a left adjoint to the right unitor of its right
adjoint. -/
lemma conjugateIsoEquiv_leftUnitor {L : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R) :
    conjugateIsoEquiv adj (Adjunction.id.comp adj) L.leftUnitor = R.rightUnitor.symm := by
  ext : 1
  exact conjugateEquiv_leftUnitor_hom adj

/-- Conjugation carries the right unitor of a left adjoint to the left unitor of its right
adjoint. -/
lemma conjugateIsoEquiv_rightUnitor {L : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R) :
    conjugateIsoEquiv adj (adj.comp Adjunction.id) L.rightUnitor = R.leftUnitor.symm := by
  ext : 1
  exact conjugateEquiv_rightUnitor_hom adj

/-- Conjugation carries the associator of three composable left adjoints to the associator
of their right adjoints. -/
lemma conjugateIsoEquiv_associator {L₀₁ : A ⥤ B} {R₁₀ : B ⥤ A} {L₁₂ : B ⥤ C} {R₂₁ : C ⥤ B}
    {L₂₃ : C ⥤ D} {R₃₂ : D ⥤ C} (adj₀₁ : L₀₁ ⊣ R₁₀) (adj₁₂ : L₁₂ ⊣ R₂₁) (adj₂₃ : L₂₃ ⊣ R₃₂) :
    conjugateIsoEquiv (adj₀₁.comp (adj₁₂.comp adj₂₃)) ((adj₀₁.comp adj₁₂).comp adj₂₃)
        (L₀₁.associator L₁₂ L₂₃) = R₃₂.associator R₂₁ R₁₀ := by
  ext : 1
  exact conjugateEquiv_associator_hom adj₀₁ adj₁₂ adj₂₃

/-- Conjugation exchanges left whiskering with right whiskering. -/
lemma conjugateIsoEquiv_isoWhiskerLeft {L₁ L₂ : B ⥤ C} {R₁ R₂ : C ⥤ B} {L : A ⥤ B} {R : B ⥤ A}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj : L ⊣ R) (e : L₂ ≅ L₁) :
    conjugateIsoEquiv (adj.comp adj₁) (adj.comp adj₂) (Functor.isoWhiskerLeft L e) =
      Functor.isoWhiskerRight (conjugateIsoEquiv adj₁ adj₂ e) R := by
  ext : 1
  exact conjugateEquiv_whiskerLeft adj₁ adj₂ adj e.hom

/-- Conjugation exchanges right whiskering with left whiskering. -/
lemma conjugateIsoEquiv_isoWhiskerRight {L₁ L₂ : A ⥤ B} {R₁ R₂ : B ⥤ A} {L : B ⥤ C} {R : C ⥤ B}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj : L ⊣ R) (e : L₂ ≅ L₁) :
    conjugateIsoEquiv (adj₁.comp adj) (adj₂.comp adj) (Functor.isoWhiskerRight e L) =
      Functor.isoWhiskerLeft R (conjugateIsoEquiv adj₁ adj₂ e) := by
  ext : 1
  exact conjugateEquiv_whiskerRight adj₁ adj₂ adj e.hom

section LiftAlgebraStr

variable {L : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R) {G : A ⥤ A} {H : B ⥤ B}

/-- Given an adjunction `L ⊣ R`, a lift `α : G ⋙ L ≅ L ⋙ H` of an endofunctor `G` of `A` to
an endofunctor `H` of `B`, and a structure map `φ : G K ⟶ K`, the structure map

```
  G (R (L K)) ──mate of α──▶ R (H (L K)) ──R α⁻¹──▶ R (L (G K)) ──R (L φ)──▶ R (L K)
```

on `R (L K)`, where the mate `R ⋙ G ⟶ H ⋙ R` of `α` is
`CategoryTheory.mateEquiv adj adj α.hom`. -/
def Adjunction.liftAlgebraStr (α : G ⋙ L ≅ L ⋙ H) {K : A} (φ : G.obj K ⟶ K) :
    G.obj (R.obj (L.obj K)) ⟶ R.obj (L.obj K) :=
  (mateEquiv adj adj α.hom).app (L.obj K) ≫ R.map (α.inv.app K ≫ L.map φ)

/-- The unit `η : K ⟶ R (L K)` intertwines `φ` and its lift `Adjunction.liftAlgebraStr`:

```
  G K ──G η──▶ G (R (L K))
   │φ              │liftAlgebraStr α φ
   ▼               ▼
   K ────η────▶ R (L K)
``` -/
lemma Adjunction.map_unit_app_comp_liftAlgebraStr (α : G ⋙ L ≅ L ⋙ H) {K : A}
    (φ : G.obj K ⟶ K) :
    G.map (adj.unit.app K) ≫ adj.liftAlgebraStr α φ = φ ≫ adj.unit.app K := by
  rw [liftAlgebraStr, ← Category.assoc, unit_mateEquiv]
  simp only [Functor.id_obj, Functor.comp_obj, Category.assoc, Functor.map_comp,
    ← R.map_comp_assoc, Iso.hom_inv_id_app, Functor.map_id, Category.id_comp]
  exact adj.unit_naturality φ


instance Adjunction.isIso_liftAlgebraStr (α : G ⋙ L ≅ L ⋙ H) {K : A} (φ : G.obj K ⟶ K)
    [IsIso (mateEquiv adj adj α.hom)] [IsIso φ] : IsIso (adj.liftAlgebraStr α φ) := by
  dsimp [liftAlgebraStr]
  infer_instance

end LiftAlgebraStr

/-- Whiskering a 2-square at the bottom corresponds, under `mateEquiv`, to whiskering its mate
on the left: for a 2-square `w` and `β : H ⟶ H'`

```
A ---G---> C            B ---R₁---> A
|          |            |           |
L₁   ⇙    L₂    ↦      H'    ⇙     G
v          v            v           v
B --H'---> D            D ---R₂---> C
```
-/
lemma mateEquiv_whiskerBottom {G : A ⥤ C} {H H' : B ⥤ D} {L₁ : A ⥤ B} {R₁ : B ⥤ A}
    {L₂ : C ⥤ D} {R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (w : TwoSquare G L₁ L₂ H)
    (β : H ⟶ H') :
    mateEquiv adj₁ adj₂ (w.whiskerBottom β) = (mateEquiv adj₁ adj₂ w).whiskerLeft β := by
  ext X
  simp [mateEquiv, TwoSquare.whiskerBottom, TwoSquare.whiskerLeft, ← Functor.map_comp]

/-- Conjugation is compatible with 2-squares: let `α : L₂ ⟶ L₁` and `α' : L₂' ⟶ L₁'` be
morphisms of left adjoints, and let `w₁ : TwoSquare G L₁ L₁' H` and
`w₂ : TwoSquare G L₂ L₂' H` be 2-squares compatible with them, `w₂ ≫ α = α' ≫ w₁`. Then the
conjugates `R₁ ⟶ R₂` and `R₁' ⟶ R₂'` of `α` and `α'` are compatible with the mates of `w₁` and
`w₂`:

```
R₁ ⋙ G ---conj α---> R₂ ⋙ G
   |                    |
mate w₁              mate w₂
   v                    v
H ⋙ R₁' --conj α'--> H ⋙ R₂'
```
-/
lemma mateEquiv_whiskerTop_conjugateEquiv {G : A ⥤ C} {H : B ⥤ D}
    {L₁ L₂ : A ⥤ B} {R₁ R₂ : B ⥤ A} {L₁' L₂' : C ⥤ D} {R₁' R₂' : D ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₁' : L₁' ⊣ R₁') (adj₂' : L₂' ⊣ R₂')
    (α : L₂ ⟶ L₁) (α' : L₂' ⟶ L₁') (w₁ : TwoSquare G L₁ L₁' H) (w₂ : TwoSquare G L₂ L₂' H)
    (h : w₂.whiskerLeft α = w₁.whiskerRight α') :
    (mateEquiv adj₂ adj₂' w₂).whiskerTop (conjugateEquiv adj₁ adj₂ α) =
      (mateEquiv adj₁ adj₁' w₁).whiskerBottom (conjugateEquiv adj₁' adj₂' α') := by
  rw [← conjugateEquiv_mateEquiv_vcomp, h, mateEquiv_conjugateEquiv_vcomp]

section Triple

open _root_.CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] {L R : C ⥤ D} {M : D ⥤ C}
  (adj₁ : L ⊣ M) (adj₂ : M ⊣ R) [IsIso adj₂.counit] (EC : C ≌ C) (ED : D ≌ D)
  (e : ED.functor ⋙ M ≅ M ⋙ EC.functor) (can : L ⟶ R)
  (hcan : ∀ F, adj₁.unit.app F ≫ M.map (can.app F) = inv (adj₂.counit.app F))

namespace Adjunction

include hcan in
/-- **The comparison `L ⟶ R` of an adjoint triple commutes with conjugate exchange
isomorphisms.** Let `L ⊣ M ⊣ R` be an adjoint triple between `C` and `D` whose second counit is
invertible, let `can : L ⟶ R` be the comparison characterised by
`η_F ≫ M (can_F) = ε_F⁻¹`, and let `EC`, `ED` be self-equivalences of `C` and `D` together with
an isomorphism `e : ED ⋙ M ≅ M ⋙ EC`. Conjugating `e` gives the exchange isomorphisms
`e_* : R ⋙ ED⁻¹ ≅ EC⁻¹ ⋙ R` (along `M ⊣ R`) and `e_! : L ⋙ ED⁻¹ ≅ EC⁻¹ ⋙ L` (along `L ⊣ M`), and
the square
```
              can ED⁻¹
  L ⋙ ED⁻¹ ──────────▶ R ⋙ ED⁻¹
     │                    │
 e_! │                    │ e_*
     ▼                    ▼
  EC⁻¹ ⋙ L ─────────▶ EC⁻¹ ⋙ R
              EC⁻¹ can
```
commutes. Both composites are determined by their transposes under `M ⊣ R` and
`L ⋙ ED⁻¹ ⊣ ED ⋙ M`, which agree by the conjugation identities for `e_!` and `e_*`. -/
lemma whiskerRight_comp_conjugateIsoEquiv_hom :
    whiskerRight can ED.inverse ≫
        (conjugateIsoEquiv (ED.toAdjunction.comp adj₂) (adj₂.comp EC.toAdjunction) e.symm).hom =
      ((conjugateIsoEquiv (EC.symm.toAdjunction.comp adj₁)
        (adj₁.comp ED.symm.toAdjunction)).symm e.symm).hom ≫ whiskerLeft EC.inverse can := by
  set s := (conjugateIsoEquiv (ED.toAdjunction.comp adj₂) (adj₂.comp EC.toAdjunction) e.symm).hom
  set t := ((conjugateIsoEquiv (EC.symm.toAdjunction.comp adj₁)
        (adj₁.comp ED.symm.toAdjunction)).symm e.symm).hom
  have ht : conjugateEquiv (EC.symm.toAdjunction.comp adj₁) (adj₁.comp ED.symm.toAdjunction) t =
      e.inv := by
    simp [t]
  have hs : ∀ F, EC.functor.map (M.map (s.app F)) ≫
      EC.functor.map (adj₂.counit.app (EC.inverse.obj F)) ≫ EC.counit.app F =
        e.inv.app (ED.inverse.obj (R.obj F)) ≫ M.map (ED.counit.app (R.obj F)) ≫
          adj₂.counit.app F := by
    intro F
    have := conjugateEquiv_counit (ED.toAdjunction.comp adj₂) (adj₂.comp EC.toAdjunction)
      e.inv F
    simpa [s, conjugateIsoEquiv] using this
  ext F
  apply ((adj₁.comp ED.symm.toAdjunction).homEquiv _ _).injective
  have hu := unit_conjugateEquiv (EC.symm.toAdjunction.comp adj₁)
    (adj₁.comp ED.symm.toAdjunction) t F
  rw [ht] at hu
  simp only [homEquiv_unit, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
    Functor.map_comp]
  simp only [Equivalence.symm_inverse, comp_obj, Equivalence.symm_functor, comp_unit_app,
    Equivalence.toAdjunction_unit, Equivalence.symm_unit, Functor.comp_map,
    Equivalence.fun_inv_map, id_obj, map_comp, Category.assoc] at hu ⊢
  have key : inv (adj₂.counit.app F) ≫ M.map (ED.counitInv.app (R.obj F)) ≫
      M.map (ED.functor.map (s.app F)) = EC.counitInv.app F ≫
        EC.functor.map (inv (adj₂.counit.app (EC.inverse.obj F))) ≫
          e.inv.app (R.obj (EC.inverse.obj F)) := by
    rw [← cancel_epi (e.inv.app (ED.inverse.obj (R.obj F)) ≫ M.map (ED.counit.app (R.obj F)) ≫
      adj₂.counit.app F)]
    have hn := e.inv.naturality (s.app F)
    simp only [Functor.comp_map] at hn
    have hc : ED.counit.app (R.obj F) ≫ ED.counitInv.app (R.obj F) = 𝟙 _ :=
      ED.counitIso.hom_inv_id_app _
    have hc' : EC.counit.app F ≫ EC.counitInv.app F = 𝟙 _ := EC.counitIso.hom_inv_id_app _
    simp only [Category.assoc, IsIso.hom_inv_id_assoc, ← M.map_comp_assoc]
    simp only [hc]
    rw [← reassoc_of% (hs F), reassoc_of% hc']
    simpa [← EC.functor.map_comp_assoc] using hn.symm
  have h₁ : M.map (ED.counitInv.app (L.obj F)) ≫ M.map (ED.counit.app (L.obj F)) = 𝟙 _ := by
    rw [← M.map_comp]; simp
  have hn := e.inv.naturality (can.app (EC.inverse.obj F))
  simp only [Functor.comp_map] at hn
  rw [reassoc_of% h₁, reassoc_of% (hcan F), key, ← reassoc_of% hu, ← hn,
    ← EC.functor.map_comp_assoc, hcan]

end Adjunction

end Triple


section IteratedMate

variable {F₁ : A ⥤ C} {U₁ : C ⥤ A} {F₂ : B ⥤ D} {U₂ : D ⥤ B}
variable {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
variable (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : F₁ ⊣ U₁) (adj₄ : F₂ ⊣ U₂)

/-- In a square of four left adjoints, the mate `R₁ ⋙ F₁ ⟶ F₂ ⋙ R₂` of an isomorphism
`F₁ ⋙ L₂ ≅ L₁ ⋙ F₂` becomes an isomorphism after applying the right adjoint `U₁` of `F₁`,
provided the units of `F₁ ⊣ U₁` and `F₂ ⊣ U₂` are isomorphisms (i.e. `F₁` and `F₂` are fully
faithful). Indeed, `U₁` of the mate is, up to these units, the iterated mate, which is the
conjugate of the isomorphism (`CategoryTheory.iterated_mateEquiv_conjugateEquiv`). -/
lemma isIso_map_mateEquiv_app_of_isIso (α : TwoSquare F₁ L₁ L₂ F₂) [IsIso α]
    [IsIso adj₃.unit] [IsIso adj₄.unit] (b : B) :
    IsIso (U₁.map ((mateEquiv adj₁ adj₂ α).app b)) := by
  have hβ : IsIso (mateEquiv adj₄ adj₃ (mateEquiv adj₁ adj₂ α)) := by
    rw [iterated_mateEquiv_conjugateEquiv]
    infer_instance
  have h := unit_mateEquiv adj₄ adj₃ (mateEquiv adj₁ adj₂ α) b
  have h' : U₁.map ((mateEquiv adj₁ adj₂ α).app b) =
      inv (adj₃.unit.app _) ≫ R₁.map (adj₄.unit.app b) ≫
        (mateEquiv adj₄ adj₃ (mateEquiv adj₁ adj₂ α)).app _ := by
    rw [IsIso.eq_inv_comp]
    exact h.symm
  rw [h']
  infer_instance

end IteratedMate

section MateWhisker

variable {G G' : A ⥤ C} {H H' : B ⥤ D} {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)

/-- The mates correspondence is compatible with whiskering by natural transformations on the
sides of the square that are not part of the adjunctions: whiskering the top and bottom of
the square `G ⋙ L₂ ⟶ L₁ ⋙ H` corresponds to whiskering the right and left of its mate
`R₁ ⋙ G ⟶ H ⋙ R₂`. -/
lemma mateEquiv_whiskerTop_whiskerBottom (α : TwoSquare G L₁ L₂ H) (σ : G' ⟶ G) (τ : H ⟶ H') :
    mateEquiv adj₁ adj₂ ((α.whiskerTop σ).whiskerBottom τ) =
      ((mateEquiv adj₁ adj₂ α).whiskerRight σ).whiskerLeft τ := by
  ext d
  simp only [mateEquiv_apply, TwoSquare.whiskerBottom, TwoSquare.whiskerTop,
    TwoSquare.whiskerLeft, TwoSquare.whiskerRight, NatTrans.comp_app, Functor.comp_obj,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.map_comp, Category.assoc,
    Functor.rightUnitor_inv_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.leftUnitor_hom_app, Functor.comp_map, Category.id_comp, Category.comp_id,
    Functor.id_obj]
  rw [Adjunction.unit_naturality_assoc, ← R₂.map_comp, ← τ.naturality, R₂.map_comp]

end MateWhisker

section MateUnitors

variable {L : A ⥤ B} {R : B ⥤ A}

/-- The mate of the unitor square `𝟭 ⋙ L ⟶ L ⋙ 𝟭` is the unitor square `R ⋙ 𝟭 ⟶ 𝟭 ⋙ R`. -/
lemma mateEquiv_unitors (adj : L ⊣ R) :
    mateEquiv adj adj (TwoSquare.mk (𝟭 A) L L (𝟭 B)
      ((Functor.leftUnitor L).hom ≫ (Functor.rightUnitor L).inv)) =
      TwoSquare.mk R (𝟭 B) (𝟭 A) R ((Functor.rightUnitor R).hom ≫ (Functor.leftUnitor R).inv) := by
  ext X
  simp

/-- The mate of the unitor square `L ⋙ 𝟭 ⟶ 𝟭 ⋙ L` with respect to the identity adjunctions is
the unitor square `𝟭 ⋙ L ⟶ L ⋙ 𝟭`. -/
lemma mateEquiv_id_id_unitors (L : A ⥤ B) :
    mateEquiv Adjunction.id Adjunction.id (TwoSquare.mk L (𝟭 A) (𝟭 B) L
      ((Functor.rightUnitor L).hom ≫ (Functor.leftUnitor L).inv)) =
      TwoSquare.mk (𝟭 A) L L (𝟭 B) ((Functor.leftUnitor L).hom ≫ (Functor.rightUnitor L).inv) := by
  ext X
  simp [Adjunction.id]

end MateUnitors

section MateUnit

variable {G : A ⥤ C} {H : B ⥤ D} {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)

/-- The mate of a 2-square `α : G ⋙ L₂ ⟶ L₁ ⋙ H` is determined by its compatibility with the
units (`CategoryTheory.unit_mateEquiv`): a 2-square `γ : R₁ ⋙ G ⟶ H ⋙ R₂` satisfying it is the
mate of `α`. -/
lemma mateEquiv_eq_of_unit (α : TwoSquare G L₁ L₂ H) (γ : TwoSquare R₁ H G R₂)
    (h : ∀ a, G.map (adj₁.unit.app a) ≫ γ.app (L₁.obj a) =
      adj₂.unit.app (G.obj a) ≫ R₂.map (α.app a)) :
    mateEquiv adj₁ adj₂ α = γ := by
  rw [← Equiv.eq_symm_apply]
  ext a
  apply (adj₂.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, ← h, unit_mateEquiv_symm adj₁ adj₂]
  rfl

end MateUnit

section ConjugateUnit

variable {L₁ L₂ : A ⥤ B} {R₁ R₂ : B ⥤ A} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)

/-- The conjugate of `α : L₂ ⟶ L₁` is determined by its compatibility with the units
(`CategoryTheory.unit_conjugateEquiv`): a natural transformation `β : R₁ ⟶ R₂` satisfying it is
the conjugate of `α`. -/
lemma conjugateEquiv_eq_of_unit (α : L₂ ⟶ L₁) (β : R₁ ⟶ R₂)
    (h : ∀ a, adj₁.unit.app a ≫ β.app (L₁.obj a) = adj₂.unit.app a ≫ R₂.map (α.app a)) :
    conjugateEquiv adj₁ adj₂ α = β := by
  rw [← Equiv.eq_symm_apply]
  ext a
  apply (adj₂.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, ← h, unit_conjugateEquiv_symm adj₁ adj₂]

/-- Blueprint `proposition-sp-unique-adjoint--1`: mates along an isomorphism of left adjoints. For
adjunctions `L₁ ⊣ R₁`, `L₂ ⊣ R₂` and a natural isomorphism `α : L₁ ≅ L₂`, the conjugate
`β = conjugateIsoEquiv adj₁ adj₂ α.symm : R₁ ≅ R₂`

1. is given by `β = R₂ ε₁ ∘ R₂ α⁻¹ R₁ ∘ η₂ R₁`, with inverse `β⁻¹ = R₁ ε₂ ∘ R₁ α R₂ ∘ η₁ R₂`;
2. carries the units and the counits to each other: `R₂ α ∘ β L₁ ∘ η₁ = η₂` and
   `ε₂ ∘ α R₂ ∘ L₁ β = ε₁`;
3. is the unique natural isomorphism `R₁ ≅ R₂` with the unit compatibility of (2). -/
theorem conjugateIsoEquiv_symm_spec (α : L₁ ≅ L₂) :
    (∀ b, (conjugateIsoEquiv adj₁ adj₂ α.symm).hom.app b =
      adj₂.unit.app (R₁.obj b) ≫ R₂.map (α.inv.app (R₁.obj b)) ≫ R₂.map (adj₁.counit.app b)) ∧
    (∀ b, (conjugateIsoEquiv adj₁ adj₂ α.symm).inv.app b =
      adj₁.unit.app (R₂.obj b) ≫ R₁.map (α.hom.app (R₂.obj b)) ≫ R₁.map (adj₂.counit.app b)) ∧
    (∀ a, adj₁.unit.app a ≫ (conjugateIsoEquiv adj₁ adj₂ α.symm).hom.app (L₁.obj a) ≫
      R₂.map (α.hom.app a) = adj₂.unit.app a) ∧
    (∀ b, L₁.map ((conjugateIsoEquiv adj₁ adj₂ α.symm).hom.app b) ≫ α.hom.app (R₂.obj b) ≫
      adj₂.counit.app b = adj₁.counit.app b) ∧
    (∀ β : R₁ ≅ R₂, (∀ a, adj₁.unit.app a ≫ β.hom.app (L₁.obj a) ≫ R₂.map (α.hom.app a) =
      adj₂.unit.app a) → β = conjugateIsoEquiv adj₁ adj₂ α.symm) := by
  refine ⟨fun b ↦ ?_, fun b ↦ ?_, fun a ↦ ?_, fun b ↦ ?_, fun β hβ ↦ ?_⟩
  · simp [conjugateEquiv_apply_app]
  · simp [conjugateEquiv_apply_app]
  · have h := unit_conjugateEquiv adj₁ adj₂ α.inv a
    simp only [conjugateIsoEquiv_apply_hom, Iso.symm_hom]
    rw [reassoc_of% h, ← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id, Category.comp_id]
  · have h := conjugateEquiv_counit adj₁ adj₂ α.inv b
    simp only [conjugateIsoEquiv_apply_hom, Iso.symm_hom]
    rw [α.hom.naturality_assoc, h, Iso.hom_inv_id_app_assoc]
  · ext1
    refine (conjugateEquiv_eq_of_unit adj₁ adj₂ α.inv β.hom fun a ↦ ?_).symm
    rw [← hβ a, Category.assoc, Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app,
      Functor.map_id, Category.comp_id]


end ConjugateUnit

section MateEquivalence

/-! ### Mates along equivalences

The mate of an isomorphism is not an isomorphism in general. It is when the two vertical functors
of the square are equivalences: their inverses are right adjoints, so the mate can be taken a
second time, and the iterated mate is the conjugate of the original transformation
(`CategoryTheory.iterated_mateEquiv_conjugateEquiv`), an isomorphism; since the units and counits
of the equivalences are isomorphisms, this forces the first mate to be an isomorphism. -/

variable {C : Type u₁} {D : Type u₂} {E : Type u₃} {F : Type u₄}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} F]
  {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)

/-- The mate `R₁ ⋙ G ⟶ H ⋙ R₂` of an isomorphism `G ⋙ L₂ ≅ L₁ ⋙ H` along adjunctions
`L₁ ⊣ R₁` and `L₂ ⊣ R₂` is an isomorphism when the vertical functors `G` and `H` are
equivalences. -/
theorem isIso_mateEquiv_of_isEquivalence [G.IsEquivalence] [H.IsEquivalence]
    (α : TwoSquare G L₁ L₂ H) [IsIso α] :
    IsIso (mateEquiv adj₁ adj₂ α) := by
  let adj₃ := G.asEquivalence.toAdjunction
  let adj₄ := H.asEquivalence.toAdjunction
  have : IsIso (mateEquiv adj₄ adj₃ (mateEquiv adj₁ adj₂ α)) := by
    rw [iterated_mateEquiv_conjugateEquiv adj₁ adj₂ adj₃ adj₄]
    exact conjugateEquiv_iso (adj₁.comp adj₄) (adj₃.comp adj₂) α
  have (d : D) : IsIso ((mateEquiv adj₁ adj₂ α).app d) := by
    have : IsIso (adj₃.unit.app (R₁.obj d)) := by
      simp only [adj₃, Equivalence.toAdjunction_unit]
      infer_instance
    have : IsIso (adj₄.unit.app d) := by
      simp only [adj₄, Equivalence.toAdjunction_unit]
      infer_instance
    have h : G.asEquivalence.inverse.map ((mateEquiv adj₁ adj₂ α).app d) =
        inv (adj₃.unit.app (R₁.obj d)) ≫ R₁.map (adj₄.unit.app d) ≫
          (mateEquiv adj₄ adj₃ (mateEquiv adj₁ adj₂ α)).app (H.obj d) :=
      (IsIso.eq_inv_comp _).mpr (unit_mateEquiv adj₄ adj₃ (mateEquiv adj₁ adj₂ α) d).symm
    have : IsIso (G.asEquivalence.inverse.map ((mateEquiv adj₁ adj₂ α).app d)) := by
      rw [h]
      infer_instance
    exact isIso_of_reflects_iso _ G.asEquivalence.inverse
  exact NatIso.isIso_of_isIso_app _

end MateEquivalence

end CategoryTheory
