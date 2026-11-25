/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHomModel
public import WeilConjectures.Algebra.Homology.RingedSiteZerothHypercohomology
import WeilConjectures.Algebra.Homology.RhomGlobalSections

/-! # Tensor-unit normalization of derived Hom sections

Source: Stacks Project, Tags 08JA and 08DJ; step 2 of
lem-pc-derived-pullback-evaluation-sections.
(blueprint: lem-pc-derived-tensor-hom-sections-unit).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace
namespace AlgebraicGeometry

section
variable {C : Type*} [Category C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C]
  (H : Cᵒᵖ × C ⥤ C)
  (q : ∀ A K L, (A ⟶ H.obj (op K, L)) ≃ (A ⊗ K ⟶ L))
  (hq : ∀ (A A' K K' L L') (a : A' ⟶ A) (b : K' ⟶ K) (c : L ⟶ L')
    (f : A ⟶ H.obj (op K, L)),
    q A' K' L' (a ≫ f ≫ H.map (b.op, c)) = (a ⊗ₘ b) ≫ q A K L f ≫ c)

include hq

omit [Preadditive C] [MonoidalPreadditive C] in
private theorem q_evaluation (A K L : C) (f : A ⟶ H.obj (op K, L)) :
    q A K L f = f ▷ K ≫ q _ K L (𝟙 _) := by
  have hh := hq _ A K K L L f (𝟙 _) (𝟙 _) (𝟙 _)
  have hi : H.map (show (op K, L) ⟶ (op K, L) from ((𝟙 K).op, 𝟙 L)) =
      𝟙 (H.obj (op K, L)) := by
    simpa only [prod_id', ← op_id] using H.map_id (op K, L)
  simpa only [hi, Category.comp_id, tensorHom_id] using hh

private def qAdd (A K L : C) : (A ⟶ H.obj (op K, L)) ≃+ (A ⊗ K ⟶ L) :=
  { q A K L with
    map_add' := by
      intro f g
      change q A K L (f + g) = q A K L f + q A K L g
      rw [q_evaluation H q hq A K L (f + g), q_evaluation H q hq A K L f,
        q_evaluation H q hq A K L g]
      simp only [MonoidalPreadditive.add_whiskerRight, Preadditive.add_comp] }

private def unitHom (A B : C) : (A ⟶ H.obj (op (𝟙_ C), B)) ≃ (A ⟶ B) :=
  (q A (𝟙_ C) B).trans (Iso.homCongr (ρ_ A) (Iso.refl B))

omit [Preadditive C] [MonoidalPreadditive C] in
private theorem unitHom_left {A A' B : C} (f : A' ⟶ A)
    (g : A ⟶ H.obj (op (𝟙_ C), B)) :
    unitHom H q A' B (f ≫ g) = f ≫ unitHom H q A B g := by
  have hh := hq A A' (𝟙_ C) (𝟙_ C) B B f (𝟙 _) (𝟙 _) g
  have hi : H.map (show (op (𝟙_ C), B) ⟶ (op (𝟙_ C), B) from
      ((𝟙 (𝟙_ C)).op, 𝟙 B)) = 𝟙 (H.obj (op (𝟙_ C), B)) := by
    simpa only [prod_id', ← op_id] using H.map_id (op (𝟙_ C), B)
  simp only [hi, Category.comp_id, tensorHom_id] at hh
  simp only [unitHom, Equiv.trans_apply, Iso.homCongr_apply, Iso.refl_hom,
    Category.comp_id, hh]
  simp only [← Category.assoc, rightUnitor_inv_naturality]

omit [Preadditive C] [MonoidalPreadditive C] in
private theorem unitHom_right {A B B' : C} (f : A ⟶ H.obj (op (𝟙_ C), B))
    (g : B ⟶ B') :
    unitHom H q A B' (f ≫ H.map ((𝟙 (𝟙_ C)).op, g)) =
      unitHom H q A B f ≫ g := by
  have hh := hq A A (𝟙_ C) (𝟙_ C) B B' (𝟙 _) (𝟙 _) g f
  simp only [Category.id_comp, tensorHom_id, id_whiskerRight] at hh
  simp only [unitHom, Equiv.trans_apply, Iso.homCongr_apply, Iso.refl_hom,
    Category.comp_id, hh, Category.assoc]

private def unitIso (B : C) : B ≅ H.obj (op (𝟙_ C), B) where
  hom := (unitHom H q B B).symm (𝟙 B)
  inv := unitHom H q _ B (𝟙 _)
  hom_inv_id := by
    have hh := unitHom_left H q hq ((unitHom H q B B).symm (𝟙 B)) (𝟙 _)
    simpa only [Category.comp_id, Equiv.apply_symm_apply] using hh.symm
  inv_hom_id := by
    apply (unitHom H q _ B).injective
    rw [unitHom_left H q hq, Equiv.apply_symm_apply, Category.comp_id]

omit [Preadditive C] [MonoidalPreadditive C] in
private theorem unitIso_natural {A B : C} (f : A ⟶ B) :
    f ≫ (unitIso H q hq B).hom =
      (unitIso H q hq A).hom ≫ H.map ((𝟙 (𝟙_ C)).op, f) := by
  apply (unitHom H q A B).injective
  rw [unitHom_left H q hq, unitHom_right H q hq]
  simp only [unitIso, Equiv.apply_symm_apply, Category.comp_id, Category.id_comp]

private theorem sectionsUnitReduction
    (Q : C ⥤ AddCommGrpCat)
    (e₀ : ∀ P : Cᵒᵖ × C, Q.obj (H.obj P) ≃+ (P.1.unop ⟶ P.2))
    (he₀ : ∀ (P P' : Cᵒᵖ × C) (f : P ⟶ P') (x : Q.obj (H.obj P)),
      e₀ P' (Q.map (H.map f) x) = f.1.unop ≫ e₀ P x ≫ f.2) :
    ∃ (γ : ∀ A, Q.obj A ≃+ (𝟙_ C ⟶ A))
      (e : ∀ P : Cᵒᵖ × C, Q.obj (H.obj P) ≃+ (P.1.unop ⟶ P.2)),
      (∀ (A B : C) (f : A ⟶ B) (x : Q.obj A), γ B (Q.map f x) = γ A x ≫ f) ∧
      (∀ (P P' : Cᵒᵖ × C) (f : P ⟶ P') (x : Q.obj (H.obj P)),
        e P' (Q.map (H.map f) x) = f.1.unop ≫ e P x ≫ f.2) ∧
      (∀ (K L : C) (x : Q.obj (H.obj (op K, L))),
        e (op K, L) x = (λ_ K).inv ≫ q _ K L (γ _ x)) := by
  let γ (A : C) := (Q.mapIso (unitIso H q hq A)).addCommGroupIsoToAddEquiv.trans
    (e₀ (op (𝟙_ C), A))
  have hγ (A B : C) (f : A ⟶ B) (x : Q.obj A) : γ B (Q.map f x) = γ A x ≫ f := by
    change e₀ (op (𝟙_ C), B) (Q.map (unitIso H q hq B).hom (Q.map f x)) =
      e₀ (op (𝟙_ C), A) (Q.map (unitIso H q hq A).hom x) ≫ f
    rw [← ConcreteCategory.comp_apply, ← Q.map_comp, unitIso_natural H q hq,
      Q.map_comp, ConcreteCategory.comp_apply]
    have hn := he₀ (op (𝟙_ C), A) (op (𝟙_ C), B) ((𝟙 _).op, f)
      (Q.map (unitIso H q hq A).hom x)
    simpa only [Quiver.Hom.unop_op, Category.id_comp] using hn
  let t (K L : C) : (𝟙_ C ⊗ K ⟶ L) ≃+ (K ⟶ L) :=
    { toEquiv := Iso.homCongr (λ_ K) (Iso.refl L)
      map_add' := by intro f g; simp [Iso.homCongr, Preadditive.comp_add] }
  let e (P : Cᵒᵖ × C) := (γ (H.obj P)).trans
    ((qAdd H q hq _ P.1.unop P.2).trans (t P.1.unop P.2))
  have hen (K L : C) (x : Q.obj (H.obj (op K, L))) :
      e (op K, L) x = (λ_ K).inv ≫ q _ K L (γ _ x) := by
    simp [e, t, qAdd, Iso.homCongr]
  refine ⟨γ, e, hγ, ?_, hen⟩
  rintro ⟨K, L⟩ ⟨K', L'⟩ ⟨a, b⟩ x
  change e (op K'.unop, L') (Q.map (H.map (a, b)) x) =
    a.unop ≫ e (op K.unop, L) x ≫ b
  rw [hen, hen, hγ]
  have hn := hq (𝟙_ C) (𝟙_ C) K.unop K'.unop L L' (𝟙 _) a.unop b (γ _ x)
  simp only [Category.id_comp, Quiver.Hom.op_unop] at hn
  rw [hn]
  simp only [id_tensorHom, ← Category.assoc, ← leftUnitor_inv_naturality]
end

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 2048 in
/-- Zeroth hypercohomology is represented by the derived tensor unit, and its
identification on internal Hom agrees with uncurrying at that unit.

Source: Stacks Project, Tags 08JA and 08DJ; the representative identification in
step 2 of lem-pc-derived-pullback-evaluation-sections.
(blueprint: lem-pc-derived-tensor-hom-sections-unit).

Proof: use rhom_global_sections to obtain a natural additive identification e0
on internal Hom. Specialize tensor-Hom at K=unit and precompose with the inverse
right unitor. This gives a family Hom(A,H(unit,B)) equiv Hom(A,B) natural in A
and B. Evaluate it and its inverse at identity maps to construct B iso H(unit,B);
its inverse laws and naturality follow from those two naturality equations.
Apply zeroth hypercohomology to this isomorphism and then e0(unit,B). This gives
a natural additive gamma(B):Q(B) equiv Hom(unit,B).
The tensor-Hom family is additive: naturality in its first variable expresses
q(f) as (f tensor identity) followed by evaluation, and tensoring is additive.
Define e(K,L) by gamma(H(K,L)), then q(unit,K,L), then precomposition with the
inverse left unitor. Its normalization equation is definitional. Naturality
of gamma and q, followed by naturality of the left unitor, proves naturality
of e in both variables. This is a categorical construction from the existing
natural global-Hom identification; no representative calculation or new
existence assumption is required. Zero and empty schemes are included. -/
theorem exists_derivedTensorHom_sections_unit (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (q : ∀ A K L : schemeDerivedCategory X,
      (A ⟶ (derivedInternalHom (Opens.grothendieckTopology X)
        X.toRingedSpace.sheaf).obj (op K, L)) ≃ (A ⊗ K ⟶ L))
    (hq : IsCanonicalDerivedTensorHom X q) :
    ∃ (γ : ∀ A : schemeDerivedCategory X,
        (ringedSiteZerothHypercohomology (Opens.grothendieckTopology X)
          X.toRingedSpace.sheaf).obj A ≃+ (𝟙_ (schemeDerivedCategory X) ⟶ A))
      (e : ∀ P : (schemeDerivedCategory X)ᵒᵖ × schemeDerivedCategory X,
        (ringedSiteZerothHypercohomology (Opens.grothendieckTopology X)
          X.toRingedSpace.sheaf).obj
          ((derivedInternalHom (Opens.grothendieckTopology X)
            X.toRingedSpace.sheaf).obj P) ≃+ (P.1.unop ⟶ P.2)),
      (∀ (A B : schemeDerivedCategory X) (f : A ⟶ B)
          (x : (ringedSiteZerothHypercohomology (Opens.grothendieckTopology X)
            X.toRingedSpace.sheaf).obj A),
        γ B ((ringedSiteZerothHypercohomology (Opens.grothendieckTopology X)
          X.toRingedSpace.sheaf).map f x) = γ A x ≫ f) ∧
      (∀ (P P' : (schemeDerivedCategory X)ᵒᵖ × schemeDerivedCategory X) (f : P ⟶ P')
          (x : (ringedSiteZerothHypercohomology (Opens.grothendieckTopology X)
            X.toRingedSpace.sheaf).obj
              ((derivedInternalHom (Opens.grothendieckTopology X)
                X.toRingedSpace.sheaf).obj P)),
        e P' ((ringedSiteZerothHypercohomology (Opens.grothendieckTopology X)
          X.toRingedSpace.sheaf).map
            ((derivedInternalHom (Opens.grothendieckTopology X)
              X.toRingedSpace.sheaf).map f) x) = f.1.unop ≫ e P x ≫ f.2) ∧
      (∀ (K L : schemeDerivedCategory X)
          (x : (ringedSiteZerothHypercohomology (Opens.grothendieckTopology X)
            X.toRingedSpace.sheaf).obj
              ((derivedInternalHom (Opens.grothendieckTopology X)
                X.toRingedSpace.sheaf).obj (op K, L))),
        e (op K, L) x = (λ_ K).inv ≫ q _ K L (γ _ x)) := by
  classical
  have : MonoidalPreadditive (schemeDerivedCategory X) := by
    let C := SheafOfModules.{u} (moduleRings X.toRingedSpace)
    let := SheafOfModules.monoidalCategory X.sheaf
    let := SheafOfModules.symmetricCategory X.sheaf
    have : MonoidalPreadditive C := Classical.choice (SheafOfModules.tensorClosed X.sheaf).1
    let : MonoidalClosed C := Classical.choice (SheafOfModules.tensorClosed X.sheaf).2.1
    have : IsGrothendieckAbelian.{u} C := SheafOfModules.isGrothendieckAbelian _
    have : Limits.HasColimitsOfSize.{0, 0} C :=
      Limits.hasColimitsOfSizeShrink.{0, 0, u, u} C
    have := schemeModule_hasFunctorialFlatResolution X
    have := DerivedCategory.hasDerivedMonoidalCategory C
    exact DerivedCategory.monoidalPreadditive
  apply Exists.elim (rhom_global_sections.{u, w}
    (Opens.grothendieckTopology X) X.sheaf)
  intro e₀ he₀
  exact sectionsUnitReduction _ q hq.1 _ e₀ he₀

end AlgebraicGeometry
