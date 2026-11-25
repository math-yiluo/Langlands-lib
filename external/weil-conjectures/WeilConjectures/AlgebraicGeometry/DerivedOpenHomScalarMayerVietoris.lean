/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedGlobalScalar
import WeilConjectures.AlgebraicGeometry.OpenDerivedLocalizationAdjunction
import WeilConjectures.AlgebraicGeometry.DerivedOpenUnionAdjunctionTriangle
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Algebra.Homology.OpenHomTriangleRealization
import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris

/-! # Scalar compatible Mayer--Vietoris on an open union

Source: Stacks Project, Tag 08BW, used in Tag 08EJ.
(blueprint: lem-sc-derived-open-hom-scalar-mayer-vietoris).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

private theorem restriction_precomp
    {C D H : Type*} [Category C] [Category D] [Category H]
    (F : C ⥤ D) (L : C ⥤ H) (T : D ⥤ H) (e : F ⋙ T ≅ L)
    {E A B : C} (s : E ⟶ A) (β : F.obj A ⟶ F.obj B) :
    e.inv.app E ≫ T.map (F.map s ≫ β) ≫ e.hom.app B =
      L.map s ≫ (e.inv.app A ≫ T.map β ≫ e.hom.app B) := by
  rw [T.map_comp]
  simpa only [Functor.comp_map, Category.assoc] using
    congrArg (fun f ↦ f ≫ T.map β ≫ e.hom.app B) (e.inv.naturality s).symm

private theorem derived_restriction_precomp
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ W : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over W))]
    {W U : X.Opens} (i : W ⟶ U) {E A B : schemeDerivedCategory X}
    (s : E ⟶ A)
    (β : (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj A ⟶
      (SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj B) :
    derivedOpenHomRestriction X.toRingedSpace i
      ((SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) U).mapDerivedCategory.map s ≫ β) =
      (SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) W).mapDerivedCategory.map s ≫
          derivedOpenHomRestriction X.toRingedSpace i β := by
  let A := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U
  let B := SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) i
  let : PreservesFiniteLimits (A ⋙ B) := comp_preservesFiniteLimits A B
  let : PreservesFiniteColimits (A ⋙ B) := comp_preservesFiniteColimits A B
  let e := Functor.mapDerivedCategoryCompIso A B ≪≫
    Functor.mapDerivedCategoryNatIso
      (SheafOfModules.overFunctorMap.{u} (moduleRings X.toRingedSpace) i)
  exact restriction_precomp A.mapDerivedCategory
    (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) W).mapDerivedCategory
    B.mapDerivedCategory e s β

private theorem transpose_restriction
    {C D H : Type*} [Category C] [Category D] [Category H]
    {F : C ⥤ D} {L : C ⥤ H} {G : D ⥤ C} {K : H ⥤ C}
    (a : F ⊣ G) (b : L ⊣ K) {E : C} (Y : D) (Z : H)
    (ρ : ∀ A : C, (F.obj A ⟶ Y) → (L.obj A ⟶ Z))
    (hρ : ∀ (A B : C) (f : A ⟶ B) g, ρ A (F.map f ≫ g) = L.map f ≫ ρ B g)
    (f : E ⟶ G.obj Y) :
    (b.homEquiv E Z).symm
        (f ≫ b.homEquiv (G.obj Y) Z (ρ _ ((a.homEquiv _ Y).symm (𝟙 _)))) =
      ρ E ((a.homEquiv E Y).symm f) := by
  rw [b.homEquiv_naturality_left_symm, Equiv.symm_apply_apply, ← hρ]
  have h := a.homEquiv_naturality_left_symm f (𝟙 (G.obj Y))
  rw [Category.comp_id] at h
  rw [← h]

private theorem boundary_of_adjunction_triangle
    {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [HasBinaryBiproducts C]
    {E N A B₁ B₂ : C} (d : N ⟶ A) (b : A ⟶ B₁ ⊞ B₂)
    (c : B₁ ⊞ B₂ ⟶ N⟦(1 : ℤ)⟧)
    (hT : Pretriangulated.Triangle.mk d b c ∈ distTriang C)
    {P Q P₁ P₂ : Type*} [AddCommGroup P] [AddCommGroup Q]
    [AddCommGroup P₁] [AddCommGroup P₂]
    (eW : (E ⟶ A) ≃+ P) (eO : (E ⟶ N) ≃+ Q)
    (eU : (E ⟶ B₁) ≃+ P₁) (eV : (E ⟶ B₂) ≃+ P₂)
    (ρU : P → P₁) (ρV : P → P₂)
    (hbU : ∀ f, eU (f ≫ b ≫ biprod.fst) = ρU (eW f))
    (hbV : ∀ f, eV (f ≫ b ≫ biprod.snd) = ρV (eW f))
    (aW : (E ⟶ E) → P → P) (aO : (E ⟶ E) → Q → Q)
    (hw : ∀ s f, eW (s ≫ f) = aW s (eW f))
    (ho : ∀ s f, eO (s ≫ f) = aO s (eO f)) :
    ∃ δ : Q →+ P,
      (∀ β, ρU β = 0 → ρV β = 0 → ∃ γ, δ γ = β) ∧
      ∀ s γ, δ (aO s γ) = aW s (δ γ) := by
  let δ : Q →+ P :=
    { toFun := fun γ ↦ eW (eO.symm γ ≫ d)
      map_zero' := by simp
      map_add' := by intro γ γ'; simp [Preadditive.add_comp] }
  refine ⟨δ, ?_, ?_⟩
  · intro β hU hV
    let f := eW.symm β
    have hf : eW f = β := eW.apply_symm_apply β
    have hfb : f ≫ b = 0 := by
      apply biprod.hom_ext
      · apply eU.injective
        simpa only [Category.assoc, zero_comp, map_zero, hbU, hf] using hU
      · apply eV.injective
        simpa only [Category.assoc, zero_comp, map_zero, hbV, hf] using hV
    obtain ⟨g, hg⟩ := (Pretriangulated.Triangle.mk d b c).coyoneda_exact₂ hT f hfb
    change f = g ≫ d at hg
    refine ⟨eO g, ?_⟩
    change eW (eO.symm (eO g) ≫ d) = β
    rw [eO.symm_apply_apply, ← hg]
    exact hf
  · intro s γ
    have hn : eO.symm (aO s γ) = s ≫ eO.symm γ := by
      apply eO.injective
      simp only [eO.apply_symm_apply, ho]
    change eW (eO.symm (aO s γ) ≫ d) = aW s (eW (eO.symm γ ≫ d))
    rw [hn, Category.assoc, hw]

/-- The boundary for Hom on an open union commutes with global scalar endomorphisms.
Its preceding term is Hom into the negative shift on the overlap. No compactness,
perfectness, quasi-coherence or support hypothesis is required.
Source: Stacks Project, Tag 08BW and the globalization paragraph of Tag 08EJ.
(blueprint: lem-sc-derived-open-hom-scalar-mayer-vietoris).

Proof: Apply the derived Hom Mayer--Vietoris sequence on W = U union V, using the
localized sites over U, V and their intersection. Associativity of restriction gives
the displayed restriction maps from the W term. The preceding negative Ext term is
identified, by the canonical shift comparison and shift-addition isomorphisms, with
Hom from E on the overlap into E'[k-1] there. Exactness at the W term gives the lift.
The sequence is natural contravariantly in E: in the triangle construction the boundary
is composition with the triangle's connecting morphism, and the extension/restriction
adjunction is natural. Apply this naturality to r times identity on the global E.
Restriction of this endomorphism is multiplication by the restricted r. This proves the
last equation, for every r, with the same additive boundary. Empty opens and k=0 are
included by the same triangle and shift identifications. -/
theorem derived_open_hom_scalar_mayer_vietoris
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (U V : X.Opens) (E E' : schemeDerivedCategory X) (k : ℤ) :
    let R := fun W : X.Opens ↦
      (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) W).mapDerivedCategory
    ∃ δ : ((R (U ⊓ V)).obj E ⟶ (R (U ⊓ V)).obj (E'⟦k - 1⟧)) →+
        ((R (U ⊔ V)).obj E ⟶ (R (U ⊔ V)).obj (E'⟦k⟧)),
      (∀ β : (R (U ⊔ V)).obj E ⟶ (R (U ⊔ V)).obj (E'⟦k⟧),
        derivedOpenHomRestriction X.toRingedSpace (homOfLE le_sup_left) β = 0 →
        derivedOpenHomRestriction X.toRingedSpace (homOfLE le_sup_right) β = 0 →
        ∃ γ, δ γ = β) ∧
      ∀ (r : RingCat.sectionsSubring (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat.{u})) γ,
        δ ((R (U ⊓ V)).map (schemeDerivedScalar X r (𝟙 E)) ≫ γ) =
          (R (U ⊔ V)).map (schemeDerivedScalar X r (𝟙 E)) ≫ δ γ := by
  classical
  let R := fun W : X.Opens ↦
    (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) W).mapDerivedCategory
  have h (W : X.Opens) : ∃ G, Nonempty (R W ⊣ G) := by
    exact open_derived_localization_adjunction X W
  choose G hG using h
  let adj (W : X.Opens) : R W ⊣ G W := (hG W).some
  let A := (G (U ⊔ V)).obj ((R (U ⊔ V)).obj (E'⟦k⟧))
  let β₀ := ((adj (U ⊔ V)).homEquiv A ((R (U ⊔ V)).obj (E'⟦k⟧))).symm (𝟙 A)
  let bU := (adj U).homEquiv A ((R U).obj (E'⟦k⟧))
    (derivedOpenHomRestriction X.toRingedSpace (homOfLE le_sup_left) β₀)
  let bV := (adj V).homEquiv A ((R V).obj (E'⟦k⟧))
    (derivedOpenHomRestriction X.toRingedSpace (homOfLE le_sup_right) β₀)
  let b := biprod.lift bU bV
  -- Bind the witnesses first to avoid generalizing these expressions through the goal.
  have htriangle := derived_open_union_adjunction_triangle X U V G adj E' k
  obtain ⟨d, c, hT⟩ := htriangle
  have hbU (f : E ⟶ A) :
      ((adj U).homEquiv E ((R U).obj (E'⟦k⟧))).symm (f ≫ b ≫ biprod.fst) =
        derivedOpenHomRestriction X.toRingedSpace (homOfLE le_sup_left)
          (((adj (U ⊔ V)).homEquiv E ((R (U ⊔ V)).obj (E'⟦k⟧))).symm f) := by
    simp only [b, biprod.lift_fst]
    exact transpose_restriction (adj (U ⊔ V)) (adj U) _ _
      (fun _ ↦ derivedOpenHomRestriction X.toRingedSpace (homOfLE le_sup_left))
      (fun _ _ f g ↦ derived_restriction_precomp X _ f g) f
  have hbV (f : E ⟶ A) :
      ((adj V).homEquiv E ((R V).obj (E'⟦k⟧))).symm (f ≫ b ≫ biprod.snd) =
        derivedOpenHomRestriction X.toRingedSpace (homOfLE le_sup_right)
          (((adj (U ⊔ V)).homEquiv E ((R (U ⊔ V)).obj (E'⟦k⟧))).symm f) := by
    simp only [b, biprod.lift_snd]
    exact transpose_restriction (adj (U ⊔ V)) (adj V) _ _
      (fun _ ↦ derivedOpenHomRestriction X.toRingedSpace (homOfLE le_sup_right))
      (fun _ _ f g ↦ derived_restriction_precomp X _ f g) f
  let eW := ((adj (U ⊔ V)).homAddEquiv E ((R (U ⊔ V)).obj (E'⟦k⟧))).symm
  let eO := ((adj (U ⊓ V)).homAddEquiv E ((R (U ⊓ V)).obj (E'⟦k - 1⟧))).symm
  let eU := ((adj U).homAddEquiv E ((R U).obj (E'⟦k⟧))).symm
  let eV := ((adj V).homAddEquiv E ((R V).obj (E'⟦k⟧))).symm
  have hboundary := boundary_of_adjunction_triangle d b c hT eW eO eU eV
    (derivedOpenHomRestriction X.toRingedSpace (homOfLE le_sup_left))
    (derivedOpenHomRestriction X.toRingedSpace (homOfLE le_sup_right))
    hbU hbV
    (fun s β ↦ (R (U ⊔ V)).map s ≫ β)
    (fun s γ ↦ (R (U ⊓ V)).map s ≫ γ)
    (fun s f ↦ (adj (U ⊔ V)).homEquiv_naturality_left_symm s f)
    (fun s f ↦ (adj (U ⊓ V)).homEquiv_naturality_left_symm s f)
  obtain ⟨δ, hex, hn⟩ := hboundary
  exact ⟨δ, hex, fun r γ ↦ hn (schemeDerivedScalar X r (𝟙 E)) γ⟩

end AlgebraicGeometry
