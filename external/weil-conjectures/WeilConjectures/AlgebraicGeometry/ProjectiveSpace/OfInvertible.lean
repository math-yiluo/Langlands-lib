/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.EffectiveCartier
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LinearProjection
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import WeilConjectures.Mathlib.AlgebraicGeometry.Gluing

/-!
# Morphisms into projective space given by sections of a module

Let `M` be an `𝒪_X`-module and `s : n → Γ(X, M)` a family of global sections such that each
`s i` is a free generator of `M` on an open `U i`, the `U i` covering `X`. On `U i` every
`s j` is a multiple `rᵢⱼ • s i`, and the coordinates `rᵢⱼ` (with `rᵢᵢ = 1`) define morphisms
`U i ⟶ ℙ(n; S)` over any `g : X ⟶ S` (`AlgebraicGeometry.ProjectiveSpace.homOfSections`). Since
`rₗⱼ = rₗᵢ rᵢⱼ` on `U i ⊓ U l`, they glue to a morphism `φ : X ⟶ ℙ(n; S)` pulling `Tⱼ / Tᵢ`
back to `rᵢⱼ`, and `φ^* 𝒪(1) ≅ M` by an isomorphism sending `φ^* Tⱼ` to `s j`.

## Main definitions

- `AlgebraicGeometry.ProjectiveSpace.homOfIsFreeGenerator`: the morphism `X ⟶ ℙ(n; S)`.
- `AlgebraicGeometry.ProjectiveSpace.twistRestrictHom`: the isomorphism `φ^* 𝒪(1) ⟶ M`.

## Main results

- `AlgebraicGeometry.ProjectiveSpace.homOfIsFreeGenerator_appLE_coordRatio`: `φ` pulls the ratio
  `Tⱼ / Tᵢ` back to `rᵢⱼ`.
- `AlgebraicGeometry.ProjectiveSpace.twistRestrictHom_app_pullbackSection`: `φ^* Tⱼ ↦ s j`.
- `AlgebraicGeometry.ProjectiveSpace.exists_hom_twistRestrict`: the packaged statement.
-/

@[expose] public section

universe u

open CategoryTheory Limits MvPolynomial

noncomputable section

namespace AlgebraicGeometry

namespace ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

private lemma appLE_eq_of_eq {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (U V e) :
    f.appLE U V e = g.appLE U V (h ▸ e) := by
  subst h
  rfl

/-- The ratio `Tⱼ / Tᵢ` of homogeneous coordinates, as a function on the standard open
`D₊(Tᵢ)` of `ℙ(n; S)`. -/
def coordRatio (n : Type u) (S : Scheme.{u}) (i j : n) : Γ(ℙ(n; S), standardOpen n S i) :=
  (toProjInt n S).app _ (Proj.awayToSection _ (MvPolynomial.X i)
    (awayXRatio (ULift.{u} ℤ) i j))

/-- If the `i`-th section is `1`, the morphism `homOfSections g s hs` pulls the ratio
`Tⱼ / Tᵢ` back to the section `s j`. -/
lemma homOfSections_appLE_coordRatio {Y : Scheme.{u}} (g : Y ⟶ S) (s : n → Γ(Y, ⊤))
    (hs : Ideal.span (Set.range s) = ⊤) {i : n} (hsi : s i = 1) (j : n) (e) :
    (homOfSections g s hs).appLE (standardOpen n S i) ⊤ e (coordRatio n S i j) = s j := by
  obtain ⟨q, hq, hq'⟩ := Proj.exists_comp_awayι_eq_fromOfGlobalSections _ (evalSections s)
    (map_irrelevant_evalSections_eq_top s hs) Nat.one_pos
    (X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) i) (by rw [evalSections_X, hsi])
  have h : homOfSections g s hs ≫ toProjInt n S = q ≫ Proj.awayι _ (MvPolynomial.X i)
      (X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) i) Nat.one_pos := by
    rw [homOfSections_toProjInt, hq]
  have h2 := Proj.comp_awayι_appLE_awayToSection _
    (X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) i) Nat.one_pos q (h ▸ e)
    (awayXRatio (ULift.{u} ℤ) i j)
  rw [← appLE_eq_of_eq h, Scheme.Hom.comp_appLE] at h2
  refine h2.trans ((hq' 1 (MvPolynomial.X j) _).trans (evalSections_X s j))

open Scheme.Modules

section Construction

variable {X S : Scheme.{u}} {n : Type u} {M : X.Modules} (s : n → Γ(M, ⊤)) (U : n → X.Opens)
  (hs : ∀ i, IsFreeGenerator (M.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op (s i)))

/-- The coefficient of `s j` with respect to the free generator `s i` on `U i`. -/
def sectionRatio (i j : n) : Γ(X, U i) :=
  (hs i).coeff (M.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op (s j))

lemma sectionRatio_smul (i j : n) :
    sectionRatio s U hs i j • M.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op (s i) =
      M.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op (s j) :=
  (hs i).coeff_smul _

@[simp]
lemma sectionRatio_self (i : n) : sectionRatio s U hs i i = 1 :=
  ((hs i).coeff_eq_iff _ 1).mpr (one_smul _ _)

/-- On `W ⊆ U i`, the section `s j` is the restriction of `sectionRatio i j` times `s i`. -/
lemma sectionRatio_map_smul {W : X.Opens} (i j : n) (h : W ≤ U i) :
    X.presheaf.map (homOfLE h).op (sectionRatio s U hs i j) •
        M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (s i) =
      M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (s j) := by
  have := presheaf_map_homOfLE_eq_smul (le_top : U i ≤ ⊤) h (sectionRatio_smul s U hs i j).symm
  exact this.symm

/-- The cocycle relation `rₗⱼ = rₗᵢ rᵢⱼ` on `U i ⊓ U l`. -/
lemma sectionRatio_mul {W : X.Opens} (i l j : n) (hi : W ≤ U i) (hl : W ≤ U l) :
    X.presheaf.map (homOfLE hl).op (sectionRatio s U hs l i) *
        X.presheaf.map (homOfLE hi).op (sectionRatio s U hs i j) =
      X.presheaf.map (homOfLE hl).op (sectionRatio s U hs l j) := by
  refine ((hs l).map hl).smul_left_injective ?_
  simp only [presheaf_map_homOfLE_map_homOfLE]
  rw [sectionRatio_map_smul s U hs l j hl, mul_comm, mul_smul,
    sectionRatio_map_smul s U hs l i hl, sectionRatio_map_smul s U hs i j hi]

/-- The family of sections `rᵢⱼ` of `U i`, as global sections of the scheme `U i`. -/
def localSections (i : n) : n → Γ(U i, ⊤) := fun j ↦ (U i).topIso.inv (sectionRatio s U hs i j)

lemma span_range_localSections (i : n) : Ideal.span (Set.range (localSections s U hs i)) = ⊤ :=
  (Ideal.eq_top_iff_one _).mpr (Ideal.subset_span ⟨i, by simp [localSections]⟩)

variable (g : X ⟶ S)

/-- The morphism `U i ⟶ ℙ(n; S)` given by the coordinates `rᵢⱼ`. -/
def localHom (i : n) : (U i).toScheme ⟶ ℙ(n; S) :=
  homOfSections ((U i).ι ≫ g) (localSections s U hs i) (span_range_localSections s U hs i)

lemma localHom_compat (i l : n) :
    X.homOfLE (inf_le_left : U i ⊓ U l ≤ U i) ≫ localHom s U hs g i =
      X.homOfLE (inf_le_right : U i ⊓ U l ≤ U l) ≫ localHom s U hs g l := by
  rw [localHom, localHom, comp_homOfSections, comp_homOfSections, X.homOfLE_ι_assoc,
    X.homOfLE_ι_assoc]
  have hu : IsUnit ((U i ⊓ U l).topIso.inv
      (X.presheaf.map (homOfLE inf_le_right).op (sectionRatio s U hs l i))) := by
    refine IsUnit.of_mul_eq_one ((U i ⊓ U l).topIso.inv
      (X.presheaf.map (homOfLE inf_le_left).op (sectionRatio s U hs i l))) ?_
    rw [← map_mul, sectionRatio_mul s U hs i l l inf_le_left inf_le_right, sectionRatio_self,
      map_one, map_one]
  refine homOfSections_eq_of_unit_mul _ hu.unit _ _ fun j ↦ ?_
  simp only [localSections, Scheme.homOfLE_appTop_topIso_inv, IsUnit.unit_spec, ← map_mul]
  rw [sectionRatio_mul s U hs i l j inf_le_left inf_le_right]

variable (hU : ⨆ i, U i = ⊤)

/-- The morphism `X ⟶ ℙ(n; S)` over `g` given by global sections `s i` of a module `M` such
that `s i` is a free generator of `M` on `U i`, for an open cover `U` of `X`: on `U i` it is
given by the coordinates `rᵢⱼ` with `s j = rᵢⱼ • s i`. -/
def homOfIsFreeGenerator : X ⟶ ℙ(n; S) :=
  Scheme.Opens.glueMorphismsOfTop U hU (localHom s U hs g) (localHom_compat s U hs g)

@[reassoc]
lemma ι_homOfIsFreeGenerator (i : n) :
    (U i).ι ≫ homOfIsFreeGenerator s U hs g hU = localHom s U hs g i :=
  Scheme.Opens.ι_glueMorphismsOfTop ..

@[reassoc (attr := simp)]
lemma homOfIsFreeGenerator_over : homOfIsFreeGenerator s U hs g hU ≫ ℙ(n; S) ↘ S = g :=
  Scheme.Opens.hom_ext_of_iSup_eq_top U hU _ _ fun i ↦ by
    rw [ι_homOfIsFreeGenerator_assoc, localHom, homOfSections_over]

lemma le_preimage_standardOpen (i : n) :
    U i ≤ homOfIsFreeGenerator s U hs g hU ⁻¹ᵁ standardOpen n S i := by
  intro x hx
  have h : (U i).ι ⁻¹ᵁ (homOfIsFreeGenerator s U hs g hU ⁻¹ᵁ standardOpen n S i) = ⊤ := by
    rw [← Scheme.Hom.comp_preimage, ι_homOfIsFreeGenerator, localHom,
      homOfSections_preimage_standardOpen]
    simp [localSections]
  have : (⟨x, hx⟩ : U i) ∈ (U i).ι ⁻¹ᵁ (homOfIsFreeGenerator s U hs g hU ⁻¹ᵁ
      standardOpen n S i) := h ▸ trivial
  exact this

private lemma topIso_inv_appLE {Y : Scheme.{u}} (f : X ⟶ Y) (W : X.Opens) (V : Y.Opens)
    (e : W ≤ f ⁻¹ᵁ V) (x : Γ(Y, V)) :
    W.topIso.inv (f.appLE V W e x) =
      (W.ι ≫ f).appLE V ⊤ (by rw [Scheme.Hom.comp_preimage]; exact fun y _ ↦ e y.2) x := by
  rw [Scheme.Hom.comp_appLE, Scheme.Opens.ι_appLE]
  simp only [Scheme.Hom.appLE, Scheme.Opens.topIso_inv]
  rw [← ConcreteCategory.comp_apply, Category.assoc, ← Functor.map_comp]
  rfl

/-- `homOfIsFreeGenerator` pulls the ratio `Tⱼ / Tᵢ` back to `rᵢⱼ` on `U i`. -/
lemma homOfIsFreeGenerator_appLE_coordRatio (i j : n) :
    (homOfIsFreeGenerator s U hs g hU).appLE (standardOpen n S i) (U i)
        (le_preimage_standardOpen s U hs g hU i) (coordRatio n S i j) =
      sectionRatio s U hs i j := by
  have h := topIso_inv_appLE _ _ _ (le_preimage_standardOpen s U hs g hU i) (coordRatio n S i j)
  rw [appLE_eq_of_eq (ι_homOfIsFreeGenerator s U hs g hU i)] at h
  have h2 := h.trans (homOfSections_appLE_coordRatio ((U i).ι ≫ g) (localSections s U hs i)
    (span_range_localSections s U hs i) (i := i) (by simp [localSections]) j _)
  exact (ConcreteCategory.bijective_of_isIso (U i).topIso.inv).1 h2

/-- The pullback `φ^* Tᵢ` is `rⱼᵢ • φ^* Tⱼ` on `U j`. -/
lemma pullbackSection_twistOneSection_map_eq_sectionRatio_smul (i j : n) {W : X.Opens}
    (hWj : W ≤ U j) :
    (twistRestrict (homOfIsFreeGenerator s U hs g hU) 1).presheaf.map
        (homOfLE (fun _ _ ↦ trivial : W ≤ homOfIsFreeGenerator s U hs g hU ⁻¹ᵁ ⊤)).op
        (pullbackSection _ (twistOneSection n S i)) =
      X.presheaf.map (homOfLE hWj).op (sectionRatio s U hs j i) •
        (twistRestrict (homOfIsFreeGenerator s U hs g hU) 1).presheaf.map
          (homOfLE (fun _ _ ↦ trivial : W ≤ homOfIsFreeGenerator s U hs g hU ⁻¹ᵁ ⊤)).op
          (pullbackSection _ (twistOneSection n S j)) := by
  have H := pullbackSection_twistOneSection_map_eq_smul (homOfIsFreeGenerator s U hs g hU) i j
  have H' := presheaf_map_homOfLE_eq_smul _
    (hWj.trans (le_preimage_standardOpen s U hs g hU j)) H
  refine H'.trans ?_
  congr 1
  rw [← homOfIsFreeGenerator_appLE_coordRatio s U hs g hU j i, Scheme.Hom.appLE,
    CommRingCat.comp_apply, Scheme.presheaf_map_map_apply]
  rfl

/-- The pullback of `Tᵢ`, restricted to `U i`. -/
def pullbackCoord (i : n) : Γ(twistRestrict (homOfIsFreeGenerator s U hs g hU) 1, U i) :=
  (twistRestrict (homOfIsFreeGenerator s U hs g hU) 1).presheaf.map
    (homOfLE (fun _ _ ↦ trivial : U i ≤ homOfIsFreeGenerator s U hs g hU ⁻¹ᵁ ⊤)).op
    (pullbackSection _ (twistOneSection n S i))

lemma isFreeGenerator_pullbackCoord (i : n) :
    IsFreeGenerator (pullbackCoord s U hs g hU i) := by
  have h := (isFreeGenerator_pullbackSection_twistOneSection
    (homOfIsFreeGenerator s U hs g hU) i).map (le_preimage_standardOpen s U hs g hU i)
  rwa [presheaf_map_homOfLE_map_homOfLE] at h

lemma pullbackCoord_map {i : n} {W : X.Opens} (h : W ≤ U i) :
    (twistRestrict (homOfIsFreeGenerator s U hs g hU) 1).presheaf.map (homOfLE h).op
        (pullbackCoord s U hs g hU i) =
      (twistRestrict (homOfIsFreeGenerator s U hs g hU) 1).presheaf.map
        (homOfLE (fun _ _ ↦ trivial : W ≤ homOfIsFreeGenerator s U hs g hU ⁻¹ᵁ ⊤)).op
        (pullbackSection _ (twistOneSection n S i)) :=
  presheaf_map_homOfLE_map_homOfLE _ _ _

lemma restrict_section_map {i : n} {W : X.Opens} (h : W ≤ U i) :
    M.presheaf.map (homOfLE h).op (M.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op (s i)) =
      M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (s i) :=
  presheaf_map_homOfLE_map_homOfLE _ _ _

lemma pullbackCoord_transition (i j : n) (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j)
    (a b : Γ(X, W))
    (hab : a • (twistRestrict (homOfIsFreeGenerator s U hs g hU) 1).presheaf.map (homOfLE hi).op
        (pullbackCoord s U hs g hU i) =
      b • (twistRestrict (homOfIsFreeGenerator s U hs g hU) 1).presheaf.map (homOfLE hj).op
        (pullbackCoord s U hs g hU j)) :
    a • M.presheaf.map (homOfLE hi).op (M.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op (s i)) =
      b • M.presheaf.map (homOfLE hj).op
        (M.presheaf.map (homOfLE (le_top : U j ≤ ⊤)).op (s j)) := by
  rw [pullbackCoord_map, pullbackCoord_map,
    pullbackSection_twistOneSection_map_eq_sectionRatio_smul s U hs g hU i j hj, smul_smul] at hab
  rw [← pullbackCoord_map s U hs g hU hj] at hab
  have hb := ((isFreeGenerator_pullbackCoord s U hs g hU j).map hj).smul_left_injective hab
  rw [restrict_section_map, restrict_section_map, ← hb,
    ← sectionRatio_map_smul s U hs j i hj, smul_smul]

/-- The morphism `φ^* 𝒪(1) ⟶ M` sending `φ^* Tᵢ` to `s i`. -/
def twistRestrictHom : twistRestrict (homOfIsFreeGenerator s U hs g hU) 1 ⟶ M :=
  glueHom hU (isFreeGenerator_pullbackCoord s U hs g hU) (pullbackCoord_transition s U hs g hU)

lemma twistRestrictHom_app_pullbackCoord (i : n) :
    (twistRestrictHom s U hs g hU).app (U i) (pullbackCoord s U hs g hU i) =
      M.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op (s i) := by
  refine (isGlueValue_glueHom_app hU (isFreeGenerator_pullbackCoord s U hs g hU)
    (pullbackCoord_transition s U hs g hU) _).unique hU
    (isFreeGenerator_pullbackCoord s U hs g hU) fun l W hW hWl a ha ↦ ?_
  have := pullbackCoord_transition s U hs g hU l i W hWl hW a 1 (by rw [one_smul]; exact ha)
  rw [one_smul] at this
  exact this.symm

instance : IsIso (twistRestrictHom s U hs g hU) := by
  refine Scheme.Modules.isIso_of_isFreeGenerator _ fun x ↦ ?_
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hU.ge (Set.mem_univ x))
  exact ⟨U i, pullbackCoord s U hs g hU i, hi, isFreeGenerator_pullbackCoord s U hs g hU i,
    (twistRestrictHom_app_pullbackCoord s U hs g hU i).symm ▸ hs i⟩

lemma twistRestrictHom_app_pullbackSection (j : n) :
    (twistRestrictHom s U hs g hU).app _ (pullbackSection _ (twistOneSection n S j)) =
      M.presheaf.map (homOfLE (le_top : homOfIsFreeGenerator s U hs g hU ⁻¹ᵁ ⊤ ≤ ⊤)).op
        (s j) := by
  refine (isGlueValue_glueHom_app hU (isFreeGenerator_pullbackCoord s U hs g hU)
    (pullbackCoord_transition s U hs g hU) _).unique hU
    (isFreeGenerator_pullbackCoord s U hs g hU) fun i W hW hWi a ha ↦ ?_
  have hT := pullbackSection_twistOneSection_map_eq_sectionRatio_smul s U hs g hU j i hWi
  rw [pullbackCoord_map] at ha
  have ha'' := ha.trans hT
  rw [← pullbackCoord_map s U hs g hU hWi] at ha''
  have ha' := ((isFreeGenerator_pullbackCoord s U hs g hU i).map hWi).smul_left_injective ha''
  rw [presheaf_map_homOfLE_map_homOfLE, restrict_section_map, ha',
    sectionRatio_map_smul s U hs i j hWi]

include hs hU in
/-- The packaged construction: a family of global sections of `M`, each a free generator of `M`
on a member of an open cover, defines a morphism `φ : X ⟶ ℙ(n; S)` over `g` together with an
isomorphism `φ^* 𝒪(1) ≅ M` sending `φ^* Tⱼ` to `s j`. -/
theorem exists_hom_twistRestrict :
    ∃ φ : X ⟶ ℙ(n; S), φ ≫ ℙ(n; S) ↘ S = g ∧ ∃ ε : twistRestrict φ 1 ⟶ M, IsIso ε ∧
      ∀ j, ε.app _ (pullbackSection φ (twistOneSection n S j)) =
        M.presheaf.map (homOfLE (le_top : φ ⁻¹ᵁ ⊤ ≤ ⊤)).op (s j) :=
  ⟨homOfIsFreeGenerator s U hs g hU, homOfIsFreeGenerator_over s U hs g hU,
    twistRestrictHom s U hs g hU, inferInstance, twistRestrictHom_app_pullbackSection s U hs g hU⟩

end Construction

section Sections

variable {X S : Scheme.{u}} {n : Type u} {M : X.Modules} {s : n → Γ(M, ⊤)}
  {φ : X ⟶ ℙ(n; S)} (ε : twistRestrict φ 1 ⟶ M) [IsIso ε]
  (hε : ∀ j, ε.app _ (pullbackSection φ (twistOneSection n S j)) =
    M.presheaf.map (homOfLE (le_top : φ ⁻¹ᵁ ⊤ ≤ ⊤)).op (s j))
include hε

/-- If `φ^* 𝒪(1) ≅ M` sends `φ^* Tᵢ` to `s i`, then `s i` is a free generator of `M` on the
preimage of the standard open `D₊(Tᵢ)`. -/
lemma isFreeGenerator_of_twistRestrict_iso (i : n) :
    IsFreeGenerator (M.presheaf.map (homOfLE (le_top : φ ⁻¹ᵁ standardOpen n S i ≤ ⊤)).op
      (s i)) := by
  have h := (isFreeGenerator_pullbackSection_twistOneSection φ i).app_hom (asIso ε)
  rwa [asIso_hom, Hom.app_presheaf_map, hε, presheaf_map_homOfLE_map_homOfLE] at h

omit [IsIso ε] in
/-- If `φ^* 𝒪(1) ≅ M` sends `φ^* Tᵢ` to `s i`, then on the preimage of `D₊(Tᵢ)` the section
`s j` is `φ^*(Tⱼ / Tᵢ) • s i`. -/
lemma map_eq_coordRatio_smul_of_twistRestrict_iso (i j : n) :
    M.presheaf.map (homOfLE (le_top : φ ⁻¹ᵁ standardOpen n S i ≤ ⊤)).op (s j) =
      φ.app (standardOpen n S i) (coordRatio n S i j) •
        M.presheaf.map (homOfLE (le_top : φ ⁻¹ᵁ standardOpen n S i ≤ ⊤)).op (s i) := by
  have h := congrArg (ε.app _) (pullbackSection_twistOneSection_map_eq_smul φ j i)
  rwa [Hom.app_smul, Hom.app_presheaf_map, Hom.app_presheaf_map, hε, hε,
    presheaf_map_homOfLE_map_homOfLE, presheaf_map_homOfLE_map_homOfLE] at h

end Sections

end ProjectiveSpace

end AlgebraicGeometry

end
