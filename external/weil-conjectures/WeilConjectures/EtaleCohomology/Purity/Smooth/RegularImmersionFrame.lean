/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.RegularImmersion
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerProductBaseChange
public import WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Frames of a closed immersion and their classes

A *frame* of a closed immersion `i : Z ⟶ X` of codimension `c`
(`AlgebraicGeometry.Scheme.Hom.EtaleFrame`) is an étale `e : U ⟶ X` with functions
`f₁, …, f_c` on `U` generating the ideal of `Z ×_X U`. Its *class* is the cup product with
supports `∂κ(f₁) ∪ ⋯ ∪ ∂κ(f_c) ∈ H^{2c}_{Z_U}(U, Λ(c))` of the Kummer boundaries
(`AlgebraicGeometry.Etale.frameClass`), and a class with supports on `Z` restricts to every frame
(`AlgebraicGeometry.Etale.frameRestriction`). These are the local pieces from which the
fundamental class of a regular closed immersion (`lemma-class-of-point--1`) and of a section of a
smooth morphism are glued.

## Main definitions

- `AlgebraicGeometry.Scheme.Hom.EtaleFrame`: a frame of a closed immersion.
- `AlgebraicGeometry.Etale.frameClass`: the class of a frame.
- `AlgebraicGeometry.Etale.frameRestriction`: the restriction of a class with supports to a frame.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.exists_etaleFrame_isOpenImmersion`: a regular closed immersion
  has Zariski frames given by regular sequences.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory ZeroObject

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Scheme.Hom

variable {X Z : Scheme.{u}}

/-- A *frame* of a closed immersion `i : Z ⟶ X` of codimension `c`: an étale `e : U ⟶ X`
together with functions `f₁, …, f_c ∈ Γ(U, 𝒪_U)` generating the ideal of `Z_U = Z ×_X U`,
recorded as a pullback square

```
  V(f₁, …, f_c) ───toZ───▶ Z
        │                  │
  zeroLocusSubschemeι      │ i
        ▼                  ▼
        U ────────e──────▶ X
```

whose left side is the closed subscheme cut out by the `f_a`
(`AlgebraicGeometry.Scheme.zeroLocusSubschemeι`). Frames exist étale-locally (indeed
Zariski-locally) for a regular closed immersion. -/
structure EtaleFrame (c : ℕ) (i : Z ⟶ X) where
  /-- The source of the étale map. -/
  U : Scheme.{u}
  /-- The étale map `e : U ⟶ X`. -/
  e : U ⟶ X
  /-- `e` is étale. -/
  etale : AlgebraicGeometry.Etale e
  /-- The functions `f₁, …, f_c` on `U`. -/
  f : Fin c → Γ(U, ⊤)
  /-- The map from the closed subscheme `V(f₁, …, f_c)` to `Z`. -/
  toZ : U.zeroLocusSubscheme (Set.range f) ⟶ Z
  /-- `V(f₁, …, f_c)` is the base change `Z ×_X U`: the `f_a` generate the ideal of `Z_U`. -/
  isPullback : IsPullback toZ (U.zeroLocusSubschemeι (Set.range f)) i e

attribute [instance] EtaleFrame.etale

/-- The Zariski frame of a closed immersion `i : Z ⟶ X` given by functions `f₁, …, f_c` on an
affine open `U` of `X` generating the ideal of `Z ∩ U`: the étale map is the inclusion of `U`,
and `V(f₁, …, f_c) ⊆ U` is identified with `Z ∩ U`. -/
noncomputable def EtaleFrame.ofSpanEq {c : ℕ} (i : Z ⟶ X) [IsClosedImmersion i]
    (U : X.affineOpens) (f : Fin c → Γ(X, U.1))
    (hf : Ideal.span (Set.range f) = (Scheme.Hom.ker i).ideal U) : i.EtaleFrame c :=
  have hker : (i ∣_ U.1).ker = (U.1.toScheme.zeroLocusSubschemeι
      (Set.range fun a ↦ U.1.topIso.inv (f a))).ker := by
    have : IsAffine U.1.toScheme := U.2
    rw [IdealSheafData.ker_subschemeι]
    refine IdealSheafData.ext_of_isAffine ?_
    rw [IdealSheafData.ideal_top_ofIdealTop, ker_morphismRestrict_ideal,
      ← IdealSheafData.map_ideal' i.ker (U := ⟨_, _⟩) (V := U)
        (eqToHom U.1.ι_image_top).op, ← hf, Ideal.map_span]
    congr 1
    ext x
    simp only [Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨a, by simp [Scheme.Opens.topIso]; rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨f a, ⟨a, rfl⟩, by simp [Scheme.Opens.topIso]; rfl⟩
  let φ := IsClosedImmersion.lift (U.1.toScheme.zeroLocusSubschemeι
    (Set.range fun a ↦ U.1.topIso.inv (f a))) (i ∣_ U.1) hker.ge
  have hφ : φ ≫ U.1.toScheme.zeroLocusSubschemeι (Set.range fun a ↦ U.1.topIso.inv (f a)) =
      i ∣_ U.1 :=
    IsClosedImmersion.lift_fac _ _ _
  have : IsIso φ := IsClosedImmersion.isIso_of_ker_eq _ _ φ hφ hker
  { U := U.1.toScheme
    e := U.1.ι
    etale := inferInstance
    f a := U.1.topIso.inv (f a)
    toZ := inv φ ≫ (i ⁻¹ᵁ U.1).ι
    isPullback := by
      refine IsPullback.of_iso (isPullback_morphismRestrict i U.1).flip (asIso φ) (Iso.refl _)
        (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_ <;> simp [hφ] }

instance EtaleFrame.isOpenImmersion_ofSpanEq {c : ℕ} (i : Z ⟶ X) [IsClosedImmersion i]
    (U : X.affineOpens) (f : Fin c → Γ(X, U.1))
    (hf : Ideal.span (Set.range f) = (Scheme.Hom.ker i).ideal U) :
    IsOpenImmersion (EtaleFrame.ofSpanEq i U f hf).e :=
  inferInstanceAs (IsOpenImmersion U.1.ι)

instance EtaleFrame.isAffine_ofSpanEq {c : ℕ} (i : Z ⟶ X) [IsClosedImmersion i]
    (U : X.affineOpens) (f : Fin c → Γ(X, U.1))
    (hf : Ideal.span (Set.range f) = (Scheme.Hom.ker i).ideal U) :
    IsAffine (EtaleFrame.ofSpanEq i U f hf).U :=
  U.2

/-- The points of `Z ∩ U` lie in the zero locus of the frame `EtaleFrame.ofSpanEq`. -/
lemma EtaleFrame.mem_range_ofSpanEq_toZ {c : ℕ} (i : Z ⟶ X) [IsClosedImmersion i]
    (U : X.affineOpens) (f : Fin c → Γ(X, U.1))
    (hf : Ideal.span (Set.range f) = (Scheme.Hom.ker i).ideal U) {z : Z} (hz : i.base z ∈ U.1) :
    z ∈ Set.range (EtaleFrame.ofSpanEq i U f hf).toZ := by
  obtain ⟨p, hp⟩ : i.base z ∈ Set.range U.1.ι.base := by rw [Scheme.Opens.range_ι]; exact hz
  obtain ⟨q, hq, -⟩ := (EtaleFrame.ofSpanEq i U f hf).isPullback.exists_scheme_point z p hp.symm
  exact ⟨q, hq⟩

/-- Blueprint `lemma-class-of-point--1`: Purity for regular closed immersions

*Frames exist Zariski-locally.* Every point of `Z` lies in the zero locus of a frame of a regular
closed immersion `i : Z ⟶ X` of codimension `c` whose étale map is the inclusion of an affine
open `U ⊆ X`: the ideal of `Z` is generated on `U` by a regular sequence `f₁, …, f_c`. -/
theorem exists_etaleFrame_isOpenImmersion (c : ℕ) (i : Z ⟶ X)
    [IsRegularImmersion c i] (z : Z) :
    ∃ F : i.EtaleFrame c, IsOpenImmersion F.e ∧ z ∈ Set.range F.toZ ∧ IsAffine F.U ∧
      RingTheory.Sequence.IsWeaklyRegular Γ(F.U, ⊤) (List.ofFn F.f) := by
  obtain ⟨U, hzU, r, hr, hreg, hI⟩ :=
    IsRegularImmersion.exists_isWeaklyRegular_generators (c := c) (i := i) (i z)
  let f : Fin c → Γ(X, U.1) := fun a ↦ r.get (a.cast hr.symm)
  have hf : Ideal.span (Set.range f) = (Scheme.Hom.ker i).ideal U := by
    rw [← hI, Ideal.ofList]
    congr 1
    ext x
    simp only [Set.mem_range, Set.mem_ofPred_eq, f]
    constructor
    · rintro ⟨a, rfl⟩
      exact List.get_mem _ _
    · intro hx
      obtain ⟨a, rfl⟩ := List.mem_iff_get.mp hx
      exact ⟨a.cast hr, rfl⟩
  refine ⟨EtaleFrame.ofSpanEq i U f hf, inferInstance,
    EtaleFrame.mem_range_ofSpanEq_toZ i U f hf hzU, inferInstance, ?_⟩
  have hf' : List.ofFn (EtaleFrame.ofSpanEq i U f hf).f = r.map U.1.topIso.inv.hom := by
    refine List.ext_get (by simp [hr]) fun n h₁ h₂ ↦ ?_
    simp [EtaleFrame.ofSpanEq, f]
  rw [hf']
  exact hreg.map_of_flat (RingHom.Flat.of_bijective
    (ConcreteCategory.bijective_of_isIso U.1.topIso.inv))

/-- A frame of the base change `i'` of `i` along an étale `e` is a frame of `i`, through the
composite étale map. -/
@[simps]
noncomputable def EtaleFrame.ofIsPullback {c : ℕ} {i : Z ⟶ X} {X' Z' : Scheme.{u}} {i' : Z' ⟶ X'}
    {e : X' ⟶ X} [AlgebraicGeometry.Etale e] {g : Z' ⟶ Z} (hg : IsPullback g i' i e)
    (F : i'.EtaleFrame c) : i.EtaleFrame c where
  U := F.U
  e := F.e ≫ e
  etale := inferInstance
  f := F.f
  toZ := F.toZ ≫ g
  isPullback := F.isPullback.paste_horiz hg

/-- The frame of the closed subscheme `V(f₁, …, f_c) ⊂ U` cut out by functions on `U` given by an
étale `j : W ⟶ U` and the pulled back functions `j^* f_a`. -/
noncomputable def EtaleFrame.ofFunctions {c : ℕ} {U W : Scheme.{u}} (f : Fin c → Γ(U, ⊤))
    (j : W ⟶ U) [AlgebraicGeometry.Etale j] :
    (U.zeroLocusSubschemeι (Set.range f)).EtaleFrame c where
  U := W
  e := j
  etale := inferInstance
  f a := j.appTop (f a)
  toZ := j.zeroLocusSubschemeMap (Set.range f) (Set.range fun a ↦ j.appTop (f a))
    (by rw [← Set.range_comp]; rfl)
  isPullback := isPullback_zeroLocusSubschemeι j (Set.range f)
    (Set.range fun a ↦ j.appTop (f a)) (by rw [← Set.range_comp]; rfl)
end Scheme.Hom

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] {X Z : Scheme.{u}}

section FrameClass

variable [Finite Λ] {c : ℕ} {i : Z ⟶ X}

/-- The exponent of `Λ` stays invertible on the domain of an étale frame. -/
instance _root_.AlgebraicGeometry.Scheme.Hom.EtaleFrame.hasInvertibleExponent
    [HasInvertibleExponent Λ X] (F : i.EtaleFrame c) : HasInvertibleExponent Λ F.U :=
  .of_hom F.e

attribute [local instance] HasInvertibleExponent.opens

/-- The *class of a frame* `(e : U ⟶ X, f₁, …, f_c)` of `Z`:

`cl(f) = ∂κ(f₁) ∪ ⋯ ∪ ∂κ(f_c) ∈ H^{2c}_{Z_U}(U, Λ(c)) = Hom(Λ_U, Ri_{U!} Ri_U^! (Λ_U(c)[2c]))`,

the iterated cup product with supports of the Kummer boundaries
(`AlgebraicGeometry.Etale.kummerBoundaryProduct`), supported on
`V(f₁) ∩ ⋯ ∩ V(f_c) = Z_U`. -/
noncomputable def frameClass [HasKummerClass Λ] [HasInvertibleExponent Λ X] (F : i.EtaleFrame c) :
    constantComplex Λ F.U ⟶
      (R(F.U.zeroLocusSubschemeι (Set.range F.f))_![ModuleCat.{u + 1} Λ]).obj
        ((R(F.U.zeroLocusSubschemeι (Set.range F.f))^![Λ]).obj
          ((tateObject Λ F.U c)⟦2 * (c : ℤ)⟧)) :=
  kummerBoundaryProduct Λ F.f

/-- The restriction of a class `γ ∈ H^{2c}_Z(X, Λ(c))` to a frame `(e : U ⟶ X, f)`, a class in
`H^{2c}_{Z_U}(U, Λ(c))`: the restriction of supports along the étale `e`
(`AlgebraicGeometry.Etale.restrictSupportedClass`), with `Λ_U ≅ Le^* Λ_X` and
`Le^* (Λ_X(c)[2c]) ≅ Λ_U(c)[2c]`. -/
noncomputable def frameRestriction [HasTateTwist Λ] [IsClosedImmersion i]
    [HasInvertibleExponent Λ X] (F : i.EtaleFrame c)
    (γ : constantComplex Λ X ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj
      ((R(i)^![Λ]).obj ((tateObject Λ X c)⟦2 * (c : ℤ)⟧))) :
    constantComplex Λ F.U ⟶
      (R(F.U.zeroLocusSubschemeι (Set.range F.f))_![ModuleCat.{u + 1} Λ]).obj
        ((R(F.U.zeroLocusSubschemeι (Set.range F.f))^![Λ]).obj
          ((tateObject Λ F.U c)⟦2 * (c : ℤ)⟧)) :=
  restrictSupportedClass Λ F.e i _ F.toZ F.isPullback
    (leftDerivedUpperStarConstantComplexIso Λ F.e).inv (leftDerivedUpperStarTateShiftIso Λ F.e c) γ

/-- A frame class restricts to the frame class of the pulled back functions. -/
lemma frameRestriction_kummerBoundaryProduct [HasKummerClass Λ] {U W : Scheme.{u}}
    [HasInvertibleExponent Λ U] (f : Fin c → Γ(U, ⊤)) (j : W ⟶ U) [AlgebraicGeometry.Etale j] :
    frameRestriction Λ (Scheme.Hom.EtaleFrame.ofFunctions f j) (kummerBoundaryProduct Λ f) =
      frameClass Λ (Scheme.Hom.EtaleFrame.ofFunctions f j) := by
  have : HasInvertibleExponent Λ W := .of_hom j
  exact restrictSupportedClass_kummerBoundaryProduct Λ j f _ (fun _ ↦ rfl) _ _

/-- Restriction of classes with supports along a composite `e' = e₁ ≫ e`, with the standard
identifications of the constant and Tate complexes: restricting `γ` along `e'` is restricting it
along `e` and then along `e₁`.
```
  H^{2c}_Z(U, Λ(c)) ---- e^* ----> H^{2c}_{Z'}(U', Λ(c))
          \                               |
           \ e'^*                         | e₁^*
            \                             v
             ------------------> H^{2c}_{Z₂}(U₂, Λ(c))
```
-/
lemma restrictSupportedClass_comp_tateShift [HasKummerClass Λ] {U U' U₂ Z Z' Z₂ : Scheme.{u}}
    [HasInvertibleExponent Λ U] [HasInvertibleExponent Λ U'] [HasInvertibleExponent Λ U₂]
    (e₁ : U₂ ⟶ U') (e : U' ⟶ U)
    (e' : U₂ ⟶ U) (he : e' = e₁ ≫ e)
    (i : Z ⟶ U) (i' : Z' ⟶ U') (i₂ : Z₂ ⟶ U₂) [IsClosedImmersion i] [IsClosedImmersion i']
    [IsClosedImmersion i₂] (g : Z' ⟶ Z) (hg : IsPullback g i' i e)
    (g₂ : Z₂ ⟶ Z') (hg₂ : IsPullback g₂ i₂ i' e₁) (g' : Z₂ ⟶ Z) (hg' : IsPullback g' i₂ i e')
    (γ : constantComplex Λ U ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj
      ((R(i)^![Λ]).obj ((tateObject Λ U c)⟦2 * (c : ℤ)⟧))) :
    restrictSupportedClass Λ e' i i₂ g' hg'
        (leftDerivedUpperStarConstantComplexIso Λ e').inv
        (leftDerivedUpperStarTateShiftIso Λ e' c) γ =
      restrictSupportedClass Λ e₁ i' i₂ g₂ hg₂
        (leftDerivedUpperStarConstantComplexIso Λ e₁).inv (leftDerivedUpperStarTateShiftIso Λ e₁ c)
        (restrictSupportedClass Λ e i i' g hg
          (leftDerivedUpperStarConstantComplexIso Λ e).inv
          (leftDerivedUpperStarTateShiftIso Λ e c) γ) := by
  rw [leftDerivedUpperStarConstantComplexIso_comp Λ e₁ e _ he,
    leftDerivedUpperStarTateShiftIso_comp Λ e₁ e _ he]
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Category.assoc]
  exact restrictSupportedClass_restrictSupportedClass Λ e e₁ e' he i
    i' i₂ g hg g₂ hg₂ g' hg' _ _ _ _ γ

/-- A local class `δ : Le^* Λ_X ⟶ Le^* (Ri_! Ri^! Λ(c)[2c])` corresponding to the class `β` with
supports on `U` restricts along `a : W ⟶ U` to the restriction of `β`:
```
  Λ_W ≅ Lw^* Λ_X ≅ La^* Le^* Λ_X --La^* δ--> La^* Le^* Ri_! Ri^! Λ(c)[2c]
     \                                                  |
      \                                                 | ≅ Lw^*, restriction of supports
       \                                                v
        ------ restriction of β along a ------> Ri'_! Ri'^! Λ(c)[2c]
```
-/
lemma constantComplexIso_inv_comp_leftDerivedUpperStarComp_map_supportedRestriction
    [HasKummerClass Λ]
    {U W X Z Z₁ Z' : Scheme.{u}} [HasInvertibleExponent Λ U] [HasInvertibleExponent Λ W]
    [HasInvertibleExponent Λ X] (e : U ⟶ X) (a : W ⟶ U) (w : W ⟶ X) (hw : w = a ≫ e)
    (i : Z ⟶ X) (i₁ : Z₁ ⟶ U) (i' : Z' ⟶ W) [IsClosedImmersion i] [IsClosedImmersion i₁]
    [IsClosedImmersion i'] (g₁ : Z₁ ⟶ Z) (hg₁ : IsPullback g₁ i₁ i e) (g₂ : Z' ⟶ Z₁)
    (hg₂ : IsPullback g₂ i' i₁ a) (g' : Z' ⟶ Z) (hg' : IsPullback g' i' i w)
    (δ : (L((e)^*[ModuleCat.{u + 1} Λ])).obj (constantComplex Λ X) ⟶
      (L((e)^*[ModuleCat.{u + 1} Λ])).obj ((R(i)_![ModuleCat.{u + 1} Λ]).obj
        ((R(i)^![Λ]).obj ((tateObject Λ X c)⟦2 * (c : ℤ)⟧))))
    (β : constantComplex Λ U ⟶ (R(i₁)_![ModuleCat.{u + 1} Λ]).obj
      ((R(i₁)^![Λ]).obj ((tateObject Λ U c)⟦2 * (c : ℤ)⟧)))
    (hδ : δ ≫ supportedRestriction _ e i i₁ g₁ hg₁ _ _ (leftDerivedUpperStarTateShiftIso Λ e c) =
      (leftDerivedUpperStarConstantComplexIso Λ e).hom ≫ β) :
    (leftDerivedUpperStarConstantComplexIso Λ w).inv ≫
        (leftDerivedUpperStarComp _ a e w hw).hom.app _ ≫ (L((a)^*[_])).map δ ≫
          (leftDerivedUpperStarComp _ a e w hw).inv.app _ ≫
            supportedRestriction _ w i i' g' hg' _ _ (leftDerivedUpperStarTateShiftIso Λ w c) =
      restrictSupportedClass Λ a i₁ i' g₂ hg₂
        (leftDerivedUpperStarConstantComplexIso Λ a).inv (leftDerivedUpperStarTateShiftIso Λ a c)
        β := by
  have ht := supportedRestriction_trans Λ e a w hw i i₁ i' g₁ hg₁ g₂ hg₂
    g' hg' _ _ _ (leftDerivedUpperStarTateShiftIso Λ e c) (leftDerivedUpperStarTateShiftIso Λ a c)
  rw [← leftDerivedUpperStarTateShiftIso_comp Λ a e w hw] at ht
  rw [ht, leftDerivedUpperStarConstantComplexIso_comp Λ a e w hw]
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Category.assoc,
    Iso.inv_hom_id_app_assoc]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, Category.assoc, hδ,
    Iso.inv_hom_id_assoc]
  rfl
end FrameClass

end Etale

end AlgebraicGeometry
