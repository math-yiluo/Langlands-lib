/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.CategoryTheory.Presentable.Finite
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.ConstructibleSheaf.FinitePushforward.Generators
public import WeilConjectures.ConstructibleSheaf.FinitePushforward.Presentation
public import WeilConjectures.ConstructibleSheaf.FinitePushforward.GenericPoint
public import WeilConjectures.ConstructibleSheaf.FinitePushforward.PointSplitting
public import WeilConjectures.SixFunctors.Etale.LowerShriek.FinitelyPresentable
import WeilConjectures.AlgebraicGeometry.ConstructibleLimitDescentGeneral
import Mathlib.CategoryTheory.Presentable.Directed
import Mathlib.CategoryTheory.Presentable.Limits
import WeilConjectures.AlgebraicGeometry.ConstructibleModuleNoetherianStalkDetector
import WeilConjectures.AlgebraicGeometry.ConstructibleModuleFiniteSelectionGeneral
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Constructible sheaves embed into finite pushforwards of constant sheaves

Let `U` be a quasi-compact and quasi-separated scheme and `C` a constructible sheaf of
`Λ`-modules on the small étale site of `U`, for a noetherian ring `Λ`. Then `C` embeds into a
finite direct sum `⨁ᵢ (hᵢ)_* Mᵢ` of pushforwards of constant sheaves with finitely generated
values `Mᵢ` along finite and finitely presented morphisms `hᵢ : Vᵢ ⟶ U` [Stacks 09Z7]. This is
the input to Gabber's effacement argument (`WeilConjectures.SixFunctors.Etale.Gabber`).

The proof goes through Noetherian approximation: the case of a Noetherian base [Stacks 09Z6]
uses that constructible sheaves are finitely presented objects of the category of sheaves
[Stacks 09Z4] and that the constant sheaf on a normal integral scheme is the pushforward of
its restriction to the generic point [Stacks 09Z5]; the general case descends `C` to a
Noetherian scheme and pulls the embedding back along the finite base change isomorphism
`AlgebraicGeometry.Etale.isIso_baseChangeMap_of_isFinite`.

The bounded constructible complexes of the blueprint (`def-weil-pbc-constructible-complexes`)
are `AlgebraicGeometry.Etale.DerivedCategory.boundedConstructible` of
`WeilConjectures.CategoryTheory.DerivedCategory.Constructible`.

## Main statements

- `AlgebraicGeometry.Etale.isIso_unit_constantSheaf_of_isIntegrallyClosed`: on a normal
  integral scheme the constant sheaf is the pushforward of its restriction to the generic
  point, or to a nonempty open subscheme.
- `AlgebraicGeometry.Etale.isFinitelyPresentable_of_isConstructibleSheaf`: constructible
  sheaves are finitely presentable.
- `AlgebraicGeometry.Etale.exists_mono_biproduct_lowerStar_of_isNoetherian`: the embedding
  over a Noetherian base.
- `AlgebraicGeometry.Etale.exists_isNoetherian_mono_biproduct_lowerStar`: Noetherian
  approximation of the embedding.
- `AlgebraicGeometry.Etale.exists_mono_biproduct_lowerStar`: the embedding over a
  quasi-compact quasi-separated base.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Étale sheaves of `Λ`-modules have finite biproducts (an abelian category has them; stated
explicitly since instance search times out on the general route). -/
noncomputable instance Etale.hasFiniteBiproducts_sheaf_moduleCat (X : Scheme.{u}) :
    HasFiniteBiproducts (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  HasFiniteBiproducts.of_hasFiniteProducts

section UnitComp

universe u'

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- The unit of `(h₁ ≫ h₂)^* ⊣ (h₁ ≫ h₂)_*` is the composite of the units of `h₂` and `h₁`, up to
the composition isomorphisms. -/
theorem Etale.unit_app_comp {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R)
    (F : Sheaf R.smallEtaleTopology A) :
    (upperStarLowerStarAdjunction A (h₁ ≫ h₂)).unit.app F ≫ (lowerStarComp A h₁ h₂).inv.app _ =
      ((upperStarLowerStarAdjunction A h₂).unit.app F ≫
        (h₂)_*[A].map ((upperStarLowerStarAdjunction A h₁).unit.app ((h₂)^*[A].obj F))) ≫
        (h₂)_*[A].map ((h₁)_*[A].map
          (((conjugateEquiv (upperStarLowerStarAdjunction A (h₁ ≫ h₂))
            ((upperStarLowerStarAdjunction A h₂).comp (upperStarLowerStarAdjunction A h₁))).symm
              (lowerStarComp A h₁ h₂).inv).app F)) := by
  rw [unit_conjugateEquiv_symm, Adjunction.comp_unit_app]
  rfl

/-- If the units of `h₁ ≫ h₂` at `F` and of `h₁` at `h₂^* F` are isomorphisms, so is the unit of
`h₂` at `F`. -/
theorem Etale.isIso_unit_app_of_comp {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R)
    (F : Sheaf R.smallEtaleTopology A)
    [IsIso ((upperStarLowerStarAdjunction A (h₁ ≫ h₂)).unit.app F)]
    [IsIso ((upperStarLowerStarAdjunction A h₁).unit.app ((h₂)^*[A].obj F))] :
    IsIso ((upperStarLowerStarAdjunction A h₂).unit.app F) := by
  have h := Etale.unit_app_comp A h₁ h₂ F
  have : IsIso ((upperStarLowerStarAdjunction A (h₁ ≫ h₂)).unit.app F ≫
      (lowerStarComp A h₁ h₂).inv.app _) := inferInstance
  rw [h] at this
  simpa only [isIso_comp_right_iff] using this

/-- If the units of `h₂` at `F` and of `h₁` at `h₂^* F` are isomorphisms, so is the unit of
`h₁ ≫ h₂` at `F`. -/
theorem Etale.isIso_unit_app_comp {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R)
    (F : Sheaf R.smallEtaleTopology A)
    [IsIso ((upperStarLowerStarAdjunction A h₂).unit.app F)]
    [IsIso ((upperStarLowerStarAdjunction A h₁).unit.app ((h₂)^*[A].obj F))] :
    IsIso ((upperStarLowerStarAdjunction A (h₁ ≫ h₂)).unit.app F) := by
  have h := Etale.unit_app_comp A h₁ h₂ F
  have : IsIso ((upperStarLowerStarAdjunction A (h₁ ≫ h₂)).unit.app F ≫
      (lowerStarComp A h₁ h₂ (h₁ ≫ h₂) rfl).inv.app _) := by
    rw [h]; infer_instance
  exact IsIso.of_isIso_comp_right _ ((lowerStarComp A h₁ h₂ (h₁ ≫ h₂) rfl).inv.app _)



/-- The unit of `g^* ⊣ g_*` along an isomorphism `g` is an isomorphism. -/
instance Etale.isIso_unit_app_of_isIso {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (F : Sheaf Y.smallEtaleTopology A) :
    IsIso ((upperStarLowerStarAdjunction A g).unit.app F) := by
  have := (upperStarLowerStarAdjunction A g).isEquivalence_left_of_isEquivalence_right
  infer_instance

end UnitComp

/-- **The open-immersion half of 09Z5 from the generic-point half.** Let `Y` be a normal integral
scheme and `j : U ⟶ Y` the inclusion of a nonempty open subscheme. If the unit
`M_Z ⟶ g_* g^* M_Z` along the generic point `g` is an isomorphism for every normal integral `Z`,
then the unit `M_Y ⟶ j_* j^* M_Y` is an isomorphism: the generic point of `Y` factors as the
generic point of `U` followed by `j`, up to the isomorphism of stalks at the generic point. -/
theorem Etale.isIso_unit_constantSheaf_of_isOpenImmersion_of_genericPoint
    (M : ModuleCat.{u + 1} Λ)
    (hgen : ∀ (Z : Scheme.{u}) [IsIntegral Z], (∀ z : Z, IsIntegrallyClosed (Z.presheaf.stalk z)) →
      IsIso ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
        (Z.fromSpecStalk (genericPoint Z))).unit.app
          ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)))
    {Y : Scheme.{u}} [IsIntegral Y] (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    {U : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j] [Nonempty U] :
    IsIso ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).unit.app
      ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) := by
  have : IsIntegral U := isIntegral_of_isOpenImmersion j
  have hU : ∀ x : U, IsIntegrallyClosed (U.presheaf.stalk x) := fun x ↦
    have := hY (j x)
    IsIntegrallyClosed.of_equiv (asIso (j.stalkMap x)).commRingCatIsoToRingEquiv
  let MY := (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M
  let gU := U.fromSpecStalk (genericPoint U)
  -- the unit of the generic point of `U` at `j^* M_Y ≅ M_U`
  have : IsIso ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) gU).unit.app
      ((j)^*[ModuleCat.{u + 1} Λ].obj MY)) :=
    (NatTrans.isIso_app_iff_of_iso _
      ((upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) j).app M)).2 (hgen U hU)
  -- the unit of the generic point of `Y`, through the point `j η_U = η_Y`
  have hη : j (genericPoint U) = genericPoint Y := genericPoint_eq_of_isOpenImmersion j
  have hY' : IsIso ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
      (Y.fromSpecStalk (j (genericPoint U)))).unit.app MY) := by
    rw [hη]
    exact hgen Y hY
  have : IsIso ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
      (Spec.map (j.stalkMap (genericPoint U)) ≫ Y.fromSpecStalk (j (genericPoint U)))).unit.app
        MY) :=
    Etale.isIso_unit_app_comp _ _ _ _
  rw [Scheme.SpecMap_stalkMap_fromSpecStalk] at this
  exact Etale.isIso_unit_app_of_comp _ gU j MY

/-- **Constant sheaves on a normal scheme.** Let `Y` be an integral scheme all of whose local
rings are integrally closed, `g : Spec K ⟶ Y` the inclusion of its generic point and `M` a
`Λ`-module. Then the unit `M_Y ⟶ g_* g^* M_Y = g_* M_{Spec K}` is an isomorphism; the same
holds for the inclusion of a nonempty open subscheme.

The blueprint states this for a finite abelian group `E`; the proof (the strict henselisation
of a normal local ring is a normal domain, so the generic fibre of `Spec 𝒪ˢʰ_{Y,ȳ}` is
irreducible) applies to an arbitrary value `M`.
(blueprint: lem-weil-pbc-normal-constant-generic)
-/
@[stacks 09Z5]
theorem Etale.isIso_unit_constantSheaf_of_isIntegrallyClosed {Y : Scheme.{u}} [IsIntegral Y]
    (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) (M : ModuleCat.{u + 1} Λ) :
    IsIso ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
        (Y.fromSpecStalk (genericPoint Y))).unit.app
          ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) ∧
      ∀ {U : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j] [Nonempty U],
        IsIso ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).unit.app
          ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) :=
  by
  -- The generic-point half: on the integral étale `Z`-schemes `W` the constant sections are
  -- `M`, and so are those over the one-point generic fibre `W ×_Z Spec K`.
  have hgen : ∀ (Z : Scheme.{u}) [IsIntegral Z],
      (∀ z : Z, IsIntegrallyClosed (Z.presheaf.stalk z)) →
        IsIso ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
          (Z.fromSpecStalk (genericPoint Z))).unit.app
            ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) :=
    fun Z _ hZ ↦ Etale.isIso_unit_constantSheaf_fromSpecStalk_genericPoint Z hZ M
  -- The open-immersion half follows from the generic-point half.
  exact ⟨hgen Y hY, fun j ↦
    Etale.isIso_unit_constantSheaf_of_isOpenImmersion_of_genericPoint Λ M hgen hY j⟩

attribute [local instance] Cardinal.fact_isRegular_aleph0 in
/-- A finite sum of extensions by zero of constant sheaves along étale morphisms from affine
schemes is finitely presentable. -/
theorem Etale.isFinitelyPresentable_sigma_etaleLowerShriek {X : Scheme.{u}} {n : ℕ}
    (U : Fin n → Scheme.{u}) (w : ∀ i, U i ⟶ X) (hw : ∀ i, Etale (w i))
    (hU : ∀ i, IsAffine (U i)) :
    IsFinitelyPresentable.{u} (∐ fun i ↦ (Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) (w i)
      (hw i)).obj ((constantSheaf (U i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (ModuleCat.of Λ Λ))) := by
  have (i : Fin n) : IsFinitelyPresentable.{u} ((Discrete.functor fun i ↦
      (Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) (w i) (hw i)).obj
        ((constantSheaf (U i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
          (ModuleCat.of Λ Λ))).obj ⟨i⟩) := by
    have := hU i
    exact Etale.isFinitelyPresentable_etaleLowerShriek_constantSheaf (w i) (hw i)
  exact isCardinalPresentable_of_isColimit' _ (colimit.isColimit _) _
    ((hasCardinalLT_aleph0_iff _).2 inferInstance)

attribute [local instance] Cardinal.fact_isRegular_aleph0 in
/-- **Constructible sheaves are finitely presentable.** On a quasi-compact quasi-separated
scheme `X`, with `Λ` Noetherian, a constructible sheaf of `Λ`-modules `F` is a finitely
presentable object of the category of sheaves: `Hom(F, -)` commutes with filtered colimits
(indexed by small categories), i.e. every morphism from `F` to a filtered colimit factors
through a stage, and two such factorisations agree at a later stage.

By Stacks 095N, `F` is a cokernel of a map between finite sums of extensions by zero `v_! Λ`
along étale maps from affine schemes; these are finitely presentable
(`AlgebraicGeometry.Etale.isFinitelyPresentable_etaleLowerShriek_constantSheaf`, by Stacks 0738),
and finitely presentable objects are closed under finite colimits.
(blueprint: lemma-finiteness-small-etale-topoi--1)
-/
@[stacks 09Z4]
theorem Etale.isFinitelyPresentable_of_isConstructibleSheaf [IsNoetherianRing Λ]
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf F] :
    IsFinitelyPresentable.{u} F := by
  -- Stacks 095N (`Etale.exists_presentation_of_isConstructibleSheaf`)
  obtain ⟨m, n, V, v, hv, hV, U, w, hw, hU, φ, π, hφπ, ⟨hc⟩⟩ :
      ∃ (m n : ℕ) (V : Fin m → Scheme.{u}) (v : ∀ j, V j ⟶ X) (hv : ∀ j, Etale (v j))
        (_ : ∀ j, IsAffine (V j)) (U : Fin n → Scheme.{u}) (w : ∀ i, U i ⟶ X)
        (hw : ∀ i, Etale (w i)) (_ : ∀ i, IsAffine (U i))
        (φ : (∐ fun j ↦ (Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) (v j) (hv j)).obj
          ((constantSheaf (V j).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
            (ModuleCat.of Λ Λ))) ⟶
          ∐ fun i ↦ (Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) (w i) (hw i)).obj
            ((constantSheaf (U i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
              (ModuleCat.of Λ Λ)))
        (π : (∐ fun i ↦ (Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) (w i) (hw i)).obj
            ((constantSheaf (U i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
              (ModuleCat.of Λ Λ))) ⟶ F)
        (hφπ : φ ≫ π = 0), Nonempty (IsColimit (CokernelCofork.ofπ π hφπ)) :=
    Etale.exists_presentation_of_isConstructibleSheaf F
  have := Etale.isFinitelyPresentable_sigma_etaleLowerShriek Λ V v hv hV
  have := Etale.isFinitelyPresentable_sigma_etaleLowerShriek Λ U w hw hU
  have (j : WalkingParallelPair) : IsFinitelyPresentable.{u} ((parallelPair φ 0).obj j) := by
    cases j <;> assumption
  exact isCardinalPresentable_of_isColimit' _ hc _ ((hasCardinalLT_aleph0_iff _).2 inferInstance)

/-- **The finite-pushforward embedding over a Noetherian base.** A constructible sheaf of
`Λ`-modules `C` on a Noetherian scheme `U` admits a monomorphism
`C ⟶ ⨁ᵢ (hᵢ)_* Mᵢ` into a finite direct sum of pushforwards of constant sheaves with finitely
generated values `Mᵢ` along finite morphisms `hᵢ : Vᵢ ⟶ U`, for `Λ` noetherian.
(blueprint: lemma-finiteness-small-etale-topoi--3)
-/
@[stacks 09Z6]
theorem Etale.exists_mono_biproduct_lowerStar_of_isNoetherian [IsNoetherianRing Λ]
    {U : Scheme.{u}} [IsNoetherian U]
    (C : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf C] :
    ∃ (r : ℕ) (V : Fin r → Scheme.{u}) (h : ∀ i, V i ⟶ U) (_ : ∀ i, IsFinite (h i))
      (M : Fin r → ModuleCat.{u + 1} Λ) (_ : ∀ i, Module.Finite Λ (M i))
      (φ : C ⟶ ⨁ fun i ↦ ((h i)_*[ModuleCat.{u + 1} Λ]).obj
        ((constantSheaf (V i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (M i))), Mono φ :=
  by
    classical
    obtain ⟨Y, f, hf, M, hM, ψ, hψ⟩ := exists_noetherian_stalk_detector Λ C
    let G (x : U) := (lowerStar (ModuleCat.{u + 1} Λ) (f x)).obj
      ((constantSheaf (Y x).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (M x))
    have htests : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (s : Spec (.of Ω) ⟶ U),
        ∃ x : U, Function.Injective
          (((Scheme.pointSmallEtale s).sheafFiber
            (A := ModuleCat.{u + 1} Λ)).map (ψ x)) := by
      intro Ω _ _ s
      exact ⟨((Scheme.SpecToEquivOfField Ω U) s).1, hψ _ Ω s rfl⟩
    obtain ⟨r, l, hφ⟩ :=
      Scheme.exists_mono_biproduct_of_constructible_module_stalk_injective_general
        Λ U C U G ψ htests
    exact ⟨r, fun i ↦ Y (l i), fun i ↦ f (l i), fun i ↦ hf (l i),
      fun i ↦ M (l i), fun i ↦ hM (l i), biproduct.lift (fun i ↦ ψ (l i)), hφ⟩

section Auxiliary

/-! ### Auxiliary lemmas -/

/-- The case of `AlgebraicGeometry.Etale.exists_isNoetherian_upperStar_iso` where `U` is already
Noetherian: take `U' = U` and `ν = 𝟙 U`. This is the trivial end of the Noetherian approximation;
the general case needs étale sheaves to descend along a limit `U = lim Uᵢ` (Stacks 01ZA). -/
theorem Etale.exists_isNoetherian_upperStar_iso_of_isNoetherian {U : Scheme.{u}} [IsNoetherian U]
    (C : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf C] :
    ∃ (U' : Scheme.{u}) (ν : U ⟶ U') (C' : Sheaf U'.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      IsNoetherian U' ∧ IsConstructibleSheaf C' ∧ Nonempty (((ν)^*[_]).obj C' ≅ C) :=
  ⟨U, 𝟙 U, C, inferInstance, inferInstance, ⟨(Etale.upperStarId _ U).app C⟩⟩

/-- **Descent of a constructible sheaf to a Noetherian scheme.** A constructible sheaf of
`Λ`-modules on a quasi-compact quasi-separated scheme `U`, for `Λ` noetherian, is the pullback
of a constructible sheaf on a Noetherian scheme `U'` along some morphism `U ⟶ U'`: its strata
are constructible and its finitely generated stalks finitely presented, so write `U` as a
cofiltered limit of schemes of finite type over `ℤ` with affine transition maps [Stacks 01ZA] and
descend the finitely many étale objects, sections and relations presenting `C` to one stage.
This is Step 2 of `lemma-finiteness-small-etale-topoi--3`. -/
theorem Etale.exists_isNoetherian_upperStar_iso [IsNoetherianRing Λ] {U : Scheme.{u}}
    [CompactSpace U]
    [QuasiSeparatedSpace U] (C : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsConstructibleSheaf C] :
    ∃ (U' : Scheme.{u}) (ν : U ⟶ U') (C' : Sheaf U'.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      IsNoetherian U' ∧ IsConstructibleSheaf C' ∧ Nonempty (((ν)^*[_]).obj C' ≅ C) :=
  by
    obtain ⟨N⟩ := U.nonempty_noetherianApproximation
    obtain ⟨I, hI, hd, hn, G, hG⟩ := IsFiltered.exists_directed N.Iᵒᵖ
    let := hI
    let := hd
    let := hn
    let := hG
    let D := G.leftOp ⋙ N.D
    let c := (Cone.mk U N.π).whisker G.leftOp
    have hc : IsLimit c := (Functor.Initial.isLimitWhiskerEquiv G.leftOp _).symm N.isLimit
    let : ∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f) :=
      fun {_ _} f ↦ N.isAffineHom_map (G.leftOp.map f)
    let : ∀ i : Iᵒᵖ, CompactSpace (D.obj i) :=
      fun i ↦ N.compactSpace_obj (G.leftOp.obj i)
    let : ∀ i : Iᵒᵖ, IsNoetherian (D.obj i) :=
      fun i ↦ N.isNoetherian_obj (G.leftOp.obj i)
    let : ∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i) :=
      fun i ↦ IsLocallyNoetherian.quasiSeparatedSpace
    obtain ⟨i, C', hC', e⟩ := Scheme.exists_constructible_limit_descent_general D c hc Λ C
    exact ⟨D.obj (Opposite.op i), c.π.app (Opposite.op i), C',
      N.isNoetherian_obj _, hC', e⟩

/-- **Pulling back a finite-pushforward embedding.** If `C'` on `U'` embeds into a finite sum
of pushforwards of constant sheaves along finite, finitely presented morphisms, then so does
its pullback along any `ν : U ⟶ U'`: pullback is exact, commutes with finite sums, and with
pushforward along finite morphisms (`AlgebraicGeometry.Etale.isIso_baseChangeMap_of_isFinite`),
and it preserves constant sheaves. 
(blueprint: lemma-finiteness-small-etale-topoi--3)
-/
theorem Etale.exists_mono_biproduct_lowerStar_upperStar {U U' : Scheme.{u}} (ν : U ⟶ U')
    (C' : Sheaf U'.smallEtaleTopology (ModuleCat.{u + 1} Λ)) {r : ℕ} (V : Fin r → Scheme.{u})
    (h : ∀ i, V i ⟶ U') [∀ i, IsFinite (h i)] [∀ i, LocallyOfFinitePresentation (h i)]
    (M : Fin r → ModuleCat.{u + 1} Λ)
    (φ : C' ⟶ ⨁ fun i ↦ ((h i)_*[ModuleCat.{u + 1} Λ]).obj
      ((constantSheaf (V i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (M i))) [Mono φ] :
    ∃ (V' : Fin r → Scheme.{u}) (h' : ∀ i, V' i ⟶ U) (_ : ∀ i, IsFinite (h' i))
      (_ : ∀ i, LocallyOfFinitePresentation (h' i))
      (φ' : ((ν)^*[_]).obj C' ⟶ ⨁ fun i ↦ ((h' i)_*[ModuleCat.{u + 1} Λ]).obj
        ((constantSheaf (V' i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (M i))), Mono φ' := by
  let sq (i : Fin r) := IsPullback.of_hasPullback (h i) ν
  have (i : Fin r) := Etale.isIso_baseChangeMap_of_isFinite (ModuleCat.{u + 1} Λ) (sq i)
  let e (i : Fin r) := asIso ((Etale.baseChangeMap (ModuleCat.{u + 1} Λ) (sq i).toCommSq).app
    ((constantSheaf (V i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (M i))) ≪≫
      ((pullback.snd (h i) ν)_*[ModuleCat.{u + 1} Λ]).mapIso
        ((upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) (pullback.fst (h i) ν)).app (M i))
  refine ⟨fun i ↦ pullback (h i) ν, fun i ↦ pullback.snd (h i) ν, fun _ ↦ inferInstance,
    fun _ ↦ inferInstance, ((ν)^*[_]).map φ ≫ (((ν)^*[_]).mapBiproduct _).hom ≫
      (biproduct.mapIso e).hom, inferInstance⟩

end Auxiliary

/-- **Noetherian approximation of the finite-pushforward embedding.** A constructible sheaf
of `Λ`-modules `C` on a quasi-compact quasi-separated scheme `U` is the pullback
`ν^* C' ≅ C` of a constructible sheaf `C'` on a Noetherian scheme `U'` along a morphism
`ν : U ⟶ U'`, and `C'` admits a monomorphism into a finite direct sum of pushforwards of
constant sheaves with finitely generated values along finite, finitely presented morphisms.

The blueprint takes `U'` to be a stage `U_λ` of an inverse system `U = lim U_λ` of Noetherian
schemes with affine transition maps; only the stage is used afterwards, so the inverse system
is not recorded. That the pullback of the embedding is an embedding of `C` is
`AlgebraicGeometry.Etale.exists_mono_biproduct_lowerStar`.
(blueprint: lemma-finiteness-small-etale-topoi--3)
-/
theorem Etale.exists_isNoetherian_mono_biproduct_lowerStar [IsNoetherianRing Λ] {U : Scheme.{u}}
    [CompactSpace U]
    [QuasiSeparatedSpace U] (C : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsConstructibleSheaf C] :
    ∃ (U' : Scheme.{u}) (ν : U ⟶ U') (C' : Sheaf U'.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      IsNoetherian U' ∧ IsConstructibleSheaf C' ∧ Nonempty (((ν)^*[_]).obj C' ≅ C) ∧
      ∃ (r : ℕ) (V : Fin r → Scheme.{u}) (h : ∀ i, V i ⟶ U') (_ : ∀ i, IsFinite (h i))
        (_ : ∀ i, LocallyOfFinitePresentation (h i))
        (M : Fin r → ModuleCat.{u + 1} Λ) (_ : ∀ i, Module.Finite Λ (M i))
        (φ : C' ⟶ ⨁ fun i ↦ ((h i)_*[ModuleCat.{u + 1} Λ]).obj
          ((constantSheaf (V i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (M i))), Mono φ := by
  obtain ⟨U', ν, C', hU', hC', e⟩ := Etale.exists_isNoetherian_upperStar_iso Λ C
  obtain ⟨r, V, h, hh, M, hM, φ, hφ⟩ := Etale.exists_mono_biproduct_lowerStar_of_isNoetherian Λ C'
  exact ⟨U', ν, C', hU', hC', e, r, V, h, hh, fun _ ↦ inferInstance, M, hM, φ, hφ⟩

/-- **Constructible sheaves embed into finite pushforwards.** A constructible sheaf of
`Λ`-modules `C` on a quasi-compact quasi-separated scheme `U` admits a monomorphism
`C ⟶ ⨁ᵢ (hᵢ)_* Mᵢ` into a finite direct sum of pushforwards of constant sheaves with finitely
generated values `Mᵢ` along finite and finitely presented morphisms `hᵢ : Vᵢ ⟶ U`, for `Λ`
noetherian. The blueprint states this for torsion sheaves, over a finite ring `Λ`, where the
`Mᵢ` are finite.
(blueprint: lemma-finiteness-small-etale-topoi--3)
-/
@[stacks 09Z7]
theorem Etale.exists_mono_biproduct_lowerStar [IsNoetherianRing Λ] {U : Scheme.{u}}
    [CompactSpace U]
    [QuasiSeparatedSpace U] (C : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsConstructibleSheaf C] :
    ∃ (r : ℕ) (V : Fin r → Scheme.{u}) (h : ∀ i, V i ⟶ U) (_ : ∀ i, IsFinite (h i))
      (_ : ∀ i, LocallyOfFinitePresentation (h i))
      (M : Fin r → ModuleCat.{u + 1} Λ) (_ : ∀ i, Module.Finite Λ (M i))
      (φ : C ⟶ ⨁ fun i ↦ ((h i)_*[ModuleCat.{u + 1} Λ]).obj
        ((constantSheaf (V i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (M i))), Mono φ := by
  obtain ⟨U', ν, C', -, -, ⟨e⟩, r, V, h, hh, hfp, M, hM, φ, hφ⟩ :=
    Etale.exists_isNoetherian_mono_biproduct_lowerStar Λ C
  obtain ⟨V', h', hh', hfp', φ', hφ'⟩ :=
    Etale.exists_mono_biproduct_lowerStar_upperStar Λ ν C' V h M φ
  exact ⟨r, V', h', hh', hfp', M, hM, e.inv ≫ φ', inferInstance⟩

end AlgebraicGeometry
