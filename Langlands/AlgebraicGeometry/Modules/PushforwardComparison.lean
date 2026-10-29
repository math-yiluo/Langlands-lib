import Langlands.AlgebraicGeometry.Modules.DerivedSections
import Langlands.Cohomology.AcyclicResolution.Comparison
import Langlands.Cohomology.AcyclicResolution.ComparisonProof

/-!
# Derived sections of a pushforward with vanishing higher direct images

Let `F : C ⥤ D` be left exact and `G : D ⥤ E` additive, and let `A : C` satisfy
`Rᵠ⁺¹ F A = 0` for all `q`. Then `F` applied to an injective resolution of `A` is a right
resolution of `F A`, and comparing it with an injective resolution of `F A` gives a map
`Rⁿ (F ⋙ G) A ⟶ Rⁿ G (F A)`. If `F` sends injective objects to `G`-acyclic objects, this map is
an isomorphism.

For schemes, `F` is the pushforward along `h : X ⟶ Y` and `G` is the `R`-module global
sections over `g : Y ⟶ Spec R`. The result is the map
`pushforwardComparison h g M hM n : Hⁿ_R(X, M) ⟶ Hⁿ_R(Y, h_* M)`, which is an isomorphism when
pushforwards along `h` of injective modules are acyclic for `R`-module global sections.
-/

noncomputable section

universe u v u' v' u'' v''

open CategoryTheory CategoryTheory.Limits HomologicalComplex AlgebraicGeometry

namespace Langlands.Cohomology.AcyclicResolution

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  {E : Type u''} [Category.{v''} E] [Abelian E]

section Augmentation

variable (F : C ⥤ D) [F.Additive] {A : C} (I : InjectiveResolution A)

/-- The augmentation `F A ⟶ F I⁰` of `F` applied to an injective resolution `I` of `A`. -/
def mapAugmentation :
    (CochainComplex.single₀ D).obj (F.obj A) ⟶ (F.mapHomologicalComplex _).obj I.cocomplex :=
  (CochainComplex.fromSingle₀Equiv _ _).symm
    ⟨F.map ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 A).inv ≫ I.ι.f 0), by
      rw [Functor.mapHomologicalComplex_obj_d, ← F.map_comp, Category.assoc,
        I.ι_f_zero_comp_complex_d, Limits.comp_zero, F.map_zero]⟩

@[simp]
lemma mapAugmentation_f_zero : (mapAugmentation F I).f 0 =
    F.map ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 A).inv ≫ I.ι.f 0) :=
  CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _

/-- If `F` is left exact and `Rᵠ⁺¹ F A = 0` for all `q`, then `F` applied to an injective
resolution of `A` is a right resolution of `F A`. -/
theorem quasiIso_mapAugmentation [HasInjectiveResolutions C] [PreservesFiniteLimits F]
    (hA : ∀ q : ℕ, IsZero ((F.rightDerived (q + 1)).obj A)) :
    QuasiIso (mapAugmentation F I) := ⟨fun n => by
  cases n with
  | zero =>
    rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros]
    · have hF := I.exact₀.map_of_mono_of_preservesKernel F inferInstance inferInstance
      refine ⟨ShortComplex.exact_of_iso
        (S₁ := (ShortComplex.mk _ _ I.ι_f_zero_comp_complex_d).map F) (ShortComplex.isoMk
          (F.mapIso (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 A) ≪≫
            (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (F.obj A)).symm)
          (Iso.refl _) (Iso.refl _) ?_ ?_) hF, ?_⟩
      · change (_ ≫ _) ≫ (mapAugmentation F I).f 0 = F.map (I.ι.f 0) ≫ 𝟙 _
        have h₁ : (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (F.obj A)).inv =
            𝟙 _ := rfl
        rw [mapAugmentation_f_zero, Functor.mapIso_hom, Iso.symm_hom, h₁]
        have key : (F.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 A).hom ≫
            𝟙 (F.obj A)) ≫ F.map ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 A).inv ≫
              I.ι.f 0) = F.map (I.ι.f 0) := by
          rw [Category.comp_id, ← F.map_comp, Iso.hom_inv_id_assoc]
        exact key.trans (Category.comp_id _).symm
      · exact (Category.id_comp _).trans (Category.comp_id _).symm
      · change Mono ((mapAugmentation F I).f 0)
        rw [mapAugmentation_f_zero]
        have : Mono ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 A).inv ≫
            I.ι.f 0) := mono_comp _ _
        exact F.map_mono _
    all_goals first | rfl | exact ((F.mapHomologicalComplex _).obj I.cocomplex).shape 0 0 (by simp)
  | succ q =>
    rw [quasiIsoAt_iff_exactAt _ _ (CochainComplex.exactAt_succ_single_obj _ _),
      HomologicalComplex.exactAt_iff_isZero_homology]
    exact (hA q).of_iso (I.isoRightDerivedObj F (q + 1)).symm⟩

end Augmentation

section Composite

variable [HasInjectiveResolutions C] [HasInjectiveResolutions D]
  {F : C ⥤ D} [F.Additive] [PreservesFiniteLimits F] (G : D ⥤ E) [G.Additive]
  {H : C ⥤ E} [H.Additive] (e : F ⋙ G ≅ H)

/-- For `e : F ⋙ G ≅ H` and `A` with `Rᵠ⁺¹ F A = 0` for all `q`, the map
`Rⁿ H A ⟶ Rⁿ G (F A)`: identify `Rⁿ H A` with `Hⁿ(G (F I))` for the chosen injective resolution
`I` of `A`, then apply the comparison of the right resolution `F I` of `F A`. -/
def compComparison (A : C) (hA : ∀ q : ℕ, IsZero ((F.rightDerived (q + 1)).obj A)) (n : ℕ) :
    (H.rightDerived n).obj A ⟶ (G.rightDerived n).obj (F.obj A) :=
  haveI := quasiIso_mapAugmentation F (injectiveResolution A) hA
  ((injectiveResolution A).isoRightDerivedObj H n).hom ≫
    (HomologicalComplex.homologyFunctor E _ n).map
      ((Functor.mapHomologicalComplexCompIso e _).inv.app (injectiveResolution A).cocomplex) ≫
    resolutionComparison G (mapAugmentation F (injectiveResolution A)) n

/-- If `F` sends injective objects to `G`-acyclic objects, `compComparison` is an
isomorphism. -/
theorem isIso_compComparison [PreservesFiniteLimits G] (A : C)
    (hA : ∀ q : ℕ, IsZero ((F.rightDerived (q + 1)).obj A))
    (hG : ∀ J : C, Injective J → ∀ q : ℕ, IsZero ((G.rightDerived (q + 1)).obj (F.obj J)))
    (n : ℕ) :
    IsIso (compComparison G e A hA n) := by
  have := quasiIso_mapAugmentation F (injectiveResolution A) hA
  have key := (acyclicResolutionComparisonStatement D E G (F.obj A) _
    (mapAugmentation F (injectiveResolution A)) inferInstance
    (fun i q => hG _ inferInstance q) (injectiveResolution (F.obj A)) _
    (comp_lift_id _ _)).2 n
  have : IsIso (resolutionComparison G (mapAugmentation F (injectiveResolution A)) n) := key
  unfold compComparison
  infer_instance

end Composite

end Langlands.Cohomology.AcyclicResolution

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

open Langlands.Cohomology.AcyclicResolution

variable {X Y : Scheme.{u}} (h : X ⟶ Y) {R : CommRingCat.{u}} (g : Y ⟶ Spec R)

/-- `R`-module global sections along `h ≫ g` are `R`-module global sections along `g` of the
pushforward along `h`. -/
def relativeGlobalSectionsCompIso :
    Scheme.Modules.pushforward h ⋙ relativeGlobalSections g ≅ relativeGlobalSections (h ≫ g) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Scheme.Modules.pushforwardComp h g) moduleSpecΓFunctor

/-- For `M : X.Modules` with vanishing higher direct images `Rᵠ⁺¹ h_* M`, the map
`Hⁿ_R(X, M) ⟶ Hⁿ_R(Y, h_* M)` of `R`-module cohomology, with `X` over `Spec R` via `h ≫ g`. -/
def pushforwardComparison (M : X.Modules)
    (hM : ∀ q : ℕ, IsZero ((higherDirectImage h (q + 1)).obj M)) (n : ℕ) :
    (relativeCohomology (h ≫ g) n).obj M ⟶
      (relativeCohomology g n).obj ((Scheme.Modules.pushforward h).obj M) :=
  compComparison (relativeGlobalSections g) (relativeGlobalSectionsCompIso h g) M hM n

/-- If pushforwards along `h` of injective modules are acyclic for `R`-module global sections,
then `pushforwardComparison` is an isomorphism. -/
theorem isIso_pushforwardComparison (M : X.Modules)
    (hM : ∀ q : ℕ, IsZero ((higherDirectImage h (q + 1)).obj M))
    (hJ : ∀ J : X.Modules, Injective J → ∀ q : ℕ,
      IsZero ((relativeCohomology g (q + 1)).obj ((Scheme.Modules.pushforward h).obj J)))
    (n : ℕ) :
    IsIso (pushforwardComparison h g M hM n) :=
  isIso_compComparison _ _ M hM hJ n

end Langlands.AlgebraicGeometry.Modules.DerivedSections
