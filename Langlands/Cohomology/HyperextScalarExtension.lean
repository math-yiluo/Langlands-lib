import Langlands.Cohomology.DivisibleSystem.SmoothScalarExtension
import Langlands.Cohomology.ExactDerivedHomology
import Langlands.Representation.Category.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Mathlib.Algebra.Homology.DerivedCategory.Linear
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RingTheory.Flat.Basic

/-!
# Extension of scalars and comparison maps on hyperext groups

Let `R → S` be an algebra of commutative rings. This module compares the groups of morphisms
used in the hyperext spectral sequence over `R` with the corresponding groups over `S`.

* `repExtendScalars_map_exact`, `smoothRepExtendScalars_map_exact`: if `S` is flat over `R`,
  extension of scalars `V ↦ S ⊗[R] V` of (smooth) representations sends exact short complexes
  to exact short complexes. Hence it preserves homology, finite limits and finite colimits
  (instances), so it is an exact functor and Mathlib's `Functor.mapDerivedCategory` applies.
* `HyperextScalarExtension.IsSemilinear R S F`: a functor `F` from an `R`-linear to an
  `S`-linear category with `F.map (r • f) = algebraMap R S r • F.map f`. Extension of scalars
  of (smooth) representations is semilinear.
* For an exact semilinear functor `F`, the `S`-linear maps
  `extBaseChangeMap : S ⊗[R] Ext^n(X, Y) → Ext^n(F X, F Y)`,
  `abutmentBaseChangeMap : S ⊗[R] Hom(K, W₀⟦n⟧) → Hom(F K, (F W)₀⟦n⟧)` and
  `cohomologyHomBaseChangeMap : S ⊗[R] Hom(H^q K, W) → Hom(H^q (F K), F W)`, where `W₀` is `W`
  placed in degree `0` and `F K` is the image of `K` under `F.mapDerivedCategory`.
* `smoothExtBaseChangeMap`, `smoothAbutmentBaseChangeMap`, `smoothCohomologyHomBaseChangeMap`:
  these maps for extension of scalars of smooth representations along a flat `R → S`.

The comparison maps are not claimed to be isomorphisms. See `HyperextScalarExtension.md`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits TensorProduct

namespace Langlands.Cohomology

universe w uR uS uG uC vC uD vD t t' s s'

section Exact

variable (R : Type uR) [CommRing R] (S : Type uS) [CommRing S] [Algebra R S]
  (G : Type uG) [Monoid G]

/-- Extension of scalars along a flat algebra `R → S` sends exact short complexes of
representations to exact short complexes. -/
theorem repExtendScalars_map_exact [Module.Flat R S] (T : ShortComplex (Rep.{w} R G))
    (hT : T.Exact) : (T.map (repExtendScalars R S G)).Exact := by
  rw [← ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep.{max uS w} S G) (ModuleCat S)),
    ShortComplex.moduleCat_exact_iff_range_eq_ker, eq_comm, ← LinearMap.exact_iff]
  rw [← ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep.{w} R G) (ModuleCat R)),
    ShortComplex.moduleCat_exact_iff_range_eq_ker, eq_comm, ← LinearMap.exact_iff] at hT
  have h := Module.Flat.lTensor_exact S hT
  rw [← LinearMap.baseChange_eq_ltensor, ← LinearMap.baseChange_eq_ltensor] at h
  exact h

instance repExtendScalars_preservesHomology [Module.Flat R S] :
    (repExtendScalars.{w} R S G).PreservesHomology :=
  Functor.preservesHomology_of_map_exact _ (repExtendScalars_map_exact R S G)

instance repExtendScalars_preservesFiniteLimits [Module.Flat R S] :
    PreservesFiniteLimits (repExtendScalars.{w} R S G) :=
  Functor.preservesFiniteLimits_of_preservesHomology _

instance repExtendScalars_preservesFiniteColimits [Module.Flat R S] :
    PreservesFiniteColimits (repExtendScalars.{w} R S G) :=
  Functor.preservesFiniteColimits_of_preservesHomology _

end Exact

section SmoothExact

variable (R : Type uR) [CommRing R] (S : Type uS) [CommRing S] [Algebra R S]
  (G : Type uG) [Group G] [TopologicalSpace G]

/-- The inclusion of smooth representations into all representations preserves kernels and
cokernels, because smooth representations are closed under both. -/
instance smoothRepToRep_preservesHomology :
    (SmoothRep.toRep : SmoothRep.{uR, uG, w} R G ⥤ Rep.{w} R G).PreservesHomology where
  preservesKernels := (smoothRepProperty.{uR, uG, w} R G).preservesKernels_ι
  preservesCokernels := (smoothRepProperty.{uR, uG, w} R G).preservesCokernels_ι

/-- Extension of scalars along a flat algebra `R → S` sends exact short complexes of smooth
representations to exact short complexes. -/
theorem smoothRepExtendScalars_map_exact [Module.Flat R S]
    (T : ShortComplex (SmoothRep.{uR, uG, w} R G)) (hT : T.Exact) :
    (T.map (smoothRepExtendScalars.{w} R S G)).Exact := by
  exact (ShortComplex.exact_map_iff_of_faithful _
    (SmoothRep.toRep : SmoothRep.{uS, uG, max uS w} S G ⥤ Rep.{max uS w} S G)).1
    (repExtendScalars_map_exact R S G (T.map SmoothRep.toRep)
      ((ShortComplex.exact_map_iff_of_faithful T
        (SmoothRep.toRep : SmoothRep.{uR, uG, w} R G ⥤ Rep.{w} R G)).2 hT))

instance smoothRepExtendScalars_preservesHomology [Module.Flat R S] :
    (smoothRepExtendScalars.{w} R S G).PreservesHomology :=
  Functor.preservesHomology_of_map_exact _ (smoothRepExtendScalars_map_exact R S G)

instance smoothRepExtendScalars_preservesFiniteLimits [Module.Flat R S] :
    PreservesFiniteLimits (smoothRepExtendScalars.{w} R S G) :=
  Functor.preservesFiniteLimits_of_preservesHomology _

instance smoothRepExtendScalars_preservesFiniteColimits [Module.Flat R S] :
    PreservesFiniteColimits (smoothRepExtendScalars.{w} R S G) :=
  Functor.preservesFiniteColimits_of_preservesHomology _

end SmoothExact

namespace HyperextScalarExtension

section Lift

variable {R : Type uR} [CommRing R] {S : Type uS} [CommRing S] [Algebra R S]

/-- The `S`-linear map `S ⊗[R] M → N`, `s ⊗ m ↦ s • φ m`, induced by an additive map
`φ : M → N` from an `R`-module to an `S`-module with `φ (r • m) = algebraMap R S r • φ m`. -/
def baseChangeLift {M : Type*} {N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module S N] (φ : M →+ N) (hφ : ∀ (r : R) (m : M), φ (r • m) = algebraMap R S r • φ m) :
    S ⊗[R] M →ₗ[S] N :=
  letI : Module R N := Module.compHom N (algebraMap R S)
  haveI : IsScalarTower R S N := ⟨fun r s n => by rw [Algebra.smul_def, mul_smul]; rfl⟩
  LinearMap.liftBaseChange S
    { toFun := φ
      map_add' := φ.map_add
      map_smul' := hφ }

@[simp]
theorem baseChangeLift_tmul {M : Type*} {N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module S N] (φ : M →+ N)
    (hφ : ∀ (r : R) (m : M), φ (r • m) = algebraMap R S r • φ m) (s : S) (m : M) :
    baseChangeLift φ hφ (s ⊗ₜ m) = s • φ m := rfl

end Lift

section Semilinear

variable (R : Type uR) [CommRing R] (S : Type uS) [CommRing S] [Algebra R S]
variable {C : Type uC} [Category.{vC} C] [Abelian C] [Linear R C]
variable {D : Type uD} [Category.{vD} D] [Abelian D] [Linear S D]

/-- A functor from an `R`-linear category to an `S`-linear category is semilinear along
`algebraMap R S` if `F.map (r • f) = algebraMap R S r • F.map f` for all `r : R` and all
morphisms `f`. -/
def IsSemilinear (F : C ⥤ D) : Prop :=
  ∀ ⦃X Y : C⦄ (r : R) (f : X ⟶ Y), F.map (r • f) = algebraMap R S r • F.map f

variable {R S} (F : C ⥤ D)

/-- A semilinear functor sends `r • 𝟙 X` to `algebraMap R S r • 𝟙 (F.obj X)`. -/
theorem IsSemilinear.map_smul_id (hF : IsSemilinear R S F) (r : R) (X : C) :
    F.map (r • 𝟙 X) = algebraMap R S r • 𝟙 (F.obj X) := by
  rw [hF, CategoryTheory.Functor.map_id]

variable [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

section Ext

variable [HasExt.{t} C] [HasExt.{t'} D]

/-- Mathlib's map `Ext^n(X, Y) → Ext^n(F X, F Y)` of an exact semilinear functor is
semilinear. -/
theorem mapExactFunctor_smul (hF : IsSemilinear R S F) {X Y : C} {n : ℕ} (r : R)
    (e : Abelian.Ext.{t} X Y n) :
    (r • e).mapExactFunctor F = algebraMap R S r • e.mapExactFunctor.{t, t'} F := by
  rw [Abelian.Ext.smul_eq_comp_mk₀, Abelian.Ext.mapExactFunctor_comp,
    Abelian.Ext.mapExactFunctor_mk₀, hF.map_smul_id, Abelian.Ext.smul_eq_comp_mk₀]

/-- The `S`-linear comparison map `S ⊗[R] Ext^n(X, Y) → Ext^n(F X, F Y)`,
`s ⊗ e ↦ s • F(e)`, of an exact semilinear functor `F`. -/
def extBaseChangeMap (hF : IsSemilinear R S F) (X Y : C) (n : ℕ) :
    S ⊗[R] Abelian.Ext.{t} X Y n →ₗ[S] Abelian.Ext.{t'} (F.obj X) (F.obj Y) n :=
  baseChangeLift (F.mapExtAddHom X Y n) (fun r e => mapExactFunctor_smul F hF r e)

@[simp]
theorem extBaseChangeMap_tmul (hF : IsSemilinear R S F) {X Y : C} {n : ℕ} (s : S)
    (e : Abelian.Ext.{t} X Y n) :
    extBaseChangeMap F hF X Y n (s ⊗ₜ[R] e) = s • e.mapExactFunctor.{t, t'} F := rfl

end Ext

section Derived

variable [HasDerivedCategory.{s} C] [HasDerivedCategory.{s'} D]

/-- The additive map `Hom(K, W₀⟦n⟧) → Hom(F K, (F W)₀⟦n⟧)` given by `F.mapDerivedCategory`,
followed by the comparison of `F.mapDerivedCategory` with the single-complex functors, where
`W₀` is `W` placed in degree `0`. -/
def abutmentMap (K : DerivedCategory C) (W : C) (n : ℤ) :
    ShiftedHom K ((DerivedCategory.singleFunctor C 0).obj W) n →+
      ShiftedHom (F.mapDerivedCategory.obj K)
        ((DerivedCategory.singleFunctor D 0).obj (F.obj W)) n where
  toFun f := f.map F.mapDerivedCategory ≫
    ((F.mapDerivedCategorySingleFunctor 0).hom.app W)⟦n⟧'
  map_zero' := by simp
  map_add' f g := by simp [Preadditive.add_comp]

theorem abutmentMap_apply (K : DerivedCategory C) (W : C) (n : ℤ)
    (f : ShiftedHom K ((DerivedCategory.singleFunctor C 0).obj W) n) :
    abutmentMap F K W n f = f.map F.mapDerivedCategory ≫
      ((F.mapDerivedCategorySingleFunctor 0).hom.app W)⟦n⟧' := rfl

/-- `abutmentMap` is natural in the coefficient object `W`. -/
theorem abutmentMap_comp_single (K : DerivedCategory C) {W W' : C} (n : ℤ)
    (f : ShiftedHom K ((DerivedCategory.singleFunctor C 0).obj W) n) (g : W ⟶ W') :
    abutmentMap F K W' n (f ≫ ((DerivedCategory.singleFunctor C 0).map g)⟦n⟧') =
      abutmentMap F K W n f ≫ ((DerivedCategory.singleFunctor D 0).map (F.map g))⟦n⟧' := by
  have hσ := (F.mapDerivedCategorySingleFunctor 0).hom.naturality g
  simp only [Functor.comp_map] at hσ
  have hσ' := congrArg (fun φ => (shiftFunctor (DerivedCategory D) n).map φ) hσ
  simp only [Functor.map_comp] at hσ'
  rw [abutmentMap_apply, abutmentMap_apply, ShiftedHom.map, ShiftedHom.map]
  simp only [Functor.map_comp, Category.assoc]
  rw [Functor.commShiftIso_hom_naturality_assoc, hσ']

/-- In `Hom(X, W₀⟦n⟧)`, composition with the image of `r • 𝟙 W` is multiplication by `r`. -/
theorem comp_single_smul_id {X : DerivedCategory C} (W : C) (n : ℤ) (r : R)
    (f : ShiftedHom X ((DerivedCategory.singleFunctor C 0).obj W) n) :
    f ≫ ((DerivedCategory.singleFunctor C 0).map (r • 𝟙 W))⟦n⟧' = r • f := by
  rw [Functor.map_smul, CategoryTheory.Functor.map_id, Functor.map_smul,
    CategoryTheory.Functor.map_id, Linear.comp_smul, Category.comp_id]

/-- `abutmentMap` is semilinear for a semilinear `F`. -/
theorem abutmentMap_smul (hF : IsSemilinear R S F) (K : DerivedCategory C) (W : C) (n : ℤ)
    (r : R) (f : ShiftedHom K ((DerivedCategory.singleFunctor C 0).obj W) n) :
    abutmentMap F K W n (r • f) = algebraMap R S r • abutmentMap F K W n f := by
  rw [← comp_single_smul_id W n r f, abutmentMap_comp_single, hF.map_smul_id,
    comp_single_smul_id]

/-- The `S`-linear comparison map `S ⊗[R] Hom(K, W₀⟦n⟧) → Hom(F K, (F W)₀⟦n⟧)`,
`s ⊗ f ↦ s • abutmentMap F K W n f`. -/
def abutmentBaseChangeMap (hF : IsSemilinear R S F) (K : DerivedCategory C) (W : C) (n : ℤ) :
    S ⊗[R] ShiftedHom K ((DerivedCategory.singleFunctor C 0).obj W) n →ₗ[S]
      ShiftedHom (F.mapDerivedCategory.obj K)
        ((DerivedCategory.singleFunctor D 0).obj (F.obj W)) n :=
  baseChangeLift (abutmentMap F K W n) (abutmentMap_smul F hF K W n)

@[simp]
theorem abutmentBaseChangeMap_tmul (hF : IsSemilinear R S F) (K : DerivedCategory C) (W : C)
    (n : ℤ) (s : S) (f : ShiftedHom K ((DerivedCategory.singleFunctor C 0).obj W) n) :
    abutmentBaseChangeMap F hF K W n (s ⊗ₜ f) = s • abutmentMap F K W n f := rfl

/-- The additive map `Hom(H^q K, W) → Hom(H^q (F K), F W)`, `φ ↦ c ≫ F.map φ`, where
`c : H^q (F K) ≅ F (H^q K)` is the Library's `exactDerivedHomologyIso`. -/
def cohomologyHomMap (K : DerivedCategory C) (W : C) (q : ℤ) :
    ((DerivedCategory.homologyFunctor C q).obj K ⟶ W) →+
      ((DerivedCategory.homologyFunctor D q).obj (F.mapDerivedCategory.obj K) ⟶ F.obj W) where
  toFun φ := (exactDerivedHomologyIso F q).hom.app K ≫ F.map φ
  map_zero' := by simp
  map_add' φ ψ := by simp

theorem cohomologyHomMap_apply (K : DerivedCategory C) (W : C) (q : ℤ)
    (φ : (DerivedCategory.homologyFunctor C q).obj K ⟶ W) :
    cohomologyHomMap F K W q φ = (exactDerivedHomologyIso F q).hom.app K ≫ F.map φ := rfl

/-- `cohomologyHomMap` is semilinear for a semilinear `F`. -/
theorem cohomologyHomMap_smul (hF : IsSemilinear R S F) (K : DerivedCategory C) (W : C)
    (q : ℤ) (r : R) (φ : (DerivedCategory.homologyFunctor C q).obj K ⟶ W) :
    cohomologyHomMap F K W q (r • φ) = algebraMap R S r • cohomologyHomMap F K W q φ := by
  rw [cohomologyHomMap_apply, cohomologyHomMap_apply, hF, Linear.comp_smul]

/-- The `S`-linear comparison map `S ⊗[R] Hom(H^q K, W) → Hom(H^q (F K), F W)`,
`s ⊗ φ ↦ s • cohomologyHomMap F K W q φ`. -/
def cohomologyHomBaseChangeMap (hF : IsSemilinear R S F) (K : DerivedCategory C) (W : C)
    (q : ℤ) :
    S ⊗[R] ((DerivedCategory.homologyFunctor C q).obj K ⟶ W) →ₗ[S]
      ((DerivedCategory.homologyFunctor D q).obj (F.mapDerivedCategory.obj K) ⟶ F.obj W) :=
  baseChangeLift (cohomologyHomMap F K W q) (cohomologyHomMap_smul F hF K W q)

@[simp]
theorem cohomologyHomBaseChangeMap_tmul (hF : IsSemilinear R S F) (K : DerivedCategory C)
    (W : C) (q : ℤ) (s : S) (φ : (DerivedCategory.homologyFunctor C q).obj K ⟶ W) :
    cohomologyHomBaseChangeMap F hF K W q (s ⊗ₜ φ) = s • cohomologyHomMap F K W q φ := rfl

end Derived

end Semilinear

section Rep

variable (R : Type uR) [CommRing R] (S : Type uS) [CommRing S] [Algebra R S]

/-- Extension of scalars of representations is semilinear along `algebraMap R S`. -/
theorem repExtendScalars_isSemilinear (G : Type uG) [Monoid G] :
    IsSemilinear R S (repExtendScalars.{w} R S G) := by
  intro X Y r f
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  refine LinearMap.ext fun z => ?_
  change S ⊗[R] X at z
  induction z using TensorProduct.inductionOn with
  | tmul s x =>
    change s ⊗ₜ[R] (r • f.hom x) = algebraMap R S r • (s ⊗ₜ[R] f.hom x)
    rw [TensorProduct.tmul_smul, algebraMap_smul]
  | add a b ha hb =>
    exact (LinearMap.map_add _ a b).trans
      ((congrArg₂ (· + ·) ha hb).trans (LinearMap.map_add _ a b).symm)

/-- Extension of scalars of smooth representations is semilinear along `algebraMap R S`. -/
theorem smoothRepExtendScalars_isSemilinear (G : Type uG) [Group G] [TopologicalSpace G] :
    IsSemilinear R S (smoothRepExtendScalars.{w} R S G) := by
  intro X Y r f
  apply SmoothRep.toRep.map_injective
  rw [Functor.map_smul (F := SmoothRep.toRep)]
  change (repExtendScalars.{w} R S G).map (SmoothRep.toRep.map (r • f)) = _
  rw [Functor.map_smul (F := SmoothRep.toRep)]
  exact repExtendScalars_isSemilinear.{w} R S G r (SmoothRep.toRep.map f)

end Rep

section Smooth

variable (R : Type uR) [CommRing R] (S : Type uS) [CommRing S] [Algebra R S] [Module.Flat R S]
  (G : Type uG) [Group G] [TopologicalSpace G]

/-- `extBaseChangeMap` for extension of scalars of smooth representations along a flat
`R → S`: `S ⊗[R] Ext^n(X, Y) → Ext^n(S ⊗[R] X, S ⊗[R] Y)`. -/
def smoothExtBaseChangeMap [HasExt.{t} (SmoothRep.{uR, uG, w} R G)]
    [HasExt.{t'} (SmoothRep.{uS, uG, max uS w} S G)] (X Y : SmoothRep.{uR, uG, w} R G)
    (n : ℕ) :
    S ⊗[R] Abelian.Ext.{t} X Y n →ₗ[S]
      Abelian.Ext.{t'} ((smoothRepExtendScalars.{w} R S G).obj X)
        ((smoothRepExtendScalars.{w} R S G).obj Y) n :=
  extBaseChangeMap (smoothRepExtendScalars.{w} R S G)
    (smoothRepExtendScalars_isSemilinear.{w} R S G) X Y n

variable [HasDerivedCategory.{s} (SmoothRep.{uR, uG, w} R G)]
  [HasDerivedCategory.{s'} (SmoothRep.{uS, uG, max uS w} S G)]

/-- `abutmentBaseChangeMap` for extension of scalars of smooth representations along a flat
`R → S`. -/
def smoothAbutmentBaseChangeMap (K : DerivedCategory (SmoothRep.{uR, uG, w} R G))
    (W : SmoothRep.{uR, uG, w} R G) (n : ℤ) :
    S ⊗[R] ShiftedHom K ((DerivedCategory.singleFunctor _ 0).obj W) n →ₗ[S]
      ShiftedHom ((smoothRepExtendScalars.{w} R S G).mapDerivedCategory.obj K)
        ((DerivedCategory.singleFunctor _ 0).obj ((smoothRepExtendScalars.{w} R S G).obj W))
        n :=
  abutmentBaseChangeMap (smoothRepExtendScalars.{w} R S G)
    (smoothRepExtendScalars_isSemilinear.{w} R S G) K W n

/-- `cohomologyHomBaseChangeMap` for extension of scalars of smooth representations along a
flat `R → S`. -/
def smoothCohomologyHomBaseChangeMap (K : DerivedCategory (SmoothRep.{uR, uG, w} R G))
    (W : SmoothRep.{uR, uG, w} R G) (q : ℤ) :
    S ⊗[R] ((DerivedCategory.homologyFunctor _ q).obj K ⟶ W) →ₗ[S]
      ((DerivedCategory.homologyFunctor _ q).obj
          ((smoothRepExtendScalars.{w} R S G).mapDerivedCategory.obj K) ⟶
        (smoothRepExtendScalars.{w} R S G).obj W) :=
  cohomologyHomBaseChangeMap (smoothRepExtendScalars.{w} R S G)
    (smoothRepExtendScalars_isSemilinear.{w} R S G) K W q

end Smooth

end HyperextScalarExtension

end Langlands.Cohomology
