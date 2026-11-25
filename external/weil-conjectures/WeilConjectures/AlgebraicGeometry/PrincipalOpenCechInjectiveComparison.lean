/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.AlgebraicGeometry.PrincipalOpenCechCoordinateMap
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

/-! # comparison to injective terms for principal-open Čech coordinates

Source: Stacks Project, Cohomology, Tag 08C1, finite augmented Čech argument.
(blueprint: lem-sc-principal-open-cech-injective-comparison).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

private noncomputable def comparisonSections
    (A : Type u) [CommRing A] (U : (Spec (.of A)).Opens) :
    SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace) ⥤ ModuleCat.{u} A where
  obj F := (modulesSpecToSheaf.obj F).obj.obj (op U)
  map g := (modulesSpecToSheaf.map g).hom.app (op U)
  map_id F := congrArg (fun g ↦ g.hom.app (op U)) (modulesSpecToSheaf.map_id F)
  map_comp g h := congrArg (fun g ↦ g.hom.app (op U)) (modulesSpecToSheaf.map_comp g h)

private instance comparisonSections_additive
    (A : Type u) [CommRing A] (U : (Spec (.of A)).Opens) :
    (comparisonSections A U).Additive where
  map_add := by intros; rfl

private theorem comparison_restriction_naturality
    (A : Type u) [CommRing A]
    {J I : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ}
    (g : J ⟶ I) (U W : (Spec (.of A)).Opens) (hle : W ≤ U)
    (n m : ℤ) (e : n = m) :
    (comparisonSections A U).map (g.f n) ≫
        (comparisonSections A U).map (eqToHom (congrArg I.X e)) ≫
        (modulesSpecToSheaf.obj (I.X m)).obj.map (homOfLE hle).op =
      (comparisonSections A U).map (eqToHom (congrArg J.X e)) ≫
        (modulesSpecToSheaf.obj (J.X m)).obj.map (homOfLE hle).op ≫
        (comparisonSections A W).map (g.f m) := by
  subst m
  change (_ ≫ 𝟙 _ ≫ _) = (𝟙 _ ≫ _)
  simp only [Category.id_comp]
  exact ((modulesSpecToSheaf.map (g.f n)).hom.naturality (homOfLE hle).op).symm

/-- A K-injective coefficient complex admits a comparison square to the subset Čech
augmentation of a complex with injective terms. The section comparison is a
quasi-isomorphism; no homology assertion about either augmentation is assumed.

Source: Stacks Project, Cohomology, Tag 08C1, finite Čech comparison, and Tag 079P,
functorial K-injective resolutions.
(blueprint: lem-sc-principal-open-cech-injective-comparison).

Proof: Choose a functorial K-injective resolution J → I with injective terms.
Since J and I are K-injective, its quasi-isomorphism is a homotopy equivalence.
Construct K₁ by applying section evaluation on V to I and changing scalars to A.
Construct T₁ as the finite product in each displayed degree, with the stated signed
vertical and deletion differential; d squared is zero by restriction naturality,
anticommutation of the signed vertical and horizontal terms, and cancellation of
pairs of deletions. The singleton restrictions define α₁. Its chain-map equation
is restriction naturality in degree zero and the cancellation of the two singleton
restrictions in degree one. Use the components of J → I in the σ and τ coordinates
to define a and b; naturality and the displayed differentials make them chain maps.
Singleton naturality gives α ≫ b = a ≫ α₁, and all other components vanish.
Section evaluation preserves the inverse comparison and its homotopies, so a is a
homotopy equivalence and a quasi-isomorphism. The analogous total homotopy uses
(-1) to the Čech degree; it is not needed for the asserted one-sided transfer.
For an empty family V is empty and both section complexes and subset products
vanish. Repetitions and empty members leave the coordinate construction valid. -/
theorem principalOpenCech_injective_comparison
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (J : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ) [J.IsKInjective] :
    let V : (Spec (.of A)).Opens := ⨆ i : Fin r, PrimeSpectrum.basicOpen (f i)
    let D : Finset (Fin r) → (Spec (.of A)).Opens :=
      fun S ↦ PrimeSpectrum.basicOpen (∏ j ∈ S, f j)
    ∀ (K T : CochainComplex (ModuleCat.{u} A) ℤ)
      (σ : ∀ n : ℤ, K.X n ≅ (modulesSpecToSheaf.obj (J.X n)).obj.obj (op V))
      (τ : ∀ n : ℤ, T.X n ≅ ModuleCat.of A
        (∀ S : {S : Finset (Fin r) // S.Nonempty},
          (modulesSpecToSheaf.obj (J.X (n + 1 - (S.val.card : ℤ)))).obj.obj (op (D S.val))))
      (α : K ⟶ T)
      (hle : ∀ (S : Finset (Fin r)) (j : Fin r), D S ≤ D (S.erase j))
      (hls : ∀ S : {S : Finset (Fin r) // S.Nonempty}, S.val.card = 1 → D S.val ≤ V)
      (he : ∀ (S : Finset (Fin r)) (j : Fin r), j ∈ S → ∀ n : ℤ,
        n + 1 - ((S.erase j).card : ℤ) = n + 1 + 1 - (S.card : ℤ))
      (hes : ∀ S : {S : Finset (Fin r) // S.Nonempty}, S.val.card = 1 → ∀ n : ℤ,
        n = n + 1 - (S.val.card : ℤ)),
      (∀ (n : ℤ) (s : K.X n),
        (σ (n + 1)).hom (K.d n (n + 1) s) =
          (modulesSpecToSheaf.map (J.d n (n + 1))).hom.app (op V) ((σ n).hom s)) →
      (∀ (n : ℤ) (s : T.X n) (S : {S : Finset (Fin r) // S.Nonempty}),
        (τ (n + 1)).hom (T.d n (n + 1) s) S =
          (-1 : A) ^ (S.val.card - 1) •
            (modulesSpecToSheaf.map
              (J.d (n + 1 - (S.val.card : ℤ)) (n + 1 + 1 - (S.val.card : ℤ)))).hom.app
                (op (D S.val)) ((τ n).hom s S) +
          ∑ j : S.val, if h : (S.val.erase j.val).Nonempty then
            (-1 : A) ^ ((S.val.filter (fun i ↦ i < j.val)).card) •
              (modulesSpecToSheaf.obj (J.X (n + 1 + 1 - (S.val.card : ℤ)))).obj.map
                (homOfLE (hle S.val j.val)).op
                ((modulesSpecToSheaf.map
                  (eqToHom (congrArg J.X (he S.val j.val j.property n)))).hom.app
                    (op (D (S.val.erase j.val))) ((τ n).hom s ⟨S.val.erase j.val, h⟩))
          else 0) →
      (∀ (n : ℤ) (s : K.X n) (S : {S : Finset (Fin r) // S.Nonempty}),
        (τ n).hom (α.f n s) S = if h : S.val.card = 1 then
          (modulesSpecToSheaf.obj (J.X (n + 1 - (S.val.card : ℤ)))).obj.map
            (homOfLE (hls S h)).op
            ((modulesSpecToSheaf.map (eqToHom (congrArg J.X (hes S h n)))).hom.app
              (op V) ((σ n).hom s)) else 0) →
      ∃ (I : CochainComplex
          (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
        (K₁ T₁ : CochainComplex (ModuleCat.{u} A) ℤ)
      (σ₁ : ∀ n : ℤ, K₁.X n ≅ (modulesSpecToSheaf.obj (I.X n)).obj.obj (op V))
      (τ₁ : ∀ n : ℤ, T₁.X n ≅ ModuleCat.of A
        (∀ S : {S : Finset (Fin r) // S.Nonempty},
          (modulesSpecToSheaf.obj (I.X (n + 1 - (S.val.card : ℤ)))).obj.obj (op (D S.val))))
        (α₁ : K₁ ⟶ T₁) (a : K ⟶ K₁) (b : T ⟶ T₁),
        (∀ n : ℤ, Injective (I.X n)) ∧
      (∀ (n : ℤ) (s : K₁.X n),
        (σ₁ (n + 1)).hom (K₁.d n (n + 1) s) =
          (modulesSpecToSheaf.map (I.d n (n + 1))).hom.app (op V) ((σ₁ n).hom s)) ∧
      (∀ (n : ℤ) (s : T₁.X n) (S : {S : Finset (Fin r) // S.Nonempty}),
        (τ₁ (n + 1)).hom (T₁.d n (n + 1) s) S =
          (-1 : A) ^ (S.val.card - 1) •
            (modulesSpecToSheaf.map
              (I.d (n + 1 - (S.val.card : ℤ)) (n + 1 + 1 - (S.val.card : ℤ)))).hom.app
                (op (D S.val)) ((τ₁ n).hom s S) +
          ∑ j : S.val, if h : (S.val.erase j.val).Nonempty then
            (-1 : A) ^ ((S.val.filter (fun i ↦ i < j.val)).card) •
              (modulesSpecToSheaf.obj (I.X (n + 1 + 1 - (S.val.card : ℤ)))).obj.map
                (homOfLE (hle S.val j.val)).op
                ((modulesSpecToSheaf.map
                  (eqToHom (congrArg I.X (he S.val j.val j.property n)))).hom.app
                    (op (D (S.val.erase j.val))) ((τ₁ n).hom s ⟨S.val.erase j.val, h⟩))
          else 0) ∧
      (∀ (n : ℤ) (s : K₁.X n) (S : {S : Finset (Fin r) // S.Nonempty}),
        (τ₁ n).hom (α₁.f n s) S = if h : S.val.card = 1 then
          (modulesSpecToSheaf.obj (I.X (n + 1 - (S.val.card : ℤ)))).obj.map
            (homOfLE (hls S h)).op
            ((modulesSpecToSheaf.map (eqToHom (congrArg I.X (hes S h n)))).hom.app
              (op V) ((σ₁ n).hom s)) else 0) ∧
        QuasiIso a ∧ α ≫ b = a ≫ α₁ := by
  classical
  dsimp only
  intro K T σ τ α hle hls he hes hK hT hα
  let V : (Spec (.of A)).Opens := ⨆ i : Fin r, PrimeSpectrum.basicOpen (f i)
  let C := SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)
  have : IsGrothendieckAbelian.{u} C :=
    SheafOfModules.isGrothendieckAbelian (moduleRings (Spec (.of A)).toRingedSpace)
  let I := (CochainComplex.kInjectiveResolutionFunctor.{u} C).obj J
  let g : J ⟶ I := (CochainComplex.toKInjectiveResolution.{u} C).app J
  have hg : QuasiIso g :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} C J).2
  have : I.IsKInjective := inferInstance
  obtain ⟨e, heq⟩ := (CochainComplex.IsKInjective.quasiIso_iff g).mp hg
  let E := comparisonSections A V
  let F := E.mapHomologicalComplex (ComplexShape.up ℤ)
  let K₁ := F.obj I
  let σ₁ : ∀ n : ℤ, K₁.X n ≅ (modulesSpecToSheaf.obj (I.X n)).obj.obj (op V) :=
    fun _ ↦ Iso.refl _
  let c : K ≅ F.obj J := HomologicalComplex.Hom.isoOfComponents σ (by
    intro n m hnm
    obtain rfl : m = n + 1 := hnm.symm
    ext s
    exact (hK n s).symm)
  let a : K ⟶ K₁ := c.hom ≫ F.map g
  have ha : QuasiIso a := by
    have : QuasiIso (F.map g) := by
      rw [← heq]
      exact (E.mapHomotopyEquiv e).quasiIso_hom
    dsimp only [a]
    infer_instance
  have hK₁ : ∀ (n : ℤ) (s : K₁.X n),
      (σ₁ (n + 1)).hom (K₁.d n (n + 1) s) =
        (modulesSpecToSheaf.map (I.d n (n + 1))).hom.app (op V) ((σ₁ n).hom s) := by
    intros
    rfl
  have hac : ∀ (n : ℤ) (s : K.X n),
      (σ₁ n).hom (a.f n s) =
        (modulesSpecToSheaf.map (g.f n)).hom.app (op V) ((σ n).hom s) := by
    intros
    rfl
  obtain ⟨T₁, τ₁, α₁, b, hT₁, hα₁, hb⟩ :=
    principalOpenCech_coordinate_map_exists A r f J I g T τ hle hls he hes
      K₁ σ₁ hT hK₁
  have hsquare : α ≫ b = a ≫ α₁ := by
    apply HomologicalComplex.hom_ext
    intro n
    apply (cancel_mono (τ₁ n).hom).mp
    ext s S
    change (τ₁ n).hom (b.f n (α.f n s)) S =
      (τ₁ n).hom (α₁.f n (a.f n s)) S
    rw [hb, hα₁, hα]
    by_cases h : S.val.card = 1
    · simp only [dite_eq_left h]
      rw [hac]
      exact (ConcreteCategory.congr_hom
        (comparison_restriction_naturality A g V _ (hls S h) n _ (hes S h n))
        ((σ n).hom s)).symm
    · simp only [dite_eq_right h, map_zero]
  exact ⟨I, K₁, T₁, σ₁, τ₁, α₁, a, b, (fun n ↦ inferInstance),
    hK₁, hT₁, hα₁, ha, hsquare⟩


end AlgebraicGeometry
