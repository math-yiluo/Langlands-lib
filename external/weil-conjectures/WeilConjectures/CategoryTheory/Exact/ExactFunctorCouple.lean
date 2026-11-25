/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.HalfPlaneConvergence
import WeilConjectures.CategoryTheory.Exact.ExactFunctorHalfPlane
import all WeilConjectures.CategoryTheory.HalfPlaneDiagonalColimits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images

/-!
# Exact functors transport exact couples

Source: Stacks Project, Homology, Section 12.21, Tags 011Q, 011R, 011S, 0AMJ,
and the transport argument of the blueprint (blueprint: lem-sp-exact-functor-couple).
The index `r` denotes the actual page `r + 2`. Object equalities identify the initial
mapped datum; subsequent identifications of subobjects are commuting isomorphisms.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

set_option autoImplicit false

universe u₁ v₁ u₂ v₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.BigradedExactCouple

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
  {B : Type u₂} [Category.{v₂} B] [Abelian B]
  (Φ : C ⥤ B) [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]
  {s : ℕ}

private theorem map_exact {U V W : C} (f : U ⟶ V) (g : V ⟶ W)
    (hz : f ≫ g = 0) (he : imageSubobject f = kernelSubobject g) :
    imageSubobject (Φ.map f) = kernelSubobject (Φ.map g) := by
  exact (ShortComplex.exact_iff_image_eq_kernel _).mp
    (((ShortComplex.exact_iff_image_eq_kernel (ShortComplex.mk f g hz)).mpr he).map Φ)

private def mapped (X : BigradedExactCouple C s) : BigradedExactCouple B s where
  D p q := Φ.obj (X.D p q)
  E p q := Φ.obj (X.E p q)
  alpha p q := Φ.map (X.alpha p q)
  f p q := Φ.map (X.f p q)
  g p q := Φ.map (X.g p q)
  alpha_f_zero p q := by rw [← Φ.map_comp, X.alpha_f_zero, Φ.map_zero]
  f_g_zero p q := by rw [← Φ.map_comp, X.f_g_zero, Φ.map_zero]
  g_alpha_zero p q := by rw [← Φ.map_comp, X.g_alpha_zero, Φ.map_zero]
  exact_alpha p q := map_exact Φ _ _ (X.alpha_f_zero p q) (X.exact_alpha p q)
  exact_f p q := map_exact Φ _ _ (X.f_g_zero p q) (X.exact_f p q)
  exact_g p q := map_exact Φ _ _ (X.g_alpha_zero p q) (X.exact_g p q)

private noncomputable def imageIso {U V : C} {U' V' : B}
    (f : U ⟶ V) (g : U' ⟶ V') (eU : Φ.obj U ≅ U') (eV : Φ.obj V ≅ V')
    (h : Φ.map f ≫ eV.hom = eU.hom ≫ g) : Φ.obj (image f) ≅ image g :=
  (PreservesImage.iso Φ f).symm ≪≫ (im (C := B)).mapIso
    (Arrow.isoMk (f := Arrow.mk (Φ.map f)) (g := Arrow.mk g) eU eV h.symm)

omit [Φ.Additive] in
private theorem imageIso_ι {U V : C} {U' V' : B}
    (f : U ⟶ V) (g : U' ⟶ V') (eU : Φ.obj U ≅ U') (eV : Φ.obj V ≅ V')
    (h : Φ.map f ≫ eV.hom = eU.hom ≫ g) :
    (imageIso Φ f g eU eV h).hom ≫ image.ι g = Φ.map (image.ι f) ≫ eV.hom := by
  have hm : image.map (Arrow.isoMk (f := Arrow.mk (Φ.map f))
      (g := Arrow.mk g) eU eV h.symm).hom ≫ image.ι g =
      image.ι (Φ.map f) ≫ eV.hom := image.map_ι _
  dsimp only [imageIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, im]
  rw [Category.assoc, hm, ← Category.assoc, PreservesImage.inv_comp_image_ι_map]

private noncomputable def cyclesIso {U V : C} {U' V' : B}
    (f : U ⟶ V) (g : U' ⟶ V') (eU : Φ.obj U ≅ U') (eV : Φ.obj V ≅ V')
    (h : Φ.map f ≫ eV.hom = eU.hom ≫ g) : Φ.obj (kernel f) ≅ kernel g :=
  PreservesKernel.iso Φ f ≪≫ kernel.mapIso (Φ.map f) g eU eV h

omit [PreservesFiniteColimits Φ] in
private theorem cyclesIso_ι {U V : C} {U' V' : B}
    (f : U ⟶ V) (g : U' ⟶ V') (eU : Φ.obj U ≅ U') (eV : Φ.obj V ≅ V')
    (h : Φ.map f ≫ eV.hom = eU.hom ≫ g) :
    (cyclesIso Φ f g eU eV h).hom ≫ kernel.ι g =
      Φ.map (kernel.ι f) ≫ eU.hom := by
  simp [cyclesIso, Category.assoc]

private noncomputable def quotientIso {U V : C} {U' V' : B}
    (f : U ⟶ V) (g : U' ⟶ V') (eU : Φ.obj U ≅ U') (eV : Φ.obj V ≅ V')
    (h : Φ.map f ≫ eV.hom = eU.hom ≫ g) : Φ.obj (cokernel f) ≅ cokernel g :=
  PreservesCokernel.iso Φ f ≪≫ cokernel.mapIso (Φ.map f) g eU eV h

omit [PreservesFiniteLimits Φ] in
private theorem quotientIso_π {U V : C} {U' V' : B}
    (f : U ⟶ V) (g : U' ⟶ V') (eU : Φ.obj U ≅ U') (eV : Φ.obj V ≅ V')
    (h : Φ.map f ≫ eV.hom = eU.hom ≫ g) :
    Φ.map (cokernel.π f) ≫ (quotientIso Φ f g eU eV h).hom =
      eV.hom ≫ cokernel.π g := by
  simp [quotientIso, ← Category.assoc]

private structure Comparison (X : BigradedExactCouple C s)
    (Y : BigradedExactCouple B s) where
  δ : ∀ p q, Φ.obj (X.D p q) ≅ Y.D p q
  φ : ∀ p q, Φ.obj (X.E p q) ≅ Y.E p q
  ha : ∀ p q, Φ.map (X.alpha p q) ≫ (δ (p - 1) (q + 1)).hom =
    (δ p q).hom ≫ Y.alpha p q
  hf : ∀ p q, Φ.map (X.f p q) ≫ (δ (p + 2) (q - 1)).hom =
    (φ p q).hom ≫ Y.f p q
  hg : ∀ p q, Φ.map (X.g p q) ≫ (φ (p + s) (q - s)).hom =
    (δ p q).hom ≫ Y.g p q

variable {Φ}

omit [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ] in
private theorem Comparison.hd {X : BigradedExactCouple C s}
    {Y : BigradedExactCouple B s} (e : Comparison Φ X Y) (p q : ℤ) :
    Φ.map (X.d p q) ≫ (e.φ (p + 2 + s) (q - 1 - s)).hom =
      (e.φ p q).hom ≫ Y.d p q := by
  dsimp only [d]
  rw [Φ.map_comp, Category.assoc, e.hg, ← Category.assoc, e.hf, Category.assoc]

private theorem derived_alpha (X : BigradedExactCouple C s) (p q : ℤ) :
    X.derived.alpha p q ≫ X.derivedDInclusion (p - 1) (q + 1) =
      X.derivedDInclusion p q ≫ X.alpha p q :=
  (Classical.choice X.derivedMaps_exists).alpha_comm p q

private theorem derived_f (X : BigradedExactCouple C s) (p q : ℤ) :
    X.derivedEProjection p q ≫ X.derived.f p q ≫
      X.derivedDInclusion (p + 2) (q - 1) = kernel.ι (X.d p q) ≫ X.f p q :=
  (Classical.choice X.derivedMaps_exists).f_comm p q

private theorem derived_g (X : BigradedExactCouple C s) (p q : ℤ) :
    factorThruImage (X.alpha (p + 1) (q - 1)) ≫ X.derived.g p q =
      X.gToCycles (p + 1) (q - 1) ≫
        X.derivedEProjection ((p + 1) + s) ((q - 1) - s) ≫
          eqToHom (by congr 1 <;> omega) :=
  (Classical.choice X.derivedMaps_exists).g_comm p q

private noncomputable def Comparison.di {X : BigradedExactCouple C s}
    {Y : BigradedExactCouple B s} (e : Comparison Φ X Y) (p q : ℤ) :
    Φ.obj (X.derivedD p q) ≅ Y.derivedD p q :=
  imageIso Φ _ _ (e.δ (p + 1) (q - 1)) (e.δ (p + 1 - 1) (q - 1 + 1))
    (e.ha (p + 1) (q - 1))

omit [Φ.Additive] in
private theorem Comparison.di_ι {X : BigradedExactCouple C s}
    {Y : BigradedExactCouple B s} (e : Comparison Φ X Y) (p q : ℤ) :
    (e.di p q).hom ≫ Y.derivedDInclusion p q =
      Φ.map (X.derivedDInclusion p q) ≫ (e.δ p q).hom := by
  dsimp only [derivedDInclusion]
  rw [← Category.assoc]
  dsimp only [Comparison.di]
  rw [imageIso_ι, Φ.map_comp, Category.assoc, Category.assoc,
    transport_square Φ (fun p q ↦ (e.δ p q).hom) (by omega) (by omega)]

private noncomputable def Comparison.ki {X : BigradedExactCouple C s}
    {Y : BigradedExactCouple B s} (e : Comparison Φ X Y) (p q : ℤ) :
    Φ.obj (kernel (X.d p q)) ≅ kernel (Y.d p q) :=
  cyclesIso Φ _ _ (e.φ p q) (e.φ (p + 2 + s) (q - 1 - s)) (e.hd p q)

omit [PreservesFiniteColimits Φ] in
private theorem Comparison.ki_ι {X : BigradedExactCouple C s}
    {Y : BigradedExactCouple B s} (e : Comparison Φ X Y) (p q : ℤ) :
    (e.ki p q).hom ≫ kernel.ι (Y.d p q) =
      Φ.map (kernel.ι (X.d p q)) ≫ (e.φ p q).hom :=
  cyclesIso_ι Φ _ _ _ _ _

omit [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ] in
private theorem Comparison.hInto {X : BigradedExactCouple C s}
    {Y : BigradedExactCouple B s} (e : Comparison Φ X Y) (p q : ℤ) :
    Φ.map (X.dInto p q) ≫ (e.φ p q).hom =
      (e.φ (p - s - 2) (q + s + 1)).hom ≫ Y.dInto p q := by
  dsimp only [dInto]
  rw [Φ.map_comp, Category.assoc,
    transport_square Φ (fun p q ↦ (e.φ p q).hom) (by omega) (by omega),
    ← Category.assoc, e.hd, Category.assoc]

omit [PreservesFiniteColimits Φ] in
private theorem Comparison.lift_comm {X : BigradedExactCouple C s}
    {Y : BigradedExactCouple B s} (e : Comparison Φ X Y) (p q : ℤ) :
    Φ.map (kernel.lift (X.d p q) (X.dInto p q) (X.dInto_comp_d p q)) ≫
      (e.ki p q).hom = (e.φ (p - s - 2) (q + s + 1)).hom ≫
        kernel.lift (Y.d p q) (Y.dInto p q) (Y.dInto_comp_d p q) := by
  apply (cancel_mono (kernel.ι (Y.d p q))).mp
  rw [Category.assoc, e.ki_ι, ← Category.assoc, ← Φ.map_comp, kernel.lift_ι,
    Category.assoc, kernel.lift_ι, e.hInto]

private noncomputable def Comparison.ei {X : BigradedExactCouple C s}
    {Y : BigradedExactCouple B s} (e : Comparison Φ X Y) (p q : ℤ) :
    Φ.obj (X.derivedE p q) ≅ Y.derivedE p q :=
  quotientIso Φ _ _ (e.φ (p - s - 2) (q + s + 1)) (e.ki p q) (e.lift_comm p q)

private theorem Comparison.ei_π {X : BigradedExactCouple C s}
    {Y : BigradedExactCouple B s} (e : Comparison Φ X Y) (p q : ℤ) :
    Φ.map (X.derivedEProjection p q) ≫ (e.ei p q).hom =
      (e.ki p q).hom ≫ Y.derivedEProjection p q :=
  quotientIso_π Φ _ _ _ _ _

omit [Φ.Additive] in
private theorem Comparison.derived_ha {X : BigradedExactCouple C s}
    {Y : BigradedExactCouple B s} (e : Comparison Φ X Y) (p q : ℤ) :
    Φ.map (X.derived.alpha p q) ≫ (e.di (p - 1) (q + 1)).hom =
      (e.di p q).hom ≫ Y.derived.alpha p q := by
  apply (cancel_mono (Y.derivedDInclusion (p - 1) (q + 1))).mp
  rw [Category.assoc, e.di_ι, ← Category.assoc, ← Φ.map_comp, derived_alpha,
    Φ.map_comp, Category.assoc, e.ha, ← Category.assoc, ← e.di_ι,
    Category.assoc]
  rw [Category.assoc, derived_alpha]

private theorem Comparison.derived_hf {X : BigradedExactCouple C s}
    {Y : BigradedExactCouple B s} (e : Comparison Φ X Y) (p q : ℤ) :
    Φ.map (X.derived.f p q) ≫ (e.di (p + 2) (q - 1)).hom =
      (e.ei p q).hom ≫ Y.derived.f p q := by
  apply (cancel_epi (Φ.map (X.derivedEProjection p q))).mp
  apply (cancel_mono (Y.derivedDInclusion (p + 2) (q - 1))).mp
  calc
    (Φ.map (X.derivedEProjection p q) ≫
        (Φ.map (X.derived.f p q) ≫ (e.di (p + 2) (q - 1)).hom)) ≫
        Y.derivedDInclusion (p + 2) (q - 1) =
        Φ.map (kernel.ι (X.d p q)) ≫ (e.φ p q).hom ≫ Y.f p q := by
      rw [Category.assoc, Category.assoc, e.di_ι, ← Φ.map_comp_assoc,
        ← Φ.map_comp_assoc, Category.assoc (X.derivedEProjection p q),
        derived_f, Φ.map_comp, Category.assoc, e.hf]
    _ = (Φ.map (X.derivedEProjection p q) ≫
        ((e.ei p q).hom ≫ Y.derived.f p q)) ≫
          Y.derivedDInclusion (p + 2) (q - 1) := by
      rw [← Category.assoc (Φ.map (kernel.ι (X.d p q))), ← e.ki_ι,
        Category.assoc, ← derived_f, ← Category.assoc, ← e.ei_π]
      simp only [Category.assoc]

omit [Φ.Additive] in
private theorem Comparison.di_factor {X : BigradedExactCouple C s}
    {Y : BigradedExactCouple B s} (e : Comparison Φ X Y) (p q : ℤ) :
    Φ.map (factorThruImage (X.alpha (p + 1) (q - 1))) ≫ (e.di p q).hom =
      (e.δ (p + 1) (q - 1)).hom ≫ factorThruImage (Y.alpha (p + 1) (q - 1)) := by
  apply (cancel_mono (image.ι (Y.alpha (p + 1) (q - 1)))).mp
  dsimp only [Comparison.di]
  rw [Category.assoc, imageIso_ι, ← Category.assoc, ← Φ.map_comp, image.fac,
    Category.assoc, image.fac, e.ha]

omit [PreservesFiniteColimits Φ] in
private theorem Comparison.gCycles {X : BigradedExactCouple C s}
    {Y : BigradedExactCouple B s} (e : Comparison Φ X Y) (p q : ℤ) :
    Φ.map (X.gToCycles p q) ≫ (e.ki (p + s) (q - s)).hom =
      (e.δ p q).hom ≫ Y.gToCycles p q := by
  apply (cancel_mono (kernel.ι (Y.d (p + s) (q - s)))).mp
  rw [Category.assoc, e.ki_ι, ← Category.assoc, ← Φ.map_comp]
  simp only [gToCycles, kernel.lift_ι, Category.assoc]
  exact e.hg p q

private theorem Comparison.derived_hg {X : BigradedExactCouple C s}
    {Y : BigradedExactCouple B s} (e : Comparison Φ X Y) (p q : ℤ) :
    Φ.map (X.derived.g p q) ≫ (e.ei (p + (s + 1 : ℕ)) (q - (s + 1 : ℕ))).hom =
      (e.di p q).hom ≫ Y.derived.g p q := by
  apply (cancel_epi (Φ.map (factorThruImage (X.alpha (p + 1) (q - 1))))).mp
  rw [← Φ.map_comp_assoc, derived_g, Φ.map_comp, Φ.map_comp]
  rw [Category.assoc, Category.assoc,
    transport_square Φ (fun p q ↦ (e.ei p q).hom) (by omega) (by omega),
    ← Category.assoc (Φ.map (X.derivedEProjection _ _)), e.ei_π,
    Category.assoc]
  rw [← Category.assoc (Φ.map (X.gToCycles (p + 1) (q - 1)))
    (e.ki (p + 1 + s) (q - 1 - s)).hom, e.gCycles]
  rw [← Category.assoc (Φ.map (factorThruImage (X.alpha (p + 1) (q - 1))))
    (e.di p q).hom, e.di_factor]
  simp only [Category.assoc, derived_g]

private noncomputable def Comparison.next {X : BigradedExactCouple C s}
    {Y : BigradedExactCouple B s} (e : Comparison Φ X Y) :
    Comparison Φ X.derived Y.derived where
  δ := e.di
  φ := e.ei
  ha := e.derived_ha
  hf := e.derived_hf
  hg := e.derived_hg

private noncomputable def filtrationIso (X : BigradedExactCouple C 0)
    (AX : ∀ n : ℤ, AlphaColimit X n)
    (AY : ∀ n : ℤ, AlphaColimit (mapped Φ X) n)
    (eA : ∀ n : ℤ, Φ.obj (AX n).obj ≅ (AY n).obj)
    (hA : ∀ n p, Φ.map ((AX n).ι p) ≫ (eA n).hom = (AY n).ι p)
    (n p : ℤ) :
    Φ.obj ((X.imageFiltration n (AX n)).step p : C) ≅
      (((mapped Φ X).imageFiltration n (AY n)).step p : B) :=
  Φ.mapIso (imageSubobjectIso ((AX n).ι p)) ≪≫
    imageIso Φ ((AX n).ι p) ((AY n).ι p) (Iso.refl _) (eA n)
      (by simpa using hA n p) ≪≫ (imageSubobjectIso ((AY n).ι p)).symm

private theorem filtrationIso_arrow (X : BigradedExactCouple C 0)
    (AX : ∀ n : ℤ, AlphaColimit X n)
    (AY : ∀ n : ℤ, AlphaColimit (mapped Φ X) n)
    (eA : ∀ n : ℤ, Φ.obj (AX n).obj ≅ (AY n).obj)
    (hA : ∀ n p, Φ.map ((AX n).ι p) ≫ (eA n).hom = (AY n).ι p)
    (n p : ℤ) :
    (filtrationIso X AX AY eA hA n p).hom ≫
        (((mapped Φ X).imageFiltration n (AY n)).step p).arrow =
      Φ.map (((X.imageFiltration n (AX n)).step p).arrow) ≫ (eA n).hom := by
  dsimp only [filtrationIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    imageFiltration]
  rw [Category.assoc, Category.assoc, imageSubobject_arrow',
    imageIso_ι, ← Category.assoc, ← Φ.map_comp, imageSubobject_arrow]

private theorem filtrationIso_step (X : BigradedExactCouple C 0)
    (AX : ∀ n : ℤ, AlphaColimit X n)
    (AY : ∀ n : ℤ, AlphaColimit (mapped Φ X) n)
    (eA : ∀ n : ℤ, Φ.obj (AX n).obj ≅ (AY n).obj)
    (hA : ∀ n p, Φ.map ((AX n).ι p) ≫ (eA n).hom = (AY n).ι p)
    (n p : ℤ) :
    Φ.map (Subobject.ofLE ((X.imageFiltration n (AX n)).step (p + 1))
      ((X.imageFiltration n (AX n)).step p)
      ((X.imageFiltration n (AX n)).antitone_step (by omega))) ≫
        (filtrationIso X AX AY eA hA n p).hom =
      (filtrationIso X AX AY eA hA n (p + 1)).hom ≫
        Subobject.ofLE (((mapped Φ X).imageFiltration n (AY n)).step (p + 1))
          (((mapped Φ X).imageFiltration n (AY n)).step p)
          (((mapped Φ X).imageFiltration n (AY n)).antitone_step (by omega)) := by
  apply (cancel_mono (((mapped Φ X).imageFiltration n (AY n)).step p).arrow).mp
  rw [Category.assoc, filtrationIso_arrow, ← Category.assoc, ← Φ.map_comp,
    Subobject.ofLE_arrow, Category.assoc, Subobject.ofLE_arrow, filtrationIso_arrow]

private noncomputable def gradedIso (X : BigradedExactCouple C 0)
    (AX : ∀ n : ℤ, AlphaColimit X n)
    (AY : ∀ n : ℤ, AlphaColimit (mapped Φ X) n)
    (eA : ∀ n : ℤ, Φ.obj (AX n).obj ≅ (AY n).obj)
    (hA : ∀ n p, Φ.map ((AX n).ι p) ≫ (eA n).hom = (AY n).ι p)
    (n p : ℤ) :
    Φ.obj ((X.imageFiltration n (AX n)).gradedPiece p) ≅
      ((mapped Φ X).imageFiltration n (AY n)).gradedPiece p :=
  quotientIso Φ _ _ (filtrationIso X AX AY eA hA n (p + 1))
    (filtrationIso X AX AY eA hA n p) (filtrationIso_step X AX AY eA hA n p)

/-! Transport of exact couples along an exact additive functor.
Source: Stacks Project, Homology, Section 12.21; blueprint: lem-sp-exact-functor-couple.
The full transport construction is retained as the next proof obligation. -/
end CategoryTheory.BigradedExactCouple
