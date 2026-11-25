/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ModuleHomComplex
public import WeilConjectures.AlgebraicGeometry.PrincipalOpenCechTotal
public import WeilConjectures.AlgebraicGeometry.KoszulOpenSystem

/-! # Signed localized Koszul evaluation

Source: Stacks Project, Tags 08D0 and 08D1
(blueprint: lem-sc-koszul-cech-localized-vertical).
The degree maps are constructed using the inverse of scalar multiplication on principal
opens. Coefficient maps commute with the scalar division used in these degree maps.
-/

@[expose] public section

universe uK

open CategoryTheory

namespace AlgebraicGeometry

variable (A : Type uK) [CommRing A]
variable (S : SheafOfModules.{uK} (moduleRings (Spec (.of A)).toRingedSpace)) (s : A)

/-- Inverse to multiplication by s^e on sections over D(s).
Source: Stacks, Tag 08D0 (blueprint: lem-sc-koszul-cech-localized-differential).
The inverse is constructed from Mathlib's proved invertibility of s on D(s).
(blueprint: lem-sc-koszul-cech-localized-vertical)
-/
noncomputable def koszulCechScalarDivision (e : ℕ) :
    ((affineOpenSections A (PrimeSpectrum.basicOpen s)).obj S) ≃ₗ[A]
      ((affineOpenSections A (PrimeSpectrum.basicOpen s)).obj S) := by
  let N := (affineOpenSections A (PrimeSpectrum.basicOpen s)).obj S
  have hu : IsUnit (algebraMap A (Module.End A (↑N)) s) :=
    Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen (M := S) s le_rfl
  exact (LinearEquiv.ofBijective (algebraMap A (Module.End A (↑N)) (s ^ e))
    ((Module.End.isUnit_iff _).mp (by simpa only [map_pow] using hu.pow e))).symm

private theorem koszulCechScalarDivision_cancel (e : ℕ)
    (x : (affineOpenSections A (PrimeSpectrum.basicOpen s)).obj S) :
    s ^ e • koszulCechScalarDivision A S s e x = x := by
  exact (koszulCechScalarDivision A S s e).symm_apply_apply x

private theorem koszulCechScalarDivision_natural
    (T : SheafOfModules.{uK} (moduleRings (Spec (.of A)).toRingedSpace))
    (g : S ⟶ T) (e : ℕ)
    (x : (affineOpenSections A (PrimeSpectrum.basicOpen s)).obj S) :
    koszulCechScalarDivision A T s e
        ((affineOpenSections A (PrimeSpectrum.basicOpen s)).map g x) =
      (affineOpenSections A (PrimeSpectrum.basicOpen s)).map g
        (koszulCechScalarDivision A S s e x) := by
  apply (koszulCechScalarDivision A T s e).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  change _ = s ^ e • ((affineOpenSections A (PrimeSpectrum.basicOpen s)).map g
    (koszulCechScalarDivision A S s e x))
  rw [← map_smul, koszulCechScalarDivision_cancel]

variable (r : ℕ) (f : Fin r → A)
variable (F : CochainComplex
  (SheafOfModules.{uK} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)

/-- Signed restriction of evaluation followed by division by the principal product.
Source: Stacks, Tags 08D0 and 08D1
(blueprint: lem-sc-koszul-cech-localized-differential).
The parameter B supplies the vectors to evaluate on, independently of total degree.
Linearity follows from linearity of cochains, restrictions and scalar division.
(blueprint: lem-sc-koszul-cech-localized-vertical)
-/
noncomputable def koszulCechLocalizedDegreeMap (e : ℕ) (n : ℤ)
    (B : ∀ J : {J : Finset (Fin r) // J.Nonempty},
      ((koszulOpenTail A r f e).extend ComplexShape.embeddingDownNat).X
        (1 - (J.val.card : ℤ))) :
    ModuleCat.of A (CochainComplex.HomComplex.Cochain
      ((koszulOpenTail A r f e).extend ComplexShape.embeddingDownNat)
      (((affineOpenSections A ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj F) n) ⟶
        principalCechTerms r f F n :=
  ModuleCat.ofHom
    { toFun := fun z J ↦
        (Int.negOnePow
          ((J.val.card - 1 : ℕ) * (n + 1 - (J.val.card : ℤ)) +
            ((J.val.card - 1) * (J.val.card - 2) / 2 : ℕ))) •
          koszulCechScalarDivision A (F.X (n + 1 - (J.val.card : ℤ))) (∏ j ∈ J.val, f j) (e + 1)
            ((modulesSpecToSheaf.obj (F.X (n + 1 - (J.val.card : ℤ)))).obj.map
              (homOfLE (le_top : principalCechIntersection r f J.val ≤ ⊤)).op
              ((z.v (1 - (J.val.card : ℤ)) (n + 1 - (J.val.card : ℤ)) (by ring)) (B J)))
      map_add' := by
        intro z z'
        funext J
        simp only [CochainComplex.HomComplex.Cochain.add_v, ModuleCat.hom_add,
          LinearMap.add_apply,
          map_add, smul_add, Pi.add_apply]
      map_smul' := by
        intro a z
        funext J
        simp only [CochainComplex.HomComplex.Cochain.smul_v, ModuleCat.hom_smul,
          LinearMap.smul_apply,
          map_smul, Pi.smul_apply, RingHom.id_apply]
        exact smul_comm _ _ _ }


/-- The localized evaluation's coefficient term has the vertical totalization sign.
Source: Stacks Project, Tag 08D1, compatibility with the second differential.
(blueprint: lem-sc-koszul-cech-localized-vertical)
Proof: restriction is natural for the coefficient differential. Its A-linearity makes
it commute with multiplication by the principal product, and hence with the inverse.
The exponent at n+1 is the exponent at n plus card(J)-1. The resulting extra sign
is precisely the vertical sign of the Cech total differential. -/
theorem koszulCechLocalized_vertical (e : ℕ) (n : ℤ)
    (J : {J : Finset (Fin r) // J.Nonempty})
    (x : (affineOpenSections A ⊤).obj (F.X (n + 1 - (J.val.card : ℤ)))) :
    (Int.negOnePow
      ((J.val.card - 1 : ℕ) * ((n + 1) + 1 - (J.val.card : ℤ)) +
        ((J.val.card - 1) * (J.val.card - 2) / 2 : ℕ))) •
      koszulCechScalarDivision A (F.X ((n + 1) + 1 - (J.val.card : ℤ)))
        (∏ j ∈ J.val, f j) (e + 1)
        ((modulesSpecToSheaf.obj (F.X ((n + 1) + 1 - (J.val.card : ℤ)))).obj.map
          (homOfLE (le_top : principalCechIntersection r f J.val ≤ ⊤)).op
          ((affineOpenSections A ⊤).map
            (F.d (n + 1 - (J.val.card : ℤ)) ((n + 1) + 1 - (J.val.card : ℤ))) x)) =
      (-1 : A) ^ (J.val.card - 1) •
        (affineOpenSections A (principalCechIntersection r f J.val)).map
          (F.d (n + 1 - (J.val.card : ℤ)) ((n + 1) + 1 - (J.val.card : ℤ)))
          ((Int.negOnePow
            ((J.val.card - 1 : ℕ) * (n + 1 - (J.val.card : ℤ)) +
              ((J.val.card - 1) * (J.val.card - 2) / 2 : ℕ))) •
            koszulCechScalarDivision A (F.X (n + 1 - (J.val.card : ℤ)))
              (∏ j ∈ J.val, f j) (e + 1)
              ((modulesSpecToSheaf.obj (F.X (n + 1 - (J.val.card : ℤ)))).obj.map
                (homOfLE (le_top : principalCechIntersection r f J.val ≤ ⊤)).op x)) := by
  have hres := ConcreteCategory.congr_hom
    ((modulesSpecToSheaf.map
      (F.d (n + 1 - (J.val.card : ℤ)) ((n + 1) + 1 - (J.val.card : ℤ)))).hom.naturality
        (homOfLE (le_top : principalCechIntersection r f J.val ≤ ⊤)).op) x
  simp only [ModuleCat.comp_apply] at hres
  change ((affineOpenSections A (principalCechIntersection r f J.val)).map
    (F.d (n + 1 - (J.val.card : ℤ)) ((n + 1) + 1 - (J.val.card : ℤ))))
    ((modulesSpecToSheaf.obj (F.X (n + 1 - (J.val.card : ℤ)))).obj.map
      (homOfLE (le_top : principalCechIntersection r f J.val ≤ ⊤)).op x) =
    _ at hres
  dsimp only [affineOpenSections] at hres ⊢
  rw [← hres]
  erw [koszulCechScalarDivision_natural]
  have hs :
      ((J.val.card - 1 : ℕ) * ((n + 1) + 1 - (J.val.card : ℤ)) +
        ((J.val.card - 1) * (J.val.card - 2) / 2 : ℕ)) =
      ((J.val.card - 1 : ℕ) * (n + 1 - (J.val.card : ℤ)) +
        ((J.val.card - 1) * (J.val.card - 2) / 2 : ℕ)) + (J.val.card - 1 : ℕ) := by ring
  rw [hs, Int.negOnePow_add, mul_smul, smul_comm]
  simp only [Units.smul_def, ← Int.cast_smul_eq_zsmul (R := A)]
  rw [Int.cast_negOnePow_natCast]
  apply congrArg (_ • ·)
  exact ((affineOpenSections A (principalCechIntersection r f J.val)).map
    (F.d (n + 1 - (J.val.card : ℤ))
      ((n + 1) + 1 - (J.val.card : ℤ)))).hom.map_smul _ _ |>.symm

end AlgebraicGeometry
