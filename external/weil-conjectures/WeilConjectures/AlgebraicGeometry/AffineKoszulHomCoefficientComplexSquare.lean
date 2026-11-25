/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.KoszulQuotientCoefficientComplex
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.HomComplexToSingleCoefficientSquare
import WeilConjectures.AlgebraicGeometry.AffineKoszulSignedDualCoefficientSquare

/-! # Finite free Koszul Hom coordinates before taking homology

Source: Stacks Project, Tag 0BQZ, displayed map of Hom complexes. -/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

private theorem exists_iso_square_trans {C : Type*} [Category* C]
    {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : C} {f : X₁ ⟶ X₂} {g : Y₁ ⟶ Y₂} {h : Z₁ ⟶ Z₂}
    (hf : ∃ (a : X₁ ≅ Y₁) (b : X₂ ≅ Y₂), f ≫ b.hom = a.hom ≫ g)
    (hg : ∃ (a : Y₁ ≅ Z₁) (b : Y₂ ≅ Z₂), g ≫ b.hom = a.hom ≫ h) :
    ∃ (a : X₁ ≅ Z₁) (b : X₂ ≅ Z₂), f ≫ b.hom = a.hom ≫ h := by
  obtain ⟨a, b, hab⟩ := hf
  obtain ⟨c, d, hcd⟩ := hg
  exact ⟨a ≪≫ c, b ≪≫ d, (CommSq.vert_comp ⟨hab⟩ ⟨hcd⟩).w⟩

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types false in
/-- Applying internal Hom to the sheafified coefficient quotient gives the
sheafification of the explicit coefficient reduction between dual complexes.
Source: Stacks Project, Tag 0BQZ, Lemma 48.15.5, displayed Hom-complex map;
Tag 01HV, Lemma 26.5.4(4)-(5), localization of associated modules.
(blueprint: lem-sc-affine-koszul-hom-coefficient-complex-square).

Proof: Substitute the equality hH identifying the given functor with Hom(E,-).
For either coefficient module M = A or A/I, project the product defining
Hom(E,M[0]) in degree k to the factor of source degree -k. All other factors
have zero target. The product lift with this component and zero in the others
is the inverse. For k >= 0, the canonical extension term is wedge^k(A^n).
Its exterior-power basis is finite. On a basic open D(g), a map from its
associated sheaf to tilde(M) is uniquely specified by its values on that basis,
which lie in M_g. A finite tuple of such values is precisely the localization
of Hom_A(wedge^k(A^n),M). These coordinate isomorphisms commute with restriction
because each basis value localizes, so they glue to sheaf isomorphisms. For
k < 0, the source term and the extended dual term are zero, giving the unique
isomorphism. Under these identifications the Hom differential is signed
precomposition: its target contribution vanishes and its source contribution
is -(-1)^k times precomposition by the Koszul boundary. At k >= 0 this is
(-1)^(k+1), the sign of both recorded dual differentials. At the boundary
from degree -1 to 0 both maps are zero. Thus the isomorphisms form chain
isomorphisms. Postcomposition with the coefficient quotient reduces each
basis value modulo I; this is exactly koszulCoefficientReductionDegree, so
the square commutes in every degree and hence as complex morphisms. This
calculation is natural in the coefficients and does not take homology or
assume regularity. For n = 0 only degree zero survives; for k > n the exterior
basis is empty. Zero rings, I = top, and empty charts give zero objects. -/
theorem affine_koszul_hom_coefficient_complex_square
    {Y : Scheme.{u}} (U : Y.affineOpens) (I : Ideal (Γ(Y, U.1)))
    (n : ℕ) (f : Fin n → Γ(Y, U.1))
    (H : CochainComplex (SheafOfModules.{u} U.1.toScheme.ringCatSheaf) ℤ ⥤
      CochainComplex (SheafOfModules.{u} U.1.toScheme.ringCatSheaf) ℤ)
    (hH : H =
      let A := (Γ(Y, U.1) : Type u)
      let T := tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom
      let E := (T.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((ExteriorAlgebra.koszulComplex A n f).extend ComplexShape.embeddingDownNat)
      (homComplexFunctor (R := U.1.toScheme.toRingedSpace.sheaf)).obj (op E)) :
    let A := (Γ(Y, U.1) : Type u)
    let T := tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom
    let TC := T.mapHomologicalComplex (ComplexShape.up ℤ)
    let S := CochainComplex.singleFunctor U.1.toScheme.Modules 0
    ∃ (cO : H.obj (S.obj (T.obj (ModuleCat.of A A))) ≅
        TC.obj ((ExteriorAlgebra.koszulDualComplex A n f).extend
          ComplexShape.embeddingUpNat))
      (cQ : H.obj (S.obj (T.obj (ModuleCat.of A (A ⧸ I)))) ≅
        TC.obj ((ExteriorAlgebra.koszulQuotientDualComplex A I n f).extend
          ComplexShape.embeddingUpNat)),
      H.map (S.map (T.map (ModuleCat.ofHom I.mkQ))) ≫ cQ.hom =
        cO.hom ≫ TC.map (HomologicalComplex.extendMap
          (ExteriorAlgebra.koszulCoefficientReduction A I n f)
          ComplexShape.embeddingUpNat) := by
  subst H
  let A := (Γ(Y, U.1) : Type u)
  let T := tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom
  let TC := T.mapHomologicalComplex (ComplexShape.up ℤ)
  let E := TC.obj
    ((ExteriorAlgebra.koszulComplex A n f).extend ComplexShape.embeddingDownNat)
  exact exists_iso_square_trans
    (homComplex_to_single_coefficient_square
      (R := U.1.toScheme.toRingedSpace.sheaf) E
      (T.obj (ModuleCat.of A A)) (T.obj (ModuleCat.of A (A ⧸ I)))
      (T.map (ModuleCat.ofHom I.mkQ)))
    (affine_koszul_signed_dual_coefficient_square U I n f)

end AlgebraicGeometry
