/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import WeilConjectures.AlgebraicGeometry.KoszulComplex

/-! # Ordered exterior coordinates for the Koszul complex

Source: Stacks Project, More on Algebra, Tag 0622 and Tag 0664.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe w
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Subsets supported in an integer cochain degree.
Source: Stacks Project, Tag 0622
(auxiliary; not a blueprint node). -/
abbrev exteriorKoszulIndex (r : ℕ) (q : ℤ) :=
  {I : Finset (Fin r) // q = -(I.card : ℤ)}

/-- The exterior Koszul complex placed in nonpositive cochain degrees.
Source: Stacks Project, Tag 0622
(auxiliary; not a blueprint node). -/
abbrev exteriorKoszulExtended {A : Type w} [CommRing A] (r : ℕ) (f : Fin r → A) :=
  (ExteriorAlgebra.koszulComplex A r f).extend ComplexShape.embeddingDownNat

/-- The ordered wedge basis, inserted into its supported cochain degree.
Source: Stacks Project, Tags 0622 and 0664
(auxiliary; not a blueprint node). -/
def exteriorKoszulBasis {A : Type w} [CommRing A] (r : ℕ) (f : Fin r → A)
    (q : ℤ) (I : exteriorKoszulIndex r q) :
    ModuleCat.of A A ⟶ (exteriorKoszulExtended r f).X q :=
  ModuleCat.ofHom ((LinearMap.id : A →ₗ[A] A).smulRight
    ((Finsupp.basisSingleOne : Module.Basis (Fin r) A (Fin r →₀ A)).exteriorPower
      (-q).toNat ⟨I.1, by
        change I.1.card = (-q).toNat
        have hi : q = -(I.1.card : ℤ) := I.2
        omega⟩)) ≫
    ((ExteriorAlgebra.koszulComplex A r f).extendXIso
      ComplexShape.embeddingDownNat (by
        change -(((-q).toNat : ℕ) : ℤ) = q
        have hi : q = -(I.1.card : ℤ) := I.2
        omega)).inv

/-- The coordinate projection dual to an ordered exterior wedge.
Source: Stacks Project, Tags 0622 and 0664
(auxiliary; not a blueprint node). -/
def exteriorKoszulCoordinate {A : Type w} [CommRing A] (r : ℕ) (f : Fin r → A)
    (q : ℤ) (I : exteriorKoszulIndex r q) :
    (exteriorKoszulExtended r f).X q ⟶ ModuleCat.of A A :=
  ((ExteriorAlgebra.koszulComplex A r f).extendXIso
    ComplexShape.embeddingDownNat (by
      change -(((-q).toNat : ℕ) : ℤ) = q
      have hi : q = -(I.1.card : ℤ) := I.2
      omega)).hom ≫
    ModuleCat.ofHom (((Finsupp.basisSingleOne :
      Module.Basis (Fin r) A (Fin r →₀ A)).exteriorPower (-q).toNat).coord
        ⟨I.1, by
          change I.1.card = (-q).toNat
          have hi : q = -(I.1.card : ℤ) := I.2
          omega⟩)

/-- The actual matrix coefficient of the exterior contraction differential.
This uses the constructed boundary map and the ordinary dual-basis projection.
Source: Stacks Project, Tag 0622
(auxiliary; not a blueprint node). -/
def exteriorKoszulCoefficient {A : Type w} [CommRing A] (r : ℕ) (f : Fin r → A)
    (q : ℤ) (I : exteriorKoszulIndex r q) (L : exteriorKoszulIndex r (q + 1)) : A :=
  (exteriorKoszulBasis r f q I ≫ (exteriorKoszulExtended r f).d q (q + 1) ≫
    exteriorKoszulCoordinate r f (q + 1) L) (1 : A)

private def indexEquiv (r k : ℕ) (q : ℤ) (h : -(k : ℤ) = q) :
    Set.powersetCard (Fin r) k ≃ exteriorKoszulIndex r q where
  toFun I := ⟨I.1, by rw [I.2]; exact h.symm⟩
  invFun I := ⟨I.1, by
    change I.1.card = k
    have hi : q = -(I.1.card : ℤ) := I.2
    omega⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem basis_decomposition {A : Type w} [CommRing A]
    (r : ℕ) (f : Fin r → A) (q : ℤ) :
    (∑ I : exteriorKoszulIndex r q,
      exteriorKoszulCoordinate r f q I ≫ exteriorKoszulBasis r f q I) =
        𝟙 ((exteriorKoszulExtended r f).X q) := by
  classical
  by_cases hq : q ≤ 0
  · let k := (-q).toNat
    have hk : -(k : ℤ) = q := by dsimp [k]; omega
    let e := indexEquiv r k q hk
    let b := ((Finsupp.basisSingleOne :
      Module.Basis (Fin r) A (Fin r →₀ A)).exteriorPower k).reindex e
    let z := (ExteriorAlgebra.koszulComplex A r f).extendXIso
      ComplexShape.embeddingDownNat hk
    have hb (I : exteriorKoszulIndex r q) : exteriorKoszulBasis r f q I =
        ModuleCat.ofHom ((LinearMap.id : A →ₗ[A] A).smulRight (b I)) ≫ z.inv := by
      simp only [exteriorKoszulBasis, b, Module.Basis.reindex_apply, e, indexEquiv]
      rfl
    have hp (I : exteriorKoszulIndex r q) : exteriorKoszulCoordinate r f q I =
        z.hom ≫ ModuleCat.ofHom (b.coord I) := by
      dsimp only [exteriorKoszulCoordinate]
      congr 1
    apply (cancel_epi z.inv).1
    apply (cancel_mono z.hom).1
    simp only [Preadditive.comp_sum, Preadditive.sum_comp, hb, hp, Category.assoc,
      Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    simp only [ModuleCat.hom_sum, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
      ModuleCat.hom_id, LinearMap.sum_apply, LinearMap.comp_apply,
      Module.Basis.coord_apply]
    change (∑ I, b.repr x I • b I) = x
    exact b.sum_repr x
  · have hz : IsZero ((exteriorKoszulExtended r f).X q) := by
      apply HomologicalComplex.isZero_extend_X
      intro k
      change -(k : ℤ) ≠ q
      omega
    exact hz.eq_of_src _ _

/-- Expansion of the actual contraction differential in its finite wedge basis.

Source: Stacks Project, Tags 0622 and 0664, finite free exterior coordinates.
(auxiliary; not a blueprint node).

Proof: in supported degrees the exterior basis and its coordinate projections
satisfy the usual finite identity sum of inclusion after projection equals
identity. Transport that identity through extendXIso. In positive degrees the
complex term is zero, so the same identity holds. Postcompose the differential
with the identity expansion of its target. Every resulting map A to A is
multiplication by its value at 1, which by definition is the displayed actual
matrix coefficient. This is a coordinate expansion of the constructed boundary,
not an assumption about its entries. No nontriviality or division is used. -/
theorem exteriorKoszulBasis_d {A : Type w} [CommRing A]
    (r : ℕ) (f : Fin r → A) (q : ℤ) (I : exteriorKoszulIndex r q) :
    exteriorKoszulBasis r f q I ≫ (exteriorKoszulExtended r f).d q (q + 1) =
      ∑ L : exteriorKoszulIndex r (q + 1),
        ModuleCat.ofHom (LinearMap.mul A A (exteriorKoszulCoefficient r f q I L)) ≫
          exteriorKoszulBasis r f (q + 1) L := by
  classical
  calc
    _ = exteriorKoszulBasis r f q I ≫ (exteriorKoszulExtended r f).d q (q + 1) ≫
        ∑ L : exteriorKoszulIndex r (q + 1),
          exteriorKoszulCoordinate r f (q + 1) L ≫
            exteriorKoszulBasis r f (q + 1) L := by
      rw [basis_decomposition, Category.comp_id]
    _ = _ := by
      simp only [Preadditive.comp_sum, ← Category.assoc]
      apply Finset.sum_congr rfl
      intro L _
      congr 1
      simp only [Category.assoc]
      let g := exteriorKoszulBasis r f q I ≫ (exteriorKoszulExtended r f).d q (q + 1) ≫
        exteriorKoszulCoordinate r f (q + 1) L
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change g.hom x = g.hom 1 * x
      have hx := g.hom.map_smul x (1 : A)
      simpa only [smul_eq_mul, mul_one, mul_comm] using hx

end CategoryTheory
