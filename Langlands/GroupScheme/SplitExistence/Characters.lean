import Langlands.GroupScheme.SplitExistence.LieWeights
import Langlands.GroupScheme.Torus.Lattice

/-! # The character lattice of `D(X)`

Each `ξ ∈ X` gives the character `χ ↦ χ(ξ)` of `D(X)`. For a lattice `X` this identifies `X` with
the Library character lattice `Hom(D(X), 𝔾ₘ)`: after a choice of basis of `X`, it is the Library
identification of the characters of the split torus `𝔾ₘ^I` with `ℤ^I`, transported along the
Library isomorphism `D(X) ≅ 𝔾ₘ^I`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitExistence

namespace ChevalleyData

variable {X : Type u} [AddCommGroup X] (k : Type u) [Field k]

/-- Evaluation of characters at `ξ`. -/
def evalChar (ξ : X) (R : Type u) [CommRing R] : (Multiplicative X →* Rˣ) →* Rˣ where
  toFun χ := χ (Multiplicative.ofAdd ξ)
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The character of `D(X)` attached to `ξ ∈ X`, on points. -/
def charPoints (ξ : X) (T : Over (Spec (CommRingCat.of k))) :
    (T ⟶ (Tk (X := X) k).toGrp.X) →* (T ⟶ (Gm (Spec (CommRingCat.of k))).X) :=
  (Gm.pointsEquiv _ T).symm.toMonoidHom.comp
    ((evalChar ξ Γ(T.left, ⊤)).comp (torusPointsEquiv k T).toMonoidHom)

theorem charPoints_naturality (ξ : X) {T T' : Over (Spec (CommRingCat.of k))} (a : T' ⟶ T)
    (x : T ⟶ (Tk (X := X) k).toGrp.X) :
    charPoints k ξ T' (a ≫ x) = a ≫ charPoints k ξ T x := by
  apply (Gm.pointsEquiv _ T').injective
  simp only [charPoints, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
    MulEquiv.apply_symm_apply]
  rw [Gm.pointsEquiv_naturality, MulEquiv.apply_symm_apply]
  rfl

/-- The character `χ ↦ χ(ξ)` of `D(X)`. -/
def charOf (ξ : X) : characterLattice (Tk (X := X) k) :=
  Additive.ofMul (homOfPoints (charPoints k ξ) fun a x => charPoints_naturality k ξ a x)

theorem gmPoints_charOf (ξ : X) (T : Over (Spec (CommRingCat.of k)))
    (x : T ⟶ (Tk (X := X) k).toGrp.X) :
    Gm.pointsEquiv _ T (x ≫ (CommGroupScheme.groupHom (charOf k ξ)).hom.hom) =
      torusPointsEquiv k T x (Multiplicative.ofAdd ξ) := by
  change Gm.pointsEquiv _ T (x ≫ (homOfPoints (charPoints k ξ) _).hom.hom) = _
  rw [comp_homOfPoints]
  exact MulEquiv.apply_symm_apply _ _

theorem charOf_add (ξ₁ ξ₂ : X) : charOf k (ξ₁ + ξ₂) = charOf k ξ₁ + charOf k ξ₂ := by
  apply CommGroupScheme.hom_ext_points
  intro T x
  apply (Gm.pointsEquiv _ T).injective
  rw [comp_groupHom_add, map_mul, gmPoints_charOf, gmPoints_charOf, gmPoints_charOf, ofAdd_add,
    map_mul]

/-- The additive map `X → X^*(D(X))`. -/
def charOfHom : X →+ characterLattice (Tk (X := X) k) :=
  AddMonoidHom.mk' (charOf k) (charOf_add k)

@[simp] theorem charOfHom_apply (ξ : X) : charOfHom k ξ = charOf k ξ := rfl

section Split

variable [Module.Finite ℤ X] [Module.Free ℤ X]

/-- The index type of the chosen basis of `X`. -/
abbrev basisIndex (X : Type u) [AddCommGroup X] [Module.Finite ℤ X] [Module.Free ℤ X] :=
  Module.Free.ChooseBasisIndex ℤ X

/-- The coordinates of `X` in the chosen basis. -/
abbrev basisEquiv (X : Type u) [AddCommGroup X] [Module.Finite ℤ X] [Module.Free ℤ X] :
    X ≃+ (basisIndex X → ℤ) :=
  (Module.Free.chooseBasis ℤ X).equivFun.toAddEquiv

theorem basisEquiv_symm_eq (m : basisIndex X → ℤ) :
    (basisEquiv X).symm m = ∑ i, m i • (basisEquiv X).symm (Pi.single i 1) := by
  conv_lhs => rw [← Finset.univ_sum_single m]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← map_zsmul, ← Pi.single_smul, smul_eq_mul, mul_one]

/-- The splitting isomorphism `D(X) ≅ 𝔾ₘ^I` of the Library. -/
abbrev splitIsoX : (Tk (X := X) k).toGrp ≅ splitTorus (Spec (CommRingCat.of k)) (basisIndex X) :=
  Diagonalizable.splitIso (CommRingCat.of k) (basisEquiv X)

theorem charOf_eq_split (ξ : X) :
    charOf k ξ = Additive.ofMul ((splitIsoX k).hom ≫ CommGroupScheme.groupHom
      ((splitTorus.characterLatticeEquiv k (basisIndex X)).symm (basisEquiv X ξ))) := by
  apply CommGroupScheme.hom_ext_points
  intro T x
  apply (Gm.pointsEquiv _ T).injective
  rw [gmPoints_charOf]
  change _ = Gm.pointsEquiv _ T ((x ≫ (splitIsoX k).hom.hom.hom) ≫ (CommGroupScheme.groupHom
    ((splitTorus.characterLatticeEquiv k (basisIndex X)).symm (basisEquiv X ξ))).hom.hom)
  rw [splitTorus.pointsEquiv_characterLatticeEquiv_symm]
  have hx : splitTorus.pointsEquiv (basisIndex X) T (x ≫ (splitIsoX k).hom.hom.hom) =
      Diagonalizable.splitPointsEquiv (CommRingCat.of k) (basisEquiv X) T x :=
    isoOfPointModels_hom _ _ _ _ _ (fun a y => splitTorus.pointsEquiv_naturality _ a y) T x
  rw [hx]
  conv_lhs => rw [← (basisEquiv X).symm_apply_apply ξ, basisEquiv_symm_eq,
    ofAdd_sum, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [ofAdd_zsmul, map_zpow]
  rfl

/-- Precomposition with an isomorphism of tori, on characters. -/
def precompEquiv : characterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of k))
      (basisIndex X)) ≃+ characterLattice (Tk (X := X) k) where
  toFun χ := Additive.ofMul ((splitIsoX k).hom ≫ CommGroupScheme.groupHom χ)
  invFun χ := Additive.ofMul ((splitIsoX k).inv ≫ CommGroupScheme.groupHom χ)
  left_inv χ := by
    change Additive.ofMul ((splitIsoX k).inv ≫ (splitIsoX k).hom ≫ CommGroupScheme.groupHom χ) = χ
    rw [Iso.inv_hom_id_assoc]
    rfl
  right_inv χ := by
    change Additive.ofMul ((splitIsoX k).hom ≫ (splitIsoX k).inv ≫ CommGroupScheme.groupHom χ) = χ
    rw [Iso.hom_inv_id_assoc]
    rfl
  map_add' χ ψ := by
    change Additive.ofMul ((splitIsoX k).hom ≫ (CommGroupScheme.groupHom χ *
      CommGroupScheme.groupHom ψ)) = _
    rw [MonObj.comp_mul]
    rfl

/-- **`X ≅ X^*(D(X))`.** -/
def charEquiv : X ≃+ characterLattice (Tk (X := X) k) :=
  ((basisEquiv X).trans (splitTorus.characterLatticeEquiv k (basisIndex X)).symm).trans
    (precompEquiv k)

theorem charEquiv_apply (ξ : X) : charEquiv k ξ = charOf k ξ := by
  rw [charOf_eq_split]
  rfl

end Split

end ChevalleyData

end Langlands.GroupScheme.SplitExistence
