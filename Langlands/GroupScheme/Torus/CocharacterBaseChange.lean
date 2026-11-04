import Langlands.GroupScheme.Torus.CocharacterPurelyInseparableDescent
import Langlands.GroupScheme.Lie.BaseChange

/-! # Actual diagonalizable homomorphisms and multiplicative points under base change -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.CocharacterDatum

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
    {Z W : CommGroupScheme (Spec (CommRingCat.of k))}
    {Λ : Type u} [AddCommGroup Λ]

/-- Postcomposition with a group-scheme homomorphism preserves multiplicativity. -/
theorem IsMult.postcomp {S : Type u} [CommRing S] [Algebra k S]
    {p : Lie.AffinePoints Z.toGrp (AddMonoidAlgebra S Λ)}
    (hp : IsMult p) (f : Z.toGrp ⟶ W.toGrp) :
    IsMult (p ≫ f.hom.hom) := by
  unfold IsMult expMap at hp ⊢
  have h := congrArg
    (GroupScheme.affinePointsTarget Z.toGrp f
      (CommAlgCat.of (CommRingCat.of k) (AddMonoidAlgebra S (Λ × Λ)))) hp
  simpa only [map_mul, GroupScheme.affinePointsTarget_apply, Lie.affineMap_apply,
    Category.assoc] using h

/-- The identity point of the actual diagonalizable group is multiplicative. -/
theorem isMult_diagonalizable_id :
    IsMult (Z := Diagonalizable.groupScheme (CommRingCat.of k) Λ)
      (𝟙 ((algSpec (CommRingCat.of k)).obj
        (op (Diagonalizable.algebra (CommRingCat.of k) Λ)))) := by
  apply (Corepresented.affinePointsEquiv
    (Diagonalizable.functor (CommRingCat.of k) Λ)
    (Diagonalizable.grpCorepresentation (CommRingCat.of k) Λ)
    (CommAlgCat.of (CommRingCat.of k) (AddMonoidAlgebra k (Λ × Λ)))).injective
  unfold expMap
  rw [map_mul]
  simp only [Lie.affineMap_apply, Category.comp_id]
  erw [Corepresented.affinePointsEquiv_map, Corepresented.affinePointsEquiv_map,
    Corepresented.affinePointsEquiv_map]
  apply MonoidHom.ext
  intro m
  apply Units.ext
  change AddMonoidAlgebra.mapDomain (diagHom Λ) (AddMonoidAlgebra.single m.toAdd (1 : k)) =
    AddMonoidAlgebra.mapDomain (AddMonoidHom.inl Λ Λ) (AddMonoidAlgebra.single m.toAdd (1 : k)) *
      AddMonoidAlgebra.mapDomain (AddMonoidHom.inr Λ Λ) (AddMonoidAlgebra.single m.toAdd (1 : k))
  simp [AddMonoidAlgebra.mapDomain_single, AddMonoidAlgebra.single_mul_single, diagHom]

/-- A homomorphism from the actual diagonalizable group gives its universal image point. -/
def pointOfHom (f : (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp ⟶ Z.toGrp) :
    Lie.AffinePoints Z.toGrp (AddMonoidAlgebra k Λ) :=
  f.hom.hom

theorem isMult_pointOfHom
    (f : (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp ⟶ Z.toGrp) :
    IsMult (pointOfHom f) := by
  simpa [pointOfHom] using
    (isMult_diagonalizable_id (k := k) (Λ := Λ)).postcomp f

variable [hZa : IsAffine Z.toGrp.X.left]

/-- Actual homomorphisms from `D(Λ)` are exactly the multiplicative universal points. -/
def homEquivMultiplicativePoints :
    ((Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp ⟶ Z.toGrp) ≃
      multiplicativePoints Z k Λ where
  toFun f := ⟨pointOfHom f, isMult_pointOfHom f⟩
  invFun p := homOfMult p.val p.property
  left_inv f := by
    apply Grp.hom_ext
    simpa [pointOfHom] using id_comp_homOfMult (pointOfHom f) (isMult_pointOfHom f)
  right_inv p := by
    apply Subtype.ext
    simpa [pointOfHom] using id_comp_homOfMult p.val p.property

@[simp]
theorem homEquivMultiplicativePoints_zero :
    homEquivMultiplicativePoints (Z := Z) (Λ := Λ) 0 = 1 := by
  apply Subtype.ext
  change (1 : (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp ⟶ Z.toGrp).hom.hom = 1
  simp

section BaseChange

omit hZa

variable (K : Type u) [Field K] [Algebra k K]

local notation "Z_K" => Functor.obj (CommGroupScheme.baseChange (algebraBaseMap k K)) Z

/-- The actual pullback comparison commutes with every exponent map. -/
theorem affineBaseChangeEquiv_expMap {Λ' : Type u} [AddCommGroup Λ']
    (g : Λ →+ Λ') (p : Lie.AffinePoints (Z_K).toGrp (AddMonoidAlgebra K Λ)) :
    Lie.affineBaseChangeEquiv k K Z.toGrp (AddMonoidAlgebra K Λ') (expMap K g p) =
      expMap K g (Lie.affineBaseChangeEquiv k K Z.toGrp (AddMonoidAlgebra K Λ) p) := by
  exact Lie.affineBaseChangeEquiv_naturality k K Z.toGrp
    (AddMonoidAlgebra.mapDomainAlgHom K K g) p

/-- Multiplicativity is preserved and reflected by the actual pullback comparison. -/
theorem isMult_affineBaseChangeEquiv_iff
    (p : Lie.AffinePoints (Z_K).toGrp (AddMonoidAlgebra K Λ)) :
    IsMult (Lie.affineBaseChangeEquiv k K Z.toGrp (AddMonoidAlgebra K Λ) p) ↔
      IsMult p := by
  unfold IsMult
  rw [← affineBaseChangeEquiv_expMap, ← affineBaseChangeEquiv_expMap,
    ← affineBaseChangeEquiv_expMap, ← map_mul]
  exact (Lie.affineBaseChangeEquiv k K Z.toGrp (AddMonoidAlgebra K (Λ × Λ))).injective.eq_iff

/-- Multiplicative points of the scheme pullback are the original multiplicative
points over the extension field's group algebra. -/
def multiplicativeBaseChangeEquiv :
    multiplicativePoints Z_K K Λ ≃* multiplicativePoints Z K Λ where
  toFun p := ⟨Lie.affineBaseChangeEquiv k K Z.toGrp _ p.val,
    (isMult_affineBaseChangeEquiv_iff K p.val).mpr p.property⟩
  invFun p := ⟨(Lie.affineBaseChangeEquiv k K Z.toGrp _).symm p.val, by
    apply (isMult_affineBaseChangeEquiv_iff K _).mp
    have hp : IsMult p.val := p.property
    simpa only [MulEquiv.apply_symm_apply] using hp⟩
  left_inv p := Subtype.ext
    ((Lie.affineBaseChangeEquiv k K Z.toGrp _).symm_apply_apply _)
  right_inv p := Subtype.ext
    ((Lie.affineBaseChangeEquiv k K Z.toGrp _).apply_symm_apply _)
  map_mul' p q := Subtype.ext
    ((Lie.affineBaseChangeEquiv k K Z.toGrp _).map_mul p.val q.val)

include hZa

local instance cocharacterBaseChangeTargetAffine : IsAffine (Z_K).toGrp.X.left := by
  change IsAffine (CategoryTheory.Limits.pullback Z.toGrp.X.hom (algebraBaseMap k K))
  infer_instance

/-- Purely inseparable extensions preserve the actual diagonalizable
homomorphism set into a finite type affine commutative group. -/
def homEquivOfIsPurelyInseparable
    [LocallyOfFiniteType Z.toGrp.X.hom] [IsPurelyInseparable k K]
    [IsAddTorsionFree Λ] :
    ((Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp ⟶ Z.toGrp) ≃
      ((Diagonalizable.groupScheme (CommRingCat.of K) Λ).toGrp ⟶ (Z_K).toGrp) :=
  (homEquivMultiplicativePoints (Z := Z) (Λ := Λ)).trans
    ((multiplicativePointsEquivOfIsPurelyInseparable (Z := Z) (F := k) (L := K)
      (Λ := Λ)).toEquiv.trans
      ((multiplicativeBaseChangeEquiv (Z := Z) (Λ := Λ) K).symm.toEquiv.trans
        (homEquivMultiplicativePoints (Z := Z_K) (Λ := Λ)).symm))

variable [LocallyOfFiniteType Z.toGrp.X.hom] [IsPurelyInseparable k K]

@[simp]
theorem homEquivOfIsPurelyInseparable_zero [IsAddTorsionFree Λ] :
    homEquivOfIsPurelyInseparable (Z := Z) (Λ := Λ) K 0 = 0 := by
  apply (homEquivMultiplicativePoints (Z := Z_K) (Λ := Λ)).injective
  change homEquivMultiplicativePoints
      ((homEquivMultiplicativePoints (Z := Z_K) (Λ := Λ)).symm
        ((multiplicativeBaseChangeEquiv (Z := Z) (Λ := Λ) K).symm
          (multiplicativePointsEquivOfIsPurelyInseparable (Z := Z)
            (F := k) (L := K) (Λ := Λ) (homEquivMultiplicativePoints 0)))) = _
  rw [Equiv.apply_symm_apply, homEquivMultiplicativePoints_zero, map_one, map_one,
    homEquivMultiplicativePoints_zero]

/-- Vanishing of all diagonalizable homomorphisms survives purely inseparable
field extension for a finite type affine commutative target. -/
theorem diagonalizable_hom_eq_zero_of_isPurelyInseparable [IsAddTorsionFree Λ]
    (hZ : ∀ f : (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp ⟶ Z.toGrp, f = 0)
    (f : (Diagonalizable.groupScheme (CommRingCat.of K) Λ).toGrp ⟶ (Z_K).toGrp) :
    f = 0 := by
  obtain ⟨g, rfl⟩ := (homEquivOfIsPurelyInseparable (Z := Z) (Λ := Λ) K).surjective f
  rw [hZ g, homEquivOfIsPurelyInseparable_zero]

/-- Vanishing of actual cocharacters survives purely inseparable field extension. -/
theorem gm_hom_eq_zero_of_isPurelyInseparable
    (hZ : ∀ f : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ Z.toGrp, f = 0)
    (f : (Gm (Spec (CommRingCat.of K))).toGrp ⟶ (Z_K).toGrp) : f = 0 := by
  let e : (Gm (Spec (CommRingCat.of k))).toGrp ≅
      (Diagonalizable.groupScheme (CommRingCat.of k) (PUnit.{u+1} → ℤ)).toGrp :=
    splitTorus.gmIso _ ≪≫
      (Diagonalizable.splitIso (CommRingCat.of k) (AddEquiv.refl (PUnit.{u+1} → ℤ))).symm
  let eK : (Gm (Spec (CommRingCat.of K))).toGrp ≅
      (Diagonalizable.groupScheme (CommRingCat.of K) (PUnit.{u+1} → ℤ)).toGrp :=
    splitTorus.gmIso _ ≪≫
      (Diagonalizable.splitIso (CommRingCat.of K) (AddEquiv.refl (PUnit.{u+1} → ℤ))).symm
  apply (cancel_epi eK.inv).mp
  rw [comp_zero]
  apply diagonalizable_hom_eq_zero_of_isPurelyInseparable K
  intro g
  apply (cancel_epi e.hom).mp
  rw [hZ (e.hom ≫ g), comp_zero]

end BaseChange

end Langlands.GroupScheme.CocharacterDatum
