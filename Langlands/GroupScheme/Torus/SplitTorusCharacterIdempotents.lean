import Langlands.GroupScheme.Torus.DiagonalizableCharacterProof

/-! # Locally constant character maps of homomorphisms of split tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace splitTorus

variable {R : Type u} [CommRing R] {I I' : Type u} [Fintype I] [Fintype I']

/-- `τ` pulls back the exponent character `m` of `𝔾_m^{I'}` to the exponent character `h m`
of `𝔾_m^I` on all points over test schemes whose structure morphism lands in `V`. -/
def CharacterMapOn
    (τ : splitTorus (Spec (CommRingCat.of R)) I ⟶ splitTorus (Spec (CommRingCat.of R)) I')
    (V : (Spec (CommRingCat.of R)).Opens) (h : (I' → ℤ) →ₗ[ℤ] (I → ℤ)) : Prop :=
  ∀ (U : Over (Spec (CommRingCat.of R))), U.hom ⁻¹ᵁ V = ⊤ →
    ∀ (x : U ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X) (m : I' → ℤ),
      ∏ j', pointsEquiv I' U (x ≫ τ.hom.hom) j' ^ m j' =
        ∏ j, pointsEquiv I U x j ^ h m j

section Idempotents

variable [DecidableEq I]
  (τ : splitTorus (Spec (CommRingCat.of R)) I ⟶ splitTorus (Spec (CommRingCat.of R)) I')

local notation "Rc" => CommRingCat.of R

/-- The coordinate split isomorphism `D(ℤ^I) ≅ 𝔾_m^I`. -/
abbrev diagIso : (Diagonalizable.groupScheme Rc (I → ℤ)).toGrp ≅ splitTorus (Spec Rc) I :=
  Diagonalizable.splitIso Rc (AddEquiv.refl (I → ℤ))

/-- The `j'`-th coordinate of `τ`, as a natural family of units on `D(ℤ^I)`. -/
def coordinateUnits (j' : I') : DiagonalizableCharacter.NaturalUnits Rc (I → ℤ) where
  app U :=
    { toFun := fun y => pointsEquiv I' U ((y ≫ (diagIso (I := I)).hom.hom.hom) ≫ τ.hom.hom) j'
      map_one' := by
        change pointsEquiv I' U ((1 ≫ (diagIso (I := I)).hom.hom.hom) ≫ τ.hom.hom) j' = 1
        rw [MonObj.one_comp, MonObj.one_comp, map_one, Pi.one_apply]
      map_mul' := fun y z => by
        change pointsEquiv I' U (((y * z) ≫ (diagIso (I := I)).hom.hom.hom) ≫ τ.hom.hom) j' =
          pointsEquiv I' U ((y ≫ (diagIso (I := I)).hom.hom.hom) ≫ τ.hom.hom) j' *
            pointsEquiv I' U ((z ≫ (diagIso (I := I)).hom.hom.hom) ≫ τ.hom.hom) j'
        rw [MonObj.mul_comp, MonObj.mul_comp, map_mul, Pi.mul_apply] }
  naturality a y := by
    change pointsEquiv I' _ (((a ≫ y) ≫ (diagIso (I := I)).hom.hom.hom) ≫ τ.hom.hom) j' =
      Units.map a.left.appTop.hom.toMonoidHom
        (pointsEquiv I' _ ((y ≫ (diagIso (I := I)).hom.hom.hom) ≫ τ.hom.hom) j')
    rw [Category.assoc, Category.assoc, pointsEquiv_naturality, Category.assoc]
    rfl

/-- The characters of `D(ℤ^I)` are the exponent monomials in the split coordinates. -/
theorem characterPointsEquiv_diag (U : Over (Spec Rc))
    (x : U ⟶ (splitTorus (Spec Rc) I).X) (m : I → ℤ) :
    Diagonalizable.characterPointsEquiv Rc (I → ℤ) U (x ≫ (diagIso (I := I)).inv.hom.hom)
        (.ofAdd m) = ∏ i, pointsEquiv I U x i ^ m i := by
  have hx : pointsEquiv I U x = Diagonalizable.splitPointsEquiv Rc (AddEquiv.refl (I → ℤ)) U
      (x ≫ (diagIso (I := I)).inv.hom.hom) := by
    have h := isoOfPointModels_inv (fun T : Over (Spec Rc) => I → (Γ(T.left, ⊤))ˣ)
      (fun a => unitsRestrict I a) (Diagonalizable.splitPointsEquiv Rc (AddEquiv.refl (I → ℤ)))
      (fun T => pointsEquiv I T)
      (Diagonalizable.splitPointsEquiv_naturality Rc (AddEquiv.refl (I → ℤ)))
      (fun a y => pointsEquiv_naturality I a y) U x
    exact h.symm
  rw [hx]
  set χ := Diagonalizable.characterPointsEquiv Rc (I → ℤ) U (x ≫ (diagIso (I := I)).inv.hom.hom)
  change χ (.ofAdd m) =
    ∏ i, Diagonalizable.charEquiv (AddEquiv.refl (I → ℤ)) _ χ i ^ m i
  conv_lhs => rw [← (Diagonalizable.charEquiv (AddEquiv.refl (I → ℤ)) _).symm_apply_apply χ]
  rfl

/-- A global section whose basic open set is everything is a unit. -/
private theorem isUnit_of_basicOpen_eq_top' {X : Scheme.{u}} {r : Γ(X, ⊤)}
    (h : X.basicOpen r = ⊤) : IsUnit r :=
  X.toLocallyRingedSpace.toRingedSpace.isUnit_of_isUnit_germ ⊤ r fun x _ =>
    (X.mem_basicOpen_top r x).1 (by rw [h]; trivial)

/-- The section algebra of a test scheme receives `R` through its structure morphism. -/
theorem algebraMap_sections (U : Over (Spec Rc)) (r : R) :
    algebraMap R ((algΓ Rc).obj U).unop r = U.hom.appTop ((Scheme.ΓSpecIso Rc).inv r) := rfl

omit [DecidableEq I] in
/-- If the coefficients of `v` become `δ_{n,M}` in `B`, then evaluating `v` at the character
`χ` gives `χ(M)`. -/
theorem lift_eq_of_coeff {Λ : Type u} [AddCommGroup Λ] {B : CommAlgCat.{u} Rc}
    (χ : Multiplicative Λ →* Bˣ) (v : AddMonoidAlgebra Rc Λ) (M : Λ)
    (h1 : algebraMap R B (v.coeff M) = 1)
    (h0 : ∀ n, n ≠ M → algebraMap R B (v.coeff n) = 0) :
    (Diagonalizable.lift Rc Λ χ).hom v = (χ (.ofAdd M) : B) := by
  conv_lhs => rw [← v.sum_coeff_single]
  rw [map_finsuppSum, Finsupp.sum, Finset.sum_eq_single M]
  · rw [Diagonalizable.lift_single, Algebra.smul_def, h1, one_mul]
  · intro n _ hn
    rw [Diagonalizable.lift_single, Algebra.smul_def, h0 n hn, zero_mul]
  · intro hM
    rw [Finsupp.notMem_support_iff.mp hM, AddMonoidAlgebra.single_zero, map_zero]

/-- **Local constancy of the character map.** Every point of `Spec R` lies in the basic open
set of an idempotent `e` over which `τ` pulls exponent characters back along one fixed linear
map. -/
theorem exists_isIdempotentElem_characterMapOn (s : Spec Rc) :
    ∃ e : R, IsIdempotentElem e ∧ s ∈ (Spec Rc).basicOpen ((Scheme.ΓSpecIso Rc).inv e) ∧
      ∃ h : (I' → ℤ) →ₗ[ℤ] (I → ℤ),
        CharacterMapOn τ ((Spec Rc).basicOpen ((Scheme.ΓSpecIso Rc).inv e)) h := by
  classical
  have hex : ∀ j', ∃ M : I → ℤ, (coordinateUnits τ j').value.coeff M ∉ s.asIdeal := by
    intro j'
    by_contra hc
    push Not at hc
    have hsum := (coordinateUnits τ j').isGrouplike_value.sum_coeff
    apply s.isPrime.ne_top
    rw [Ideal.eq_top_iff_one]
    have h1 : ((1 : DiagonalizableCharacter.baseAlg Rc) : R) ∈ s.asIdeal := by
      rw [← hsum]
      exact Ideal.sum_mem _ (fun n _ => hc n)
    exact h1
  choose M hM using hex
  set c : I' → R := fun j' => (coordinateUnits τ j').value.coeff (M j') with hc
  have hidem : ∀ j', IsIdempotentElem (c j') := fun j' =>
    (coordinateUnits τ j').isGrouplike_value.isIdempotentElem_coeff (M j')
  set e : R := ∏ j', c j' with he
  have he_idem : IsIdempotentElem e :=
    Finset.prod_induction _ IsIdempotentElem (fun _ _ ha hb => ha.mul hb)
      IsIdempotentElem.one (fun j' _ => hidem j')
  have hes : e ∉ s.asIdeal := by
    have : s.asIdeal.IsPrime := s.isPrime
    rw [he, Ideal.IsPrime.prod_mem_iff]
    rintro ⟨j', -, hj'⟩
    exact hM j' hj'
  refine ⟨e, he_idem, ?_, Fintype.linearCombination ℤ M, ?_⟩
  · rw [basicOpen_eq_of_affine]
    exact hes
  intro U hU x m
  -- the image of `e` in `Γ(U)` is `1`
  let φ : R →+* Γ(U.left, ⊤) := algebraMap R ((algΓ Rc).obj U).unop
  have hφ : ∀ r, φ r = U.hom.appTop ((Scheme.ΓSpecIso Rc).inv r) := fun _ => rfl
  have hunit : IsUnit (φ e) := by
    rw [hφ]
    apply isUnit_of_basicOpen_eq_top'
    rw [← Scheme.preimage_basicOpen_top]
    exact hU
  have hc1 : ∀ j', φ (c j') = 1 := by
    intro j'
    have hdvd : φ (c j') ∣ φ e := map_dvd φ (Finset.dvd_prod_of_mem c (Finset.mem_univ j'))
    exact (IsIdempotentElem.iff_eq_one_of_isUnit (isUnit_of_dvd_unit hdvd hunit)).1
      ((hidem j').map φ)
  have hc0 : ∀ j' n, n ≠ M j' → φ ((coordinateUnits τ j').value.coeff n) = 0 := by
    intro j' n hn
    have h := (coordinateUnits τ j').isGrouplike_value.coeff_mul_coeff_of_ne hn
    have h' := congrArg φ h
    rw [map_mul, map_zero] at h'
    have h1 : φ ((coordinateUnits τ j').value.coeff (M j')) = 1 := hc1 j'
    rwa [h1, one_mul] at h'
  -- the coordinates of `τ` are the characters `M j'`
  set y := x ≫ (diagIso (I := I)).inv.hom.hom with hy
  have hx : x = y ≫ (diagIso (I := I)).hom.hom.hom := by
    rw [hy, Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id, Grp.id_hom_hom, Category.comp_id]
  set χ := Diagonalizable.characterPointsEquiv Rc (I → ℤ) U y with hχ
  have hpt : ∀ j', pointsEquiv I' U (x ≫ τ.hom.hom) j' = χ (.ofAdd (M j')) := by
    intro j'
    apply Units.ext
    have h := (coordinateUnits τ j').app_eq U y
    have hl : ((coordinateUnits τ j').app U y : Γ(U.left, ⊤)) =
        (pointsEquiv I' U (x ≫ τ.hom.hom) j' : Γ(U.left, ⊤)) := by
      rw [hx]
      rfl
    rw [hl] at h
    rw [h]
    exact lift_eq_of_coeff _ _ _ (hc1 j') (hc0 j')
  calc ∏ j', pointsEquiv I' U (x ≫ τ.hom.hom) j' ^ m j'
      = ∏ j', χ (.ofAdd (M j')) ^ m j' := Finset.prod_congr rfl fun j' _ => by rw [hpt]
    _ = χ (.ofAdd (Fintype.linearCombination ℤ M m)) := by
        rw [Fintype.linearCombination_apply, ofAdd_sum, map_prod]
        refine Finset.prod_congr rfl fun j' _ => ?_
        rw [ofAdd_zsmul, map_zpow]
    _ = ∏ j, pointsEquiv I U x j ^ (Fintype.linearCombination ℤ M m) j :=
        characterPointsEquiv_diag U x _

end Idempotents

end splitTorus

end Langlands.GroupScheme
