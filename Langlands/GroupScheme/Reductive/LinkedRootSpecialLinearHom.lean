import Langlands.GroupScheme.SpecialLinearBinaryPresentation
import Langlands.GroupScheme.Reductive.LinkedRootRationalRelation
import Langlands.GroupScheme.GaloisPointRational
import Langlands.GroupScheme.Reductive.SplitRankOneRootCellUniversal
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # The rank-one homomorphism from binary SL of a linked root parametrization -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

namespace LinkedRootParametrization

open RankOneRootCellRelation SpecialLinear.BinaryPresentation

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {i : T.toGrp ⟶ G} {α : characterLattice T} {ν : cocharacterLattice T}

section TestScheme

variable (Z : Over (Spec (CommRingCat.of k)))

/-- The cocharacter `ν`, composed with `i`, at a unit of the global sections of the test
scheme `Z`. -/
def cocharacterPointAt (i : T.toGrp ⟶ G) (ν : cocharacterLattice T) :
    Γ(Z.left, ⊤)ˣ →* (Z ⟶ G.X) where
  toFun u := (Gm.pointsEquiv _ Z).symm u ≫ (CommGroupScheme.groupHom ν).hom.hom ≫ i.hom.hom
  map_one' := by
    simp only [map_one, MonObj.one_comp]
  map_mul' a b := by
    simp only [map_mul, MonObj.mul_comp]

omit [IsAffineHom G.X.hom] in
theorem cocharacterPointAt_apply (u : Γ(Z.left, ⊤)ˣ) :
    cocharacterPointAt Z i ν u =
      (Gm.pointsEquiv _ Z).symm u ≫ (CommGroupScheme.groupHom ν).hom.hom ≫ i.hom.hom :=
  rfl

/-- On the cocharacter point at a unit `u`, the character `α` takes the value
`u ^ ⟨α, ν⟩`. -/
theorem cu_cocharacterAt (u : Γ(Z.left, ⊤)ˣ) :
    cu α ((Gm.pointsEquiv _ Z).symm u ≫ (CommGroupScheme.groupHom ν).hom.hom) =
      u ^ latticePairing T α ν := by
  rw [cu, ← comp_groupHom_comp, eq_gmEndEquiv_zsmul k (ν ≫ α), comp_groupHom_zsmul,
    ← latticePairing_apply]
  have hid : ∀ x : Z ⟶ (Gm (Spec (CommRingCat.of k))).X,
      x ≫ (CommGroupScheme.groupHom (𝟙 (Gm (Spec (CommRingCat.of k))))).hom.hom = x :=
    fun x => Category.comp_id x
  rw [hid, map_zpow, MulEquiv.apply_symm_apply]

variable (X : LinkedRootParametrization i α ν)

/-- The cocharacter point at `u` scales the positive root group by `u ^ 2` when
`⟨α, ν⟩ = 2`. -/
theorem cocharacterPointAt_conj_positive (h2 : latticePairing T α ν = 2)
    (u : Γ(Z.left, ⊤)ˣ) (c : Γ(Z.left, ⊤)) :
    cocharacterPointAt Z i ν u * (gpt c ≫ X.positive.hom.hom) *
        (cocharacterPointAt Z i ν u)⁻¹ =
      gpt ((u : Γ(Z.left, ⊤)) ^ 2 * c) ≫ X.positive.hom.hom := by
  have h := X.positive_equivariant Z
    ((Gm.pointsEquiv _ Z).symm u ≫ (CommGroupScheme.groupHom ν).hom.hom) c
  rw [charValue_eq_cu, cu_cocharacterAt, h2] at h
  simp only [Category.assoc] at h
  have hv : ((u ^ (2 : ℤ) : Γ(Z.left, ⊤)ˣ) : Γ(Z.left, ⊤)) = (u : Γ(Z.left, ⊤)) ^ 2 := by
    rw [zpow_two, Units.val_mul, sq]
  rw [hv] at h
  exact h

/-- The cocharacter point at `u` scales the negative root group by `u⁻¹ ^ 2` when
`⟨α, ν⟩ = 2`. -/
theorem cocharacterPointAt_conj_negative (h2 : latticePairing T α ν = 2)
    (u : Γ(Z.left, ⊤)ˣ) (c : Γ(Z.left, ⊤)) :
    cocharacterPointAt Z i ν u * (gpt c ≫ X.negative.hom.hom) *
        (cocharacterPointAt Z i ν u)⁻¹ =
      gpt (((u⁻¹ : Γ(Z.left, ⊤)ˣ) : Γ(Z.left, ⊤)) ^ 2 * c) ≫ X.negative.hom.hom := by
  have h := X.negative_equivariant Z
    ((Gm.pointsEquiv _ Z).symm u ≫ (CommGroupScheme.groupHom ν).hom.hom) c
  rw [charValue_eq_cu, cu_neg, cu_cocharacterAt, h2] at h
  simp only [Category.assoc] at h
  have hv : (((u ^ (2 : ℤ))⁻¹ : Γ(Z.left, ⊤)ˣ) : Γ(Z.left, ⊤)) =
      ((u⁻¹ : Γ(Z.left, ⊤)ˣ) : Γ(Z.left, ⊤)) ^ 2 := by
    rw [zpow_two, mul_inv, Units.val_mul, sq]
  rw [hv] at h
  exact h

/-- The points of a linked root parametrization over a test scheme `Z`, read through a
ring map `σ` from a field `E` to the global sections of `Z`, satisfy the big-cell
relations of binary `SL` over `E`, provided `⟨α, ν⟩ = 2`. -/
def bigCellRelationsAt (h2 : latticePairing T α ν = 2) (E : Type u) [Field E]
    (σ : E →+* Γ(Z.left, ⊤)) : BigCellRelations E (Z ⟶ G.X) where
  x c := gpt (σ c) ≫ X.positive.hom.hom
  y c := gpt (σ c) ≫ X.negative.hom.hom
  h := (cocharacterPointAt Z i ν).comp (Units.map σ.toMonoidHom)
  x_add a a' := by
    simp only [map_add, gpt_add, MonObj.mul_comp]
  y_add b b' := by
    simp only [map_add, gpt_add, MonObj.mul_comp]
  conj_x u a := by
    rw [MonoidHom.comp_apply, cocharacterPointAt_conj_positive Z X h2, map_mul, map_pow,
      Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
  conj_y u b := by
    rw [MonoidHom.comp_apply, cocharacterPointAt_conj_negative Z X h2, map_mul, map_pow,
      ← map_inv, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      Units.val_inv_eq_inv_val]
  rel a b u hu := by
    have h := X.relation Z (gpt (σ a)) (gpt (σ b)) (gpt (σ ((u : E)⁻¹ * a)))
      (gpt (σ ((u : E)⁻¹ * b))) (Units.map σ.toMonoidHom u)
      (by simp [hu]) (by simp [Units.val_inv_eq_inv_val])
      (by simp [Units.val_inv_eq_inv_val])
    exact h

@[simp] theorem bigCellRelationsAt_x (h2 : latticePairing T α ν = 2) (E : Type u) [Field E]
    (σ : E →+* Γ(Z.left, ⊤)) (c : E) :
    (X.bigCellRelationsAt Z h2 E σ).x c = gpt (σ c) ≫ X.positive.hom.hom :=
  rfl

@[simp] theorem bigCellRelationsAt_y (h2 : latticePairing T α ν = 2) (E : Type u) [Field E]
    (σ : E →+* Γ(Z.left, ⊤)) (c : E) :
    (X.bigCellRelationsAt Z h2 E σ).y c = gpt (σ c) ≫ X.negative.hom.hom :=
  rfl

@[simp] theorem bigCellRelationsAt_h (h2 : latticePairing T α ν = 2) (E : Type u) [Field E]
    (σ : E →+* Γ(Z.left, ⊤)) (v : Eˣ) :
    (X.bigCellRelationsAt Z h2 E σ).h v =
      cocharacterPointAt Z i ν (Units.map σ.toMonoidHom v) :=
  rfl

end TestScheme

variable (X : LinkedRootParametrization i α ν)

/-- The rational points `x₊`, `x₋` and the cocharacter points satisfy the big-cell relations
of binary `SL` over `k`, provided `⟨α, ν⟩ = 2`. -/
def bigCellRelations (h2 : latticePairing T α ν = 2) :
    BigCellRelations k (rationalPoints G) :=
  X.bigCellRelationsAt (Over.mk (𝟙 (Spec (CommRingCat.of k)))) h2 k (secMap k)

@[simp] theorem bigCellRelations_x (h2 : latticePairing T α ν = 2) (c : k) :
    (X.bigCellRelations h2).x c = X.xpPoint c :=
  rfl

@[simp] theorem bigCellRelations_y (h2 : latticePairing T α ν = 2) (c : k) :
    (X.bigCellRelations h2).y c = X.xmPoint c :=
  rfl

@[simp] theorem bigCellRelations_h (h2 : latticePairing T α ν = 2) (v : kˣ) :
    (X.bigCellRelations h2).h v = cocharacterPoint i ν v :=
  rfl

section Extension

variable (k) (E : Type u) [Field E] [Algebra k E]

/-- The spectrum of a field extension `E` of `k`, as a test scheme over `Spec k`. -/
abbrev extensionTest : Over (Spec (CommRingCat.of k)) :=
  Over.mk (GaloisPointComparison.baseMap k E)

/-- The structure map of the extension test scheme, as a map to the terminal test
scheme. -/
def extensionMap : extensionTest k E ⟶ Over.mk (𝟙 (Spec (CommRingCat.of k))) :=
  Over.homMk (GaloisPointComparison.baseMap k E) (by simp)

/-- Pulling rational points back to the extension test scheme. -/
def extensionPoints : rationalPoints G →* (extensionTest k E ⟶ G.X) where
  toFun x := extensionMap k E ≫ x
  map_one' := MonObj.comp_one _
  map_mul' _ _ := MonObj.comp_mul _ _ _

omit [IsAffineHom G.X.hom] in
@[simp] theorem extensionPoints_apply (x : rationalPoints G) :
    extensionPoints k E x = extensionMap k E ≫ x :=
  rfl

/-- Pulling rational points back to a field extension is injective. -/
theorem extensionPoints_injective : Function.Injective (extensionPoints (G := G) k E) := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  intro x y hxy
  apply (GaloisPointComparison.rationalCoeffEquiv k G).injective
  apply GaloisPoint.extend_injective k E G
  apply Over.OverMorphism.ext
  have h := congrArg (fun p => p.left) hxy
  change GaloisPointComparison.baseMap k E ≫ x.left =
    GaloisPointComparison.baseMap k E ≫ y.left at h
  change GaloisPointComparison.baseMap k E ≫ (GaloisPointComparison.rationalCoeffEquiv k G x).left =
    GaloisPointComparison.baseMap k E ≫ (GaloisPointComparison.rationalCoeffEquiv k G y).left
  rw [GaloisPointComparison.rationalCoeffEquiv_left,
    GaloisPointComparison.rationalCoeffEquiv_left]
  exact h

/-- The identification of `E` with the global sections of `Spec E`. -/
abbrev extensionSecMap : E →+* Γ((extensionTest k E).left, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of E)).inv.hom

theorem extensionMap_appTop_secMap (c : k) :
    (extensionMap k E).left.appTop (secMap k c) = extensionSecMap k E (algebraMap k E c) := by
  have h := congrArg (fun g => g.hom c)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap k E)))
  exact h.symm

end Extension

/-- A linked root parametrization with `⟨α, ν⟩ = 2` gives a homomorphism from `SL₂(k)` to
the rational points of `G` sending the upper, lower and diagonal matrices to `x₊`, `x₋` and
the cocharacter points. The field `k` may be finite. -/
theorem exists_specialLinearHom (h2 : latticePairing T α ν = 2) :
    ∃ φ : Matrix.SpecialLinearGroup (Fin 2) k →* rationalPoints G,
      (∀ t, φ (upper t) = X.xpPoint t) ∧ (∀ t, φ (lower t) = X.xmPoint t) ∧
        ∀ v, φ (diag v) = cocharacterPoint i ν v := by
  let E := AlgebraicClosure k
  let R' := X.bigCellRelationsAt (extensionTest k E) h2 E (extensionSecMap k E)
  refine exists_hom_of_embedding R' exists_ne_ne_of_infinite (algebraMap k E)
    (extensionPoints k E) (extensionPoints_injective k E) X.xpPoint X.xmPoint
    (cocharacterPoint i ν) ?_ ?_ ?_
  · intro t
    rw [extensionPoints_apply, xpPoint, ← Category.assoc, comp_gpt,
      extensionMap_appTop_secMap]
    rfl
  · intro t
    rw [extensionPoints_apply, xmPoint, ← Category.assoc, comp_gpt,
      extensionMap_appTop_secMap]
    rfl
  · intro v
    rw [extensionPoints_apply, bigCellRelationsAt_h, cocharacterPointAt_apply]
    change extensionMap k E ≫ ((Gm.pointsEquiv _ _).symm (Units.map (secMap k).toMonoidHom v) ≫
      (CommGroupScheme.groupHom ν).hom.hom ≫ i.hom.hom) = _
    rw [← Category.assoc, ← RootCell.symm_pointsEquiv_comp]
    congr 2
    apply Units.ext
    rw [RootCell.coe_units_map, Units.coe_map, Units.coe_map]
    exact extensionMap_appTop_secMap k E v

/-- The rank-one homomorphism `SL₂(k) → G(k)` of a linked root parametrization with
`⟨α, ν⟩ = 2`. -/
def specialLinearHom (h2 : latticePairing T α ν = 2) :
    Matrix.SpecialLinearGroup (Fin 2) k →* rationalPoints G :=
  Classical.choose (X.exists_specialLinearHom h2)

theorem specialLinearHom_upper (h2 : latticePairing T α ν = 2) (t : k) :
    X.specialLinearHom h2 (upper t) = X.xpPoint t :=
  (Classical.choose_spec (X.exists_specialLinearHom h2)).1 t

theorem specialLinearHom_lower (h2 : latticePairing T α ν = 2) (t : k) :
    X.specialLinearHom h2 (lower t) = X.xmPoint t :=
  (Classical.choose_spec (X.exists_specialLinearHom h2)).2.1 t

theorem specialLinearHom_diag (h2 : latticePairing T α ν = 2) (v : kˣ) :
    X.specialLinearHom h2 (diag v) = cocharacterPoint i ν v :=
  (Classical.choose_spec (X.exists_specialLinearHom h2)).2.2 v

/-- The Weyl matrix goes to `x₊(-1) x₋(1) x₊(-1)`. -/
theorem specialLinearHom_weylMatrix (h2 : latticePairing T α ν = 2) :
    X.specialLinearHom h2 SpecialLinear.BinaryUpper.weylMatrix =
      X.xpPoint (-1) * X.xmPoint 1 * X.xpPoint (-1) := by
  rw [weylMatrix_eq, map_mul, map_mul, specialLinearHom_upper, specialLinearHom_lower]

/-- The rank-one homomorphism is the only homomorphism with the prescribed values on the
upper and lower unipotent matrices. -/
theorem eq_specialLinearHom (h2 : latticePairing T α ν = 2)
    (φ : Matrix.SpecialLinearGroup (Fin 2) k →* rationalPoints G)
    (hx : ∀ t, φ (upper t) = X.xpPoint t) (hy : ∀ t, φ (lower t) = X.xmPoint t) :
    φ = X.specialLinearHom h2 :=
  hom_ext (fun t => by rw [hx, specialLinearHom_upper])
    (fun t => by rw [hy, specialLinearHom_lower])

end LinkedRootParametrization

end Langlands.GroupScheme
