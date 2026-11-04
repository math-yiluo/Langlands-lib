import Langlands.GroupScheme.CentralSurjectionImage.SurjectiveCharacterPoint

/-! # Infinite-order character values without commutativity -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme

open CentralSurjectionImage CocharacterDatum

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}

namespace rationalCharacters

/-- A surjective character of any group scheme takes a value of infinite order at
some point over an algebraically closed extension field. -/
theorem exists_infiniteOrder_point_of_surjective (χ : rationalCharacters G)
    (hχ : Surjective χ.toMul.hom.hom.left) :
    ∃ (K : Type u) (_ : Field K) (_ : IsAlgClosed K) (_ : Algebra k K)
      (x : Lie.AffinePoints G K), ∀ n : ℕ, n ≠ 0 →
        Lie.characterValue (𝟙 (Gm (Spec (CommRingCat.of k)))) (x ≫ χ.toMul.hom.hom) ^ n ≠ 1 := by
  classical
  let R := CommRingCat.of k
  let L := FractionRing (Polynomial k)
  let X₀ : L := algebraMap (Polynomial k) L Polynomial.X
  have hX₀ : X₀ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (Polynomial k) L)).mpr Polynomial.X_ne_zero
  let t₀ : Lˣ := Units.mk0 X₀ hX₀
  let G₁ := Gm (Spec R)
  let y : Lie.AffinePoints G₁.toGrp L :=
    (Gm.affinePointsEquiv (R := CommRingCat.of L)
      ((algSpec R).obj (op (CommAlgCat.of R L))).hom).symm t₀
  let yL : Spec (CommRingCat.of L) ⟶ G₁.X.left := y.left
  let χL := χ.toMul.hom.hom.left
  obtain ⟨z, hz⟩ := hχ.surj (yL (IsLocalRing.closedPoint L))
  let α := G₁.X.left.descResidueField (Scheme.stalkClosedPointTo yL)
  have hα : Spec.map α ≫ G₁.X.left.fromSpecResidueField _ = yL :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField L _ yL
  let β := (G₁.X.left.residueFieldCongr hz.symm).hom ≫ χL.residueFieldMap z
  have hβ : Spec.map β ≫ G₁.X.left.fromSpecResidueField _ =
      G.X.left.fromSpecResidueField z ≫ χL := by
    rw [Spec.map_comp, Category.assoc, Scheme.residueFieldCongr_fromSpecResidueField,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
  obtain ⟨K, _, _, a, b, hab⟩ := exists_isAlgClosed_compositum β.hom α.hom
  let : Algebra k K := (b.comp (algebraMap k L)).toAlgebra
  let b' : L →ₐ[k] K := { b with commutes' := fun r => rfl }
  let x' : Spec (CommRingCat.of K) ⟶ G.X.left :=
    Spec.map (CommRingCat.ofHom a) ≫ G.X.left.fromSpecResidueField z
  have e : β ≫ CommRingCat.ofHom a = α ≫ CommRingCat.ofHom b := by
    ext r
    exact congrArg (fun f : _ →+* K => f r) hab
  have hx' : x' ≫ χL = Spec.map (CommRingCat.ofHom b) ≫ yL := by
    calc x' ≫ χL = Spec.map (CommRingCat.ofHom a) ≫ (G.X.left.fromSpecResidueField z ≫ χL) :=
          Category.assoc _ _ _
      _ = Spec.map (CommRingCat.ofHom a) ≫ (Spec.map β ≫ G₁.X.left.fromSpecResidueField _) := by
          rw [hβ]
      _ = Spec.map (β ≫ CommRingCat.ofHom a) ≫ G₁.X.left.fromSpecResidueField _ := by
          simp only [Spec.map_comp, Category.assoc]
      _ = Spec.map (α ≫ CommRingCat.ofHom b) ≫ G₁.X.left.fromSpecResidueField _ := by rw [e]
      _ = Spec.map (CommRingCat.ofHom b) ≫ (Spec.map α ≫ G₁.X.left.fromSpecResidueField _) := by
          simp only [Spec.map_comp, Category.assoc]
      _ = Spec.map (CommRingCat.ofHom b) ≫ yL := congrArg (Spec.map (CommRingCat.ofHom b) ≫ ·) hα
  have hw : x' ≫ G.X.hom = ((algSpec R).obj (op (CommAlgCat.of R K))).hom := by
    have h1 : χL ≫ G₁.X.hom = G.X.hom := Over.w χ.toMul.hom.hom
    have h2 : yL ≫ G₁.X.hom = ((algSpec R).obj (op (CommAlgCat.of R L))).hom := Over.w y
    rw [← h1, ← Category.assoc, hx', Category.assoc, h2, algSpec_obj_hom, algSpec_obj_hom,
      ← Spec.map_comp]
    rfl
  let x : Lie.AffinePoints G K := Over.homMk x' hw
  refine ⟨K, inferInstance, inferInstance, inferInstance, x, ?_⟩
  have hxχ : x ≫ χ.toMul.hom.hom = Lie.affineMap G₁.toGrp b' y := by
    apply Over.OverMorphism.ext
    change x' ≫ χL = ((algSpec R).map (CommAlgCat.ofHom b').op).left ≫ yL
    rw [hx']
    rfl
  have hval : Lie.characterValue (𝟙 (Gm (Spec (CommRingCat.of k)))) (x ≫ χ.toMul.hom.hom) =
      Units.map b'.toMonoidHom t₀ := by
    have h1 : Lie.characterValue (𝟙 (Gm (Spec (CommRingCat.of k)))) (x ≫ χ.toMul.hom.hom) =
        Lie.characterValue (𝟙 G₁) (Lie.affineMap G₁.toGrp b' y) := by
      rw [characterValue_id, ← hxχ]
      rfl
    rw [h1, characterValue_affineMap, characterValue_id]
    congr 1
    exact MulEquiv.apply_symm_apply _ _
  intro n hn h
  rw [hval, ← map_pow] at h
  have h' := congrArg (fun u : Kˣ => (u : K)) h
  simp only [Units.coe_map, Units.val_pow_eq_pow_val, Units.val_one] at h'
  apply X_pow_ne_one (k := k) n hn
  apply b'.toRingHom.injective
  rw [map_one]
  exact h'

end rationalCharacters

/-- Surjectivity supplies an infinite-order value after extending the field, with no
commutativity, finiteness, smoothness or connectedness assumption on the source. -/
def SurjectiveCharacterInfiniteOrderPointStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (χ : rationalCharacters G), Surjective χ.toMul.hom.hom.left →
    ∃ (K : Type u) (_ : Field K) (_ : IsAlgClosed K) (_ : Algebra k K)
      (x : Lie.AffinePoints G K), ∀ n : ℕ, n ≠ 0 →
        Lie.characterValue (𝟙 (Gm (Spec (CommRingCat.of k))))
          (x ≫ χ.toMul.hom.hom) ^ n ≠ 1

/-- Lift a transcendental unit and embed the two residue fields into a common algebraically
closed field. -/
theorem surjectiveCharacterInfiniteOrderPoint :
    SurjectiveCharacterInfiniteOrderPointStatement.{u} := by
  intro k _ G χ hχ
  exact rationalCharacters.exists_infiniteOrder_point_of_surjective χ hχ

end Langlands.GroupScheme
