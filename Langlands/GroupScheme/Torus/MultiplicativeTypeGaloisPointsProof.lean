import Langlands.GroupScheme.Torus.MultiplicativeTypeGaloisPointsStatement
import Langlands.GroupScheme.Torus.MultiplicativeTypeFiniteGaloisSplittingProof
import Langlands.GroupScheme.Torus.MultiplicativeTypeSplitCategory
import Langlands.GroupScheme.AlgebraicGaloisPointDescent

/-! # Points of multiplicative-type groups over intermediate fields -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme
namespace MultiplicativeTypeGaloisPoints

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000

section Evaluation

variable {F : Type u} [Field F]
  {H : GroupScheme (Spec (CommRingCat.of F))}
  {M : Type u} [AddCommGroup M]
  (e : H ≅ (Diagonalizable.groupScheme (CommRingCat.of F) M).toGrp)

/-- Pullback along the specified diagonalizable model identifies all actual characters. -/
private def modelCharacters : M ≃+ rationalCharacters H :=
  (DiagonalizableCharacter.evalCharacterEquiv F M).trans
    { toFun := characterRestrict e.hom
      invFun := characterRestrict e.inv
      left_inv := fun χ => by
        change Additive.ofMul (e.inv ≫ e.hom ≫ χ.toMul) = χ
        rw [← Category.assoc, e.inv_hom_id, Category.id_comp]
        rfl
      right_inv := fun χ => by
        change Additive.ofMul (e.hom ≫ e.inv ≫ χ.toMul) = χ
        rw [← Category.assoc, e.hom_inv_id, Category.id_comp]
        rfl
      map_add' := (characterRestrict e.hom).map_add }

/-- The actual point model of a diagonalizable group, with values in field units. -/
private def modelPoints : rationalPoints H ≃* (Multiplicative M →* Fˣ) :=
  (isoPointsEquiv e (Over.mk (𝟙 _))).trans
    ((Diagonalizable.characterPointsEquiv (CommRingCat.of F) M (Over.mk (𝟙 _))).trans
      (MulEquiv.monoidHomCongrRight
        (Units.mapEquiv (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.toMulEquiv)))

/-- The character correspondence and the point correspondence agree by evaluation. -/
private theorem eval_modelCharacters (x : rationalPoints H) (m : M) :
    rationalCharacterEval (modelCharacters e m) x = modelPoints e x (.ofAdd m) := by
  rw [modelCharacters, AddEquiv.trans_apply, DiagonalizableCharacter.evalCharacterEquiv_apply]
  change rationalCharacterEval
    (characterRestrict e.hom (DiagonalizableCharacter.evalCharacter _ M m)) x = _
  rw [rationalCharacterEval_characterRestrict]
  change Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom.toMonoidHom
      (Gm.pointsEquiv _ _ ((x ≫ e.hom.hom.hom) ≫
        (CommGroupScheme.groupHom (DiagonalizableCharacter.evalCharacter _ M m)).hom.hom)) = _
  rw [DiagonalizableCharacter.evalCharacter_apply]
  rfl

include e

/-- Characters separate the points of every group with a diagonalizable model. -/
private theorem evaluation_ext {x y : rationalPoints H}
    (h : ∀ χ : rationalCharacters H, rationalCharacterEval χ x = rationalCharacterEval χ y) :
    x = y := by
  apply (modelPoints e).injective
  apply MonoidHom.ext
  intro m
  simpa only [eval_modelCharacters, ofAdd_toAdd] using
    h (modelCharacters e m.toAdd)

/-- Every multiplicative character-value function is represented by a point. -/
private theorem exists_evaluation (f : rationalCharacters H → Fˣ)
    (hf : ∀ χ ψ, f (χ + ψ) = f χ * f ψ) :
    ∃ x : rationalPoints H, ∀ χ, rationalCharacterEval χ x = f χ := by
  have hzero : f 0 = 1 := by
    apply mul_left_cancel (a := f 0)
    rw [mul_one, ← hf, zero_add]
  let g : Multiplicative M →* Fˣ :=
    { toFun := fun m => f (modelCharacters e m.toAdd)
      map_one' := by simpa using hzero
      map_mul' := fun m n => by
        change f (modelCharacters e (m.toAdd + n.toAdd)) = _
        rw [map_add, hf] }
  refine ⟨(modelPoints e).symm g, fun χ => ?_⟩
  obtain ⟨m, rfl⟩ := (modelCharacters e).surjective χ
  rw [eval_modelCharacters, MulEquiv.apply_symm_apply]
  rfl

end Evaluation

section Descent

open GaloisPoint
open Langlands.AlgebraicGeometry.PointTopology

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffine G.X.left]
  (K : IntermediateField k L)

/-- Coordinates commute with extension from an intermediate field. -/
private theorem coordinates_intermediate (x : G.affinePoints (CommAlgCat.of k K))
    (a : AffineCoordinateRing k G.X) :
    coordinates k G L (G.affinePointMap (CommAlgCat.ofHom K.val) x) a =
      K.val (coordinates k G K x a) := by
  rw [coordinates_apply, coordinates_apply]
  exact G.affinePointEvaluation_map (CommAlgCat.ofHom K.val) x a

/-- Extension from an intermediate field is injective. -/
private theorem intermediate_injective :
    Function.Injective (G.affinePointMap (CommAlgCat.ofHom K.val)) := by
  intro x y h
  apply (coordinates k G K).injective
  apply AlgHom.ext
  intro a
  apply K.val.injective
  change K.val (coordinates k G K x a) = K.val (coordinates k G K y a)
  rw [← coordinates_intermediate, ← coordinates_intermediate, h]

/-- An intermediate-field point is fixed by every coefficient automorphism fixing that field. -/
private theorem conjugate_intermediate (σ : L ≃ₐ[k] L) (hσ : ∀ a ∈ K, σ a = a)
    (x : G.affinePoints (CommAlgCat.of k K)) :
    conjugate k L G σ (G.affinePointMap (CommAlgCat.ofHom K.val) x) =
      G.affinePointMap (CommAlgCat.ofHom K.val) x := by
  apply (coordinates k G L).injective
  ext a
  rw [coordinates_conjugate, coordinates_intermediate]
  exact hσ _ (coordinates k G K x a).property

/-- A point fixed by the fixing subgroup descends to the intermediate field. -/
private theorem exists_intermediate [IsGalois k L]
    (x : G.affinePoints (CommAlgCat.of k L))
    (hx : ∀ σ : L ≃ₐ[k] L, (∀ a ∈ K, σ a = a) → conjugate k L G σ x = x) :
    ∃ y : G.affinePoints (CommAlgCat.of k K),
      G.affinePointMap (CommAlgCat.ofHom K.val) y = x := by
  have hcoord (a : AffineCoordinateRing k G.X) : coordinates k G L x a ∈ K := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup K, IntermediateField.mem_fixedField_iff]
    intro σ hσ
    have h := congrArg (fun z => coordinates k G L z a)
      (hx σ ((IntermediateField.mem_fixingSubgroup_iff K σ).mp hσ))
    simpa only [coordinates_conjugate] using h
  let f : AffineCoordinateRing k G.X →ₐ[k] K :=
    (coordinates k G L x).codRestrict K.toSubalgebra hcoord
  refine ⟨(coordinates k G K).symm f, ?_⟩
  apply (coordinates k G L).injective
  ext a
  rw [coordinates_intermediate, Equiv.apply_symm_apply]
  rfl

end Descent

section IntermediateValues

open GaloisPoint GaloisPointComparison

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  (G : GroupScheme (Spec (CommRingCat.of k))) (K : IntermediateField k L)

private def intermediatePoint (x : G.affinePoints (CommAlgCat.of k K)) :
    rationalPoints (baseChanged k L G) :=
  (baseChangeCoeffEquiv k L G).symm (G.affinePointMap (CommAlgCat.ofHom K.val) x)

private def characterValues (x : rationalPoints (baseChanged k L G))
    (χ : rationalCharacters (baseChanged k L G)) : Lˣ :=
  rationalCharacterEval (G := (GroupScheme.baseChange (algebraBaseMap k L)).obj G) χ x

private def characterConjugate (σ : L ≃ₐ[k] L)
    (χ : rationalCharacters (baseChanged k L G)) : rationalCharacters (baseChanged k L G) :=
  rationalCharacters.galoisRepresentation k L G σ χ

private def unitConjugate (σ : L ≃ₐ[k] L) (z : Lˣ) : Lˣ :=
  Units.map σ.toMonoidHom z

private def intermediateValues (x : G.affinePoints (CommAlgCat.of k K)) :
    rationalCharacters (baseChanged k L G) → Lˣ :=
  characterValues k L G (intermediatePoint k L G K x)

private def IsEquivariantValue (f : rationalCharacters (baseChanged k L G) → Lˣ) : Prop :=
  (∀ χ ψ, f (χ + ψ) = f χ * f ψ) ∧
    ∀ σ : L ≃ₐ[k] L, (∀ a ∈ K, σ a = a) → ∀ χ,
      f (characterConjugate k L G σ χ) = unitConjugate k L σ (f χ)

private theorem intermediatePoint_injective [IsAffine G.X.left] :
    Function.Injective (intermediatePoint k L G K) :=
  (baseChangeCoeffEquiv k L G).symm.injective.comp (intermediate_injective k L G K)

private theorem rationalConjugate_fixed_iff (σ : L ≃ₐ[k] L)
    (x : rationalPoints (baseChanged k L G)) :
    rationalConjugate k L G σ x = x ↔
      conjugate k L G σ (baseChangeCoeffEquiv k L G x) = baseChangeCoeffEquiv k L G x := by
  rw [← baseChangeCoeffEquiv_rationalConjugate, (baseChangeCoeffEquiv k L G).injective.eq_iff]

private theorem characterValues_apply (x : rationalPoints (baseChanged k L G))
    (χ : rationalCharacters (baseChanged k L G)) :
    characterValues k L G x χ =
      rationalCharacterEval (G := (GroupScheme.baseChange (algebraBaseMap k L)).obj G) χ x := rfl

private theorem characterConjugate_apply (σ : L ≃ₐ[k] L)
    (χ : rationalCharacters (baseChanged k L G)) :
    characterConjugate k L G σ χ = rationalCharacters.galoisRepresentation k L G σ χ := rfl

private theorem characterValues_conjugate_left (σ : L ≃ₐ[k] L)
    (x : rationalPoints (baseChanged k L G)) (χ : rationalCharacters (baseChanged k L G)) :
    characterValues k L G (rationalConjugate k L G σ x) (characterConjugate k L G σ χ) =
      rationalCharacterEval (G := (GroupScheme.baseChange (algebraBaseMap k L)).obj G)
        (rationalCharacters.galoisRepresentation k L G σ χ) (rationalConjugate k L G σ x) :=
  -- Separate congruence in the character from unfolding the evaluation map.
  (congrArg (characterValues k L G (rationalConjugate k L G σ x))
    (characterConjugate_apply k L G σ χ)).trans
      (characterValues_apply k L G (rationalConjugate k L G σ x) _)

private theorem characterValues_conjugate_right (σ : L ≃ₐ[k] L)
    (x : rationalPoints (baseChanged k L G)) (χ : rationalCharacters (baseChanged k L G)) :
    Units.map σ.toMonoidHom (rationalCharacterEval χ x) =
      unitConjugate k L σ (characterValues k L G x χ) := rfl

private theorem characterValues_conjugate (σ : L ≃ₐ[k] L)
    (x : rationalPoints (baseChanged k L G)) (χ : rationalCharacters (baseChanged k L G)) :
    characterValues k L G (rationalConjugate k L G σ x) (characterConjugate k L G σ χ) =
      unitConjugate k L σ (characterValues k L G x χ) :=
  (characterValues_conjugate_left k L G σ x χ).trans
    ((rationalCharacterEval_galoisRepresentation k L G σ χ x).trans
      (characterValues_conjugate_right k L G σ x χ))

private theorem characterConjugate_inv (σ : L ≃ₐ[k] L)
    (χ : rationalCharacters (baseChanged k L G)) :
    characterConjugate k L G σ (characterConjugate k L G σ⁻¹ χ) = χ :=
  rationalCharacters.galoisRepresentation_self_inv k L G σ χ

private theorem intermediateValues_equivariant [IsAffine G.X.left]
    (x : G.affinePoints (CommAlgCat.of k K))
    (σ : L ≃ₐ[k] L) (hσ : ∀ a ∈ K, σ a = a)
    (χ : rationalCharacters (baseChanged k L G)) :
    intermediateValues k L G K x (characterConjugate k L G σ χ) =
      unitConjugate k L σ (intermediateValues k L G K x χ) := by
  have hfixed :=
    (rationalConjugate_fixed_iff k L G σ (intermediatePoint k L G K x)).mpr (by
      rw [intermediatePoint, MulEquiv.apply_symm_apply]
      exact conjugate_intermediate k L G K σ hσ x)
  exact (congrArg (fun p => characterValues k L G p (characterConjugate k L G σ χ))
    hfixed.symm).trans (characterValues_conjugate k L G σ (intermediatePoint k L G K x) χ)

private theorem rationalConjugate_preserves_evaluation
    (f : rationalCharacters (baseChanged k L G) → Lˣ)
    (x : rationalPoints (baseChanged k L G)) (hx : ∀ χ, characterValues k L G x χ = f χ)
    (σ : L ≃ₐ[k] L)
    (hequiv : ∀ χ, f (characterConjugate k L G σ χ) = unitConjugate k L σ (f χ)) :
    ∀ χ : rationalCharacters (baseChanged k L G),
      characterValues k L G (rationalConjugate k L G σ x) χ = characterValues k L G x χ := by
  intro χ
  let ψ := characterConjugate k L G σ⁻¹ χ
  have hχ : characterConjugate k L G σ ψ = χ := characterConjugate_inv k L G σ χ
  calc
    characterValues k L G (rationalConjugate k L G σ x) χ =
        characterValues k L G (rationalConjugate k L G σ x) (characterConjugate k L G σ ψ) :=
      congrArg (characterValues k L G (rationalConjugate k L G σ x)) hχ.symm
    _ = unitConjugate k L σ (characterValues k L G x ψ) := characterValues_conjugate k L G σ x ψ
    _ = unitConjugate k L σ (f ψ) := congrArg (unitConjugate k L σ) (hx ψ)
    _ = f (characterConjugate k L G σ ψ) := (hequiv ψ).symm
    _ = f χ := congrArg f hχ
    _ = characterValues k L G x χ := (hx χ).symm

private theorem rationalConjugate_eq_of_characterValues
    {M : Type u} [AddCommGroup M]
    (e : baseChanged k L G ≅ (Diagonalizable.groupScheme (CommRingCat.of L) M).toGrp)
    (f : rationalCharacters (baseChanged k L G) → Lˣ)
    (x : rationalPoints (baseChanged k L G)) (hx : ∀ χ, characterValues k L G x χ = f χ)
    (σ : L ≃ₐ[k] L)
    (hequiv : ∀ χ, f (characterConjugate k L G σ χ) = unitConjugate k L σ (f χ)) :
    rationalConjugate k L G σ x = x :=
  evaluation_ext (F := L) (H := baseChanged k L G) e
    (x := rationalConjugate k L G σ x) (y := x)
    (rationalConjugate_preserves_evaluation k L G f x hx σ hequiv)

private theorem exists_intermediateValue [IsGalois k L] [IsAffine G.X.left]
    {M : Type u} [AddCommGroup M]
    (e : baseChanged k L G ≅ (Diagonalizable.groupScheme (CommRingCat.of L) M).toGrp)
    (f : rationalCharacters (baseChanged k L G) → Lˣ) (hf : IsEquivariantValue k L G K f) :
    f ∈ Set.range (intermediateValues k L G K) := by
  obtain ⟨x, hx⟩ := exists_evaluation e f hf.1
  have hfixed (σ : L ≃ₐ[k] L) (hσ : ∀ a ∈ K, σ a = a) :
      conjugate k L G σ (baseChangeCoeffEquiv k L G x) = baseChangeCoeffEquiv k L G x :=
    (rationalConjugate_fixed_iff k L G σ x).mp
      (rationalConjugate_eq_of_characterValues k L G e f x hx σ (hf.2 σ hσ))
  obtain ⟨y, hy⟩ := exists_intermediate k L G K (baseChangeCoeffEquiv k L G x) hfixed
  have hpoint : intermediatePoint k L G K y = x := by
    rw [intermediatePoint, hy, MulEquiv.symm_apply_apply]
  exact ⟨y, funext fun χ => (congrArg (rationalCharacterEval χ) hpoint).trans (hx χ)⟩

private theorem intermediateValues_injective [IsAffine G.X.left]
    {M : Type u} [AddCommGroup M]
    (e : baseChanged k L G ≅ (Diagonalizable.groupScheme (CommRingCat.of L) M).toGrp) :
    Function.Injective (intermediateValues k L G K) := by
  intro x y h
  exact intermediatePoint_injective k L G K
    (evaluation_ext (F := L) (H := baseChanged k L G) e
      (x := intermediatePoint k L G K x) (y := intermediatePoint k L G K y) (congrFun h))

private theorem intermediateValues_mul (x : G.affinePoints (CommAlgCat.of k K))
    (χ ψ : rationalCharacters (baseChanged k L G)) :
    intermediateValues k L G K x (χ + ψ) =
      intermediateValues k L G K x χ * intermediateValues k L G K x ψ :=
  rationalCharacterEval_add χ ψ (intermediatePoint k L G K x)

private theorem intermediateValues_spec [IsAffine G.X.left]
    (x : G.affinePoints (CommAlgCat.of k K)) :
    IsEquivariantValue k L G K (intermediateValues k L G K x) :=
  ⟨intermediateValues_mul k L G K x, intermediateValues_equivariant k L G K x⟩

private theorem intermediateValues_range [IsGalois k L] [IsAffine G.X.left]
    {M : Type u} [AddCommGroup M]
    (e : baseChanged k L G ≅ (Diagonalizable.groupScheme (CommRingCat.of L) M).toGrp) :
    Set.range (intermediateValues k L G K) = {f | IsEquivariantValue k L G K f} :=
  Set.Subset.antisymm (Set.range_subset_iff.mpr (intermediateValues_spec k L G K))
    (fun f hf => exists_intermediateValue k L G K e f hf)

end IntermediateValues

end MultiplicativeTypeGaloisPoints

open GaloisPointComparison MultiplicativeTypeGaloisPoints in
/-- Evaluation identifies the points over an intermediate field of a separable closure
with the multiplicative character-value functions equivariant under its fixing subgroup. -/
theorem multiplicativeTypeGaloisPoints : MultiplicativeTypeGaloisPointsStatement.{u} := by
  intro k _ G _ _ hG Ks _ _ _ K
  have : IsAffine G.X.left := hG.isAffine
  have : IsSepClosed Ks := IsSepClosure.sep_closed k
  obtain ⟨_, _, _, ⟨e⟩⟩ :=
    MultiplicativeTypeSplitting.isFGDiagonalizable_of_isSepClosed (baseChanged k Ks G)
      (MultiplicativeTypeSplitting.isMultiplicativeType_baseChange_of_isAlgebraic k Ks G hG)
  exact ⟨intermediateValues_injective k Ks G K e, intermediateValues_range k Ks G K e⟩

end Langlands.GroupScheme
