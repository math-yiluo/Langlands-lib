import Langlands.GroupScheme.Torus.Weights
import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.InnerAutomorphismHom

/-! # Maximal tori, normalizing points and the Weyl action -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-! ### Maximal tori -/

section Maximal

variable {k : Type u} [Field k]

/-- A homomorphism `i : T ⟶ G` from a commutative group scheme over a field is a maximal torus
when `T` is a torus, `i` is a closed subgroup, and `i` does not factor through a strictly larger
closed torus: whenever `i = f ≫ i'` with `i' : T' ⟶ G` a closed torus, `f` is an isomorphism. -/
def IsMaximalTorus {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} (i : T.toGrp ⟶ G) : Prop :=
  IsTorus T.toGrp ∧ IsClosedSubgroup i ∧
    ∀ (T' : CommGroupScheme (Spec (CommRingCat.of k))) (i' : T'.toGrp ⟶ G)
      (f : T.toGrp ⟶ T'.toGrp), IsTorus T'.toGrp → IsClosedSubgroup i' → f ≫ i' = i → IsIso f

end Maximal

/-! ### Normalizing points -/

section Normalizer

variable {S : Scheme.{u}} {T : CommGroupScheme S} {G : GroupScheme S}

/-- A base point `n ∈ G(S)` normalizes `i : T ⟶ G` through the automorphism `σ` of `T` when
conjugation by `n` restricts along `i` to `σ`: `i ≫ int(n) = σ ≫ i`. -/
def IsNormalizingPoint (i : T.toGrp ⟶ G) (n : Over.mk (𝟙 S) ⟶ G.X) (σ : T ≅ T) : Prop :=
  i ≫ (G.innerIso n).hom = CommGroupScheme.groupHom σ.hom ≫ i

variable {i : T.toGrp ⟶ G}

theorem IsNormalizingPoint.one : IsNormalizingPoint i 1 (Iso.refl T) := by
  rw [IsNormalizingPoint, innerIso_one_hom, Category.comp_id]
  exact (Category.id_comp i).symm

theorem IsNormalizingPoint.mul {n m : Over.mk (𝟙 S) ⟶ G.X} {σ τ : T ≅ T}
    (hn : IsNormalizingPoint i n σ) (hm : IsNormalizingPoint i m τ) :
    IsNormalizingPoint i (n * m) (τ ≪≫ σ) := by
  rw [IsNormalizingPoint] at *
  rw [innerIso_mul_hom, ← Category.assoc, hm, Category.assoc, hn, ← Category.assoc]
  rfl

theorem IsNormalizingPoint.inv {n : Over.mk (𝟙 S) ⟶ G.X} {σ : T ≅ T}
    (hn : IsNormalizingPoint i n σ) : IsNormalizingPoint i n⁻¹ σ.symm := by
  rw [IsNormalizingPoint] at *
  rw [innerIso_inv_hom, Iso.comp_inv_eq, Category.assoc, hn, ← Category.assoc]
  change i = CommGroupScheme.groupHom (σ.inv ≫ σ.hom) ≫ i
  rw [Iso.inv_hom_id]
  exact (Category.id_comp i).symm

theorem isNormalizingPoint_refl_iff {n : Over.mk (𝟙 S) ⟶ G.X} :
    IsNormalizingPoint i n (Iso.refl T) ↔ i ≫ (G.innerIso n).hom = i := by
  rw [IsNormalizingPoint]
  exact ⟨fun h => h.trans (Category.id_comp i), fun h => h.trans (Category.id_comp i).symm⟩

variable (i)

/-- The points of `G(S)` normalizing `i`: those admitting an automorphism `σ` of `T` with
`IsNormalizingPoint i n σ`. -/
def normalizerPoints : Subgroup (Over.mk (𝟙 S) ⟶ G.X) where
  carrier := {n | ∃ σ : T ≅ T, IsNormalizingPoint i n σ}
  one_mem' := ⟨Iso.refl T, IsNormalizingPoint.one⟩
  mul_mem' := by
    rintro n m ⟨σ, hσ⟩ ⟨τ, hτ⟩
    exact ⟨τ ≪≫ σ, hσ.mul hτ⟩
  inv_mem' := by
    rintro n ⟨σ, hσ⟩
    exact ⟨σ.symm, hσ.inv⟩

/-- The points of `G(S)` centralizing `i`: those normalizing `i` through the identity of `T`. -/
def centralizerPoints : Subgroup (Over.mk (𝟙 S) ⟶ G.X) where
  carrier := {n | IsNormalizingPoint i n (Iso.refl T)}
  one_mem' := IsNormalizingPoint.one
  mul_mem' := by
    intro n m hn hm
    have h := IsNormalizingPoint.mul hn hm
    rwa [Iso.refl_trans] at h
  inv_mem' := by
    intro n hn
    have h := IsNormalizingPoint.inv hn
    rwa [Iso.refl_symm] at h

theorem mem_normalizerPoints {n : Over.mk (𝟙 S) ⟶ G.X} :
    n ∈ normalizerPoints i ↔ ∃ σ : T ≅ T, IsNormalizingPoint i n σ :=
  Iff.rfl

theorem mem_centralizerPoints {n : Over.mk (𝟙 S) ⟶ G.X} :
    n ∈ centralizerPoints i ↔ i ≫ (G.innerIso n).hom = i :=
  isNormalizingPoint_refl_iff

theorem centralizerPoints_le_normalizerPoints : centralizerPoints i ≤ normalizerPoints i :=
  fun _ hn => ⟨Iso.refl T, hn⟩

/-- A chosen automorphism of `T` through which a normalizing point acts. It is unique when the
underlying morphism of `i` is a monomorphism (`IsNormalizingPoint.unique`). -/
def normalizingAut (n : normalizerPoints i) : T ≅ T :=
  Classical.choose n.2

theorem isNormalizingPoint_normalizingAut (n : normalizerPoints i) :
    IsNormalizingPoint i n (normalizingAut i n) :=
  Classical.choose_spec n.2

/-- If the underlying morphism of schemes of `i` is a monomorphism, the automorphism through
which a point normalizes `i` is unique. -/
theorem IsNormalizingPoint.unique [Mono i.hom.hom.left] {n : Over.mk (𝟙 S) ⟶ G.X}
    {σ τ : T ≅ T} (hσ : IsNormalizingPoint i n σ) (hτ : IsNormalizingPoint i n τ) : σ = τ := by
  have h : CommGroupScheme.groupHom σ.hom ≫ i = CommGroupScheme.groupHom τ.hom ≫ i :=
    hσ.symm.trans hτ
  have h' := congrArg (fun f => f.hom.hom.left) h
  simp only [Grp.comp_hom_hom, Over.comp_left] at h'
  have h'' := (cancel_mono _).1 h'
  apply Iso.ext
  change Additive.ofMul (CommGroupScheme.groupHom σ.hom) =
    Additive.ofMul (CommGroupScheme.groupHom τ.hom)
  congr 1
  apply Grp.hom_ext
  exact Over.OverMorphism.ext h''

/-- Precomposition with the inverse of an automorphism `σ` of `T`, on characters. -/
def characterAut (σ : T ≅ T) : characterLattice T ≃ₗ[ℤ] characterLattice T :=
  AddEquiv.toIntLinearEquiv
    { toFun := fun χ => σ.inv ≫ χ
      invFun := fun χ => σ.hom ≫ χ
      left_inv := fun χ => by simp
      right_inv := fun χ => by simp
      map_add' := fun χ ψ => Preadditive.comp_add _ _ _ _ _ _ }

@[simp] theorem characterAut_apply (σ : T ≅ T) (χ : characterLattice T) :
    characterAut σ χ = σ.inv ≫ χ := rfl

/-- The Weyl action of the normalizer on characters, `n ↦ (χ ↦ σ⁻¹ ≫ χ)` where `n` normalizes
`i` through `σ`, for `i` whose underlying morphism of schemes is a monomorphism. -/
def weylAction [Mono i.hom.hom.left] :
    normalizerPoints i →* (characterLattice T ≃ₗ[ℤ] characterLattice T) where
  toFun n := characterAut (normalizingAut i n)
  map_one' := by
    have h : normalizingAut i 1 = Iso.refl T :=
      (isNormalizingPoint_normalizingAut i 1).unique i IsNormalizingPoint.one
    apply LinearEquiv.ext
    intro χ
    rw [h, characterAut_apply]
    exact Category.id_comp χ
  map_mul' n m := by
    have h : normalizingAut i (n * m) = normalizingAut i m ≪≫ normalizingAut i n :=
      (isNormalizingPoint_normalizingAut i (n * m)).unique i
        ((isNormalizingPoint_normalizingAut i n).mul (isNormalizingPoint_normalizingAut i m))
    apply LinearEquiv.ext
    intro χ
    rw [h, LinearEquiv.mul_apply, characterAut_apply, characterAut_apply, characterAut_apply,
      Iso.trans_inv, Category.assoc]

theorem weylAction_apply [Mono i.hom.hom.left] (n : normalizerPoints i)
    (χ : characterLattice T) : weylAction i n χ = (normalizingAut i n).inv ≫ χ := rfl

theorem weylAction_eq [Mono i.hom.hom.left] {n : normalizerPoints i} {σ : T ≅ T}
    (h : IsNormalizingPoint i n σ) (χ : characterLattice T) : weylAction i n χ = σ.inv ≫ χ := by
  rw [weylAction_apply, (isNormalizingPoint_normalizingAut i n).unique i h]

/-- The image of the Weyl action in the automorphisms of the character lattice. -/
def weylImage [Mono i.hom.hom.left] : Subgroup (characterLattice T ≃ₗ[ℤ] characterLattice T) :=
  (weylAction i).range

end Normalizer

/-! ### Normalizing points permute weight spaces and roots -/

section WeightSpaces

variable {R : CommRingCat.{u}} {T : CommGroupScheme (Spec R)} {G : GroupScheme (Spec R)}
  [IsAffineHom G.X.hom] {i : T.toGrp ⟶ G}

/-- The adjoint action of a base point `n ∈ G(R)` on `Lie(G)(R)`. -/
abbrev basePointAdjoint (n : Over.mk (𝟙 (Spec R)) ⟶ G.X) :
    Module.End R (Additive (lieKernel G R)) :=
  adjoint G R (G.constantPoint n _)

theorem basePointAdjoint_inv_mul (n : Over.mk (𝟙 (Spec R)) ⟶ G.X) :
    basePointAdjoint n⁻¹ * basePointAdjoint n = 1 := by
  rw [basePointAdjoint, basePointAdjoint, ← map_mul, constantPoint_inv, inv_mul_cancel, map_one]

theorem basePointAdjoint_mul_inv (n : Over.mk (𝟙 (Spec R)) ⟶ G.X) :
    basePointAdjoint n * basePointAdjoint n⁻¹ = 1 := by
  rw [basePointAdjoint, basePointAdjoint, ← map_mul, constantPoint_inv, mul_inv_cancel, map_one]

/-- A point normalizing `i` through `σ` carries the weight space of `χ` into that of
`σ⁻¹ ≫ χ`. -/
theorem IsNormalizingPoint.adjoint_mem_weightSpace {n : Over.mk (𝟙 (Spec R)) ⟶ G.X}
    {σ : T ≅ T} (h : IsNormalizingPoint i n σ) {χ : characterLattice T}
    {X : Additive (lieKernel G R)} (hX : X ∈ weightSpace i χ) :
    basePointAdjoint n X ∈ weightSpace i (σ.inv ≫ χ) := by
  intro A _ _ t
  set U := (algSpec R).obj (op (CommAlgCat.of R A))
  set nA := G.constantPoint n U
  set t' := t ≫ (CommGroupScheme.groupHom σ.inv).hom.hom
  have hnA : Lie.affineMap G (Algebra.ofId R A)
      (G.constantPoint n ((algSpec R).obj (op (CommAlgCat.of R R)))) = nA :=
    G.constantPoint_naturality n _
  have hσ : (CommGroupScheme.groupHom σ.inv).hom.hom ≫ (CommGroupScheme.groupHom σ.hom).hom.hom =
      𝟙 _ := by
    rw [← Grp.comp_hom_hom]
    exact (congrArg (fun f => (CommGroupScheme.groupHom f).hom.hom) σ.inv_hom_id).trans
      (Grp.id_hom_hom _)
  have hpt : t ≫ i.hom.hom = nA * (t' ≫ i.hom.hom) * nA⁻¹ := by
    have h1 := congrArg (fun f => t' ≫ f.hom.hom) h
    simp only [Grp.comp_hom_hom] at h1
    rw [← Category.assoc, comp_innerIso_hom] at h1
    rw [h1, ← Category.assoc, Category.assoc t, hσ, Category.comp_id]
  rw [basePointAdjoint, adjoint_naturality, hnA, hpt, map_mul, map_mul, Module.End.mul_apply,
    Module.End.mul_apply, ← Module.End.mul_apply (adjoint G A nA⁻¹), ← map_mul, inv_mul_cancel,
    map_one, Module.End.one_apply, hX A t', map_smul, Lie.characterValue_comp]

/-- A point normalizing `i` through `σ` maps the weight space of `χ` onto that of `σ⁻¹ ≫ χ`. -/
theorem IsNormalizingPoint.map_weightSpace {n : Over.mk (𝟙 (Spec R)) ⟶ G.X} {σ : T ≅ T}
    (h : IsNormalizingPoint i n σ) (χ : characterLattice T) :
    (weightSpace i χ).map (basePointAdjoint n) = weightSpace i (σ.inv ≫ χ) := by
  apply le_antisymm
  · rintro _ ⟨X, hX, rfl⟩
    exact h.adjoint_mem_weightSpace hX
  · intro Y hY
    have hY' := h.inv.adjoint_mem_weightSpace hY
    rw [Iso.symm_inv, Iso.hom_inv_id_assoc] at hY'
    refine ⟨basePointAdjoint n⁻¹ Y, hY', ?_⟩
    change (basePointAdjoint n * basePointAdjoint n⁻¹) Y = Y
    rw [basePointAdjoint_mul_inv, Module.End.one_apply]

theorem weightSpace_eq_bot_iff_of_isNormalizingPoint {n : Over.mk (𝟙 (Spec R)) ⟶ G.X}
    {σ : T ≅ T} (h : IsNormalizingPoint i n σ) (χ : characterLattice T) :
    weightSpace i (σ.inv ≫ χ) = ⊥ ↔ weightSpace i χ = ⊥ := by
  have hinj : Function.Injective (basePointAdjoint n) := by
    intro X Y hXY
    have := congrArg (basePointAdjoint n⁻¹) hXY
    change (basePointAdjoint n⁻¹ * basePointAdjoint n) X =
      (basePointAdjoint n⁻¹ * basePointAdjoint n) Y at this
    rwa [basePointAdjoint_inv_mul, Module.End.one_apply, Module.End.one_apply] at this
  rw [← h.map_weightSpace χ]
  constructor
  · intro h0
    apply Submodule.map_injective_of_injective hinj
    rw [h0, Submodule.map_bot]
  · intro h0
    rw [h0, Submodule.map_bot]

variable [Mono i.hom.hom.left]

/-- The Weyl action maps the weight space of `χ` onto that of its image (via `Ad`). -/
theorem map_weightSpace_weylAction (n : normalizerPoints i) (χ : characterLattice T) :
    (weightSpace i χ).map (basePointAdjoint (n : Over.mk (𝟙 (Spec R)) ⟶ G.X)) =
      weightSpace i (weylAction i n χ) := by
  rw [weylAction_apply]
  exact (isNormalizingPoint_normalizingAut i n).map_weightSpace χ

/-- The Weyl action permutes the roots. -/
theorem weylAction_mem_roots_iff (n : normalizerPoints i) (χ : characterLattice T) :
    weylAction i n χ ∈ roots i ↔ χ ∈ roots i := by
  have h0 : weylAction i n χ = 0 ↔ χ = 0 := (weylAction i n).map_eq_zero_iff
  have hb := weightSpace_eq_bot_iff_of_isNormalizingPoint (isNormalizingPoint_normalizingAut i n) χ
  rw [← weylAction_apply] at hb
  simp only [mem_roots, ne_eq, h0, hb]

end WeightSpaces

end Langlands.GroupScheme
