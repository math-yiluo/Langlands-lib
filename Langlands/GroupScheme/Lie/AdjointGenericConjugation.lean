import Langlands.GroupScheme.Lie.AdjointDominance
import Langlands.GroupScheme.Rational.RationalFunctionFieldAlgebra
import Langlands.AlgebraicGeometry.PointTopology.IteratedAffineSpace
import Mathlib.AlgebraicGeometry.Geometrically.Irreducible

/-! # Generic conjugation into an adjoint slice -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.Lie

set_option backward.isDefEq.respectTransparency false

section Points

variable {X Y : Scheme.{u}} [IrreducibleSpace Y]

/-- The map from the function field of `Y` to the residue field of `X` at a point `ξ` whose
image under `f` specializes to the generic point of `Y`. -/
def functionFieldToResidueField (f : X ⟶ Y) (ξ : X) (h : f ξ ⤳ genericPoint Y) :
    Y.functionField ⟶ X.residueField ξ :=
  Y.presheaf.stalkSpecializes h ≫ f.stalkMap ξ ≫ X.residue ξ

/-- The residue-field point at `ξ`, followed by `f`, factors through the generic point of
`Y` by `functionFieldToResidueField`. -/
theorem SpecMap_functionFieldToResidueField (f : X ⟶ Y) (ξ : X) (h : f ξ ⤳ genericPoint Y) :
    Spec.map (functionFieldToResidueField f ξ h) ≫ Y.fromSpecStalk (genericPoint Y) =
      X.fromSpecResidueField ξ ≫ f := by
  simp only [functionFieldToResidueField, Spec.map_comp, Category.assoc,
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.SpecMap_stalkMap_fromSpecStalk,
    Scheme.fromSpecResidueField]

/-- On global sections, the canonical morphism `Spec 𝒪_{X,x} ⟶ X` is the germ at `x`. -/
theorem ΓSpecIso_hom_fromSpecStalk_appTop (x : X) (a : Γ(X, ⊤)) :
    (Scheme.ΓSpecIso (X.presheaf.stalk x)).hom ((X.fromSpecStalk x).appTop a) =
      X.presheaf.germ ⊤ x trivial a := by
  have h : (X.fromSpecStalk x).appTop ≫ (Scheme.ΓSpecIso (X.presheaf.stalk x)).hom =
      X.presheaf.germ ⊤ x trivial := by
    simp only [Scheme.fromSpecStalk_appTop, homOfLE_refl, op_id, CategoryTheory.Functor.map_id,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact ConcreteCategory.congr_hom h a

end Points

section Generic

open MatrixRepresentation

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  {e : Type} [Fintype e] {d : ℕ}

/-- The generic Lie element: the Lie element over the function field of `𝔸^d`, with
`𝔸^d` indexed by `ULift (Fin d)`, whose coordinates are the coordinate functions. -/
def genericLieElement [IsAffineHom G.X.hom] (c : FiniteCoordinates G d) :
    Additive (lieKernel G (𝔸(ULift.{u} (Fin d); Spec (CommRingCat.of k))).functionField) :=
  (c.equiv (.of (CommRingCat.of k) _)).symm fun i =>
    rationalFunctionFieldCoordinate k (ULift.{u} (Fin d)) (ULift.up i)

/-- The product `G × 𝔸^e` of an irreducible `G` with affine space is irreducible. -/
instance irreducibleSpace_tensor_coefficientSpace [IrreducibleSpace G.X.left] :
    IrreducibleSpace (G.X ⊗ coefficientSpace e (CommRingCat.of k)).left :=
  inferInstanceAs (IrreducibleSpace ↥(Limits.pullback (C := Scheme.{u}) G.X.hom
    (𝔸(ULift.{u} e; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k))))

omit [Fintype e] in
/-- The first projection `G × 𝔸^e ⟶ G` sends the generic point to the generic point. -/
theorem fst_genericPoint_tensor_coefficientSpace [IrreducibleSpace G.X.left] :
    (fst G.X (coefficientSpace e (CommRingCat.of k))).left
        (genericPoint (G.X ⊗ coefficientSpace e (CommRingCat.of k)).left) =
      genericPoint G.X.left := by
  have hsurj : Function.Surjective (Limits.pullback.fst (C := Scheme.{u}) G.X.hom
      (𝔸(ULift.{u} e; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k))) :=
    Scheme.Hom.surjective _
  refine (Langlands.AlgebraicGeometry.PointTopology.isGenericPoint_univ_of_denseRange
    (fst G.X (coefficientSpace e (CommRingCat.of k))).left.continuous hsurj.denseRange
    (genericPoint_spec _)).eq (genericPoint_spec _)

/-- At a point `σ = (g, t)` of `G × 𝔸^e` over `Spec S` whose image under the adjoint slice map
factors through the generic point of `𝔸^d` by `ψ`, the Lie element `Ad(g) (B t)` has as
coordinates the images under `ψ` of the coordinate functions. -/
theorem equiv_adjoint_sliceMap_of_factor [IsAffineHom G.X.hom] (c : FiniteCoordinates G d)
    (B : Matrix (Fin d) e k) (S : CommAlgCat.{u} (CommRingCat.of k))
    (σ : (algSpec (CommRingCat.of k)).obj (op S) ⟶ G.X ⊗ coefficientSpace e (CommRingCat.of k))
    (ψ : (𝔸(ULift.{u} (Fin d); Spec (CommRingCat.of k))).functionField ⟶ CommRingCat.of S)
    (hψ : Spec.map ψ ≫ (𝔸(ULift.{u} (Fin d); Spec (CommRingCat.of k))).fromSpecStalk
        (genericPoint _) = σ.left ≫ (sliceMap (adjointRepresentation c) B).left) :
    c.equiv S (adjoint G S (σ ≫ fst _ _) ((c.equiv S).symm
        (B.map (algebraMap (CommRingCat.of k) S) *ᵥ fun j =>
          (Scheme.ΓSpecIso (CommRingCat.of S)).hom (coefficientCoordinates (σ ≫ snd _ _) j)))) =
      fun i => ψ (rationalFunctionFieldCoordinate k (ULift.{u} (Fin d)) (ULift.up i)) := by
  rw [← adjointRepresentation_affineAction, LinearEquiv.apply_symm_apply, affineAction_apply,
    ← affineCoordinates_sliceMap, lift_comp_fst_snd]
  funext i
  have h₁ : coefficientCoordinates (σ ≫ sliceMap (adjointRepresentation c) B) i =
      (Spec.map ψ).appTop (((𝔸(ULift.{u} (Fin d); Spec (CommRingCat.of k))).fromSpecStalk
        (genericPoint _)).appTop (AffineSpace.coord _ (ULift.up i))) := by
    change (σ.left ≫ (sliceMap (adjointRepresentation c) B).left).appTop _ = _
    rw [← hψ, Scheme.Hom.comp_appTop]
    rfl
  rw [h₁]
  refine (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_naturality ψ) _).trans ?_
  change ψ ((Scheme.ΓSpecIso _).hom (((𝔸(ULift.{u} (Fin d); Spec (CommRingCat.of k))).fromSpecStalk
    (genericPoint _)).appTop (AffineSpace.coord _ (ULift.up i)))) = _
  rw [ΓSpecIso_hom_fromSpecStalk_appTop]
  rfl

/-- **Generic conjugation into an adjoint slice.** Let `G` be an irreducible group over a
field `k` with affine structure morphism and finite Lie coordinates `c`, and let `B` be a
matrix whose adjoint slice map `(g, t) ↦ Ad(g) (B t)` has dense range. Then there are a field
extension `L` of `k`, a `k`-algebra map `φ` from the function field `K` of `𝔸^d` to `L`, a point
`g` of `G` over `L` whose image is the generic point of `G`, and a Lie element `Z` over `L`
with coordinates in the column space of `B`, such that `Ad(g) Z` is the image under `φ` of the
generic Lie element. -/
theorem exists_adjoint_eq_genericLieElement_of_denseRange [IsAffineHom G.X.hom]
    [IrreducibleSpace G.X.left] (c : FiniteCoordinates G d) (B : Matrix (Fin d) e k)
    (hB : DenseRange (sliceMap (adjointRepresentation c) B).left) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra k L)
      (φ : (𝔸(ULift.{u} (Fin d); Spec (CommRingCat.of k))).functionField →ₐ[k] L)
      (g : Lie.AffinePoints G L) (Z : Additive (lieKernel G L)),
      genericPoint G.X.left ∈ Set.range g.left ∧
      c.equiv (.of (CommRingCat.of k) L) Z ∈ Set.range (B.map (algebraMap k L)).mulVec ∧
      adjoint G L g Z = lieKernelMapLinear G φ (genericLieElement c) := by
  have hξ := Langlands.AlgebraicGeometry.PointTopology.isGenericPoint_univ_of_denseRange
    (sliceMap (adjointRepresentation c) B).left.continuous hB
    (genericPoint_spec (G.X ⊗ coefficientSpace e (CommRingCat.of k)).left)
  have hsp : (sliceMap (adjointRepresentation c) B).left
      (genericPoint (G.X ⊗ coefficientSpace e (CommRingCat.of k)).left) ⤳
        genericPoint (𝔸(ULift.{u} (Fin d); Spec (CommRingCat.of k))) :=
    hξ.specializes (Set.mem_univ _)
  let ψ := functionFieldToResidueField (Y := 𝔸(ULift.{u} (Fin d); Spec (CommRingCat.of k)))
    (sliceMap (adjointRepresentation c) B).left _ hsp
  have hψ := SpecMap_functionFieldToResidueField
    (Y := 𝔸(ULift.{u} (Fin d); Spec (CommRingCat.of k)))
    (sliceMap (adjointRepresentation c) B).left _ hsp
  let L := (G.X ⊗ coefficientSpace e (CommRingCat.of k)).left.residueField
    (genericPoint (G.X ⊗ coefficientSpace e (CommRingCat.of k)).left)
  let s := (G.X ⊗ coefficientSpace e (CommRingCat.of k)).left.fromSpecResidueField
    (genericPoint (G.X ⊗ coefficientSpace e (CommRingCat.of k)).left)
  let _ : Algebra k L :=
    (Spec.preimage (s ≫ (G.X ⊗ coefficientSpace e (CommRingCat.of k)).hom)).hom.toAlgebra
  have hL : Spec.map (CommRingCat.ofHom (algebraMap k L)) =
      s ≫ (G.X ⊗ coefficientSpace e (CommRingCat.of k)).hom :=
    Spec.map_preimage _
  have hfY : (sliceMap (adjointRepresentation c) B).left ≫
      (𝔸(ULift.{u} (Fin d); Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)) =
        (G.X ⊗ coefficientSpace e (CommRingCat.of k)).hom :=
    Over.w (sliceMap (adjointRepresentation c) B)
  have hcomm : CommRingCat.ofHom (algebraMap k
      (𝔸(ULift.{u} (Fin d); Spec (CommRingCat.of k))).functionField) ≫ ψ =
        CommRingCat.ofHom (algebraMap k L) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hL, ← hfY, ← Category.assoc, ← hψ, Category.assoc]
    congr 1
    exact algebraBaseMap_rationalFunctionField k (ULift.{u} (Fin d))
  let φ : (𝔸(ULift.{u} (Fin d); Spec (CommRingCat.of k))).functionField →ₐ[k] L :=
    { ψ.hom with commutes' := fun r => ConcreteCategory.congr_hom hcomm r }
  let S : CommAlgCat.{u} (CommRingCat.of k) := .of (CommRingCat.of k) L
  let σ : (algSpec (CommRingCat.of k)).obj (op S) ⟶ G.X ⊗ coefficientSpace e (CommRingCat.of k) :=
    Over.homMk s hL.symm
  refine ⟨L, inferInstance, inferInstance, φ, σ ≫ fst _ _, (c.equiv S).symm
    (B.map (algebraMap (CommRingCat.of k) S) *ᵥ fun j =>
      (Scheme.ΓSpecIso (CommRingCat.of S)).hom (coefficientCoordinates (σ ≫ snd _ _) j)),
    ?_, ⟨_, (LinearEquiv.apply_symm_apply _ _).symm⟩, ?_⟩
  · obtain ⟨a⟩ : Nonempty (Spec (CommRingCat.of S)) := inferInstance
    refine ⟨a, ?_⟩
    change (fst G.X (coefficientSpace e (CommRingCat.of k))).left (s a) = _
    rw [Scheme.fromSpecResidueField_apply]
    exact fst_genericPoint_tensor_coefficientSpace
  · apply (c.equiv S).injective
    refine (equiv_adjoint_sliceMap_of_factor c B S σ ψ hψ).trans ?_
    refine Eq.trans ?_ (c.naturality (CommAlgCat.ofHom φ) (genericLieElement c)).symm
    funext i
    rw [genericLieElement, LinearEquiv.apply_symm_apply]
    rfl

/-- **Generic conjugation into an adjoint slice, span form.** Let `G` be a smooth irreducible
affine group over a field `k` with finite Lie coordinates `c`, `B` a matrix, `t₀` a vector, and
`Y₀` the Lie element with coordinates `B t₀`. If the image of `ad(Y₀)` and the column space
of `B` together span `k^d`, the conclusion of
`exists_adjoint_eq_genericLieElement_of_denseRange` holds. -/
theorem exists_adjoint_eq_genericLieElement [IsAffineHom G.X.hom] [Smooth G.X.hom]
    [IrreducibleSpace G.X.left] (c : FiniteCoordinates G d) (B : Matrix (Fin d) e k)
    (t₀ : e → k)
    (h : LinearMap.range (adjointDifferentialFamily c
        ((c.equiv (.of (CommRingCat.of k) k)).symm (B *ᵥ t₀))) ⊔
      LinearMap.range B.mulVecLin = ⊤) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra k L)
      (φ : (𝔸(ULift.{u} (Fin d); Spec (CommRingCat.of k))).functionField →ₐ[k] L)
      (g : Lie.AffinePoints G L) (Z : Additive (lieKernel G L)),
      genericPoint G.X.left ∈ Set.range g.left ∧
      c.equiv (.of (CommRingCat.of k) L) Z ∈ Set.range (B.map (algebraMap k L)).mulVec ∧
      adjoint G L g Z = lieKernelMapLinear G φ (genericLieElement c) :=
  exists_adjoint_eq_genericLieElement_of_denseRange c B (denseRange_adjointSliceMap c B t₀ h)

end Generic

end Langlands.GroupScheme.Lie
