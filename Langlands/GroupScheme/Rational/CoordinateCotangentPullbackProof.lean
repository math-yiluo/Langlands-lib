import Langlands.GroupScheme.Rational.CoordinateCotangentPullbackStatement

/-! # Actual cotangent pullback preserves equivariant character weights: proof -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.CoordinateWeights

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]

section BaseChange

variable (A : Type u) [CommRing A] [Algebra k A]

/-- The actual coordinate pullback after the coefficient extension A/k. -/
def basePullback (f : G.X ⟶ H.X) :
    A ⊗[k] CharacterUnits.Coord H →ₐ[A] A ⊗[k] CharacterUnits.Coord G :=
  AlgHom.liftEquiv k A (CharacterUnits.Coord H) (A ⊗[k] CharacterUnits.Coord G)
    (Algebra.TensorProduct.includeRight.comp (pullback f))

@[simp] theorem basePullback_tmul (f : G.X ⟶ H.X) (a : A) (z : CharacterUnits.Coord H) :
    basePullback A f (a ⊗ₜ[k] z) = a ⊗ₜ[k] pullback f z := by
  change a • ((1 : A) ⊗ₜ[k] pullback f z) = _
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- On functions from the original coordinate algebra, it is the original pullback. -/
theorem basePullback_coordinates (f : G.X ⟶ H.X) :
    ((basePullback A f).restrictScalars k).comp Algebra.TensorProduct.includeRight =
      Algebra.TensorProduct.includeRight.comp (pullback f) :=
  (AlgHom.liftEquiv k A (CharacterUnits.Coord H) (A ⊗[k] CharacterUnits.Coord G)).symm_apply_apply _

/-- The base-changed pullback fixes the coefficient factor. -/
theorem basePullback_includeLeft (f : G.X ⟶ H.X) :
    ((basePullback A f).restrictScalars k).comp
        (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] CharacterUnits.Coord H) =
      Algebra.TensorProduct.includeLeft := by
  ext a
  simp [Algebra.TensorProduct.includeLeft_apply]

/-- An actual group homomorphism preserves the full tensor augmentation. -/
theorem baseAugmentation_basePullback (f : G ⟶ H) :
    (baseAugmentation G A).comp (basePullback A f.hom.hom) = baseAugmentation H A := by
  apply Algebra.TensorProduct.ext'
  intro a z
  change evaluate (1 : Lie.AffinePoints G A) (basePullback A f.hom.hom (a ⊗ₜ[k] z)) =
    evaluate (1 : Lie.AffinePoints H A) (a ⊗ₜ[k] z)
  rw [basePullback_tmul, evaluate_tmul, evaluate_tmul, Lie.pointCoordinates_one,
    Lie.pointCoordinates_one]
  congr 1
  exact congrArg (Algebra.ofId k A) (DFunLike.congr_fun (pullback_origin f) z)

/-- The base-changed pullback preserves the base-changed augmentation ideals. -/
theorem basePullback_augmentation (f : G ⟶ H) :
    baseAugmentationIdeal H A ≤
      (baseAugmentationIdeal G A).comap (basePullback A f.hom.hom) := by
  intro z hz
  change baseAugmentation G A (basePullback A f.hom.hom z) = 0
  rw [← AlgHom.comp_apply, baseAugmentation_basePullback]
  exact hz

/-- The induced A-linear pullback on the base-changed augmentation quotients. -/
def baseCotangentPullback (f : G ⟶ H) : BaseCotangent H A →ₗ[A] BaseCotangent G A :=
  Ideal.mapCotangent (baseAugmentationIdeal H A) (baseAugmentationIdeal G A)
    (basePullback A f.hom.hom) (basePullback_augmentation A f)

/-- Scalar extension of cotangent classes commutes with pullback. -/
theorem cotangentBaseChange_cotangentPullback (f : G ⟶ H) (q : Cotangent H) :
    cotangentBaseChange (A := A) (cotangentPullback f q) =
      baseCotangentPullback A f (cotangentBaseChange q) := by
  obtain ⟨z, rfl⟩ := (augmentationIdeal H).toCotangent_surjective q
  simp only [cotangentBaseChange, baseCotangentPullback, cotangentPullback,
    Ideal.mapCotangent_toCotangent]
  congr 1
  apply Subtype.ext
  change (1 : A) ⊗ₜ[k] pullback f.hom.hom z.val =
    basePullback A f.hom.hom ((1 : A) ⊗ₜ[k] z.val)
  rw [basePullback_tmul]

/-- Base-changed pullback sends the target universal point to the composite of the source one. -/
theorem affineMap_basePullback_universal (f : G.X ⟶ H.X) :
    Lie.affineMap H ((basePullback A f).restrictScalars k)
        ((Lie.pointCoordinates H).symm Algebra.TensorProduct.includeRight) =
      (Lie.pointCoordinates G).symm Algebra.TensorProduct.includeRight ≫ f := by
  apply (Lie.pointCoordinates H).injective
  rw [Lie.pointCoordinates_naturality, Equiv.apply_symm_apply, coordinates_comp,
    Equiv.apply_symm_apply]
  exact basePullback_coordinates A f

/-- Equivariance makes base-changed pullback intertwine the actual coordinate actions. -/
theorem actionPullback_basePullback (b : AutomorphicAction S.toGrp G)
    (c : AutomorphicAction S.toGrp H) (f : G.X ⟶ H.X) (hf : IsEquivariant b c f)
    (s : Lie.AffinePoints S.toGrp A) :
    (actionPullback b s).comp (basePullback A f) =
      (basePullback A f).comp (actionPullback c s) := by
  apply Algebra.TensorProduct.ext_ring
  change (((actionPullback b s).restrictScalars k).comp
      ((basePullback A f).restrictScalars k)).comp Algebra.TensorProduct.includeRight =
    (((basePullback A f).restrictScalars k).comp
      ((actionPullback c s).restrictScalars k)).comp Algebra.TensorProduct.includeRight
  rw [AlgHom.comp_assoc, AlgHom.comp_assoc, basePullback_coordinates,
    actionPullback_coordinates, ← AlgHom.comp_assoc, actionPullback_coordinates]
  unfold actionCoordinates
  rw [← coordinates_comp,
    ← Lie.pointCoordinates_naturality H ((basePullback A f).restrictScalars k),
    RelativeRoot.act_affineMap, affineMap_basePullback_universal, ← Lie.affineMap_comp,
    basePullback_includeLeft]
  exact congrArg (fun p => Lie.pointCoordinates H p) (hf _ _ _)

/-- Base-changed cotangent pullback intertwines the actual cotangent actions. -/
theorem cotangentAction_baseCotangentPullback (b : AutomorphicAction S.toGrp G)
    (c : AutomorphicAction S.toGrp H) (f : G ⟶ H) (hf : IsEquivariant b c f.hom.hom)
    (s : Lie.AffinePoints S.toGrp A) (x : BaseCotangent H A) :
    cotangentAction b s (baseCotangentPullback A f x) =
      baseCotangentPullback A f (cotangentAction c s x) := by
  obtain ⟨z, rfl⟩ := (baseAugmentationIdeal H A).toCotangent_surjective x
  simp only [cotangentAction, baseCotangentPullback, Ideal.mapCotangent_toCotangent]
  congr 1
  apply Subtype.ext
  exact DFunLike.congr_fun (actionPullback_basePullback A b c f.hom.hom hf s) z.val

end BaseChange

/-- Equivariant pullback sends cotangent χ-eigenvectors to cotangent χ-eigenvectors. -/
theorem cotangentPullback_mem_weightSpace (b : AutomorphicAction S.toGrp G)
    (c : AutomorphicAction S.toGrp H) (f : G ⟶ H) (hf : IsEquivariant b c f.hom.hom)
    (χ : characterLattice S) {q : Cotangent H} (hq : q ∈ cotangentWeightSpace c χ) :
    cotangentPullback f q ∈ cotangentWeightSpace b χ := by
  have hq' : IsCotangentEigenvector c χ q := hq
  intro A _ _ s
  rw [cotangentBaseChange_cotangentPullback, cotangentAction_baseCotangentPullback A b c f hf,
    hq' A s, map_smul]

omit [IsAffineHom G.X.hom] [IsAffineHom H.X.hom] in
/-- The inverse of an equivariant isomorphism is equivariant. -/
theorem isEquivariant_inv (b : AutomorphicAction S.toGrp G) (c : AutomorphicAction S.toGrp H)
    (e : G ≅ H) (he : IsEquivariant b c e.hom.hom.hom) :
    IsEquivariant c b e.inv.hom.hom := by
  have hi : e.inv.hom.hom ≫ e.hom.hom.hom = 𝟙 H.X := ((Grp.forget _).mapIso e).inv_hom_id
  intro T s h
  apply (cancel_mono e.hom.hom.hom).1
  rw [Category.assoc, he T s (h ≫ e.inv.hom.hom), Category.assoc, hi,
    Category.comp_id, Category.comp_id]

/-- Injective equivariant cotangent pullback includes the cotangent support. -/
theorem cotangentSupport_subset (b : AutomorphicAction S.toGrp G)
    (c : AutomorphicAction S.toGrp H) (f : G ⟶ H) (hf : IsEquivariant b c f.hom.hom)
    (hinj : Function.Injective (cotangentPullback f)) :
    cotangentSupport c ⊆ cotangentSupport b := by
  rintro χ ⟨q, hq, hχ⟩
  refine ⟨cotangentPullback f q, ?_, cotangentPullback_mem_weightSpace b c f hf χ hχ⟩
  intro h0
  exact hq (hinj (h0.trans (map_zero _).symm))

/-- Actual equivariant group-scheme isomorphisms preserve cotangent support. -/
theorem cotangentSupport_eq_of_iso (b : AutomorphicAction S.toGrp G)
    (c : AutomorphicAction S.toGrp H) (e : G ≅ H) (he : IsEquivariant b c e.hom.hom.hom) :
    cotangentSupport b = cotangentSupport c :=
  Set.Subset.antisymm
    (cotangentSupport_subset c b e.inv (isEquivariant_inv b c e he)
      (cotangentPullbackEquiv e.symm).injective)
    (cotangentSupport_subset b c e.hom he (cotangentPullbackEquiv e).injective)

/-- The exact published target `CotangentPullbackStatement`. -/
theorem cotangentPullbackStatement : CotangentPullbackStatement.{u} := by
  intro k _ G H hG hH S b c
  refine ⟨fun f hf χ => ?_, fun e he => cotangentSupport_eq_of_iso b c e he⟩
  rw [Submodule.map_le_iff_le_comap]
  intro q hq
  exact cotangentPullback_mem_weightSpace b c f hf χ hq

end Langlands.GroupScheme.CoordinateWeights
