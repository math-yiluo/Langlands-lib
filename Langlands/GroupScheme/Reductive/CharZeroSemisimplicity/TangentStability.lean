import Langlands.GroupScheme.MatrixRepresentation.DenseRationalStability
import Langlands.GroupScheme.MatrixRepresentation.CharacterSpanEmbedding
import Langlands.GroupScheme.Dynamic.Functoriality
import Langlands.GroupScheme.CorepresentedClosedSubgroup
import Langlands.GroupScheme.Rational.SemigroupIntersectionGeometry
import Langlands.GroupScheme.Rational.ActionLieRigidity
import Langlands.GroupScheme.AffineCartierSmoothProof
import Langlands.GroupScheme.Lie.TangentSemisimplicity

/-! # Stable subspaces are detected by rational points and by tangent matrices -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry Module
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  {n : Type} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
/-- A matrix with columns in a subspace maps every vector into that subspace. -/
theorem mulVec_mem_of_columns {d : ℕ} {W : Submodule k (n → k)} {B : Matrix n (Fin d) k}
    (hcols : ∀ j, (fun i => B i j) ∈ W) (w : Fin d → k) : B *ᵥ w ∈ W := by
  have he : B *ᵥ w = ∑ j, w j • (fun i => B i j) := by
    ext i
    simp [Matrix.mulVec, dotProduct, mul_comm]
  rw [he]
  exact Submodule.sum_mem _ (fun j _ => W.smul_mem _ (hcols j))

/-- Stability on every affine test gives stability under the rational-point matrices. -/
theorem IsStableSubspace.rationalMatrix_mulVec_mem [IsAffineHom G.X.hom]
    {ρ : MatrixRepresentation G n} {W : Submodule k (n → k)} (hW : ρ.IsStableSubspace W)
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) {v : n → k} (hv : v ∈ W) :
    (ρ.rationalMatrix g : Matrix n n k) *ᵥ v ∈ W := by
  classical
  obtain ⟨d, B, C, -, hcols, hproj⟩ := exists_subspace_split_coordinates W
  have hst := hW.isStableCoordinates B C hcols hproj (Over.mk (𝟙 _)) g
  let e := (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv
  have hB : (B.map (scalarMap (Over.mk (𝟙 (Spec (CommRingCat.of k)))))).map
      e.toRingHom = B := by
    ext r s
    exact e.apply_symm_apply _
  have hC : (C.map (scalarMap (Over.mk (𝟙 (Spec (CommRingCat.of k)))))).map
      e.toRingHom = C := by
    ext r s
    exact e.apply_symm_apply _
  have hM : ((ρ.pointMatrix (Over.mk (𝟙 (Spec (CommRingCat.of k))))) g).val.map
      e.toRingHom = (ρ.rationalMatrix g : Matrix n n k) := rfl
  have hst' := congrArg (fun M => Matrix.map M e.toRingHom) hst
  simp only [Matrix.map_mul (f := e.toRingHom), hB, hC, hM] at hst'
  have hv' : B *ᵥ (C *ᵥ v) = v := (Matrix.mulVec_mulVec v B C).trans (hproj v hv)
  rw [← hv', Matrix.mulVec_mulVec, hst', ← Matrix.mulVec_mulVec]
  exact mulVec_mem_of_columns hcols _

/-- Stability on every affine test gives stability under every tangent matrix. -/
theorem IsStableSubspace.tangentMatrix_mulVec_mem {ρ : MatrixRepresentation G n}
    {W : Submodule k (n → k)} (hW : ρ.IsStableSubspace W) (X : lieKernel G k)
    {v : n → k} (hv : v ∈ W) : ρ.tangentMatrix k X *ᵥ v ∈ W := by
  have h := hW (CommAlgCat.of (CommRingCat.of k) (DualNumber k)) X.val v hv
    (TrivSqZeroExt.sndHom k k)
  rw [affineMatrix_eq_matrixUnit] at h
  convert h using 1
  funext i
  change _ = TrivSqZeroExt.snd (((1 + GeneralLinear.DualNumber.epsilonMatrix
    (ρ.tangentMatrix k X)) *ᵥ (fun j => algebraMap k (DualNumber k) (v j))) i)
  simp [Matrix.mulVec, dotProduct, Matrix.add_apply, Matrix.one_apply,
    TrivSqZeroExt.snd_sum, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_mul, mul_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

section Rational

variable [IsAlgClosed k] [IsReduced G.X.left] [LocallyOfFiniteType G.X.hom]

/-- Stability under all rational-point matrices implies stability on every
affine test, including nonreduced test algebras. -/
theorem isStableSubspace_of_rationalMatrix (ρ : MatrixRepresentation G n)
    (W : Submodule k (n → k))
    (h : ∀ g v, v ∈ W → (ρ.rationalMatrix g : Matrix n n k) *ᵥ v ∈ W) :
    ρ.IsStableSubspace W := by
  classical
  obtain ⟨d, B, C, hCB, hcols, hproj⟩ := exists_subspace_split_coordinates W
  have hstable : ρ.IsStableCoordinates B C := by
    apply isStableCoordinates_of_rationalMatrix ρ B C
    intro g
    have hmat : (B * C) * ((ρ.rationalMatrix g : Matrix n n k) * B) =
        (ρ.rationalMatrix g : Matrix n n k) * B := by
      ext r s
      exact congrFun (hproj _ (h g _ (hcols s))) r
    simpa only [Matrix.mul_assoc] using hmat.symm
  have hrange : LinearMap.range B.mulVecLin = W := by
    apply le_antisymm
    · rintro v ⟨w, rfl⟩
      exact mulVec_mem_of_columns hcols w
    · intro v hv
      exact ⟨C *ᵥ v, (Matrix.mulVec_mulVec v B C).trans (hproj v hv)⟩
  rw [← hrange]
  exact (intertwines_restrictCoordinates ρ B C hCB hstable).isStableSubspace_range

/-- On a reduced group locally of finite type over an algebraically closed field,
all-test stability is stability under the rational-point matrices. -/
theorem isStableSubspace_iff_rationalMatrix [IsAffineHom G.X.hom]
    (ρ : MatrixRepresentation G n) (W : Submodule k (n → k)) :
    ρ.IsStableSubspace W ↔
      ∀ g v, v ∈ W → (ρ.rationalMatrix g : Matrix n n k) *ᵥ v ∈ W :=
  ⟨fun hW g _ hv => hW.rationalMatrix_mulVec_mem g hv,
    isStableSubspace_of_rationalMatrix ρ W⟩

end Rational

omit [DecidableEq n] in
/-- Every subspace is a coordinate subspace for some basis indexed by the same
finite type. -/
theorem exists_basis_coordinateSubspace (W : Submodule k (n → k)) :
    ∃ (b : Basis n k (n → k)) (S : Set n),
      ∀ v, v ∈ W ↔ ∀ i, i ∉ S → b.repr v i = 0 := by
  classical
  obtain ⟨s, hsW, hspan, hli⟩ := exists_linearIndependent k (W : Set (n → k))
  let b₀ := Basis.extend hli.linearIndepOn_id
  let σ := b₀.indexEquiv (Pi.basisFun k n)
  let b := b₀.reindex σ
  refine ⟨b, σ '' {x | (x : n → k) ∈ s}, ?_⟩
  have himage : b '' (σ '' {x | (x : n → k) ∈ s}) = s := by
    rw [← Set.image_comp]
    ext y
    simp only [Set.mem_image, Set.mem_ofPred_eq, Function.comp_apply, b,
      Basis.reindex_apply, Equiv.symm_apply_apply, b₀, Basis.extend_apply_self]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      exact ⟨⟨y, Basis.subset_extend _ ⟨⟨y, hy⟩, rfl⟩⟩, hy, rfl⟩
  have hW : W = Submodule.span k (b '' (σ '' {x | (x : n → k) ∈ s})) := by
    rw [himage, hspan, Submodule.span_eq]
  intro v
  rw [hW, Basis.mem_span_image]
  constructor
  · intro h i hi
    by_contra hne
    exact hi (h (Finsupp.mem_support_iff.mpr hne))
  · intro h i hi
    by_contra hne
    exact Finsupp.mem_support_iff.mp hi (h i hne)

/-- Membership of an affine point in the inverse image of a block parabolic. -/
theorem mem_comap_blockParabolic_affine (σ : MatrixRepresentation G n) (e : n → ℤ)
    (A : CommAlgCat.{u} (CommRingCat.of k))
    (x : (algSpec (CommRingCat.of k)).obj (op A) ⟶ G.X) :
    x ∈ ((GeneralLinear.blockParabolic n (CommRingCat.of k) e).comap σ).carrier _ ↔
      ∀ i j, e i < e j → (σ.affineMatrix A x : Matrix n n A) i j = 0 := by
  rw [SubgroupFunctor.mem_comap, GeneralLinear.mem_blockParabolic,
    GeneralLinear.pointsEquiv_eq_affinePointsEquiv]
  have hinj : Function.Injective (Corepresented.affineSectionsIso A).inv.hom := by
    intro a b hab
    have hleft (a : A) : (Corepresented.affineSectionsIso A).hom.hom
        ((Corepresented.affineSectionsIso A).inv.hom a) = a :=
      ConcreteCategory.congr_hom (Corepresented.affineSectionsIso A).inv_hom_id a
    exact (hleft a).symm.trans ((congrArg _ hab).trans (hleft b))
  refine forall_congr' fun i => forall_congr' fun j => imp_congr_right fun _ => ?_
  change (Corepresented.affineSectionsIso A).inv.hom _ = 0 ↔ _
  exact ⟨fun h => hinj (h.trans (map_zero _).symm), fun h => h ▸ map_zero _⟩

/-- The conjugate by a basis-coordinate point is intertwined by the coordinate matrix. -/
theorem intertwines_conjugate_basisCoordinatePoint (ρ : MatrixRepresentation G n)
    (b : Basis n k (n → k)) :
    Intertwines ρ (ρ.conjugate (basisCoordinatePoint b))
      (basisCoordinateGL b : Matrix n n k) := by
  intro A x
  rw [conjugate_affineMatrix, affineMatrix_constantPoint, rationalMatrix_basisCoordinatePoint]
  let U := Matrix.GeneralLinearGroup.map (algebraMap k A) (basisCoordinateGL b)
  change (U : Matrix n n A) * _ = ((U * ρ.affineMatrix A x * U⁻¹ : GL n A) : Matrix n n A) * U
  rw [← Units.val_mul, ← Units.val_mul, inv_mul_cancel_right]

section CharZero

variable [CharZero k] [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  [Smooth G.X.hom] [ConnectedSpace G.X.left]

/-- On a smooth connected group in characteristic zero, if every tangent matrix
vanishes in the entries `(i, j)` with `e i < e j`, then the whole group maps into
the block parabolic of `e`. -/
theorem comap_blockParabolic_eq_top (ρ : MatrixRepresentation G n) (e : n → ℤ)
    (h : ∀ (X : lieKernel G k) i j, e i < e j → ρ.tangentMatrix k X i j = 0) :
    (GeneralLinear.blockParabolic n (CommRingCat.of k) e).comap ρ = ⊤ := by
  have hrep := (GeneralLinear.isRepresentedBy_blockParabolic n (CommRingCat.of k) e)
    |>.comap_subgroupIntersectionFst
      (GeneralLinear.isClosedSubgroup_blockParabolicHom n (CommRingCat.of k) e) ρ
  have hcl := isClosedSubgroup_subgroupIntersectionFst ρ
    (GeneralLinear.isClosedSubgroup_blockParabolicHom n (CommRingCat.of k) e)
  let jP := subgroupIntersectionFst ρ (GeneralLinear.blockParabolicHom n (CommRingCat.of k) e)
  have : IsClosedImmersion jP.hom.hom.left := hcl
  have hA : IsAffineHom (subgroupIntersection ρ
      (GeneralLinear.blockParabolicHom n (CommRingCat.of k) e)).X.hom := by
    rw [← jP.hom.hom.w]
    infer_instance
  have hL : LocallyOfFiniteType (subgroupIntersection ρ
      (GeneralLinear.blockParabolicHom n (CommRingCat.of k) e)).X.hom := by
    rw [← jP.hom.hom.w]
    infer_instance
  refine RelativeRoot.eq_top_of_smooth_closed_of_tangentSubmodule_eq_top jP hrep hcl
    (affineCartierSmooth k _ hA hL) ?_
  apply top_unique
  intro X _
  rw [RelativeRoot.mem_tangentSubmodule, mem_comap_blockParabolic_affine,
    affineMatrix_eq_matrixUnit]
  intro i l hil
  have hne : i ≠ l := fun h => (lt_irrefl (e i)) (h ▸ hil)
  change (1 + GeneralLinear.DualNumber.epsilonMatrix (ρ.tangentMatrix k X.toMul)) i l = 0
  rw [Matrix.add_apply, Matrix.one_apply_ne hne, zero_add,
    GeneralLinear.DualNumber.epsilonMatrix_apply, h _ i l hil, TrivSqZeroExt.inr_zero]

/-- On a smooth connected group in characteristic zero, a subspace stable under
every tangent matrix is stable on every affine test. The proof applies the
Lie-algebra rigidity of smooth closed subgroups to the inverse image of a block
parabolic in adapted coordinates. -/
theorem isStableSubspace_of_tangentMatrix (ρ : MatrixRepresentation G n)
    (W : Submodule k (n → k))
    (h : ∀ (X : lieKernel G k) v, v ∈ W → ρ.tangentMatrix k X *ᵥ v ∈ W) :
    ρ.IsStableSubspace W := by
  classical
  obtain ⟨b, S, hbW⟩ := exists_basis_coordinateSubspace W
  let U : GL n k := basisCoordinateGL b
  let ρ' := ρ.conjugate (basisCoordinatePoint b)
  let e : n → ℤ := fun i => if i ∈ S then 1 else 0
  have he (i j : n) : e i < e j ↔ i ∉ S ∧ j ∈ S := by
    simp only [e]
    split_ifs <;> simp_all
  have hU (v : n → k) : (U : Matrix n n k) *ᵥ v = b.repr v := by
    change b.toMatrix (Pi.basisFun k n) *ᵥ v = _
    have h := (Pi.basisFun k n).toMatrix_mulVec_repr b v
    rwa [show ((Pi.basisFun k n).repr v : n → k) = v from
      funext fun i => by simp] at h
  have hint := intertwines_conjugate_basisCoordinatePoint ρ b
  let C : Submodule k (n → k) :=
    { carrier := {c | ∀ i, i ∉ S → c i = 0}
      add_mem' := fun ha hb i hi => by simp [ha i hi, hb i hi]
      zero_mem' := fun _ _ => rfl
      smul_mem' := fun a c hc i hi => by simp [hc i hi] }
  have hmemC (c : n → k) : c ∈ C ↔ ∀ i, i ∉ S → c i = 0 := Iff.rfl
  have hWC : W = C.comap (U : Matrix n n k).mulVecLin := by
    ext v
    rw [hbW, Submodule.mem_comap, Matrix.mulVecLin_apply, hU, hmemC]
  have hUU (c : n → k) : (U : Matrix n n k) *ᵥ (((U⁻¹ : GL n k) : Matrix n n k) *ᵥ c) = c := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec]
  have htan (X : lieKernel G k) (i l : n) (hi : i ∉ S) (hl : l ∈ S) :
      ρ'.tangentMatrix k X i l = 0 := by
    have hc := hint.tangentMatrix X
    let c : n → k := Pi.single l 1
    let w := ((U⁻¹ : GL n k) : Matrix n n k) *ᵥ c
    have hw : w ∈ W := by
      rw [hWC, Submodule.mem_comap, Matrix.mulVecLin_apply, hUU, hmemC]
      intro r hr
      exact Pi.single_eq_of_ne (by rintro rfl; exact hr hl) 1
    have hMw := h X w hw
    rw [hWC, Submodule.mem_comap, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hc,
      ← Matrix.mulVec_mulVec, hUU, hmemC] at hMw
    have hi' := hMw i hi
    rw [Matrix.mulVec_single_one, Matrix.col_apply] at hi'
    exact hi'
  let F := (GeneralLinear.blockParabolic n (CommRingCat.of k) e).comap ρ'
  have hF : F = ⊤ := comap_blockParabolic_eq_top ρ' e fun X i l hil =>
    htan X i l ((he i l).1 hil).1 ((he i l).1 hil).2
  have hC : ρ'.IsStableSubspace C := by
    intro A x v hv ℓ
    have hx : x ∈ F.carrier _ := by
      rw [hF]
      trivial
    rw [mem_comap_blockParabolic_affine] at hx
    rw [hmemC] at hv ⊢
    intro i hi
    have hzero : ((ρ'.affineMatrix A x : Matrix n n A) *ᵥ
        fun l => algebraMap k A (v l)) i = 0 := by
      simp only [Matrix.mulVec, dotProduct]
      apply Finset.sum_eq_zero
      intro l _
      by_cases hl : l ∈ S
      · rw [hx i l ((he i l).2 ⟨hi, hl⟩), zero_mul]
      · rw [hv l hl, map_zero, mul_zero]
    change ℓ _ = 0
    rw [hzero, map_zero]
  rw [hWC]
  exact hC.comap hint

/-- On a smooth connected group in characteristic zero, all-test stability is
stability under every tangent matrix. -/
theorem isStableSubspace_iff_tangentMatrix (ρ : MatrixRepresentation G n)
    (W : Submodule k (n → k)) :
    ρ.IsStableSubspace W ↔
      ∀ (X : lieKernel G k) v, v ∈ W → ρ.tangentMatrix k X *ᵥ v ∈ W :=
  ⟨fun hW X _ hv => hW.tangentMatrix_mulVec_mem X hv,
    isStableSubspace_of_tangentMatrix ρ W⟩

end CharZero

end Langlands.GroupScheme.MatrixRepresentation
