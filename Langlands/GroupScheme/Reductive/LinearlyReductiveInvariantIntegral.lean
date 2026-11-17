import Langlands.GroupScheme.Reductive.CharZeroInvariantIntegral
import Langlands.GroupScheme.MatrixRepresentation.StableSubrepresentation

/-! # Normalized invariant integration for linearly reductive groups -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {n : ℕ} (ρ : MatrixRepresentation G (Fin n))

/-- Pairing with a fixed vector is an invariant linear functional on the dual, on every
coefficient of every affine test. -/
theorem dual_coefficient_pairing (v : Fin n → k) (hv : ρ.IsFixedVector v)
    (A : CommAlgCat.{u} (CommRingCat.of k)) (x : G.affinePoints A)
    (c : Fin n → k) (ℓ : A →ₗ[k] k) :
    (fun i => ℓ (((ρ.dual.affineMatrix A x : Matrix (Fin n) (Fin n) A) *ᵥ
      (fun j => algebraMap k A (c j))) i)) ⬝ᵥ v = ℓ 1 * (c ⬝ᵥ v) := by
  have hfix := hv.affine A x⁻¹
  rw [map_inv] at hfix
  have hp :
      ((ρ.dual.affineMatrix A x : Matrix (Fin n) (Fin n) A) *ᵥ
        (fun j => algebraMap k A (c j))) ⬝ᵥ (fun i => algebraMap k A (v i)) =
      algebraMap k A (c ⬝ᵥ v) := by
    rw [dual_affineMatrix, GeneralLinear.matrixContragredient_coe, dotProduct_comm,
      Matrix.dotProduct_transpose_mulVec, hfix]
    exact ((algebraMap k A).map_dotProduct c v).symm
  have hs (a : A) (t : k) : ℓ (a * algebraMap k A t) = ℓ a * t := by
    rw [mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  calc
    _ = ℓ (((ρ.dual.affineMatrix A x : Matrix (Fin n) (Fin n) A) *ᵥ
        (fun j => algebraMap k A (c j))) ⬝ᵥ (fun i => algebraMap k A (v i))) := by
      simp only [dotProduct, map_sum, hs]
    _ = _ := by rw [hp, Algebra.algebraMap_eq_smul_one, map_smul, smul_eq_mul, mul_comm]

/-- If the dual is a sum of simple actual subrepresentations, a nonzero fixed vector has a
fixed dual vector pairing to one with it. -/
theorem exists_dual_fixed_of_simple_span [IsAffineHom G.X.hom]
    (hss : sSup {W : Submodule k (Fin n → k) |
      ρ.dual.IsStableSubspace W ∧ W ≠ ⊥ ∧
        ∀ U : Submodule k (Fin n → k), ρ.dual.IsStableSubspace U → U ≤ W →
          U = ⊥ ∨ U = W} = ⊤)
    (v : Fin n → k) (hv : v ≠ 0) (hfix : ρ.IsFixedVector v) :
    ∃ c : Fin n → k, ρ.dual.IsFixedVector c ∧ c ⬝ᵥ v = 1 := by
  classical
  let q : (Fin n → k) →ₗ[k] k :=
    { toFun := fun c => c ⬝ᵥ v
      map_add' := fun _ _ => add_dotProduct _ _ _
      map_smul' := fun _ _ => smul_dotProduct _ _ _ }
  have hker : ρ.dual.IsStableSubspace (LinearMap.ker q) := by
    intro A x c hc ℓ
    change _ ⬝ᵥ v = 0
    rw [dual_coefficient_pairing ρ v hfix, show c ⬝ᵥ v = 0 from hc, mul_zero]
  have hnle : ¬ (⊤ : Submodule k (Fin n → k)) ≤ LinearMap.ker q := by
    intro h
    apply hv
    funext i
    have hi := h (Submodule.mem_top (x := Pi.single i 1))
    change Pi.single i 1 ⬝ᵥ v = 0 at hi
    simpa only [single_dotProduct, one_mul, Pi.zero_apply] using hi
  obtain ⟨W, hW, hnW⟩ : ∃ W, (ρ.dual.IsStableSubspace W ∧ W ≠ ⊥ ∧
      ∀ U : Submodule k (Fin n → k), ρ.dual.IsStableSubspace U → U ≤ W →
        U = ⊥ ∨ U = W) ∧ ¬ W ≤ LinearMap.ker q := by
    by_contra h
    push Not at h
    apply hnle
    rw [← hss]
    exact sSup_le h
  obtain ⟨c, hcW, hc⟩ := Set.not_subset.mp
    (show ¬ (W : Set (Fin n → k)) ⊆ (LinearMap.ker q : Set (Fin n → k)) from hnW)
  have hWker : W ⊓ LinearMap.ker q = ⊥ := by
    have hstable : ρ.dual.IsStableSubspace (W ⊓ LinearMap.ker q) :=
      fun A x c hc ℓ => ⟨hW.1 A x c hc.1 ℓ, hker A x c hc.2 ℓ⟩
    rcases hW.2.2 _ hstable inf_le_left with h | h
    · exact h
    · exact False.elim (hnW (h ▸ inf_le_right))
  have hcfix : ρ.dual.IsFixedVector c := by
    rw [isFixedVector_iff_affine_model ρ.dual (Lie.coordinateIso G)]
    funext i
    apply Unipotent.eq_of_forall_dual k
    intro ℓ
    have hmem : (fun i => ℓ (((ρ.dual.affineMatrix (Lie.coordinateAlgebra G)
        (Lie.coordinateIso G).hom : Matrix (Fin n) (Fin n) (Lie.coordinateAlgebra G)) *ᵥ
          (fun j => algebraMap k (Lie.coordinateAlgebra G) (c j))) i)) -
        ℓ 1 • c ∈ W ⊓ LinearMap.ker q := by
      refine ⟨W.sub_mem (hW.1 _ _ c hcW ℓ) (W.smul_mem _ hcW), ?_⟩
      change q _ = 0
      rw [map_sub, map_smul]
      change _ ⬝ᵥ v - ℓ 1 * (c ⬝ᵥ v) = 0
      rw [dual_coefficient_pairing ρ v hfix, sub_self]
    rw [hWker, Submodule.mem_bot] at hmem
    have he := sub_eq_zero.mp hmem
    have hi := congrFun he i
    simpa [Algebra.algebraMap_eq_smul_one, map_smul, mul_comm] using hi
  refine ⟨(q c)⁻¹ • c, ?_, ?_⟩
  · intro T x
    have hs : (fun i => scalarMap T (((q c)⁻¹ • c) i)) =
        scalarMap T ((q c)⁻¹) • (fun i => scalarMap T (c i)) := by
      funext i
      exact map_mul _ _ _
    change _ *ᵥ (fun i => scalarMap T (((q c)⁻¹ • c) i)) = _
    rw [hs, Matrix.mulVec_smul, hcfix T x]
  · rw [smul_dotProduct]
    exact inv_mul_cancel₀ (show q c ≠ 0 from hc)

end Langlands.GroupScheme.MatrixRepresentation


namespace Langlands.GroupScheme

namespace AffineLinearEmbedding

open Chevalley MatrixRepresentation TensorProduct Coalgebra Module

variable {k : Type u} [Field k] (H : GroupScheme (Spec (CommRingCat.of k)))
  [IsAffineHom H.X.hom]
  (hss : ∀ (m : ℕ) (σ : MatrixRepresentation H (Fin m)),
    sSup {W : Submodule k (Fin m → k) | σ.IsStableSubspace W ∧ W ≠ ⊥ ∧
      ∀ U : Submodule k (Fin m → k), σ.IsStableSubspace U → U ≤ W →
        U = ⊥ ∨ U = W} = ⊤)

include hss

/-- Linear reductivity gives normalized right integrals on each finite set of coordinates. -/
theorem exists_right_integral_of_linearReductivity (T : Finset (Lie.coordinateAlgebra H)) :
    letI := bialgebra (corepresentableBy H (Lie.coordinateIso H))
    ∃ r : Module.Dual k (Lie.coordinateAlgebra H), r 1 = 1 ∧
      ∀ y ∈ T, IsRightIntegralAt r y := by
  classical
  let e := corepresentableBy H (Lie.coordinateIso H)
  let := bialgebra e
  let B := Lie.coordinateAlgebra H
  let hR : IsField (CommRingCat.of k) := Field.toIsField k
  let V : Submodule k B := regularSpan (insert 1 T)
  have hV : ∀ (f : Module.Dual k B) (v : B), v ∈ V → rightAct f v ∈ V :=
    fun f _ hv => rightAct_mem_regularSpan _ f hv
  have h1V : (1 : B) ∈ V := subset_regularSpan _ (Finset.mem_insert_self _ _)
  let N := finrank k V
  let b : Basis (Fin N) k V := Module.finBasis k V
  let M := subspaceMatrix V b
  let ρ := regularRepresentation e hR V b hV
  -- The universal point of the model and its coordinates.
  let T₀ := (algSpec (CommRingCat.of k)).obj (op B)
  let φ := (Corepresented.affineSectionsIso B).inv.hom
  have hφ : Function.Injective φ := by
    intro a a' h
    have h1 := ConcreteCategory.congr_hom (Corepresented.affineSectionsIso B).inv_hom_id a
    have h2 := ConcreteCategory.congr_hom (Corepresented.affineSectionsIso B).inv_hom_id a'
    exact h1.symm.trans ((congrArg (Corepresented.affineSectionsIso B).hom.hom h).trans h2)
  let x₀ : T₀ ⟶ (Corepresented.groupScheme H.affinePointFunctor e).X := 𝟙 _
  have hM : ∀ i j, (ρ.pointMatrix T₀ x₀ : Matrix (Fin N) (Fin N) Γ(T₀.left, ⊤)) i j =
      φ (M i j) := by
    intro i j
    refine (regularRepresentation_pointMatrix e hR V b hV T₀ x₀ i j).trans ?_
    rw [Unipotent.homEquiv_symm_pointsEquiv_affine]
    have h0 : algSpec.fullyFaithful.preimage (X := op B) (Y := op B) x₀ = 𝟙 _ :=
      algSpec.fullyFaithful.preimage_id
    rw [h0, unop_id, Category.id_comp]
    rfl
  have hs : ∀ c : k, scalarMap T₀ c = φ (algebraMap k B c) := by
    intro c
    rw [φ.commutes]
    rfl
  have hsum : ∀ (w : Fin N → k) (P : Fin N → B),
      ∑ j, φ (P j) * φ (algebraMap k B (w j)) = φ (∑ j, w j • P j) := by
    intro w P
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, map_mul, mul_comm]
  -- The coordinates of `1` form a fixed vector of the regular representation.
  let u : Fin N → k := fun i => extendedCoord V b i 1
  have hu1 : ∑ i, u i • (b i : B) = 1 := basis_expand V b h1V
  have hu0 : u ≠ 0 := by
    intro h
    apply Unipotent.one_ne_zero' k B
    rw [← hu1, h]
    simp
  have hrowu : ∀ i, ∑ j, u j • M i j = u i • (1 : B) := by
    intro i
    have hleft1 : leftAct (extendedCoord V b i) (1 : B) = u i • (1 : B) := by
      rw [leftAct_apply, Bialgebra.comul_one, Algebra.TensorProduct.one_def,
        LinearMap.rTensor_tmul, TensorProduct.lid_tmul]
    rw [← hleft1, ← hu1, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul]
    rfl
  have hfix : ρ.IsFixedVector u := by
    rw [isFixedVector_iff_universal]
    funext i
    change ∑ j, (ρ.pointMatrix T₀ x₀ : Matrix (Fin N) (Fin N) Γ(T₀.left, ⊤)) i j *
      scalarMap T₀ (u j) = scalarMap T₀ (u i)
    simp only [hM, hs]
    exact (hsum u (M i)).trans
      (congrArg φ (by rw [hrowu i, Algebra.smul_def, mul_one]))
  -- Restrict to the original group and use the simple-span hypothesis for the dual.
  let iso := modelIso H (Lie.coordinateIso H)
  let ρH := ρ.restrict iso.inv
  have hfixH : ρH.IsFixedVector u := by
    intro T' x
    rw [pointMatrix_restrict]
    exact hfix T' _
  obtain ⟨c, hc, hcu⟩ := exists_dual_fixed_of_simple_span ρH (hss _ ρH.dual) u hu0 hfixH
  have hhi : iso.hom.hom.hom ≫ iso.inv.hom.hom = 𝟙 _ := by
    rw [← Grp.comp_hom_hom, Iso.hom_inv_id]
    rfl
  have hcol : ∀ j, ∑ i, c i • M i j = c j • (1 : B) := by
    intro j
    apply hφ
    have h := hc T₀ (x₀ ≫ iso.hom.hom.hom)
    rw [dual_restrict, pointMatrix_restrict, Category.assoc, hhi, Category.comp_id,
      dual_pointMatrix, contragredient_mulVec_eq_iff] at h
    have hj := congrFun h j
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, hM, hs] at hj
    exact (hsum c fun i => M i j).symm.trans
      (hj.trans (congrArg φ (Algebra.algebraMap_eq_smul_one _)))
  -- The integral is the corresponding combination of coordinate functionals.
  let r : Module.Dual k B := ∑ i, c i • extendedCoord V b i
  have hrb : ∀ j, r (b j : B) = c j := by
    intro j
    simp [r, LinearMap.sum_apply, extendedCoord_basis, Matrix.one_apply]
  have hr1 : r 1 = 1 := by
    rw [← hcu]
    simp [r, LinearMap.sum_apply, dotProduct, u]
  have hlin : ∀ a : B, leftAct r a = ∑ i, c i • leftAct (extendedCoord V b i) a := by
    intro a
    apply Unipotent.eq_of_forall_dual k
    intro g
    rw [apply_leftAct, map_sum]
    simp only [r, LinearMap.sum_apply, LinearMap.smul_apply, map_smul, apply_leftAct]
  have hleft : ∀ j, leftAct r (b j : B) = c j • (1 : B) := by
    intro j
    rw [hlin, ← hcol j]
    rfl
  refine ⟨r, hr1, fun y hy => ?_⟩
  have hyV : y ∈ V := subset_regularSpan _ (Finset.mem_insert_of_mem hy)
  change leftAct r y = r y • (1 : B)
  rw [← basis_expand V b hyV, map_sum, map_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, map_smul, hleft j, hrb j, smul_smul, smul_eq_mul]

/-- Composing local right integrals with the antipode gives, for every finite set of
coordinates, a normalized functional that is a left integral at each of them. -/
theorem exists_left_integral_finset_of_linearReductivity (T : Finset (Lie.coordinateAlgebra H)) :
    letI := bialgebra (corepresentableBy H (Lie.coordinateIso H))
    ∃ l : Module.Dual k (Lie.coordinateAlgebra H), l 1 = 1 ∧
      ∀ y ∈ T, IsLeftIntegralAt l y := by
  classical
  let e := corepresentableBy H (Lie.coordinateIso H)
  let := bialgebra e
  obtain ⟨r, hr1, hr⟩ := exists_right_integral_of_linearReductivity H hss (T.image (Corepresented.antipode e).hom)
  refine ⟨r ∘ₗ (Corepresented.antipode e).hom.toLinearMap, ?_, fun y hy => ?_⟩
  · change r ((Corepresented.antipode e).hom 1) = 1
    rw [map_one, hr1]
  · refine isLeftIntegralAt_comp (Corepresented.antipode e).hom (fun z => ?_) (antipode_antipode e)
      (hr _ (Finset.mem_image_of_mem _ hy))
    exact AlgHom.congr_fun (comul_comp_antipode e) z

/-- The simple-span hypothesis gives a global normalized left integral on the coordinate bialgebra. -/
theorem exists_left_integral_of_linearReductivity :
    letI := bialgebra (corepresentableBy H (Lie.coordinateIso H))
    ∃ ℓ : Module.Dual k (Lie.coordinateAlgebra H), ℓ 1 = 1 ∧
      ∀ z, IsLeftIntegralAt ℓ z := by
  let := bialgebra (corepresentableBy H (Lie.coordinateIso H))
  refine exists_left_integral (fun y => ?_) (exists_left_integral_finset_of_linearReductivity H hss)
  obtain ⟨r, hr1, hr⟩ := exists_right_integral_of_linearReductivity H hss {y}
  exact ⟨r, hr1, hr y (Finset.mem_singleton_self y)⟩

end AffineLinearEmbedding

open AffineLinearEmbedding

/-- A normalized invariant integral on the coordinate algebra of any affine linearly
reductive group, over an arbitrary field. -/
def invariantIntegralOfLinearReductivity {k : Type u} [Field k]
    (H : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom H.X.hom]
    (hss : ∀ (m : ℕ) (σ : MatrixRepresentation H (Fin m)),
      sSup {W : Submodule k (Fin m → k) | σ.IsStableSubspace W ∧ W ≠ ⊥ ∧
        ∀ U : Submodule k (Fin m → k), σ.IsStableSubspace U → U ≤ W →
          U = ⊥ ∨ U = W} = ⊤) :
    CoordinateIntegration.InvariantIntegral H :=
  let := bialgebra (corepresentableBy H (Lie.coordinateIso H))
  let h := exists_left_integral_of_linearReductivity H hss
  CoordinateIntegration.InvariantIntegral.ofCoordinateCoproduct H h.choose h.choose_spec.1
    fun z => by
      rw [coordinateCoproduct_eq_comul]
      change CoordinateIntegration.contract H _ _ (Coalgebra.comul (R := k) z) = _
      rw [contract_comul]
      exact (h.choose_spec.2 z).trans (Algebra.algebraMap_eq_smul_one _).symm

end Langlands.GroupScheme
