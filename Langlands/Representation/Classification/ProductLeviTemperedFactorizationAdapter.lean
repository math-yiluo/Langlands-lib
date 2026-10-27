import Langlands.Representation.Classification.ProductLeviTemperedSufficiencyStatement
import Langlands.Representation.Classification.TemperedExponentStatement
import Langlands.Representation.Classification.BlockTensorAnalyticStatement
import Langlands.Representation.Classification.ProductLeviCentralCharacter
import Langlands.Representation.Classification.ProductLeviDualOppositeAdapter
import Langlands.Representation.CuspidalSupport.LeviAdmissibleFactorizationProof
import Langlands.Representation.CuspidalSupport.LeviTensorReflectionProof

/-!
# Product-Levi tempered sufficiency from the GL criterion and block tensors

The exponent criterion for temperedness on `GL_n` and the comparison of
temperedness for actual block tensors imply the upper core form of product-Levi
tempered sufficiency. An irreducible admissible representation of a product
Levi is a block tensor of irreducible admissible factors. Refining one outer
block and leaving the others whole, a fixed basis tensor in the other slots
embeds the Jacquet module of one factor in the refined Jacquet module of the
product, so every exponent of a factor gives a generalized exponent of the
product. The core bounds then make every factor tempered.
-/

noncomputable section

namespace Langlands

open GeneralLinear Geometric
open scoped BigOperators NNReal TensorProduct

universe uF uV

namespace ProductLeviTemperedFactorization

section Linear

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- If `P (J z) = c • J (Q z)` for every `z`, the same holds for all powers,
with `c ^ k`. -/
theorem pow_apply_of_apply (J : V →ₗ[ℂ] W) (P : Module.End ℂ W) (Q : Module.End ℂ V)
    (c : ℂ) (h : ∀ z, P (J z) = c • J (Q z)) (k : ℕ) (z : V) :
    (P ^ k) (J z) = c ^ k • J ((Q ^ k) z) := by
  induction k generalizing z with
  | zero => simp
  | succ k ih =>
    rw [pow_succ P, Module.End.mul_apply, h, map_smul, ih, smul_smul, ← pow_succ',
      pow_succ Q, Module.End.mul_apply]

end Linear

section Slots

open Module

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {H : ι → Type*} [∀ j, Group (H j)]
  {V : ι → Type*} [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)]
  {W : Type*} [AddCommGroup W] [Module ℂ W]

/-- For a representation equivalent to an external tensor whose factors other
than `i` are nonzero, inserting a fixed basis tensor in the other slots and
contracting against its coordinate give linear maps `ins` and `con` with
`con ∘ ins = id`. Insertion intertwines the action of factor `i` with the
action through `Pi.mulSingle i`, and contraction intertwines group elements
that are trivial away from `i` with their `i`-th component. -/
theorem exists_slot_insertion (ρ : ∀ j, Representation ℂ (H j) (V j))
    {σ : Representation ℂ (∀ j, H j) W} (e : σ.Equiv (FiniteTensor.external ρ)) (i : ι)
    (hne : ∀ j, j ≠ i → Nontrivial (V j)) :
    ∃ (ins : V i →ₗ[ℂ] W) (con : W →ₗ[ℂ] V i),
      (∀ x, con (ins x) = x) ∧
      (∀ h x, ins (ρ i h x) = σ (Pi.mulSingle i h) (ins x)) ∧
      (∀ g w, (∀ j, j ≠ i → g j = 1) → con (σ g w) = ρ i (g i) (con w)) := by
  classical
  let J := ({i}ᶜ : Set ι)
  let b := fun j : J => Basis.ofVectorSpace ℂ (V j)
  have hb : ∀ j : J, Nonempty (Basis.ofVectorSpaceIndex ℂ (V j)) := by
    intro j
    let := hne j j.property
    exact (b j).index_nonempty
  let a := fun j : J => Classical.choice (hb j)
  let c := Basis.piTensorProduct b
  let E := PiTensorProduct.equivPiTensorComplSingletonTensor ℂ V i
  let insT : V i →ₗ[ℂ] ⨂[ℂ] j, V j :=
    E.symm.toLinearMap ∘ₗ TensorProduct.mk ℂ (⨂[ℂ] j : J, V j) (V i) (c a)
  let conT : (⨂[ℂ] j, V j) →ₗ[ℂ] V i :=
    (TensorProduct.lid ℂ (V i)).toLinearMap ∘ₗ
      TensorProduct.map (c.coord a) LinearMap.id ∘ₗ E.toLinearMap
  have hinsT : ∀ (f : V i →ₗ[ℂ] V i) x,
      insT (f x) = PiTensorProduct.map (FiniteTensor.slot i f) (insT x) := by
    intro f x
    apply E.injective
    rw [FiniteTensor.split_map_slot]
    simp [insT, E]
  have hconT : ∀ (f : V i →ₗ[ℂ] V i) z,
      conT (PiTensorProduct.map (FiniteTensor.slot i f) z) = f (conT z) := by
    intro f z
    simp only [conT, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
    rw [FiniteTensor.split_map_slot]
    generalize E z = y
    induction y using TensorProduct.inductionOn with
    | tmul y v => simp
    | add y y' hy hy' => simp only [map_add, hy, hy']
  refine ⟨e.symm.toLinearMap ∘ₗ insT, conT ∘ₗ e.toLinearMap, ?_, ?_, ?_⟩
  · intro x
    simp [insT, conT, c, Basis.coord_apply]
  · intro h x
    simp only [LinearMap.coe_comp, Function.comp_apply, Representation.Equiv.coe_toLinearMap]
    rw [hinsT, ← FiniteTensor.external_mulSingle]
    exact Representation.IntertwiningMap.isIntertwining _ _ e.symm.toIntertwiningMap
      (Pi.mulSingle i h) (insT x)
  · intro g w hg
    have hg' : g = Pi.mulSingle i (g i) := by
      funext j
      by_cases hj : j = i
      · subst hj
        simp
      · rw [Pi.mulSingle_eq_of_ne hj, hg j hj]
    have he : e (σ g w) = FiniteTensor.external ρ (Pi.mulSingle i (g i)) (e w) := by
      rw [← hg']
      exact Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g w
    simp only [LinearMap.coe_comp, Function.comp_apply, Representation.Equiv.coe_toLinearMap]
    rw [he, FiniteTensor.external_mulSingle, hconT]

end Slots

section Blocks

variable {R : Type*} [CommRing R]

/-- Block scalars of a one-block shape are scalar matrices. -/
theorem blockScalar_of_length_eq_one {m : ℕ} (B : BlockShape m) (hB : B.length = 1)
    (c : Fin B.length → Rˣ) : B.blockScalar R c = scalar (∏ k, c k) := by
  have : Subsingleton (Fin B.length) := by
    rw [hB]
    infer_instance
  apply Units.ext
  rw [B.coe_blockScalar, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  congr 1
  funext x
  rw [Fintype.prod_subsingleton c (B.indexEquiv.symm x).1]

end Blocks

section Blocks

variable {n : ℕ} (C : BlockShape n) (D : BlockRefinement C) (R : Type*) [CommRing R]

/-- The fine coordinates `a_(e(i,k))` inside the outer block `i`. -/
def innerCoords (i : Fin C.length) :
    (Fin (C.flatten D).length → Rˣ) →* (Fin (D i).length → Rˣ) where
  toFun a k := a (C.flattenBlockEquiv D ⟨i, k⟩)
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem innerCoords_apply (i : Fin C.length) (a : Fin (C.flatten D).length → Rˣ)
    (k : Fin (D i).length) :
    innerCoords C D R i a k = a (C.flattenBlockEquiv D ⟨i, k⟩) := rfl

/-- In every outer block `j ≠ i`, the product of the fine coordinates of `j`;
in block `i`, the unit. -/
def otherBlockProducts (i : Fin C.length) :
    (Fin (C.flatten D).length → Rˣ) →* (Fin C.length → Rˣ) where
  toFun a j := if j = i then 1 else ∏ k : Fin (D j).length, a (C.flattenBlockEquiv D ⟨j, k⟩)
  map_one' := by
    funext j
    split_ifs <;> simp
  map_mul' a a' := by
    funext j
    simp only [Pi.mul_apply]
    split_ifs
    · simp
    · exact Finset.prod_mul_distrib

theorem otherBlockProducts_apply (i : Fin C.length) (a : Fin (C.flatten D).length → Rˣ)
    (j : Fin C.length) :
    otherBlockProducts C D R i a j =
      if j = i then 1 else ∏ k : Fin (D j).length, a (C.flattenBlockEquiv D ⟨j, k⟩) := rfl

theorem continuous_innerCoords [TopologicalSpace R] (i : Fin C.length) :
    Continuous (innerCoords C D R i) :=
  continuous_pi fun _ => continuous_apply _

theorem continuous_otherBlockProducts [TopologicalSpace R] [IsTopologicalRing R]
    (i : Fin C.length) : Continuous (otherBlockProducts C D R i) := by
  change Continuous fun (a : Fin (C.flatten D).length → Rˣ) (j : Fin C.length) =>
    if j = i then (1 : Rˣ) else ∏ k : Fin (D j).length, a (C.flattenBlockEquiv D ⟨j, k⟩)
  refine continuous_pi fun j => ?_
  split_ifs
  · exact continuous_const
  · exact continuous_finsetProd _ fun k _ => continuous_apply _

theorem continuous_blockScalarLevi [TopologicalSpace R] :
    Continuous (C.blockScalarLevi R) :=
  continuous_pi fun j =>
    (GeneralLinear.scalarContinuous (n := C.size j)).continuous.comp (continuous_apply j)

/-- If every outer block other than `i` is left whole, a flattened block
scalar is the inner block scalar of block `i` times an outer block scalar. -/
theorem flattenedLeviEquiv_blockScalarLevi_val (i : Fin C.length)
    (hD : ∀ j, j ≠ i → (D j).length = 1) (c : Fin (C.flatten D).length → Rˣ) :
    (flattenedLeviEquiv R C D ((C.flatten D).blockScalarLevi R c)).val =
      Pi.mulSingle i ((D i).blockScalar R (innerCoords C D R i c)) *
        C.blockScalarLevi R (otherBlockProducts C D R i c) := by
  funext j
  rw [Geometric.flattenedLeviEquiv_blockScalarLevi_apply, Pi.mul_apply, C.blockScalarLevi_apply,
    otherBlockProducts_apply]
  by_cases hj : j = i
  · subst hj
    rw [Pi.mulSingle_eq_same, ite_eq_left rfl, map_one, mul_one]
    rfl
  · rw [Pi.mulSingle_eq_of_ne hj, ite_eq_right hj, one_mul,
      blockScalar_of_length_eq_one (D j) (hD j hj)]

/-- A scalar matrix in block `i` is the outer block scalar of `Pi.mulSingle i`. -/
theorem mulSingle_scalar_eq_blockScalarLevi (i : Fin C.length) (a : Rˣ) :
    (Pi.mulSingle i (scalar a) : C.Levi R) = C.blockScalarLevi R (Pi.mulSingle i a) := by
  funext j
  rw [C.blockScalarLevi_apply]
  by_cases hj : j = i
  · subst hj
    rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
  · rw [Pi.mulSingle_eq_of_ne hj, Pi.mulSingle_eq_of_ne hj, map_one]

end Blocks

section Padic

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- The explicit modulus of a one-block shape is trivial. -/
theorem leviModulus_of_length_eq_one {m : ℕ} (B : BlockShape m) (hB : B.length = 1)
    (g : B.Levi F.Carrier) : T.leviModulus B g = 1 := by
  have : Subsingleton (Fin B.length) := by
    rw [hB]
    infer_instance
  rw [T.leviModulus_apply]
  apply Finset.prod_eq_one
  intro k _
  have hf : Finset.univ.filter (fun j : Fin B.length => k < j) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
    exact le_of_eq (Subsingleton.elim j k)
  rw [hf, Finset.prod_empty]

/-- If every outer block other than `i` is left whole, the refined modulus of
a flattened block scalar is the modulus of its inner block scalar in block `i`. -/
theorem refinedLeviModulus_blockScalarLevi {n : ℕ} (C : BlockShape n)
    (D : BlockRefinement C) (i : Fin C.length) (hD : ∀ j, j ≠ i → (D j).length = 1)
    (c : Fin (C.flatten D).length → F.Carrierˣ) :
    T.refinedLeviModulus C D
        (flattenedLeviEquiv F.Carrier C D ((C.flatten D).blockScalarLevi F.Carrier c)) =
      T.leviModulus (D i) ((D i).blockScalarLevi F.Carrier (innerCoords C D F.Carrier i c)) := by
  rw [T.refinedLeviModulus_apply, Fintype.prod_eq_single i]
  · rw [PadicField.TopologicalData.refinedLeviBlock_flattenedLeviEquiv,
      Geometric.flattenedLeviProductEquiv_blockScalarLevi]
    rfl
  · intro j hj
    exact leviModulus_of_length_eq_one T (D j) (hD j hj) _

/-- Refine the outer block `i` by `D i` and leave the other blocks whole. Maps
`ins` and `con` as in `exists_slot_insertion` induce an injective map from the
Jacquet module of the factor along `D i` to the refined Jacquet module. It
carries the split-centre action at the inner coordinates of block `i` to the
refined action of the flattened block scalar, up to the scalar character of the
other blocks. -/
theorem exists_refinedJacquet_embedding {n : ℕ} (C : BlockShape n)
    {W : Type*} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (C.Levi F.Carrier) W)
    (ω : (Fin C.length → F.Carrierˣ) →* ℂˣ)
    (hω : Classification.HasScalarCharacter σ (C.blockScalarLevi F.Carrier) ω)
    (i : Fin C.length) {X : Type*} [AddCommGroup X] [Module ℂ X]
    (τ : Representation ℂ (GeneralLinear (C.size i) F.Carrier) X)
    (ins : X →ₗ[ℂ] W) (con : W →ₗ[ℂ] X) (hci : ∀ x, con (ins x) = x)
    (hins : ∀ h x, ins (τ h x) = σ (Pi.mulSingle i h) (ins x))
    (hcon : ∀ g w, (∀ j, j ≠ i → g j = 1) → con (σ g w) = τ (g i) (con w))
    (D : BlockRefinement C) (hD : ∀ j, j ≠ i → (D j).length = 1) :
    ∃ J : (D i).JacquetModule τ →ₗ[ℂ] RefinedJacquetModule C D σ,
      Function.Injective J ∧
      ∀ (a : Fin (C.flatten D).length → F.Carrierˣ) (y : (D i).JacquetModule τ),
        T.normalizedRefinedJacquet C D σ
            (flattenedLeviEquiv F.Carrier C D ((C.flatten D).blockScalarLevi F.Carrier a))
            (J y) =
          (ω (otherBlockProducts C D F.Carrier i a) : ℂ) •
            J (T.splitCentreJacquet (D i) τ (innerCoords C D F.Carrier i a) y) := by
  classical
  have hmem : ∀ u : (D i).unipotentRadical F.Carrier,
      (Pi.mulSingle i (u : (D i).parabolic F.Carrier).val : C.Levi F.Carrier) ∈
        refinedUnipotent F.Carrier C D := by
    intro u
    rw [mem_refinedUnipotent]
    intro j
    by_cases hj : j = i
    · subst hj
      rw [Pi.mulSingle_eq_same]
      exact Subgroup.mem_map.mpr ⟨u.val, u.property, rfl⟩
    · rw [Pi.mulSingle_eq_of_ne hj]
      exact Subgroup.one_mem _
  let J : (D i).JacquetModule τ →ₗ[ℂ] RefinedJacquetModule C D σ :=
    Jacquet.lift (τ.comp ((D i).parabolic F.Carrier).subtype) ((D i).unipotentRadical F.Carrier)
      (refinedJacquetMk C D σ ∘ₗ ins) (fun u => by
        apply LinearMap.ext
        intro x
        change refinedJacquetMk C D σ (ins (τ (u : (D i).parabolic F.Carrier).val x)) =
          refinedJacquetMk C D σ (ins x)
        rw [hins]
        exact Jacquet.mk_apply_subgroup σ (refinedUnipotent F.Carrier C D) ⟨_, hmem u⟩ (ins x))
  have hN : ∀ j, j ≠ i → (D j).unipotentSubgroup F.Carrier = ⊥ := fun j hj =>
    (D j).singleBlock_unipotentSubgroup_eq_bot (hD j hj) F.Carrier
  let P : RefinedJacquetModule C D σ →ₗ[ℂ] (D i).JacquetModule τ :=
    Jacquet.lift σ (refinedUnipotent F.Carrier C D) ((D i).jacquetMk τ ∘ₗ con) (fun g => by
      apply LinearMap.ext
      intro w
      change (D i).jacquetMk τ (con (σ g.val w)) = (D i).jacquetMk τ (con w)
      have hg := (mem_refinedUnipotent F.Carrier C D g.val).mp g.property
      have hone : ∀ j, j ≠ i → g.val j = 1 := by
        intro j hj
        have h := hg j
        rw [hN j hj, Subgroup.mem_bot] at h
        exact h
      rw [hcon g.val w hone]
      obtain ⟨u, hu, hue⟩ := Subgroup.mem_map.mp (hg i)
      rw [← hue]
      exact Jacquet.mk_apply_subgroup (τ.comp ((D i).parabolic F.Carrier).subtype)
        ((D i).unipotentRadical F.Carrier) ⟨u, hu⟩ (con w))
  have hPJ : Function.LeftInverse P J := by
    intro y
    obtain ⟨x, rfl⟩ := (D i).jacquetMk_surjective τ y
    change (D i).jacquetMk τ (con (ins x)) = (D i).jacquetMk τ x
    rw [hci]
  refine ⟨J, hPJ.injective, ?_⟩
  intro a y
  obtain ⟨x, rfl⟩ := (D i).jacquetMk_surjective τ y
  rw [T.splitCentreJacquet_mk, map_smul]
  change T.normalizedRefinedJacquet C D σ _ (refinedJacquetMk C D σ (ins x)) =
    _ • (_ • refinedJacquetMk C D σ (ins (τ ((D i).leviEmbedding F.Carrier
      ((D i).blockScalarLevi F.Carrier (innerCoords C D F.Carrier i a))) x)))
  rw [T.normalizedRefinedJacquet_mk, flattenedLeviEquiv_blockScalarLevi_val C D F.Carrier i hD a,
    map_mul, Module.End.mul_apply, hω, map_smul, ← hins, map_smul,
    T.refinedLeviInverseHalfModulus_apply, refinedLeviModulus_blockScalarLevi T C D i hD a,
    smul_comm]
  rfl

/-- The core bounds of a product-Levi representation bound every exponent of
the factor in block `i`, for a refinement that refines only block `i`. -/
theorem jacquetExponent_bound_of_core {n : ℕ} (C : BlockShape n)
    {W : Type*} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (C.Levi F.Carrier) W)
    (ω : (Fin C.length → F.Carrierˣ) →* ℂˣ)
    (hω : Classification.HasScalarCharacter σ (C.blockScalarLevi F.Carrier) ω)
    (hunit : ∀ a, ‖(ω a : ℂ)‖ = 1)
    (hωopen : letI := T.topology; IsOpen (ω.ker : Set (Fin C.length → F.Carrierˣ)))
    (hcore : letI := T.topology
      ∀ (D : BlockRefinement C) (ψ : (Fin (C.flatten D).length → F.Carrierˣ) →* ℂˣ),
        IsOpen (ψ.ker : Set (Fin (C.flatten D).length → F.Carrierˣ)) →
        IsGeneralizedEigencharacter
          ((T.normalizedRefinedJacquet C D σ).comp
            ((flattenedLeviEquiv F.Carrier C D).toMonoidHom.comp
              ((C.flatten D).blockScalarLevi F.Carrier))) ψ →
        ∀ a : Fin (C.flatten D).length → F.Carrierˣ,
          (∀ j : Fin C.length, Monotone (fun i : Fin (D j).length =>
            T.normalizedAbs (a (C.flattenBlockEquiv D ⟨j, i⟩) : F.Carrier))) →
          ‖(ψ a : ℂ)‖ ≤ 1)
    (i : Fin C.length) {X : Type*} [AddCommGroup X] [Module ℂ X]
    (τ : Representation ℂ (GeneralLinear (C.size i) F.Carrier) X)
    (ins : X →ₗ[ℂ] W) (con : W →ₗ[ℂ] X) (hci : ∀ x, con (ins x) = x)
    (hins : ∀ h x, ins (τ h x) = σ (Pi.mulSingle i h) (ins x))
    (hcon : ∀ g w, (∀ j, j ≠ i → g j = 1) → con (σ g w) = τ (g i) (con w))
    (D : BlockRefinement C) (hD : ∀ j, j ≠ i → (D j).length = 1)
    (χ : (Fin (D i).length → F.Carrierˣ) →* ℂˣ) (hχ : T.IsJacquetExponent (D i) τ χ)
    (a : Fin (D i).length → F.Carrierˣ)
    (ha : Monotone fun k => T.normalizedAbs (a k : F.Carrier)) :
    ‖(χ a : ℂ)‖ ≤ 1 := by
  classical
  let := T.topology
  let := T.moduleTopology
  let : IsTopologicalRing F.Carrier := IsModuleTopology.isTopologicalRing (Padic p) F.Carrier
  obtain ⟨J, hJ, hJeq⟩ :=
    exists_refinedJacquet_embedding T C σ ω hω i τ ins con hci hins hcon D hD
  let r := innerCoords C D F.Carrier i
  let b := otherBlockProducts C D F.Carrier i
  let ψ : (Fin (C.flatten D).length → F.Carrierˣ) →* ℂˣ := χ.comp r * ω.comp b
  have hψopen : IsOpen (ψ.ker : Set (Fin (C.flatten D).length → F.Carrierˣ)) := by
    have h1 : IsOpen ((χ.comp r).ker : Set (Fin (C.flatten D).length → F.Carrierˣ)) :=
      hχ.1.preimage (continuous_innerCoords C D F.Carrier i)
    have h2 : IsOpen ((ω.comp b).ker : Set (Fin (C.flatten D).length → F.Carrierˣ)) :=
      hωopen.preimage (continuous_otherBlockProducts C D F.Carrier i)
    apply Subgroup.isOpen_mono (H₁ := (χ.comp r).ker ⊓ (ω.comp b).ker)
    · intro x hx
      rw [Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker] at hx
      rw [MonoidHom.mem_ker]
      change (χ.comp r) x * (ω.comp b) x = 1
      rw [hx.1, hx.2, mul_one]
    · exact h1.inter h2
  have hgen : IsGeneralizedEigencharacter
      ((T.normalizedRefinedJacquet C D σ).comp
        ((flattenedLeviEquiv F.Carrier C D).toMonoidHom.comp
          ((C.flatten D).blockScalarLevi F.Carrier))) ψ := by
    obtain ⟨k, y, hy, hk⟩ := (isGeneralizedEigencharacter_iff _ _).mp hχ.2
    refine (isGeneralizedEigencharacter_iff _ _).mpr
      ⟨k, J y, fun h => hy (hJ (h.trans (map_zero J).symm)), fun c => ?_⟩
    have hstep : ∀ z, (((T.normalizedRefinedJacquet C D σ).comp
        ((flattenedLeviEquiv F.Carrier C D).toMonoidHom.comp
          ((C.flatten D).blockScalarLevi F.Carrier))) c - (ψ c : ℂ) • 1) (J z) =
        (ω (b c) : ℂ) • J ((T.splitCentreJacquet (D i) τ (r c) - (χ (r c) : ℂ) • 1) z) := by
      intro z
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
        MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, map_sub, map_smul, smul_sub]
      rw [hJeq c z, smul_smul]
      congr 2
      change ((χ (r c) * ω (b c) : ℂˣ) : ℂ) = (ω (b c) : ℂ) * (χ (r c) : ℂ)
      rw [Units.val_mul, mul_comm]
    rw [pow_apply_of_apply J _ _ _ hstep k y, hk (r c), map_zero, smul_zero]
  let f : ((j : Fin C.length) × Fin (D j).length) → F.Carrierˣ := fun q =>
    if h : q.1 = i then a (h ▸ q.2) else 1
  let a' : Fin (C.flatten D).length → F.Carrierˣ := fun k => f ((C.flattenBlockEquiv D).symm k)
  have ha' : ∀ q, a' (C.flattenBlockEquiv D q) = f q := by
    intro q
    simp only [a', Equiv.symm_apply_apply]
  have ha'i : ∀ k, a' (C.flattenBlockEquiv D ⟨i, k⟩) = a k := by
    intro k
    rw [ha']
    exact dite_eq_left rfl
  have hmono : ∀ j : Fin C.length, Monotone (fun k : Fin (D j).length =>
      T.normalizedAbs (a' (C.flattenBlockEquiv D ⟨j, k⟩) : F.Carrier)) := by
    intro j
    by_cases hj : j = i
    · subst hj
      simpa only [ha'i] using ha
    · have : Subsingleton (Fin (D j).length) := by
        rw [hD j hj]
        infer_instance
      exact Subsingleton.monotone _
  have hb := hcore D ψ hψopen hgen a' hmono
  have hra : r a' = a := funext ha'i
  have hψa : ‖(ψ a' : ℂ)‖ = ‖(χ a : ℂ)‖ := by
    change ‖((χ (r a') * ω (b a') : ℂˣ) : ℂ)‖ = _
    rw [Units.val_mul, norm_mul, hunit, mul_one, hra]
  rw [← hψa]
  exact hb

end Padic

end ProductLeviTemperedFactorization

open ProductLeviTemperedFactorization in
/-- The GL exponent criterion and the block-tensor temperedness comparison
imply the upper core form of product-Levi tempered sufficiency. -/
theorem glProductLeviTemperedExponentSufficiency_of_criterion
    (hcrit : GLTemperedExponentCriterionStatement.{uF, uV})
    (htensor : GLBlockTensorTemperedStatement.{uF, uV}) :
    GLProductLeviTemperedExponentSufficiencyStatement.{uF, uV} := by
  classical
  intro p _ F T
  let := T.topology
  intro n hn C S ω hirr hadm hω hunit hcore
  obtain ⟨A, hAI, hAA, ⟨e⟩⟩ :=
    CuspidalSupport.padicLeviAdmissibleFactorization.{uF, uV} p F T n hn C ⟨S, hadm.1⟩
      hirr hadm
  have hne : ∀ j, Nontrivial (A j).obj.V := by
    intro j
    let := hAI j
    exact IsSimpleModule.nontrivial
      (MonoidAlgebra ℂ (GeneralLinear (C.size j) F.Carrier)) (A j).representation.asModule
  have hSne : Nontrivial S.V := by
    let := hirr
    exact IsSimpleModule.nontrivial (MonoidAlgebra ℂ (C.Levi F.Carrier)) S.ρ.asModule
  have hωopen : IsOpen (ω.ker : Set (Fin C.length → F.Carrierˣ)) := by
    let := T.moduleTopology
    let : IsTopologicalRing F.Carrier := IsModuleTopology.isTopologicalRing (Padic p) F.Carrier
    exact Classification.HasScalarCharacter.isOpen_ker hω
      (continuous_blockScalarLevi C F.Carrier) hadm.1
  have hbound : ∀ (i : Fin C.length) (B : BlockShape (C.size i))
      (χ : (Fin B.length → F.Carrierˣ) →* ℂˣ), T.IsJacquetExponent B (A i).representation χ →
      ∀ a : Fin B.length → F.Carrierˣ, Monotone (fun k => T.normalizedAbs (a k : F.Carrier)) →
        ‖(χ a : ℂ)‖ ≤ 1 := by
    intro i B
    obtain ⟨ins, con, hci, hins, hcon⟩ :=
      exists_slot_insertion (fun j => (A j).representation) e i (fun j _ => hne j)
    let S₀ : BlockRefinement C := fun j =>
      { length := 1
        size := fun _ => C.size j
        positive := fun _ => C.positive j
        sum_eq := by simp }
    let D : BlockRefinement C := Function.update S₀ i B
    have hD : ∀ j, j ≠ i → (D j).length = 1 := by
      intro j hj
      simp [D, S₀, hj]
    have key := fun χ => jacquetExponent_bound_of_core T C S.ρ ω hω hunit hωopen hcore i
      (A i).representation ins con hci hins hcon D hD χ
    have hDi : D i = B := by simp [D]
    rw [hDi] at key
    exact key
  have hscalar : ∀ (i : Fin C.length) (a : F.Carrierˣ) (v : (A i).obj.V),
      (A i).representation (GeneralLinear.scalar a) v =
        ((ω.comp (MonoidHom.mulSingle (fun _ => F.Carrierˣ) i)) a : ℂ) • v := by
    intro i a v
    obtain ⟨ins, con, hci, hins, -⟩ :=
      exists_slot_insertion (fun j => (A j).representation) e i (fun j _ => hne j)
    have h := hins (GeneralLinear.scalar a) v
    rw [mulSingle_scalar_eq_blockScalarLevi C F.Carrier i a, hω] at h
    have h2 := congrArg con h
    rw [hci, map_smul, hci] at h2
    exact h2
  have htemp : ∀ i, T.IsTempered (A i).representation := fun i =>
    (hcrit p F T (C.size i) (C.positive i) (A i).obj.V (A i).representation
      (ω.comp (MonoidHom.mulSingle (fun _ => F.Carrierˣ) i)) (hAA i) (hscalar i)).mpr
      (hbound i)
  have := T.leviTopologicalGroup C
  intro Q mQ bQ μ hμ
  exact isTemperedModCenter_of_equiv e.symm μ
    ((htensor p F T n hn C (fun j => (A j).obj.V) (fun j => (A j).representation)
      hAI hAA).mp htemp μ)

end Langlands
