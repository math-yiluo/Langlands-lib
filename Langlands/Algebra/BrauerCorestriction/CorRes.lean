import Langlands.Algebra.BrauerCorestriction.BrauerClass
import Langlands.Algebra.BrauerCorestriction.PermUnits

/-!
# The tensor descent of a scalar extension

For a central simple `K`-algebra `B` and `A = L ⊗_K B`, the tensor product of the conjugates of
`A` contains `C = ⨂_K σ, B` through `⨂ b_σ ↦ ⨂ (1 ⊗ (1 ⊗ b_σ))`, and the Galois action restricts
on `C` to the permutation of tensor factors. Twisting the Galois action on `⨂_σ A^σ` by the
permutation units of `C` gives a semilinear action whose fixed space is a module for the
descended algebra and for `Cᵐᵒᵖ`.
-/

universe u

open TensorProduct PiTensorProduct Module
open Langlands.PiTensorSemilinear

namespace Langlands.BrauerCorestriction

section Embed

variable (K L N : Type u) [Field K] [Field L] [Field N] [Algebra K L] [Algebra K N]
variable (B : Type u) [Ring B] [Algebra K B]

/-- The factor map `B → (L ⊗_K B)^σ`, `b ↦ 1 ⊗ (1 ⊗ b)`, semilinear over `K → N`. -/
noncomputable def baseFactor (σ : L →ₐ[K] N) :
    B →ₛₗ[algebraMap K N] Conj (L ⊗[K] B) σ where
  toFun b := (1 : Twist σ) ⊗ₜ[L] ((1 : L) ⊗ₜ[K] b)
  map_add' x y := by rw [tmul_add, tmul_add]
  map_smul' k b := by
    rw [← TensorProduct.smul_tmul, show (k • (1 : L)) = algebraMap K L k from
      (Algebra.algebraMap_eq_smul_one k).symm, ← mul_one (algebraMap K L k),
      ← smul_eq_mul, ← smul_tmul', ← TensorProduct.smul_tmul, smul_tmul']
    congr 1
    change (σ (algebraMap K L k) * 1 : N) = algebraMap K N k * 1
    rw [σ.commutes]

variable {K L N B}

theorem baseFactor_apply (σ : L →ₐ[K] N) (b : B) :
    baseFactor K L N B σ b = (1 : Twist σ) ⊗ₜ[L] ((1 : L) ⊗ₜ[K] b) := rfl

theorem baseFactor_one (σ : L →ₐ[K] N) : baseFactor K L N B σ 1 = 1 := rfl

theorem baseFactor_mul (σ : L →ₐ[K] N) (x y : B) :
    baseFactor K L N B σ (x * y) = baseFactor K L N B σ x * baseFactor K L N B σ y := by
  simp only [baseFactor_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one]

variable (K L N B)

/-- The embedding `⨂_K σ, B → ⨂_N σ, (L ⊗_K B)^σ`. -/
noncomputable def baseEmbed :
    (⨂[K] _ : (L →ₐ[K] N), B) →ₐ[K] ConjTensor K L N (L ⊗[K] B) where
  toFun := piTensorSemilinear (algebraMap K N) (fun σ => baseFactor K L N B σ)
  map_one' := piTensorSemilinear_one _ (fun σ => baseFactor_one σ)
  map_mul' := piTensorSemilinear_mul _ (fun σ => baseFactor_mul σ)
  map_zero' := map_zero _
  map_add' := map_add _
  commutes' k := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    change piTensorSemilinear (algebraMap K N) (fun σ => baseFactor K L N B σ) (k • 1) = _
    rw [map_smulₛₗ, piTensorSemilinear_one _ (fun σ => baseFactor_one σ), algebraMap_smul]

variable {K L N B}

theorem baseEmbed_tprod (b : (L →ₐ[K] N) → B) :
    baseEmbed K L N B (PiTensorProduct.tprod K b) =
      PiTensorProduct.tprod N (fun σ => (1 : Twist σ) ⊗ₜ[L] ((1 : L) ⊗ₜ[K] b σ)) :=
  piTensorSemilinear_tprod _ b

theorem actMap_smul_base (g : N ≃ₐ[K] N) (k : K) (t : ConjTensor K L N (L ⊗[K] B)) :
    actMap (L ⊗[K] B) g (k • t) = k • actMap (L ⊗[K] B) g t := by
  rw [← algebraMap_smul N k t, map_smulₛₗ, RingHom.coe_coe, AlgEquiv.commutes, algebraMap_smul]

/-- The Galois action restricts on `⨂_K B` to the permutation of tensor factors. -/
theorem actMap_baseEmbed [Fintype (L →ₐ[K] N)] (g : N ≃ₐ[K] N)
    (c : ⨂[K] _ : (L →ₐ[K] N), B) :
    actMap (L ⊗[K] B) g (baseEmbed K L N B c) =
      baseEmbed K L N B (permAlgEquiv K (L →ₐ[K] N) B (galPerm g) c) := by
  induction c using PiTensorProduct.induction_on with
  | smul_tprod r b =>
    rw [map_smul, actMap_smul_base, map_smul, map_smul, baseEmbed_tprod, actMap_tprod,
      permAlgEquiv_tprod, baseEmbed_tprod]
    congr 2
    funext τ
    rw [conjMap_tmul, twistHom_apply]
    congr 1
    exact map_one g
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

end Embed

section Twisted

variable (K L N : Type u) [Field K] [Field L] [Field N] [Algebra K L] [Algebra K N]
variable (B : Type u) [Ring B] [Algebra K B] [FiniteDimensional K B] [Algebra.IsCentral K B]
  [IsSimpleRing B]
variable [Fintype (L →ₐ[K] N)] [DecidableEq (L →ₐ[K] N)]

/-- `g ↦ (σ ↦ g ∘ σ)` as a group homomorphism into the permutations of the embeddings. -/
def galPermHom : (N ≃ₐ[K] N) →* Equiv.Perm (L →ₐ[K] N) where
  toFun := galPerm
  map_one' := by
    ext σ l
    rfl
  map_mul' g h := by
    ext σ l
    rfl

/-- The permutation unit of `⨂_K B` attached to a Galois automorphism. -/
noncomputable def twistUnit (g : N ≃ₐ[K] N) : (⨂[K] _ : (L →ₐ[K] N), B)ˣ :=
  permUnits K B (L →ₐ[K] N) (galPermHom K L N g)

theorem twistUnit_conj (g : N ≃ₐ[K] N) (c : ⨂[K] _ : (L →ₐ[K] N), B) :
    (twistUnit K L N B g).val * c * ((twistUnit K L N B g)⁻¹).val =
      permAlgEquiv K (L →ₐ[K] N) B (galPerm g) c :=
  permUnits_conj K B (L →ₐ[K] N) (galPermHom K L N g) c

/-- The Galois action twisted by the permutation units: `t ↦ g(t) · j(w_g)`. -/
noncomputable def twistAct (g : N ≃ₐ[K] N) :
    ConjTensor K L N (L ⊗[K] B) →+ ConjTensor K L N (L ⊗[K] B) where
  toFun t := actMap (L ⊗[K] B) g t * baseEmbed K L N B (twistUnit K L N B g).val
  map_zero' := by rw [map_zero, zero_mul]
  map_add' x y := by rw [map_add, add_mul]

theorem twistAct_apply (g : N ≃ₐ[K] N) (t : ConjTensor K L N (L ⊗[K] B)) :
    twistAct K L N B g t = actMap (L ⊗[K] B) g t * baseEmbed K L N B (twistUnit K L N B g).val :=
  rfl

/-- The twisted Galois action is a semilinear action. -/
noncomputable def twistedAction :
    GaloisDescent.SemilinearAction K N (ConjTensor K L N (L ⊗[K] B)) where
  act := twistAct K L N B
  one_act t := by
    rw [twistAct_apply, actMap_one_apply, twistUnit, map_one, map_one, Units.val_one, map_one,
      mul_one]
  mul_act g h t := by
    simp only [twistAct_apply]
    rw [actMap_mul, actMap_baseEmbed, ← actMap_mul_apply, ← twistUnit_conj, mul_assoc,
      ← map_mul (baseEmbed K L N B)]
    congr 2
    simp only [twistUnit, map_mul, Units.val_mul, mul_assoc, Units.inv_mul, mul_one]
  act_smul g x t := by
    have : IsScalarTower N (ConjTensor K L N (L ⊗[K] B)) (ConjTensor K L N (L ⊗[K] B)) :=
      IsScalarTower.right (R := N) (A := ConjTensor K L N (L ⊗[K] B))
    rw [twistAct_apply, twistAct_apply, map_smulₛₗ, smul_mul_assoc]
    rfl

theorem twistedAction_act (g : N ≃ₐ[K] N) (t : ConjTensor K L N (L ⊗[K] B)) :
    (twistedAction K L N B).act g t =
      actMap (L ⊗[K] B) g t * baseEmbed K L N B (twistUnit K L N B g).val := rfl

/-- The fixed space of the twisted action. -/
noncomputable abbrev twistFixed : Submodule K (ConjTensor K L N (L ⊗[K] B)) :=
  (twistedAction K L N B).fixed

theorem mem_twistFixed (x : ConjTensor K L N (L ⊗[K] B)) :
    x ∈ twistFixed K L N B ↔ ∀ g : N ≃ₐ[K] N,
      actMap (L ⊗[K] B) g x * baseEmbed K L N B (twistUnit K L N B g).val = x := Iff.rfl

theorem mul_mem_twistFixed {d : ConjTensor K L N (L ⊗[K] B)}
    (hd : d ∈ corAlg K L N (L ⊗[K] B)) {x : ConjTensor K L N (L ⊗[K] B)}
    (hx : x ∈ twistFixed K L N B) : d * x ∈ twistFixed K L N B := by
  rw [mem_twistFixed] at hx ⊢
  rw [mem_corAlg] at hd
  intro g
  rw [actMap_mul, hd g, mul_assoc, hx g]

theorem mul_baseEmbed_mem_twistFixed {x : ConjTensor K L N (L ⊗[K] B)}
    (hx : x ∈ twistFixed K L N B) (c : ⨂[K] _ : (L →ₐ[K] N), B) :
    x * baseEmbed K L N B c ∈ twistFixed K L N B := by
  rw [mem_twistFixed] at hx ⊢
  intro g
  rw [actMap_mul, actMap_baseEmbed, ← twistUnit_conj, mul_assoc, ← map_mul (baseEmbed K L N B)]
  have hc : (twistUnit K L N B g).val * c * ((twistUnit K L N B g)⁻¹).val *
      (twistUnit K L N B g).val = (twistUnit K L N B g).val * c := by
    rw [mul_assoc, Units.inv_mul, mul_one]
  rw [hc, map_mul, ← mul_assoc, hx g]

end Twisted

section Bimodule

variable (K L N : Type u) [Field K] [Field L] [Field N] [Algebra K L] [Algebra K N]
variable (B : Type u) [Ring B] [Algebra K B] [FiniteDimensional K B] [Algebra.IsCentral K B]
  [IsSimpleRing B]
variable [Fintype (L →ₐ[K] N)] [DecidableEq (L →ₐ[K] N)]

omit [FiniteDimensional K B] [Algebra.IsCentral K B] [IsSimpleRing B]
  [Fintype (L →ₐ[K] N)] [DecidableEq (L →ₐ[K] N)] in
theorem conjTensor_mul_smul (k : K) (a b : ConjTensor K L N (L ⊗[K] B)) :
    a * (k • b) = k • (a * b) := by
  have : SMulCommClass K (ConjTensor K L N (L ⊗[K] B)) (ConjTensor K L N (L ⊗[K] B)) :=
    Algebra.to_smulCommClass (R := K) (A := ConjTensor K L N (L ⊗[K] B))
  exact mul_smul_comm k a b

omit [FiniteDimensional K B] [Algebra.IsCentral K B] [IsSimpleRing B]
  [Fintype (L →ₐ[K] N)] [DecidableEq (L →ₐ[K] N)] in
theorem conjTensor_smul_mul (k : K) (a b : ConjTensor K L N (L ⊗[K] B)) :
    (k • a) * b = k • (a * b) := by
  have : IsScalarTower K (ConjTensor K L N (L ⊗[K] B)) (ConjTensor K L N (L ⊗[K] B)) :=
    IsScalarTower.right (R := K) (A := ConjTensor K L N (L ⊗[K] B))
  exact smul_mul_assoc k a b

/-- The descended algebra acts on the twisted fixed space by left multiplication. -/
noncomputable def leftAct :
    corAlg K L N (L ⊗[K] B) →ₐ[K] Module.End K (twistFixed K L N B) where
  toFun d :=
    { toFun := fun x => ⟨d * x, mul_mem_twistFixed K L N B d.2 x.2⟩
      map_add' := fun x y => Subtype.ext (mul_add _ _ _)
      map_smul' := fun k x => Subtype.ext (conjTensor_mul_smul K L N B k _ _) }
  map_one' := by
    ext x
    exact one_mul _
  map_mul' d e := by
    ext x
    exact mul_assoc _ _ _
  map_zero' := by
    ext x
    exact zero_mul _
  map_add' d e := by
    ext x
    exact add_mul _ _ _
  commutes' k := by
    ext x
    change (algebraMap K (ConjTensor K L N (L ⊗[K] B)) k) * (x : ConjTensor K L N (L ⊗[K] B)) =
      k • (x : ConjTensor K L N (L ⊗[K] B))
    rw [Algebra.algebraMap_eq_smul_one, conjTensor_smul_mul, one_mul]

/-- The opposite of `⨂_K B` acts on the twisted fixed space by right multiplication. -/
noncomputable def rightAct :
    (⨂[K] _ : (L →ₐ[K] N), B)ᵐᵒᵖ →ₐ[K] Module.End K (twistFixed K L N B) where
  toFun c :=
    { toFun := fun x => ⟨x * baseEmbed K L N B c.unop,
        mul_baseEmbed_mem_twistFixed K L N B x.2 c.unop⟩
      map_add' := fun x y => Subtype.ext (add_mul _ _ _)
      map_smul' := fun k x => Subtype.ext (conjTensor_smul_mul K L N B k _ _) }
  map_one' := by
    ext x
    change (x : ConjTensor K L N (L ⊗[K] B)) * baseEmbed K L N B 1 = x
    rw [map_one, mul_one]
  map_mul' c d := by
    ext x
    change (x : ConjTensor K L N (L ⊗[K] B)) * baseEmbed K L N B (d.unop * c.unop) =
      (x * baseEmbed K L N B d.unop) * baseEmbed K L N B c.unop
    rw [map_mul, mul_assoc]
  map_zero' := by
    ext x
    change (x : ConjTensor K L N (L ⊗[K] B)) * baseEmbed K L N B 0 = 0
    rw [map_zero, mul_zero]
  map_add' c d := by
    ext x
    change (x : ConjTensor K L N (L ⊗[K] B)) * baseEmbed K L N B (c.unop + d.unop) = _
    rw [map_add, mul_add]
    rfl
  commutes' k := by
    ext x
    change (x : ConjTensor K L N (L ⊗[K] B)) *
        baseEmbed K L N B (algebraMap K (⨂[K] _ : (L →ₐ[K] N), B) k) =
      k • (x : ConjTensor K L N (L ⊗[K] B))
    rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one, conjTensor_mul_smul, mul_one]

/-- The bimodule action `corAlg (L ⊗ B) ⊗_K (⨂_K B)ᵐᵒᵖ → End_K(twisted fixed space)`. -/
noncomputable def bimoduleAct :
    corAlg K L N (L ⊗[K] B) ⊗[K] (⨂[K] _ : (L →ₐ[K] N), B)ᵐᵒᵖ →ₐ[K]
      Module.End K (twistFixed K L N B) :=
  Algebra.TensorProduct.lift (leftAct K L N B) (rightAct K L N B) (fun d c => by
    ext x
    exact (mul_assoc _ _ _).symm)

end Bimodule

section SplitTensor

variable (K L N : Type u) [Field K] [Field L] [Field N] [Algebra K L] [Algebra K N]
variable (B : Type u) [Ring B] [Algebra K B] [FiniteDimensional K B] [Algebra.IsCentral K B]
  [IsSimpleRing B]
variable [Fintype (L →ₐ[K] N)] [DecidableEq (L →ₐ[K] N)]
variable [FiniteDimensional K L] [FiniteDimensional K N] [IsGalois K N]

theorem finrank_twistFixed :
    finrank K (twistFixed K L N B) = finrank K B ^ Nat.card (L →ₐ[K] N) := by
  have : Module.Free K (twistFixed K L N B) :=
    @Module.Free.of_divisionRing K (twistFixed K L N B) _ inferInstance inferInstance
  rw [← Module.finrank_baseChange (R := N) (S := K) (M' := twistFixed K L N B),
    (twistedAction K L N B).descentEquiv.finrank_eq, finrank_conjTensor,
    Module.finrank_baseChange]

theorem finrank_twistFixed_pos : 0 < finrank K (twistFixed K L N B) := by
  rw [finrank_twistFixed]
  exact pow_pos Module.finrank_pos _

/-- The bimodule action written in a basis of the twisted fixed space. -/
noncomputable def bimoduleMatrix :
    corAlg K L N (L ⊗[K] B) ⊗[K] (⨂[K] _ : (L →ₐ[K] N), B)ᵐᵒᵖ →ₐ[K]
      Matrix (Fin (finrank K (twistFixed K L N B))) (Fin (finrank K (twistFixed K L N B))) K :=
  have : Module.Free K (twistFixed K L N B) :=
    @Module.Free.of_divisionRing K (twistFixed K L N B) _ inferInstance inferInstance
  have : Module.Finite K (twistFixed K L N B) :=
    Module.finite_of_finrank_pos (finrank_twistFixed_pos K L N B)
  (LinearMap.toMatrixAlgEquiv (Module.finBasis K (twistFixed K L N B))).toAlgHom.comp
    (bimoduleAct K L N B)

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem bimoduleMatrix_bijective : Function.Bijective (bimoduleMatrix K L N B) := by
  have : Algebra.IsCentral L (L ⊗[K] B) := Langlands.CentralSimple.isCentral_baseChange K B L
  have : IsSimpleRing (L ⊗[K] B) := Langlands.CentralSimple.isSimpleRing_baseChange K B L
  have : FiniteDimensional K (corAlg K L N (L ⊗[K] B)) := finiteDimensional_corAlg K L N _
  have : Algebra.IsCentral K (corAlg K L N (L ⊗[K] B)) := isCentral_corAlg K L N _
  have : IsSimpleRing (corAlg K L N (L ⊗[K] B)) := isSimpleRing_corAlg K L N _
  obtain ⟨hc, hs⟩ := piTensor_isCentral_isSimpleRing K (fun _ : (L →ₐ[K] N) => B)
  have : FiniteDimensional K (⨂[K] _ : (L →ₐ[K] N), B) := PiTensorProduct.finite
  have : Module.Free K (corAlg K L N (L ⊗[K] B)) :=
    @Module.Free.of_divisionRing K (corAlg K L N (L ⊗[K] B)) _ inferInstance inferInstance
  let instR : Ring (corAlg K L N (L ⊗[K] B) ⊗[K] (⨂[K] _ : (L →ₐ[K] N), B)ᵐᵒᵖ) :=
    Algebra.TensorProduct.instRing (R := K) (A := corAlg K L N (L ⊗[K] B))
      (B := (⨂[K] _ : (L →ₐ[K] N), B)ᵐᵒᵖ)
  have hsimp : IsSimpleRing (corAlg K L N (L ⊗[K] B) ⊗[K] (⨂[K] _ : (L →ₐ[K] N), B)ᵐᵒᵖ) :=
    @Langlands.CentralSimple.isSimpleRing_tensor K _ (corAlg K L N (L ⊗[K] B)) inferInstance
      inferInstance ((⨂[K] _ : (L →ₐ[K] N), B)ᵐᵒᵖ) inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance inferInstance
  have hpos := finrank_twistFixed_pos K L N B
  have : NeZero (finrank K (twistFixed K L N B)) := ⟨hpos.ne'⟩
  have hinj : Function.Injective (bimoduleMatrix K L N B) := by
    rcases @IsSimpleRing.injective_ringHom_or_subsingleton_codomain
      (corAlg K L N (L ⊗[K] B) ⊗[K] (⨂[K] _ : (L →ₐ[K] N), B)ᵐᵒᵖ)
      (Matrix (Fin (finrank K (twistFixed K L N B))) (Fin (finrank K (twistFixed K L N B))) K)
      inferInstance hsimp inferInstance (bimoduleMatrix K L N B).toRingHom with h | h
    · exact h
    · exact absurd h (not_subsingleton _)
  refine ⟨hinj, ?_⟩
  have hd : finrank K (corAlg K L N (L ⊗[K] B) ⊗[K] (⨂[K] _ : (L →ₐ[K] N), B)ᵐᵒᵖ) =
      finrank K (Matrix (Fin (finrank K (twistFixed K L N B)))
        (Fin (finrank K (twistFixed K L N B))) K) := by
    rw [Module.finrank_tensorProduct, finrank_corAlg_eq_pow, Module.finrank_baseChange,
      ← (MulOpposite.opLinearEquiv K).finrank_eq, finrank_piTensor_const, Module.finrank_matrix,
      Fintype.card_fin, Module.finrank_self, mul_one, finrank_twistFixed,
      Nat.card_eq_fintype_card]
  have : FiniteDimensional K
      (corAlg K L N (L ⊗[K] B) ⊗[K] (⨂[K] _ : (L →ₐ[K] N), B)ᵐᵒᵖ) :=
    @Module.Finite.tensorProduct K _ _ _ _ _ _ _ _ _
  have key := @LinearMap.injective_iff_surjective_of_finrank_eq_finrank K
    (corAlg K L N (L ⊗[K] B) ⊗[K] (⨂[K] _ : (L →ₐ[K] N), B)ᵐᵒᵖ) _ inferInstance inferInstance
    (Matrix (Fin (finrank K (twistFixed K L N B))) (Fin (finrank K (twistFixed K L N B))) K)
    inferInstance inferInstance inferInstance inferInstance hd
    { toFun := bimoduleMatrix K L N B
      map_add' := map_add _
      map_smul' := fun c x => map_smul (bimoduleMatrix K L N B) c x }
  exact key.mp hinj

/-- The descended algebra of `L ⊗_K B`, tensored with the opposite of `⨂_K B`, is a full
matrix algebra over `K`. -/
noncomputable def corResSplitEquiv :
    corAlg K L N (L ⊗[K] B) ⊗[K] (⨂[K] _ : (L →ₐ[K] N), B)ᵐᵒᵖ ≃ₐ[K]
      Matrix (Fin (finrank K (twistFixed K L N B))) (Fin (finrank K (twistFixed K L N B))) K :=
  AlgEquiv.ofBijective (bimoduleMatrix K L N B) (bimoduleMatrix_bijective K L N B)

end SplitTensor

end Langlands.BrauerCorestriction
