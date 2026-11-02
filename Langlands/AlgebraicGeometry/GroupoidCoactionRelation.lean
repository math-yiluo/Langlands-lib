import Langlands.AlgebraicGeometry.GroupoidCoactionUniversal
import Langlands.AlgebraicGeometry.GroupoidCoactionInvariants
import Mathlib.RingTheory.TensorProduct.Maps

/-! # The relation-ring coaction -/

universe u

open TensorProduct

namespace Langlands.AlgebraicGeometry.GroupoidCoaction

variable {B C : Type u} [CommRing B] [CommRing C] [Algebra B C]
variable {t : B →+* C}

private def tensorRingLift {D : Type u} [CommRing D]
    (f g : C →+* D) (h : f.comp (algebraMap B C) = g.comp (algebraMap B C)) :
    C ⊗[B] C →+* D := by
  letI : Algebra B D := (f.comp (algebraMap B C)).toAlgebra
  let f' : C →ₐ[B] D := ⟨f, fun _ => rfl⟩
  let g' : C →ₐ[B] D := ⟨g, fun b => (congrArg (fun q : B →+* D => q b) h).symm⟩
  exact (Algebra.TensorProduct.lift f' g' (fun _ _ => Commute.all _ _)).toRingHom

private lemma tensorRingLift_tmul {D : Type u} [CommRing D]
    (f g : C →+* D) (h : f.comp (algebraMap B C) = g.comp (algebraMap B C))
    (c d : C) : tensorRingLift f g h (c ⊗ₜ d) = f c * g d :=
  rfl

/-- The arrow obtained by reversing the left universal arrow with common source. -/
noncomputable def relationInverseLeft (hE : RingEtaleEquivalenceRelation t) :
    C →+* C ⊗[B] C :=
  (hE.symm (C ⊗[B] C)
    (Algebra.TensorProduct.includeLeft : C →ₐ[B] C ⊗[B] C).toRingHom).choose

lemma relationInverseLeft_comp_t (hE : RingEtaleEquivalenceRelation t) :
    (relationInverseLeft hE).comp t =
      (Algebra.TensorProduct.includeLeft : C →ₐ[B] C ⊗[B] C).toRingHom.comp
        (algebraMap B C) :=
  (hE.symm (C ⊗[B] C)
    (Algebra.TensorProduct.includeLeft : C →ₐ[B] C ⊗[B] C).toRingHom).choose_spec.1

lemma relationInverseLeft_comp_source (hE : RingEtaleEquivalenceRelation t) :
    (relationInverseLeft hE).comp (algebraMap B C) =
      (Algebra.TensorProduct.includeLeft : C →ₐ[B] C ⊗[B] C).toRingHom.comp t :=
  (hE.symm (C ⊗[B] C)
    (Algebra.TensorProduct.includeLeft : C →ₐ[B] C ⊗[B] C).toRingHom).choose_spec.2

lemma relation_pair_compat (hE : RingEtaleEquivalenceRelation t) :
    (Algebra.TensorProduct.includeRight : C →ₐ[B] C ⊗[B] C).toRingHom.comp
        (algebraMap B C) =
      (relationInverseLeft hE).comp t := by
  rw [relationInverseLeft_comp_t]
  ext b
  simp

/-- The difference of the universal arrows with equal source. -/
noncomputable def relationCoactionHom (hE : RingEtaleEquivalenceRelation t) :
    C →+* C ⊗[B] C :=
  (hE.trans (C ⊗[B] C)
    (Algebra.TensorProduct.includeRight : C →ₐ[B] C ⊗[B] C).toRingHom
    (relationInverseLeft hE) (relation_pair_compat hE)).choose

@[simp]
lemma relationCoactionHom_target (hE : RingEtaleEquivalenceRelation t) (b : B) :
    relationCoactionHom hE (t b) = (1 : C) ⊗ₜ t b :=
  congrArg (fun q : B →+* C ⊗[B] C => q b)
    (hE.trans (C ⊗[B] C)
      (Algebra.TensorProduct.includeRight : C →ₐ[B] C ⊗[B] C).toRingHom
      (relationInverseLeft hE) (relation_pair_compat hE)).choose_spec.1

@[simp]
lemma relationCoactionHom_source (hE : RingEtaleEquivalenceRelation t) (b : B) :
    relationCoactionHom hE (algebraMap B C b) = t b ⊗ₜ (1 : C) := by
  have hs := (hE.trans (C ⊗[B] C)
    (Algebra.TensorProduct.includeRight : C →ₐ[B] C ⊗[B] C).toRingHom
    (relationInverseLeft hE) (relation_pair_compat hE)).choose_spec.2
  exact congrArg (fun q : B →+* C ⊗[B] C => q b)
    (hs.trans (relationInverseLeft_comp_source hE))

lemma relationCoactionHom_smul (hE : RingEtaleEquivalenceRelation t) (b : B) (c : C) :
    relationCoactionHom hE (b • c) = t b • relationCoactionHom hE c := by
  rw [Algebra.smul_def, map_mul, relationCoactionHom_source]
  simp [Algebra.smul_def]

private def specializeRingHom {T : Type u} [CommRing T] [Algebra B T]
    (φ : C →ₐ[B] T) : C ⊗[B] C →+* T ⊗[B] C :=
  (Algebra.TensorProduct.map φ (AlgHom.id B C)).toRingHom

private lemma specializeRingHom_eq {T : Type u} [CommRing T] [Algebra B T]
    (φ : C →ₐ[B] T) (x : C ⊗[B] C) :
    specializeRingHom φ x = LinearMap.rTensor C φ.toLinearMap x := by
  induction x <;> simp_all [specializeRingHom]

private noncomputable def composeRelationRingHom (hE : RingEtaleEquivalenceRelation t)
    {T : Type u} [CommRing T] [Algebra B T]
    (φ₁ : C →+* T) (φ₂ : C →ₐ[B] T)
    (h : φ₁.comp (algebraMap B C) = (φ₂ : C →+* T).comp t) :
    C ⊗[B] C →+* T ⊗[B] C :=
  tensorRingLift
    ((Algebra.TensorProduct.includeLeft : T →ₐ[B] T ⊗[B] C).toRingHom.comp φ₁)
    ((specializeRingHom φ₂).comp (relationCoactionHom hE)) (by
      ext b
      simp only [RingHom.comp_apply, relationCoactionHom_source]
      have hb : φ₁ (algebraMap B C b) = φ₂ (t b) :=
        congrArg (fun q : B →+* T => q b) h
      simp [specializeRingHom, hb])

private lemma composeRelationRingHom_eq (hE : RingEtaleEquivalenceRelation t)
    {T : Type u} [CommRing T] [Algebra B T]
    (φ₁ : C →+* T) (φ₂ : C →ₐ[B] T)
    (h : φ₁.comp (algebraMap B C) = (φ₂ : C →+* T).comp t)
    (x : C ⊗[B] C) :
    composeRelationRingHom hE φ₁ φ₂ h x =
      coactionCompose t C (relationCoactionHom hE).toAddMonoidHom
        (relationCoactionHom_smul hE) φ₁ φ₂ h x := by
  induction x with
  | tmul c d =>
    rw [coactionCompose_tmul]
    change (φ₁ c ⊗ₜ (1 : C)) * specializeRingHom φ₂ (relationCoactionHom hE d) =
      φ₁ c • LinearMap.rTensor C φ₂.toLinearMap (relationCoactionHom hE d)
    rw [specializeRingHom_eq]
    simp [Algebra.smul_def]
  | add x y hx hy => simp [hx, hy]

/-- Functions on the relation ring, with its original source-module structure. -/
noncomputable def relation (hE : RingEtaleEquivalenceRelation t) : GroupoidCoaction t C where
  coaction := (relationCoactionHom hE).toAddMonoidHom
  map_smul := relationCoactionHom_smul hE
  counit T _ _ φ hφ c := by
    have heq : (specializeRingHom φ).comp (relationCoactionHom hE) =
        (Algebra.TensorProduct.includeRight : C →ₐ[B] T ⊗[B] C).toRingHom := by
      apply hE.hom_ext
      · ext b
        simp [specializeRingHom]
      · ext b
        change specializeRingHom φ (relationCoactionHom hE (algebraMap B C b)) =
          (1 : T) ⊗ₜ algebraMap B C b
        rw [relationCoactionHom_source]
        have hb : φ (t b) = algebraMap B T b :=
          congrArg (fun q : B →+* T => q b) hφ
        simp [specializeRingHom, hb, Algebra.algebraMap_eq_smul_one, tmul_smul, smul_tmul']
    have hc := congrArg (fun q : C →+* T ⊗[B] C => q c) heq
    change specializeRingHom φ (relationCoactionHom hE c) = (1 : T) ⊗ₜ c at hc
    exact (specializeRingHom_eq φ _).symm.trans hc
  coassoc T _ _ φ₁ φ₂ φ₃ h h₃ c := by
    have heq : (specializeRingHom φ₃).comp (relationCoactionHom hE) =
        (composeRelationRingHom hE φ₁ φ₂ h).comp (relationCoactionHom hE) := by
      apply hE.hom_ext
      · ext b
        simp [composeRelationRingHom, tensorRingLift_tmul, specializeRingHom]
      · ext b
        have hb : φ₃ (t b) = φ₁ (t b) :=
          congrArg (fun q : B →+* T => q b) h₃
        simp [composeRelationRingHom, tensorRingLift_tmul, specializeRingHom, hb]
    have hc := congrArg (fun q : C →+* T ⊗[B] C => q c) heq
    change specializeRingHom φ₃ (relationCoactionHom hE c) =
      composeRelationRingHom hE φ₁ φ₂ h (relationCoactionHom hE c) at hc
    exact (specializeRingHom_eq φ₃ _).symm.trans
      (hc.trans (composeRelationRingHom_eq hE φ₁ φ₂ h _))

lemma relationCoactionHom_mul (hE : RingEtaleEquivalenceRelation t) (c : C) :
    Algebra.TensorProduct.lmul' B (relationCoactionHom hE c) = t (hE.identity c) := by
  have heq : (Algebra.TensorProduct.lmul' B).toRingHom.comp (relationCoactionHom hE) =
      t.comp hE.identity.toRingHom := by
    apply hE.hom_ext
    · ext b
      have hb : hE.identity (t b) = b :=
        congrArg (fun q : B →+* B => q b) hE.identity_comp_t
      simp [hb]
    · ext b
      simp
  exact congrArg (fun q : C →+* C => q c) heq

lemma relation_mem_invariants_iff (hE : RingEtaleEquivalenceRelation t) (c : C) :
    c ∈ (relation hE).invariants ↔ c = t (hE.identity c) := by
  constructor
  · intro hc
    change relationCoactionHom hE c = (1 : C) ⊗ₜ c at hc
    have hm := congrArg (Algebra.TensorProduct.lmul' B : C ⊗[B] C →ₐ[B] C) hc
    simpa only [relationCoactionHom_mul, Algebra.TensorProduct.lmul'_apply_tmul, one_mul]
      using hm.symm
  · intro hc
    change relationCoactionHom hE c = (1 : C) ⊗ₜ c
    rw [hc, relationCoactionHom_target]

/-- The target map identifies `B` with the invariants of the relation-ring coaction. -/
noncomputable def relationInvariantMap (hE : RingEtaleEquivalenceRelation t) :
    B →ₗ[invariantRing t] (relation hE).invariantSubmodule where
  toFun b := ⟨t b, relationCoactionHom_target hE b⟩
  map_add' b b' := Subtype.ext (t.map_add b b')
  map_smul' a b := by
    apply Subtype.ext
    change t ((a : B) • b) = (a : B) • t b
    simp only [smul_eq_mul, map_mul, Algebra.smul_def]
    rw [a.property]

@[simp]
lemma relationInvariantMap_coe (hE : RingEtaleEquivalenceRelation t) (b : B) :
    (relationInvariantMap hE b : C) = t b := rfl

lemma relationInvariantMap_bijective (hE : RingEtaleEquivalenceRelation t) :
    Function.Bijective (relationInvariantMap hE) := by
  have ht : Function.Injective t := by
    apply Function.LeftInverse.injective (g := hE.identity)
    intro b
    exact congrArg (fun q : B →+* B => q b) hE.identity_comp_t
  constructor
  · intro b b' h
    exact ht (congrArg Subtype.val h)
  · intro c
    refine ⟨hE.identity c, Subtype.ext ?_⟩
    exact ((relation_mem_invariants_iff hE c).mp c.property).symm

/-- The canonical invariant-module equivalence for the relation ring. -/
noncomputable def relationInvariantEquiv (hE : RingEtaleEquivalenceRelation t) :
    B ≃ₗ[invariantRing t] (relation hE).invariantSubmodule :=
  LinearEquiv.ofBijective (relationInvariantMap hE) (relationInvariantMap_bijective hE)

@[simp]
lemma relationInvariantEquiv_apply (hE : RingEtaleEquivalenceRelation t) (b : B) :
    (relationInvariantEquiv hE b : C) = t b := rfl

@[simp]
lemma relationInvariantEquiv_symm_apply (hE : RingEtaleEquivalenceRelation t)
    (c : (relation hE).invariantSubmodule) :
    (relationInvariantEquiv hE).symm c = hE.identity c := by
  apply (relationInvariantEquiv hE).injective
  apply Subtype.ext
  change ((relationInvariantEquiv hE) ((relationInvariantEquiv hE).symm c) : C) =
    t (hE.identity c)
  rw [LinearEquiv.apply_symm_apply]
  exact (relation_mem_invariants_iff hE c).mp c.property

end Langlands.AlgebraicGeometry.GroupoidCoaction
