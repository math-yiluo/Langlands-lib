import Langlands.Representation.Tensor.FiniteEquivalences
import Mathlib.Data.Fintype.EquivFin

/-! Dependent reindexing and finite outer regrouping of external tensor representations. -/

noncomputable section

open scoped TensorProduct

namespace Langlands.FiniteTensor

universe uR uI uJ uK uG uV

section Coordinates
variable {I : Type uI} {J : Type uJ} (H : I → Type uG) [∀ i, Group (H i)]

/-- Reindex the dependent product group by precomposition. -/
def reindexGroup (e : J ≃ I) : (∀ i, H i) ≃* (∀ j, H (e j)) where
  toEquiv := (Equiv.piCongrLeft H e).symm
  map_mul' _ _ := rfl

@[simp] theorem reindexGroup_apply (e : J ≃ I) (g : ∀ i, H i) (j : J) :
    reindexGroup H e g j = g (e j) := rfl

@[simp] theorem reindexGroup_symm_apply_image (e : J ≃ I)
    (g : ∀ j, H (e j)) (j : J) :
    (reindexGroup H e).symm g (e j) = g j :=
  Equiv.piCongrLeft_apply_apply H e g j

theorem reindexGroup_symm_apply (e : J ≃ I) (g : ∀ j, H (e j)) (i : I) :
    (reindexGroup H e).symm g i = e.apply_symm_apply i ▸ g (e.symm i) := rfl

/-- Dependent product coordinates grouped into fibers. -/
def regroupGroup {K : J → Type uK} (e : Sigma K ≃ I) :
    (∀ i, H i) ≃* (∀ j, ∀ k : K j, H (e ⟨j, k⟩)) where
  toEquiv := (reindexGroup H e).toEquiv.trans (Equiv.piCurry (fun j k => H (e ⟨j,k⟩)))
  map_mul' _ _ := rfl

@[simp] theorem regroupGroup_apply {K : J → Type uK} (e : Sigma K ≃ I)
    (g : ∀ i, H i) (j : J) (k : K j) :
    regroupGroup H e g j k = g (e ⟨j,k⟩) := rfl

@[simp] theorem regroupGroup_symm_apply_image {K : J → Type uK} (e : Sigma K ≃ I)
    (g : ∀ j, ∀ k : K j, H (e ⟨j,k⟩)) (j : J) (k : K j) :
    (regroupGroup H e).symm g (e ⟨j,k⟩) = g j k :=
  reindexGroup_symm_apply_image H e (fun p => g p.1 p.2) ⟨j,k⟩

theorem regroupGroup_symm_apply {K : J → Type uK} (e : Sigma K ≃ I)
    (g : ∀ j, ∀ k : K j, H (e ⟨j,k⟩)) (i : I) :
    (regroupGroup H e).symm g i =
      e.apply_symm_apply i ▸ g (e.symm i).1 (e.symm i).2 := rfl

variable [∀ i, TopologicalSpace (H i)]

/-- Reindexing for the ordinary product topologies, with no continuity assumptions on multiplication. -/
def reindexGroupContinuous (e : J ≃ I) : (∀ i, H i) ≃ₜ* (∀ j, H (e j)) where
  toMulEquiv := reindexGroup H e
  continuous_toFun := (Homeomorph.piCongrLeft e).symm.continuous_toFun
  continuous_invFun := (Homeomorph.piCongrLeft e).continuous_toFun

/-- Nested product coordinates for the ordinary product topologies. -/
def regroupGroupContinuous {K : J → Type uK} (e : Sigma K ≃ I) :
    (∀ i, H i) ≃ₜ* (∀ j, ∀ k : K j, H (e ⟨j,k⟩)) where
  toMulEquiv := regroupGroup H e
  continuous_toFun := continuous_pi (fun j => continuous_pi (fun k => continuous_apply _))
  continuous_invFun := by
    apply (reindexGroupContinuous H e).continuous_invFun.comp
    exact continuous_pi (fun p => (continuous_apply p.2).comp (continuous_apply p.1))

@[simp] theorem reindexGroupContinuous_toMulEquiv (e : J ≃ I) :
    (reindexGroupContinuous H e).toMulEquiv = reindexGroup H e := rfl

@[simp] theorem regroupGroupContinuous_toMulEquiv {K : J → Type uK} (e : Sigma K ≃ I) :
    (regroupGroupContinuous H e).toMulEquiv = regroupGroup H e := rfl
end Coordinates

section FinAssociator
variable (R : Type uR) [CommRing R]

private abbrev sigmaFinSucc {n : ℕ} (K : Fin (n+1) → Type uK) :
    K 0 ⊕ (Sigma (fun j : Fin n => K j.succ)) ≃ Sigma K where
  toFun := Sum.elim (fun k => ⟨0,k⟩) (fun p => ⟨p.1.succ,p.2⟩)
  invFun p := Fin.cases (fun k => Sum.inl k) (fun j k => Sum.inr ⟨j,k⟩) p.1 p.2
  left_inv := by rintro (k | ⟨j,k⟩) <;> rfl
  right_inv := by rintro ⟨j,k⟩; revert k; refine Fin.cases ?_ (fun j => ?_) j <;> intro k <;> rfl

set_option backward.isDefEq.respectTransparency false in
private theorem finRegroup_exists (n : ℕ) :
    ∀ (K : Fin n → Type uK) (V : Sigma K → Type uV)
      [∀ p, AddCommGroup (V p)] [∀ p, Module R (V p)],
    ∃ E : PiTensorProduct R V ≃ₗ[R]
        PiTensorProduct R (fun j => PiTensorProduct R (fun k : K j => V ⟨j,k⟩)),
      ∀ v, E (PiTensorProduct.tprod R v) =
        PiTensorProduct.tprod R (fun j => PiTensorProduct.tprod R (fun k => v ⟨j,k⟩)) := by
  intro K V _ _
  induction n with
  | zero =>
    refine ⟨(PiTensorProduct.isEmptyEquiv (R := R) (s := V) (Sigma K)).trans
      (PiTensorProduct.isEmptyEquiv (R := R)
        (s := fun j => PiTensorProduct R (fun k : K j => V ⟨j,k⟩)) (Fin 0)).symm, ?_⟩
    intro v
    apply (PiTensorProduct.isEmptyEquiv (R := R)
      (s := fun j => PiTensorProduct R (fun k : K j => V ⟨j,k⟩)) (Fin 0)).injective
    simp
  | succ n ih =>
    obtain ⟨E, hE⟩ := ih (fun j => K j.succ) (fun p => V ⟨p.1.succ,p.2⟩)
    let s := sigmaFinSucc K
    let F := ((PiTensorProduct.reindex R V s.symm).trans
      (PiTensorProduct.tmulEquivDep R (fun p => V (s p))).symm).trans
      (TensorProduct.congr (LinearEquiv.refl R _) E)
    refine ⟨F.trans (headTailLinearEquiv R
      (fun j => PiTensorProduct R (fun k : K j => V ⟨j,k⟩))).symm, ?_⟩
    intro v
    apply (headTailLinearEquiv R
      (fun j => PiTensorProduct R (fun k : K j => V ⟨j,k⟩))).injective
    change (headTailLinearEquiv R
      (fun j => PiTensorProduct R (fun k : K j => V ⟨j,k⟩)))
      ((headTailLinearEquiv R
        (fun j => PiTensorProduct R (fun k : K j => V ⟨j,k⟩))).symm
          (F (PiTensorProduct.tprod R v))) = _
    rw [LinearEquiv.apply_symm_apply, headTailLinearEquiv_tprod]
    dsimp only [F, LinearEquiv.trans_apply]
    rw [PiTensorProduct.reindex_tprod]
    have ht := PiTensorProduct.tmulEquivDep_symm_apply R (fun p => V (s p))
      (fun p => v (s p))
    refine (congrArg (TensorProduct.congr (LinearEquiv.refl R _) E) ht).trans ?_
    change (TensorProduct.congr (LinearEquiv.refl R _) E)
      (PiTensorProduct.tprod R (fun k => v ⟨0,k⟩) ⊗ₜ[R]
        PiTensorProduct.tprod R (fun p => v ⟨p.1.succ,p.2⟩)) = _
    rw [TensorProduct.congr_tmul, LinearEquiv.refl_apply, hE]

end FinAssociator

section Linear
variable (R : Type uR) [CommRing R]
variable {J : Type uJ} [Finite J] (K : J → Type uK)
variable (W : Sigma K → Type uV) [∀ p, AddCommGroup (W p)] [∀ p, Module R (W p)]

set_option backward.isDefEq.respectTransparency false in
private theorem sigmaRegroup_exists :
    ∃ E : PiTensorProduct R W ≃ₗ[R]
        PiTensorProduct R (fun j => PiTensorProduct R (fun k : K j => W ⟨j,k⟩)),
      ∀ v, E (PiTensorProduct.tprod R v) =
        PiTensorProduct.tprod R (fun j => PiTensorProduct.tprod R (fun k => v ⟨j,k⟩)) := by
  let := Fintype.ofFinite J
  let f := Fintype.equivFin J
  let s := Equiv.sigmaCongrLeft (β := K) f.symm
  let M := fun j => PiTensorProduct R (fun k : K j => W ⟨j,k⟩)
  obtain ⟨E, hE⟩ := finRegroup_exists R (Fintype.card J)
    (fun j => K (f.symm j)) (fun p => W (s p))
  refine ⟨((PiTensorProduct.reindex R W s.symm).trans E).trans
    (PiTensorProduct.reindex R M f).symm, ?_⟩
  intro v
  apply (PiTensorProduct.reindex R M f).injective
  change (PiTensorProduct.reindex R M f)
    ((PiTensorProduct.reindex R M f).symm
      (E (PiTensorProduct.reindex R W s.symm (PiTensorProduct.tprod R v)))) = _
  rw [LinearEquiv.apply_symm_apply, PiTensorProduct.reindex_tprod]
  exact (hE (fun p => v (s p))).trans
    (PiTensorProduct.reindex_tprod (R := R) (s := M) f
      (fun j => PiTensorProduct.tprod R (fun k => v ⟨j,k⟩))).symm

/-- The dependent Sigma associator, constructed by finite outer induction. -/
def sigmaRegroupLinearEquiv :
    PiTensorProduct R W ≃ₗ[R]
      PiTensorProduct R (fun j => PiTensorProduct R (fun k : K j => W ⟨j,k⟩)) :=
  Classical.choose (sigmaRegroup_exists R K W)

@[simp] theorem sigmaRegroupLinearEquiv_tprod (v : ∀ p, W p) :
    sigmaRegroupLinearEquiv R K W (PiTensorProduct.tprod R v) =
      PiTensorProduct.tprod R (fun j => PiTensorProduct.tprod R (fun k => v ⟨j,k⟩)) :=
  Classical.choose_spec (sigmaRegroup_exists R K W) v

@[simp] theorem sigmaRegroupLinearEquiv_symm_tprod (v : ∀ p, W p) :
    (sigmaRegroupLinearEquiv R K W).symm
      (PiTensorProduct.tprod R (fun j => PiTensorProduct.tprod R (fun k => v ⟨j,k⟩))) =
        PiTensorProduct.tprod R v := by
  rw [← sigmaRegroupLinearEquiv_tprod, LinearEquiv.symm_apply_apply]
end Linear

section RegroupLinear
variable (R : Type uR) [CommRing R] {I : Type uI} {J : Type uJ}
variable (V : I → Type uV) [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
variable [Finite J] {K : J → Type uK}

/-- Reindex by a dependent partition and group the fibers into nested tensors. -/
def regroupLinearEquiv (e : Sigma K ≃ I) :
    PiTensorProduct R V ≃ₗ[R]
      PiTensorProduct R (fun j => PiTensorProduct R (fun k : K j => V (e ⟨j,k⟩))) :=
  (PiTensorProduct.reindex R V e.symm).trans
    (sigmaRegroupLinearEquiv R K (fun p => V (e p)))

@[simp] theorem regroupLinearEquiv_tprod (e : Sigma K ≃ I) (v : ∀ i, V i) :
    regroupLinearEquiv R V e (PiTensorProduct.tprod R v) =
      PiTensorProduct.tprod R (fun j => PiTensorProduct.tprod R (fun k => v (e ⟨j,k⟩))) := by
  simp [regroupLinearEquiv]

@[simp] theorem regroupLinearEquiv_symm_tprod (e : Sigma K ≃ I) (v : ∀ i, V i) :
    (regroupLinearEquiv R V e).symm
      (PiTensorProduct.tprod R (fun j => PiTensorProduct.tprod R (fun k => v (e ⟨j,k⟩)))) =
        PiTensorProduct.tprod R v := by
  rw [← regroupLinearEquiv_tprod, LinearEquiv.symm_apply_apply]
end RegroupLinear

section Actions
variable {R : Type uR} [CommRing R] {I : Type uI} {J : Type uJ}
variable {H : I → Type uG} [∀ i, Group (H i)]
variable {V : I → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]

/-- Actual reindexing of an external action, with inverse coordinate pullback. -/
def reindexEquiv (e : J ≃ I) (ρ : ∀ i, Representation R (H i) (V i)) :
    Representation.Equiv ((external ρ).comp (reindexGroup H e).symm.toMonoidHom)
      (external (fun j => ρ (e j))) :=
  Representation.Equiv.mk (PiTensorProduct.reindex R V e.symm) (fun g => by
    ext v
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      external_tprod, PiTensorProduct.reindex_tprod, Equiv.symm_symm,
      reindexGroup_symm_apply_image])

@[simp] theorem reindexEquiv_toLinearEquiv (e : J ≃ I)
    (ρ : ∀ i, Representation R (H i) (V i)) :
    (reindexEquiv e ρ).toLinearEquiv = PiTensorProduct.reindex R V e.symm := rfl

@[simp] theorem reindexEquiv_tprod (e : J ≃ I)
    (ρ : ∀ i, Representation R (H i) (V i)) (v : ∀ i, V i) :
    reindexEquiv e ρ (PiTensorProduct.tprod R v) =
      PiTensorProduct.tprod R (fun j => v (e j)) :=
  PiTensorProduct.reindex_tprod e.symm v

@[simp] theorem reindexEquiv_symm_tprod (e : J ≃ I)
    (ρ : ∀ i, Representation R (H i) (V i)) (v : ∀ i, V i) :
    (reindexEquiv e ρ).symm (PiTensorProduct.tprod R (fun j => v (e j))) =
      PiTensorProduct.tprod R v := by
  rw [← reindexEquiv_tprod e ρ, Representation.Equiv.symm_apply_apply]

theorem reindexEquiv_apply_action (e : J ≃ I)
    (ρ : ∀ i, Representation R (H i) (V i)) (g : ∀ j, H (e j)) (x : PiTensorProduct R V) :
    reindexEquiv e ρ (external ρ ((reindexGroup H e).symm g) x) =
      external (fun j => ρ (e j)) g (reindexEquiv e ρ x) :=
  DFunLike.congr_fun ((reindexEquiv e ρ).isIntertwining' g) x

variable [Finite J] {K : J → Type uK}

/-- Actual nested regrouping of external representations. -/
def regroupEquiv (e : Sigma K ≃ I) (ρ : ∀ i, Representation R (H i) (V i)) :
    Representation.Equiv ((external ρ).comp (regroupGroup H e).symm.toMonoidHom)
      (external (fun j => external (fun k : K j => ρ (e ⟨j,k⟩)))) :=
  Representation.Equiv.mk (regroupLinearEquiv R V e) (fun g => by
    ext v
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      external_tprod, regroupLinearEquiv_tprod, regroupGroup_symm_apply_image])

@[simp] theorem regroupEquiv_toLinearEquiv (e : Sigma K ≃ I)
    (ρ : ∀ i, Representation R (H i) (V i)) :
    (regroupEquiv e ρ).toLinearEquiv = regroupLinearEquiv R V e := rfl

@[simp] theorem regroupEquiv_tprod (e : Sigma K ≃ I)
    (ρ : ∀ i, Representation R (H i) (V i)) (v : ∀ i, V i) :
    regroupEquiv e ρ (PiTensorProduct.tprod R v) =
      PiTensorProduct.tprod R (fun j => PiTensorProduct.tprod R (fun k => v (e ⟨j,k⟩))) :=
  regroupLinearEquiv_tprod R V e v

@[simp] theorem regroupEquiv_symm_tprod (e : Sigma K ≃ I)
    (ρ : ∀ i, Representation R (H i) (V i)) (v : ∀ i, V i) :
    (regroupEquiv e ρ).symm
      (PiTensorProduct.tprod R (fun j => PiTensorProduct.tprod R (fun k => v (e ⟨j,k⟩)))) =
        PiTensorProduct.tprod R v :=
  regroupLinearEquiv_symm_tprod R V e v

/-- Intertwining on every tensor, with the actual nested action. -/
theorem regroupEquiv_apply_action (e : Sigma K ≃ I)
    (ρ : ∀ i, Representation R (H i) (V i))
    (g : ∀ j, ∀ k : K j, H (e ⟨j,k⟩)) (x : PiTensorProduct R V) :
    regroupEquiv e ρ (external ρ ((regroupGroup H e).symm g) x) =
      external (fun j => external (fun k : K j => ρ (e ⟨j,k⟩))) g (regroupEquiv e ρ x) :=
  DFunLike.congr_fun ((regroupEquiv e ρ).isIntertwining' g) x
end Actions

end Langlands.FiniteTensor
