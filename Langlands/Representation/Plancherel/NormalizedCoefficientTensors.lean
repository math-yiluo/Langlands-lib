import Langlands.Representation.Plancherel.CoefficientTensors
import Langlands.Representation.Aubert.General.InductionCarrierTransport
import Langlands.Representation.Smooth.Schur.Proof

/-!
# Normalized induced coefficient tensors and choice independence

The tensor side of Waldspurger V.1, specialized to the existing actual
Haar-normalized induction. Schur's lemma is applied to the inducing
representation to prove the representative transport in VI.1 independent of
the chosen equivalence.
-/

noncomputable section

open scoped TensorProduct

namespace Langlands.Plancherel

universe uR uG uV uW uX

section ScalarCancellation

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G]
  {A : SmoothRep.{uR, uG, uV} R G} {B : SmoothRep.{uR, uG, uW} R G}

/-- A scalar change of the vector equivalence cancels its inverse pullback
on the smooth dual. The statement needs no separate nonzero-scalar premise. -/
theorem coefficientTensorCongr_eq_of_scalar
    (e f : A.representation.Equiv B.representation) (c : R)
    (hc : ∀ v, f v = c • e v) :
    coefficientTensorCongr f = coefficientTensorCongr e := by
  have hinv (w : B) : c • f.symm w = e.symm w := by
    apply e.injective
    calc
      e (c • f.symm w) = c • e (f.symm w) := map_smul e c _
      _ = f (f.symm w) := (hc (f.symm w)).symm
      _ = w := f.apply_symm_apply w
      _ = e (e.symm w) := (e.apply_symm_apply w).symm
  have hdual (ℓ : SmoothDual A.representation) :
      c • contragredientMap f.symm.toIntertwiningMap ℓ =
        contragredientMap e.symm.toIntertwiningMap ℓ := by
    apply Subtype.ext
    apply LinearMap.ext
    intro w
    change c • ℓ.val (f.symm w) = ℓ.val (e.symm w)
    rw [← map_smul, hinv]
  apply LinearEquiv.ext
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul v ℓ =>
    simp only [coefficientTensorCongr_tmul, hc v]
    rw [TensorProduct.smul_tmul, hdual]
  | add t s ht hs => simp only [map_add, ht, hs]

end ScalarCancellation

section AdmissibleChoice

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {A : SmoothRep.{0, uG, uV} ℂ G} {B : SmoothRep.{0, uG, uW} ℂ G}

/-- Equivalences out of an irreducible admissible complex representation differ
by a scalar, by Schur applied on their common source. -/
theorem admissibleEquiv_exists_scalar (hA : IsAdmissible A.representation)
    (hi : A.representation.IsIrreducible)
    (e f : A.representation.Equiv B.representation) :
    ∃ c : ℂ, ∀ v, f v = c • e v := by
  obtain ⟨c, hc, _⟩ := admissibleSchur_scalarEndomorphism A.representation hA hi
    (e.symm.toIntertwiningMap.comp f.toIntertwiningMap)
  refine ⟨c, ?_⟩
  intro v
  have hv : e.symm (f v) = c • v :=
    congrArg (fun T : A.representation.IntertwiningMap A.representation => T v) hc
  have he := congrArg e hv
  simpa only [e.apply_symm_apply, map_smul] using he

variable [IsTopologicalGroup G]

/-- The coefficient tensor transport itself is independent of the equivalence
when its source representation is irreducible admissible. -/
theorem coefficientTensorCongr_eq_of_admissible
    (hA : IsAdmissible A.representation) (hi : A.representation.IsIrreducible)
    (e f : A.representation.Equiv B.representation) :
    coefficientTensorCongr e = coefficientTensorCongr f := by
  obtain ⟨c, hc⟩ := admissibleEquiv_exists_scalar hA hi e f
  exact (coefficientTensorCongr_eq_of_scalar e f c hc).symm

end AdmissibleChoice

section NormalizedInduction

open Aubert.General

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G}

/-- The tensor of actual Haar-normalized induction with its actual smooth dual. -/
abbrev NormalizedCoefficientTensor (h : IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set G)) (A : SmoothRep.{0, uG, uV} ℂ M) :=
  CoefficientTensor ((normalizedInductionFunctor h hU).obj A)

/-- The coefficient map on the tensor side of normalized induction. -/
def normalizedCoefficientMap (h : IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set G)) (A : SmoothRep.{0, uG, uV} ℂ M) :
    NormalizedCoefficientTensor h hU A →ₗ[ℂ] LocallyConstant G ℂ :=
  coefficientTensorMap ((normalizedInductionFunctor h hU).obj A)

@[simp]
theorem normalizedCoefficientMap_tmul (h : IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set G)) (A : SmoothRep.{0, uG, uV} ℂ M)
    (v : (normalizedInductionFunctor h hU).obj A)
    (ℓ : SmoothDual ((normalizedInductionFunctor h hU).obj A).representation) (g : G) :
    normalizedCoefficientMap h hU A (v ⊗ₜ[ℂ] ℓ) g =
      ℓ.val (((normalizedInductionFunctor h hU).obj A).representation g v) := rfl

/-- Every actual normalized induced tensor coefficient is bi-invariant under
one open subgroup. -/
theorem normalizedCoefficientMap_biInvariant (h : IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set G)) (A : SmoothRep.{0, uG, uV} ℂ M)
    (t : NormalizedCoefficientTensor h hU A) :
    ∃ K : OpenSubgroup G, ∀ (k l : K) (g : G),
      normalizedCoefficientMap h hU A t ((k : G) * g * (l : G)) =
        normalizedCoefficientMap h hU A t g :=
  coefficientTensorMap_biInvariant _ t

variable {A : SmoothRep.{0, uG, uV} ℂ M} {B : SmoothRep.{0, uG, uW} ℂ M}
  {C : SmoothRep.{0, uG, uX} ℂ M}

/-- Transport the inducing equivalence pointwise through actual normalized
induction, then take its tensor with inverse smooth-dual pullback. -/
def normalizedCoefficientTransport (h : IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set G)) (e : A.representation.Equiv B.representation) :
    NormalizedCoefficientTensor h hU A ≃ₗ[ℂ] NormalizedCoefficientTensor h hU B :=
  coefficientTensorCongr (normalizedInductionEquivOfEquiv h hU e)

@[simp]
theorem normalizedCoefficientTransport_tmul (h : IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set G)) (e : A.representation.Equiv B.representation)
    (v : (normalizedInductionFunctor h hU).obj A)
    (ℓ : SmoothDual ((normalizedInductionFunctor h hU).obj A).representation) :
    normalizedCoefficientTransport h hU e (v ⊗ₜ[ℂ] ℓ) =
      normalizedInductionEquivOfEquiv h hU e v ⊗ₜ[ℂ]
        contragredientMap (normalizedInductionEquivOfEquiv h hU e).symm.toIntertwiningMap ℓ :=
  rfl

/-- Transport preserves the actual locally constant coefficient function. -/
theorem normalizedCoefficientMap_transport (h : IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set G)) (e : A.representation.Equiv B.representation)
    (t : NormalizedCoefficientTensor h hU A) :
    normalizedCoefficientMap h hU B (normalizedCoefficientTransport h hU e t) =
      normalizedCoefficientMap h hU A t :=
  coefficientTensorMap_congr (normalizedInductionEquivOfEquiv h hU e) t

/-- Tensor transport intertwines the external product-group actions. -/
theorem normalizedCoefficientTransport_action (h : IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set G)) (e : A.representation.Equiv B.representation)
    (x : G × G) (t : NormalizedCoefficientTensor h hU A) :
    normalizedCoefficientTransport h hU e
        (coefficientTensorAction ((normalizedInductionFunctor h hU).obj A) x t) =
      coefficientTensorAction ((normalizedInductionFunctor h hU).obj B) x
        (normalizedCoefficientTransport h hU e t) :=
  coefficientTensorCongr_action (normalizedInductionEquivOfEquiv h hU e) x t

/-- The pointwise normalized induction comparison preserves scalar relations
between equivalences of inducing representations. -/
theorem normalizedInductionEquivOfEquiv_scalar (h : IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set G)) (e f : A.representation.Equiv B.representation)
    (c : ℂ) (hc : ∀ v, f v = c • e v)
    (v : (normalizedInductionFunctor h hU).obj A) :
    normalizedInductionEquivOfEquiv h hU f v =
      c • normalizedInductionEquivOfEquiv h hU e v := by
  apply Subtype.ext
  apply Subtype.ext
  funext g
  exact hc (Induction.eval P (inducingRepresentation h hU A) v g)

/-- Schur is used on the inducing Levi representation. No irreducibility of
the normalized induced representation is assumed. -/
theorem normalizedCoefficientTransport_independent
    (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
    (hA : IsAdmissible A.representation) (hi : A.representation.IsIrreducible)
    (e f : A.representation.Equiv B.representation) :
    normalizedCoefficientTransport h hU e = normalizedCoefficientTransport h hU f := by
  obtain ⟨c, hc⟩ := admissibleEquiv_exists_scalar hA hi e f
  exact (coefficientTensorCongr_eq_of_scalar
    (normalizedInductionEquivOfEquiv h hU e)
    (normalizedInductionEquivOfEquiv h hU f) c
    (normalizedInductionEquivOfEquiv_scalar h hU e f c hc)).symm

@[simp]
theorem normalizedCoefficientTransport_refl (h : IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set G)) (t : NormalizedCoefficientTensor h hU A) :
    normalizedCoefficientTransport h hU
      (Representation.Equiv.refl A.representation) t = t := by
  have he : normalizedInductionEquivOfEquiv h hU
      (Representation.Equiv.refl A.representation) =
        Representation.Equiv.refl
          ((normalizedInductionFunctor h hU).obj A).representation := by
    apply Representation.Equiv.ext
    funext v
    rfl
  simp only [normalizedCoefficientTransport, he, coefficientTensorCongr_refl]

/-- Successive inducing equivalences give the composite tensor transport. -/
theorem normalizedCoefficientTransport_trans (h : IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set G)) (e : A.representation.Equiv B.representation)
    (f : B.representation.Equiv C.representation) (t : NormalizedCoefficientTensor h hU A) :
    normalizedCoefficientTransport h hU (e.trans f) t =
      normalizedCoefficientTransport h hU f (normalizedCoefficientTransport h hU e t) := by
  have he : normalizedInductionEquivOfEquiv h hU (e.trans f) =
      (normalizedInductionEquivOfEquiv h hU e).trans
        (normalizedInductionEquivOfEquiv h hU f) := by
    apply Representation.Equiv.ext
    funext v
    rfl
  simp only [normalizedCoefficientTransport, he, coefficientTensorCongr_trans]

end NormalizedInduction

end Langlands.Plancherel
