import Langlands.Representation.Jacquet.ReciprocityStatement

/-! # Character-twisted reciprocity through actual coinvariants -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Jacquet

universe uG uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} {W : Type uW}
variable [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

namespace CharacterReciprocity

variable (P N : Subgroup G) (hNP : N ≤ P) (hPN : P ≤ Subgroup.normalizer N)
variable (rho : Representation ℂ G V) (sigma : Representation ℂ P W)
variable (chi : Induction.SmoothCharacter ℂ P)

/-- Evaluation at identity, before descending to coinvariants. -/
def evaluation
    (F : rho.IntertwiningMap (Induction.normalizedSmoothInduced P chi sigma)) : V →ₗ[ℂ] W where
  toFun v := Induction.eval P (twist chi.toMonoidHom sigma) (F v) 1
  map_add' v w := by
    change ((F (v + w)).1.1) 1 = _
    rw [map_add]
    rfl
  map_smul' c v := by
    change ((F (c • v)).1.1) 1 = _
    rw [map_smul]
    rfl

/-- Equivariance identifies evaluation of a translate with evaluation at that point. -/
theorem evaluation_translate
    (F : rho.IntertwiningMap (Induction.normalizedSmoothInduced P chi sigma))
    (g : G) (v : V) :
    evaluation P rho sigma chi F (rho g v) =
      Induction.eval P (twist chi.toMonoidHom sigma) (F v) g := by
  have h := Representation.IntertwiningMap.isIntertwining _ _ F g v
  have hh := congrArg (fun f => Induction.eval P (twist chi.toMonoidHom sigma) f 1) h
  change (F (rho g v)).1.1 1 = (F v).1.1 (1 * g) at hh
  change (F (rho g v)).1.1 1 = (F v).1.1 g
  simpa only [one_mul] using hh

/-- Covariance gives the character factor on the evaluated map. -/
theorem evaluation_covariance
    (F : rho.IntertwiningMap (Induction.normalizedSmoothInduced P chi sigma))
    (p : P) (v : V) :
    evaluation P rho sigma chi F (rho p v) =
      (chi.toMonoidHom p : ℂ) • sigma p (evaluation P rho sigma chi F v) := by
  rw [evaluation_translate]
  have h := (F v).1.property p 1
  change (F v).1.1 ((p : G) * 1) =
    (chi.toMonoidHom p : ℂ) • sigma p ((F v).1.1 1) at h
  change (F v).1.1 p = (chi.toMonoidHom p : ℂ) • sigma p ((F v).1.1 1)
  simpa only [mul_one] using h

variable (hSigmaN : ∀ (n : N) (w : W), sigma ⟨(n : G), hNP n.property⟩ w = w)
variable (hChiN : ∀ n : N, chi.toMonoidHom ⟨(n : G), hNP n.property⟩ = 1)

/-- Evaluation kills the actual subgroup relations. -/
def descendedEvaluation
    (F : rho.IntertwiningMap (Induction.normalizedSmoothInduced P chi sigma)) :
    Coinvariants rho N →ₗ[ℂ] W :=
  lift rho N (evaluation P rho sigma chi F) (by
    intro n
    ext v
    have h := evaluation_covariance P rho sigma chi F ⟨(n : G), hNP n.property⟩ v
    simpa only [hChiN n, Units.val_one, one_smul, hSigmaN n, LinearMap.comp_apply] using h)

/-- Descended evaluation intertwines the inverse character twist with `sigma`. -/
def forward
    (F : rho.IntertwiningMap (Induction.normalizedSmoothInduced P chi sigma)) :
    (twist chi.toMonoidHom⁻¹ (action rho N P hPN)).IntertwiningMap sigma where
  toLinearMap := descendedEvaluation P N (hNP := hNP) rho sigma chi hSigmaN hChiN F
  isIntertwining' p := by
    ext v
    change descendedEvaluation P N (hNP := hNP) rho sigma chi hSigmaN hChiN F
      ((((chi.toMonoidHom p)⁻¹ : ℂˣ) : ℂ) • mk rho N (rho p v)) = _
    rw [map_smul]
    change (((chi.toMonoidHom p)⁻¹ : ℂˣ) : ℂ) •
      evaluation P rho sigma chi F (rho p v) =
        sigma p (evaluation P rho sigma chi F v)
    rw [evaluation_covariance]
    simp [smul_smul]

omit [IsTopologicalGroup G] in
/-- Move the inverse character on the source to the target. -/
theorem untwisted_covariance
    (A : (twist chi.toMonoidHom⁻¹ (action rho N P hPN)).IntertwiningMap sigma)
    (p : P) (q : Coinvariants rho N) :
    A (action rho N P hPN p q) = (chi.toMonoidHom p : ℂ) • sigma p (A q) := by
  have h := Representation.IntertwiningMap.isIntertwining _ _ A p q
  change A ((((chi.toMonoidHom p)⁻¹ : ℂˣ) : ℂ) • action rho N P hPN p q) = _ at h
  rw [map_smul] at h
  have hh := congrArg (fun w : W => (chi.toMonoidHom p : ℂ) • w) h
  simpa [smul_smul] using hh

/-- The orbit-function construction before restricting to smooth vectors. -/
def orbitMap
    (A : (twist chi.toMonoidHom⁻¹ (action rho N P hPN)).IntertwiningMap sigma) :
    rho.IntertwiningMap (Induction.equivariantAction P (twist chi.toMonoidHom sigma)) where
  toLinearMap :=
    { toFun := fun v => ⟨fun g => A (mk rho N (rho g v)), by
        intro p g
        change A (mk rho N (rho ((p : G) * g) v)) =
          (chi.toMonoidHom p : ℂ) • sigma p (A (mk rho N (rho g v)))
        rw [map_mul, Module.End.mul_apply]
        exact untwisted_covariance P N hPN rho sigma chi A p (mk rho N (rho g v))⟩
      map_add' := by intros; ext g; simp
      map_smul' := by intros; ext g; simp }
  isIntertwining' g := by
    ext v x
    change A (mk rho N (rho x (rho g v))) = A (mk rho N (rho (x * g) v))
    rw [map_mul, Module.End.mul_apply]

/-- Smoothness of the source makes the orbit functions uniformly right smooth. -/
def backward (hRho : IsSmooth rho)
    (A : (twist chi.toMonoidHom⁻¹ (action rho N P hPN)).IntertwiningMap sigma) :
    rho.IntertwiningMap (Induction.normalizedSmoothInduced P chi sigma) :=
  smoothLift hRho (orbitMap P N hPN rho sigma chi A)

/-- The concrete character reciprocity equivalence. -/
def equivalence (hRho : IsSmooth rho) :
    (rho.IntertwiningMap (Induction.normalizedSmoothInduced P chi sigma)) ≃ₗ[ℂ]
      ((twist chi.toMonoidHom⁻¹ (action rho N P hPN)).IntertwiningMap sigma) where
  toFun := forward P N (hNP := hNP) hPN rho sigma chi hSigmaN hChiN
  invFun := backward P N hPN rho sigma chi hRho
  left_inv F := by
    ext v g
    change evaluation P rho sigma chi F (rho g v) =
      Induction.eval P (twist chi.toMonoidHom sigma) (F v) g
    exact evaluation_translate P rho sigma chi F g v
  right_inv A := by
    ext v
    change A (mk rho N (rho 1 v)) = A (mk rho N v)
    rw [map_one, Module.End.one_apply]
  map_add' F H := by
    ext v
    rfl
  map_smul' c F := by
    ext v
    rfl

@[simp]
theorem equivalence_mk (hRho : IsSmooth rho)
    (F : rho.IntertwiningMap (Induction.normalizedSmoothInduced P chi sigma)) (v : V) :
    equivalence P N (hNP := hNP) hPN rho sigma chi hSigmaN hChiN hRho F (mk rho N v) =
      Induction.eval P (twist chi.toMonoidHom sigma) (F v) 1 := rfl

end CharacterReciprocity

omit [IsTopologicalGroup G] in
/-- Character-twisted first adjointness, with the exact published hypotheses and evaluation formula. -/
theorem characterReciprocity : CharacterReciprocityStatement (G := G) (V := V) (W := W) := by
  intro _ _ _ P N hNP hPN _ rho sigma chi hRho _ hSigmaN hChiN
  exact ⟨CharacterReciprocity.equivalence P N (hNP := hNP) hPN rho sigma chi hSigmaN hChiN hRho,
    fun F v => rfl⟩

end Langlands.Jacquet
