import Langlands.Group.GL.SingleBlock
import Langlands.Representation.Induction.BlockFactors
import Langlands.Representation.Tensor.FiniteEquivalences
import Langlands.Representation.Smooth.Transfer.PullbackProof

/-! Evaluation equivalences for single-block normalized induction. -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Induction

universe uR uG uV

variable {R : Type uR} {G : Type uG} {V : Type uV}
variable [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [AddCommGroup V] [Module R V]

/-- Evaluation for a full subgroup, with the inducing action identified on its elements. -/
def smoothInducedTopEquiv (P : Subgroup G) (hP : P = ⊤)
    (σ : Representation R P V) (ρ : Representation R G V)
    (hσ : ∀ p : P, σ p = ρ (p : G)) (hρ : IsSmooth ρ) :
    (smoothInduced P σ).Equiv ρ where
  toFun f := eval P σ f 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun v := smoothFunctionOf P σ (fun g => ρ g v)
    (by intro p x; rw [hσ, map_mul]; rfl)
    (hρ v).choose (by
      intro k x
      rw [map_mul]
      change ρ x (ρ (k : G) v) = ρ x v
      exact congrArg (ρ x) ((hρ v).choose_spec k))
  left_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    funext g
    let p : P := ⟨g, by rw [hP]; trivial⟩
    have h := f.1.2 p 1
    change ρ g (f.1.1 1) = f.1.1 g
    simpa only [hσ, mul_one, p, Subgroup.coe_mk, Subgroup.subtype_apply] using h.symm
  right_inv v := by
    change ρ 1 v = v
    simp
  isIntertwining' g := by
    ext f
    let p : P := ⟨g, by rw [hP]; trivial⟩
    have h := f.1.2 p 1
    change f.1.1 (1 * g) = ρ g (f.1.1 1)
    simpa only [hσ, mul_one, one_mul, p, Subgroup.coe_mk, Subgroup.subtype_apply] using h

@[simp]
theorem smoothInducedTopEquiv_apply (P : Subgroup G) (hP : P = ⊤)
    (σ : Representation R P V) (ρ : Representation R G V)
    (hσ : ∀ p : P, σ p = ρ (p : G)) (hρ : IsSmooth ρ)
    (f : SmoothFunctions P σ) :
    smoothInducedTopEquiv P hP σ ρ hσ hρ f = eval P σ f 1 := rfl

@[simp]
theorem smoothInducedTopEquiv_symm_eval (P : Subgroup G) (hP : P = ⊤)
    (σ : Representation R P V) (ρ : Representation R G V)
    (hσ : ∀ p : P, σ p = ρ (p : G)) (hρ : IsSmooth ρ) (v : V) (g : G) :
    eval P σ ((smoothInducedTopEquiv P hP σ ρ hσ hρ).symm v) g = ρ g v := rfl

end Langlands.Induction

namespace Langlands.GeneralLinear.BlockShape

universe uF uV

variable {R : Type uF} [CommRing R] {n : ℕ} (B : BlockShape n) (hB : B.length = 1)

/-- The unique inverse Levi coordinate is precisely transport along its full-rank equality. -/
theorem singleBlockLeviEquiv_symm_coordinate (g : GeneralLinear n R) (i : Fin B.length) :
    (B.singleBlockLeviEquiv hB R).symm g i =
      (GeneralLinear.reindex (R := R) (finCongr (B.singleBlock_size hB i))).symm g := by
  apply Units.ext
  ext a b
  change g (B.index i a) (B.index i b) =
    g (finCongr (B.singleBlock_size hB i) a) (finCongr (B.singleBlock_size hB i) b)
  have ha : B.index i a = finCongr (B.singleBlock_size hB i) a := by
    apply Fin.ext
    exact B.singleBlock_index_val hB i a
  have hb : B.index i b = finCongr (B.singleBlock_size hB i) b := by
    apply Fin.ext
    exact B.singleBlock_index_val hB i b
  rw [ha, hb]

/-- The published singleton tensor equivalence, on any chosen index of a one-block shape. -/
def singleBlockTensorEquiv [TopologicalSpace R] {V : Fin B.length → Type uV}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) R) (V i)) (i : Fin B.length) :
    (B.blockTensor σ).Equiv ((σ i).comp (Pi.evalMonoidHom _ i)) := by
  rcases B with ⟨l, s, hp, hs⟩
  dsimp at hB
  subst l
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  let e := FiniteTensor.singletonEquiv σ
  refine Representation.Equiv.mk e.toLinearEquiv ?_
  intro g
  apply LinearMap.ext
  intro v
  let H := fun j : Fin 1 => GeneralLinear (s j) R
  have hg : (FiniteTensor.evalOne H).symm (g 0) = g :=
    (FiniteTensor.evalOneContinuous H).symm_apply_apply g
  have hh := FiniteTensor.singletonEquiv_apply_action σ (g 0) v
  rw [hg] at hh
  exact hh

end Langlands.GeneralLinear.BlockShape

namespace Langlands.PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
variable (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)
variable (hB : B.length = 1)

include hB

/-- The explicit single-block modulus is an empty product of block-pair factors. -/
@[simp] theorem singleBlock_leviModulus (m : B.Levi F.Carrier) :
    T.leviModulus B m = 1 := by
  rw [T.leviModulus_apply]
  apply Finset.prod_eq_one
  intro i _
  apply Finset.prod_eq_one
  intro j hj
  have hij := (Finset.mem_filter.mp hj).2
  have he : i = j := (B.eq_singleBlockIndex hB i).trans
    (B.eq_singleBlockIndex hB j).symm
  exact False.elim ((ne_of_lt hij) he)

@[simp] theorem singleBlock_parabolicModulus (g : B.parabolic F.Carrier) :
    T.parabolicModulus B g = 1 :=
  T.singleBlock_leviModulus B hB _

@[simp] theorem singleBlock_leviHalfModulus (m : B.Levi F.Carrier) :
    T.leviHalfModulus B m = 1 :=
  (T.leviHalfModulus_eq_one B m).mpr (T.singleBlock_leviModulus B hB m)

@[simp] theorem singleBlock_parabolicHalfModulus (g : B.parabolic F.Carrier) :
    T.parabolicHalfModulus B g = 1 :=
  T.singleBlock_leviHalfModulus B hB _

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Evaluation at the identity identifies normalized induction from a single block
with the original Levi action transported to the ambient general linear group. -/
def singleBlockNormalizedInducedEquiv (σ : Representation ℂ (B.Levi F.Carrier) V)
    (hσ : letI := T.leviTopology B; IsSmooth σ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    (T.normalizedParabolicInduced B σ).Equiv
      (σ.comp (B.singleBlockLeviEquiv hB F.Carrier).symm.toMonoidHom) := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  let e := B.singleBlockLeviEquivContinuous hB F.Carrier
  exact Induction.smoothInducedTopEquiv (B.parabolic F.Carrier)
    (B.singleBlock_parabolic_eq_top hB F.Carrier)
    (twist (T.parabolicHalfModulus B) (σ.comp (B.leviProjection F.Carrier)))
    (σ.comp (B.singleBlockLeviEquiv hB F.Carrier).symm.toMonoidHom)
    (by
      intro g
      ext v
      change (T.parabolicHalfModulus B g : ℂ) •
        σ (B.leviProjection F.Carrier g) v = _
      rw [T.singleBlock_parabolicHalfModulus B hB]
      simp only [Units.val_one, one_smul]
      rfl)
    (isSmooth_comp e.symm.toMonoidHom e.symm.continuous hσ)

variable (σ : Representation ℂ (B.Levi F.Carrier) V)
variable (hσ : letI := T.leviTopology B; IsSmooth σ)

@[simp]
theorem singleBlockNormalizedInducedEquiv_apply
    (f : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      Induction.SmoothFunctions (B.parabolic F.Carrier)
        (twist (T.parabolicHalfModulus B) (σ.comp (B.leviProjection F.Carrier)))) :
    T.singleBlockNormalizedInducedEquiv B hB σ hσ f = f.1.1 1 := rfl

@[simp]
theorem singleBlockNormalizedInducedEquiv_symm_eval (v : V)
    (g : GeneralLinear n F.Carrier) :
    (T.singleBlockNormalizedInducedEquiv B hB σ hσ).symm v |>.1.1 g =
      σ ((B.singleBlockLeviEquiv hB F.Carrier).symm g) v := rfl

/-- The forward and inverse constructions recover each induced function. -/
theorem singleBlockNormalizedInducedEquiv_left_inv
    (f : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      Induction.SmoothFunctions (B.parabolic F.Carrier)
        (twist (T.parabolicHalfModulus B) (σ.comp (B.leviProjection F.Carrier)))) :
    (T.singleBlockNormalizedInducedEquiv B hB σ hσ).symm
      (T.singleBlockNormalizedInducedEquiv B hB σ hσ f) = f :=
  (T.singleBlockNormalizedInducedEquiv B hB σ hσ).symm_apply_apply f

/-- Evaluation of the inverse construction recovers the original vector. -/
theorem singleBlockNormalizedInducedEquiv_right_inv (v : V) :
    T.singleBlockNormalizedInducedEquiv B hB σ hσ
      ((T.singleBlockNormalizedInducedEquiv B hB σ hσ).symm v) = v :=
  (T.singleBlockNormalizedInducedEquiv B hB σ hσ).apply_symm_apply v

/-- Right translation becomes the transported Levi action under evaluation. -/
theorem singleBlockNormalizedInducedEquiv_action (g : GeneralLinear n F.Carrier)
    (f : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      Induction.SmoothFunctions (B.parabolic F.Carrier)
        (twist (T.parabolicHalfModulus B) (σ.comp (B.leviProjection F.Carrier)))) :
    T.singleBlockNormalizedInducedEquiv B hB σ hσ
      (T.normalizedParabolicInduced B σ g f) =
        σ ((B.singleBlockLeviEquiv hB F.Carrier).symm g)
          (T.singleBlockNormalizedInducedEquiv B hB σ hσ f) :=
  DFunLike.congr_fun ((T.singleBlockNormalizedInducedEquiv B hB σ hσ).isIntertwining' g) f

section Product

variable {W : Fin B.length → Type uV}
variable [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

/-- A one-block normalized product is its unique factor, after the explicit rank transport. -/
def singleBlockNormalizedProductEquiv
    (τ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (W i))
    (hτ : letI := T.topology; ∀ i, IsSmooth (τ i)) (i : Fin B.length) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    (T.normalizedProductInduced B τ).Equiv
      ((τ i).comp
        (GeneralLinear.reindex (R := F.Carrier) (finCongr (B.singleBlock_size hB i))).symm.toMonoidHom) := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  let e := B.singleBlockTensorEquiv hB τ i
  refine (T.singleBlockNormalizedInducedEquiv B hB (B.blockTensor τ)
    (FiniteTensor.isSmooth_external τ hτ)).trans
    (Representation.Equiv.mk e.toLinearEquiv ?_)
  intro g
  apply LinearMap.ext
  intro v
  have hh := DFunLike.congr_fun
    (e.isIntertwining' ((B.singleBlockLeviEquiv hB F.Carrier).symm g)) v
  change e ((B.blockTensor τ) ((B.singleBlockLeviEquiv hB F.Carrier).symm g) v) =
    τ i ((B.singleBlockLeviEquiv hB F.Carrier).symm g i) (e v) at hh
  rw [B.singleBlockLeviEquiv_symm_coordinate hB g i] at hh
  exact hh

/-- Product evaluation is evaluation at one followed by the existing singleton tensor map. -/
@[simp] theorem singleBlockNormalizedProductEquiv_apply
    (τ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (W i))
    (hτ : letI := T.topology; ∀ i, IsSmooth (τ i)) (i : Fin B.length)
    (f : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      Induction.SmoothFunctions (B.parabolic F.Carrier)
        (twist (T.parabolicHalfModulus B) ((B.blockTensor τ).comp (B.leviProjection F.Carrier)))) :
    letI := T.topology
    T.singleBlockNormalizedProductEquiv B hB τ hτ i f =
      B.singleBlockTensorEquiv hB τ i (f.1.1 1) := rfl

end Product

end Langlands.PadicField.TopologicalData
