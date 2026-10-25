import Langlands.Representation.Induction.BlockFactors
import Langlands.Representation.Induction.OppositeParabolic
import Langlands.Group.GL.ReverseBlocks

/-! Inverse-transpose transport of actual normalized block induction. -/

noncomputable section

open scoped BigOperators NNReal

namespace Langlands.Induction

universe uR uG uV

variable {R : Type uR} {G : Type uG} {V : Type uV}
variable [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [AddCommGroup V] [Module R V]
variable {P Q : Subgroup G} {σ : Representation R P V} {τ : Representation R Q V}

/-- Precomposition by a continuous automorphism, with the actual comap open stabilizer. -/
def precomposeSmoothFunction (θ : G ≃ₜ* G) (e : Q ≃* P)
    (he : ∀ q : Q, (e q : G) = θ q) (hστ : ∀ q : Q, σ (e q) = τ q)
    (f : SmoothFunctions P σ) : SmoothFunctions Q τ :=
  ⟨⟨fun x => eval P σ f (θ x), by
    intro q x
    change eval P σ f (θ ((q : G) * x)) = τ q (eval P σ f (θ x))
    rw [map_mul, ← he q]
    exact (f.1.2 (e q) (θ x)).trans (congrArg (fun A : Module.End R V => A (eval P σ f (θ x))) (hστ q))⟩, by
    obtain ⟨K, hK⟩ := f.property
    refine ⟨K.comap θ.toMonoidHom θ.continuous, ?_⟩
    intro k
    apply Subtype.ext
    funext x
    change eval P σ f (θ (x * (k : G))) = eval P σ f (θ x)
    rw [map_mul]
    exact congrArg (fun φ : EquivariantFunctions P σ => φ.1 (θ x))
      (hK ⟨θ (k : G), k.property⟩)⟩

omit [IsTopologicalGroup G] in
private theorem precompose_symm_subgroup (θ : G ≃ₜ* G) (e : Q ≃* P)
    (he : ∀ q : Q, (e q : G) = θ q) (p : P) :
    (e.symm p : G) = θ.symm p := by
  apply θ.injective
  rw [← he, e.apply_symm_apply, θ.apply_symm_apply]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
private theorem precompose_symm_rep (e : Q ≃* P)
    (hστ : ∀ q : Q, σ (e q) = τ q) (p : P) : τ (e.symm p) = σ p := by
  rw [← hστ, e.apply_symm_apply]

/-- A bicontinuous automorphism transports smooth induction, pulling back the ambient action. -/
def precomposeSmoothInducedEquiv (θ : G ≃ₜ* G) (e : Q ≃* P)
    (he : ∀ q : Q, (e q : G) = θ q) (hστ : ∀ q : Q, σ (e q) = τ q) :
    Representation.Equiv ((smoothInduced P σ).comp θ.toMonoidHom) (smoothInduced Q τ) where
  toFun := precomposeSmoothFunction θ e he hστ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun := precomposeSmoothFunction θ.symm e.symm
    (precompose_symm_subgroup θ e he) (precompose_symm_rep e hστ)
  left_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    change eval P σ f (θ (θ.symm x)) = eval P σ f x
    rw [θ.apply_symm_apply]
  right_inv h := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    change eval Q τ h (θ.symm (θ x)) = eval Q τ h x
    rw [θ.symm_apply_apply]
  isIntertwining' g := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    apply Subtype.ext
    funext x
    change eval P σ f (θ x * θ g) = eval P σ f (θ (x * g))
    rw [map_mul]

@[simp] theorem precomposeSmoothInducedEquiv_eval (θ : G ≃ₜ* G) (e : Q ≃* P)
    (he : ∀ q : Q, (e q : G) = θ q) (hστ : ∀ q : Q, σ (e q) = τ q)
    (f : SmoothFunctions P σ) (x : G) :
    eval Q τ (precomposeSmoothInducedEquiv θ e he hστ f) x = eval P σ f (θ x) := rfl

@[simp] theorem precomposeSmoothInducedEquiv_symm_eval (θ : G ≃ₜ* G) (e : Q ≃* P)
    (he : ∀ q : Q, (e q : G) = θ q) (hστ : ∀ q : Q, σ (e q) = τ q)
    (h : SmoothFunctions Q τ) (x : G) :
    eval P σ ((precomposeSmoothInducedEquiv θ e he hστ).symm h) x =
      eval Q τ h (θ.symm x) := rfl

/-- The forward map transports an entire uniform stabilizer by comap under `θ`. -/
theorem precomposeSmoothInducedEquiv_stabilizer (θ : G ≃ₜ* G) (e : Q ≃* P)
    (he : ∀ q : Q, (e q : G) = θ q) (hστ : ∀ q : Q, σ (e q) = τ q)
    (f : SmoothFunctions P σ) (K : OpenSubgroup G)
    (hK : ∀ (k : K) (x : G), eval P σ f (x * (k : G)) = eval P σ f x)
    (k : K.comap θ.toMonoidHom θ.continuous) (x : G) :
    eval Q τ (precomposeSmoothInducedEquiv θ e he hστ f) (x * (k : G)) =
      eval Q τ (precomposeSmoothInducedEquiv θ e he hστ f) x := by
  change eval P σ f (θ (x * (k : G))) = eval P σ f (θ x)
  rw [map_mul]
  exact hK ⟨θ (k : G), k.property⟩ (θ x)

/-- The inverse map transports an entire uniform stabilizer by comap under `θ.symm`. -/
theorem precomposeSmoothInducedEquiv_symm_stabilizer (θ : G ≃ₜ* G) (e : Q ≃* P)
    (he : ∀ q : Q, (e q : G) = θ q) (hστ : ∀ q : Q, σ (e q) = τ q)
    (h : SmoothFunctions Q τ) (K : OpenSubgroup G)
    (hK : ∀ (k : K) (x : G), eval Q τ h (x * (k : G)) = eval Q τ h x)
    (k : K.comap θ.symm.toMonoidHom θ.symm.continuous) (x : G) :
    eval P σ ((precomposeSmoothInducedEquiv θ e he hστ).symm h) (x * (k : G)) =
      eval P σ ((precomposeSmoothInducedEquiv θ e he hστ).symm h) x := by
  change eval Q τ h (θ.symm (x * (k : G))) = eval Q τ h (θ.symm x)
  rw [map_mul]
  exact hK ⟨θ.symm (k : G), k.property⟩ (θ.symm x)

end Langlands.Induction

namespace Langlands.GeneralLinear.BlockShape

universe uF uV
variable {n : ℕ} (B : BlockShape n) (R : Type uF) [CommRing R]

/-- Inverse transpose identifies the original opposite parabolic with the upper one. -/
def oppositeToUpperInverseTranspose : B.oppositeParabolic R ≃* B.parabolic R where
  toFun q := ⟨inverseTranspose n R q, by
    apply (B.inverseTranspose_mem_oppositeParabolic_iff R _).mp
    simpa only [inverseTranspose_involutive] using q.property⟩
  invFun p := ⟨inverseTranspose n R p,
    (B.inverseTranspose_mem_oppositeParabolic_iff R p).mpr p.property⟩
  left_inv q := Subtype.ext (inverseTranspose_involutive n R q)
  right_inv p := Subtype.ext (inverseTranspose_involutive n R p)
  map_mul' q r := Subtype.ext ((inverseTranspose n R).map_mul q r)

@[simp] theorem oppositeToUpperInverseTranspose_apply (q : B.oppositeParabolic R) :
    (B.oppositeToUpperInverseTranspose R q : GeneralLinear n R) =
      inverseTranspose n R q := rfl

/-- The diagonal projection of inverse transpose is the inverse transpose of each lower block. -/
theorem leviProjection_oppositeToUpperInverseTranspose (q : B.oppositeParabolic R)
    (i : Fin B.length) :
    B.leviProjection R (B.oppositeToUpperInverseTranspose R q) i =
      inverseTranspose (B.size i) R (B.oppositeLeviProjection R q i) := by
  apply Units.ext
  ext a b
  exact congrArg (fun m : B.Levi R => m i b a)
    ((B.oppositeLeviProjection R).map_inv q)

variable {V : Fin B.length → Type uV}
variable [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

/-- Actual indexed tensor actions commute with inverse transpose on the same block family. -/
theorem blockTensor_inverseTranspose
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) R) (V i)) (m : B.Levi R) :
    B.blockTensor σ (fun i => inverseTranspose (B.size i) R (m i)) =
      B.blockTensor (fun i => (σ i).comp (inverseTranspose (B.size i) R).toMonoidHom) m := rfl

/-- Compatibility on the whole tensor carrier, after the actual parabolic projections. -/
theorem blockTensor_leviProjection_inverseTranspose
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) R) (V i))
    (q : B.oppositeParabolic R) :
    B.blockTensor σ (B.leviProjection R (B.oppositeToUpperInverseTranspose R q)) =
      B.blockTensor (fun i => (σ i).comp (inverseTranspose (B.size i) R).toMonoidHom)
        (B.oppositeLeviProjection R q) := by
  rw [← B.blockTensor_inverseTranspose R σ]
  exact congrArg (B.blockTensor σ)
    (funext (B.leviProjection_oppositeToUpperInverseTranspose R q))

end Langlands.GeneralLinear.BlockShape

namespace Langlands.PadicField.TopologicalData

universe uF
variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
variable (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)

/-- Transposition preserves the determinant, so inverse transpose inverts its normalized norm. -/
theorem determinantNorm_inverseTranspose (r : ℕ) (g : GeneralLinear r F.Carrier) :
    T.determinantNorm r (GeneralLinear.inverseTranspose r F.Carrier g) =
      (T.determinantNorm r g)⁻¹ := by
  have hd : GeneralLinear.determinant (GeneralLinear.inverseTranspose r F.Carrier g) =
      (GeneralLinear.determinant g)⁻¹ := by
    rw [← map_inv]
    apply Units.ext
    exact Matrix.det_transpose _
  change T.normalizedAbsUnits _ = _
  rw [hd, map_inv]
  rfl

/-- Each determinant factor in the explicit upper modulus inverts, without changing block order. -/
theorem leviModulus_inverseTranspose (m : B.Levi F.Carrier) :
    T.leviModulus B (fun i => GeneralLinear.inverseTranspose (B.size i) F.Carrier (m i)) =
      (T.leviModulus B m)⁻¹ := by
  classical
  rw [T.leviModulus_apply, T.leviModulus_apply]
  simp only [T.determinantNorm_inverseTranspose, inv_pow, ← Finset.prod_inv_distrib,
    inv_div_inv, inv_div]

/-- The canonical positive square root respects the derived full-modulus inversion. -/
theorem leviHalfModulus_inverseTranspose (m : B.Levi F.Carrier) :
    T.leviHalfModulus B (fun i => GeneralLinear.inverseTranspose (B.size i) F.Carrier (m i)) =
      (T.leviHalfModulus B m)⁻¹ := by
  change (Units.map (Complex.ofRealHom.comp NNReal.toRealHom).toMonoidHom)
    ((Units.map NNReal.sqrtHom.toMonoidHom) (T.leviModulus B _)) = _
  rw [T.leviModulus_inverseTranspose, map_inv, map_inv]
  rfl

/-- The positive upper half modulus under inverse transpose is the opposite half modulus. -/
theorem parabolicHalfModulus_oppositeToUpperInverseTranspose
    (q : B.oppositeParabolic F.Carrier) :
    T.parabolicHalfModulus B (B.oppositeToUpperInverseTranspose F.Carrier q) =
      T.oppositeParabolicHalfModulus B q := by
  rw [parabolicHalfModulus_apply, oppositeParabolicHalfModulus_apply,
    ← T.leviHalfModulus_inverseTranspose]
  exact congrArg (T.leviHalfModulus B)
    (funext (B.leviProjection_oppositeToUpperInverseTranspose F.Carrier q))

universe uV
variable {V : Fin B.length → Type uV}
variable [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

/-- The actual normalized inducing actions agree on inverse-transposed lower elements. -/
theorem inverseTransposeProductInducing
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i))
    (q : B.oppositeParabolic F.Carrier) :
    twist (T.parabolicHalfModulus B) ((B.blockTensor σ).comp (B.leviProjection F.Carrier))
        (B.oppositeToUpperInverseTranspose F.Carrier q) =
      twist (T.oppositeParabolicHalfModulus B)
        ((B.blockTensor (fun i => (σ i).comp
          (GeneralLinear.inverseTranspose (B.size i) F.Carrier).toMonoidHom)).comp
            (B.oppositeLeviProjection F.Carrier)) q := by
  apply LinearMap.ext
  intro v
  change (T.parabolicHalfModulus B (B.oppositeToUpperInverseTranspose F.Carrier q) : ℂ) •
      B.blockTensor σ (B.leviProjection F.Carrier
        (B.oppositeToUpperInverseTranspose F.Carrier q)) v =
    (T.oppositeParabolicHalfModulus B q : ℂ) •
      B.blockTensor (fun i => (σ i).comp
        (GeneralLinear.inverseTranspose (B.size i) F.Carrier).toMonoidHom)
          (B.oppositeLeviProjection F.Carrier q) v
  rw [T.parabolicHalfModulus_oppositeToUpperInverseTranspose,
    B.blockTensor_leviProjection_inverseTranspose]

/-- Precomposition by inverse transpose transports normalized upper block induction
with pulled-back ambient action to normalized opposite induction of the pulled-back factors. -/
def inverseTransposeProductToOppositeEquiv
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Representation.Equiv
      ((T.normalizedProductInduced B σ).comp
        (GeneralLinear.inverseTranspose n F.Carrier).toMonoidHom)
      (T.normalizedOppositeParabolicInduced B
        (B.blockTensor (fun i => (σ i).comp
          (GeneralLinear.inverseTranspose (B.size i) F.Carrier).toMonoidHom))) := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  exact Induction.precomposeSmoothInducedEquiv
    (GeneralLinear.inverseTransposeContinuous n F.Carrier)
    (B.oppositeToUpperInverseTranspose F.Carrier) (fun _ => rfl)
    (T.inverseTransposeProductInducing B σ)

@[simp] theorem inverseTransposeProductToOppositeEquiv_eval
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i))
    (f : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      Induction.SmoothFunctions (B.parabolic F.Carrier)
        (twist (T.parabolicHalfModulus B)
          ((B.blockTensor σ).comp (B.leviProjection F.Carrier))))
    (x : GeneralLinear n F.Carrier) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Induction.eval (B.oppositeParabolic F.Carrier)
        (twist (T.oppositeParabolicHalfModulus B)
          ((B.blockTensor (fun i => (σ i).comp
            (GeneralLinear.inverseTranspose (B.size i) F.Carrier).toMonoidHom)).comp
              (B.oppositeLeviProjection F.Carrier)))
        (T.inverseTransposeProductToOppositeEquiv B σ f) x =
      Induction.eval (B.parabolic F.Carrier)
        (twist (T.parabolicHalfModulus B) ((B.blockTensor σ).comp (B.leviProjection F.Carrier)))
        f (GeneralLinear.inverseTranspose n F.Carrier x) := rfl

@[simp] theorem inverseTransposeProductToOppositeEquiv_symm_eval
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i))
    (h : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      Induction.SmoothFunctions (B.oppositeParabolic F.Carrier)
        (twist (T.oppositeParabolicHalfModulus B)
          ((B.blockTensor (fun i => (σ i).comp
            (GeneralLinear.inverseTranspose (B.size i) F.Carrier).toMonoidHom)).comp
              (B.oppositeLeviProjection F.Carrier))))
    (x : GeneralLinear n F.Carrier) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Induction.eval (B.parabolic F.Carrier)
        (twist (T.parabolicHalfModulus B) ((B.blockTensor σ).comp (B.leviProjection F.Carrier)))
        ((T.inverseTransposeProductToOppositeEquiv B σ).symm h) x =
      Induction.eval (B.oppositeParabolic F.Carrier)
        (twist (T.oppositeParabolicHalfModulus B)
          ((B.blockTensor (fun i => (σ i).comp
            (GeneralLinear.inverseTranspose (B.size i) F.Carrier).toMonoidHom)).comp
              (B.oppositeLeviProjection F.Carrier)))
        h (GeneralLinear.inverseTranspose n F.Carrier x) := rfl

section Stabilizers

variable (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i))

/-- One upper uniform open right stabilizer transports to its continuous inverse-transpose comap. -/
theorem inverseTransposeProductToOppositeEquiv_stabilizer :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ (f : Induction.SmoothFunctions (B.parabolic F.Carrier) (twist (T.parabolicHalfModulus B)
          ((B.blockTensor σ).comp (B.leviProjection F.Carrier))))
      (K : OpenSubgroup (GeneralLinear n F.Carrier)),
      (∀ (k : K) (x : GeneralLinear n F.Carrier),
        Induction.eval (B.parabolic F.Carrier) (twist (T.parabolicHalfModulus B)
          ((B.blockTensor σ).comp (B.leviProjection F.Carrier))) f (x * (k : GeneralLinear n F.Carrier)) =
          Induction.eval (B.parabolic F.Carrier) (twist (T.parabolicHalfModulus B)
          ((B.blockTensor σ).comp (B.leviProjection F.Carrier))) f x) →
      ∀ (k : K.comap (GeneralLinear.inverseTranspose n F.Carrier).toMonoidHom
          (GeneralLinear.continuous_inverseTranspose n F.Carrier))
        (x : GeneralLinear n F.Carrier),
        Induction.eval (B.oppositeParabolic F.Carrier) (twist (T.oppositeParabolicHalfModulus B)
          ((B.blockTensor (fun i => (σ i).comp
            (GeneralLinear.inverseTranspose (B.size i) F.Carrier).toMonoidHom)).comp
              (B.oppositeLeviProjection F.Carrier)))
            (T.inverseTransposeProductToOppositeEquiv B σ f)
            (x * (k : GeneralLinear n F.Carrier)) =
          Induction.eval (B.oppositeParabolic F.Carrier) (twist (T.oppositeParabolicHalfModulus B)
          ((B.blockTensor (fun i => (σ i).comp
            (GeneralLinear.inverseTranspose (B.size i) F.Carrier).toMonoidHom)).comp
              (B.oppositeLeviProjection F.Carrier)))
            (T.inverseTransposeProductToOppositeEquiv B σ f) x := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro f K hK k x
  exact Induction.precomposeSmoothInducedEquiv_stabilizer
    (GeneralLinear.inverseTransposeContinuous n F.Carrier)
    (B.oppositeToUpperInverseTranspose F.Carrier) (fun _ => rfl)
    (T.inverseTransposeProductInducing B σ) f K hK k x

/-- One opposite uniform open right stabilizer transports to the same continuous comap. -/
theorem inverseTransposeProductToOppositeEquiv_symm_stabilizer :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ (h : Induction.SmoothFunctions (B.oppositeParabolic F.Carrier) (twist (T.oppositeParabolicHalfModulus B)
          ((B.blockTensor (fun i => (σ i).comp
            (GeneralLinear.inverseTranspose (B.size i) F.Carrier).toMonoidHom)).comp
              (B.oppositeLeviProjection F.Carrier))))
      (K : OpenSubgroup (GeneralLinear n F.Carrier)),
      (∀ (k : K) (x : GeneralLinear n F.Carrier),
        Induction.eval (B.oppositeParabolic F.Carrier) (twist (T.oppositeParabolicHalfModulus B)
          ((B.blockTensor (fun i => (σ i).comp
            (GeneralLinear.inverseTranspose (B.size i) F.Carrier).toMonoidHom)).comp
              (B.oppositeLeviProjection F.Carrier))) h
            (x * (k : GeneralLinear n F.Carrier)) =
          Induction.eval (B.oppositeParabolic F.Carrier) (twist (T.oppositeParabolicHalfModulus B)
          ((B.blockTensor (fun i => (σ i).comp
            (GeneralLinear.inverseTranspose (B.size i) F.Carrier).toMonoidHom)).comp
              (B.oppositeLeviProjection F.Carrier))) h x) →
      ∀ (k : K.comap (GeneralLinear.inverseTranspose n F.Carrier).toMonoidHom
          (GeneralLinear.continuous_inverseTranspose n F.Carrier))
        (x : GeneralLinear n F.Carrier),
        Induction.eval (B.parabolic F.Carrier) (twist (T.parabolicHalfModulus B)
          ((B.blockTensor σ).comp (B.leviProjection F.Carrier)))
            ((T.inverseTransposeProductToOppositeEquiv B σ).symm h)
            (x * (k : GeneralLinear n F.Carrier)) =
          Induction.eval (B.parabolic F.Carrier) (twist (T.parabolicHalfModulus B)
          ((B.blockTensor σ).comp (B.leviProjection F.Carrier)))
            ((T.inverseTransposeProductToOppositeEquiv B σ).symm h) x := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro h K hK k x
  exact Induction.precomposeSmoothInducedEquiv_symm_stabilizer
    (GeneralLinear.inverseTransposeContinuous n F.Carrier)
    (B.oppositeToUpperInverseTranspose F.Carrier) (fun _ => rfl)
    (T.inverseTransposeProductInducing B σ) h K hK k x

end Stabilizers

end Langlands.PadicField.TopologicalData
