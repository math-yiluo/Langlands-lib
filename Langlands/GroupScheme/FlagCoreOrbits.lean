import Langlands.GroupScheme.FlagCoreQuotient
import Langlands.GroupScheme.MatrixRepresentationTensor

/-! # Closed orbits of a line, its dual line and their tensor for the flag covering core -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Matrix
open scoped CategoryTheory.MonObj Kronecker

namespace Langlands.GroupScheme.FlagCore

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
variable {m : Type} [Fintype m] [DecidableEq m]

/-- The subgroup `b : B ⟶ G` stabilizes the line of `v` under the matrix representation `σ`: on
every test scheme `T`, every `T`-point of `B` maps the image `v_T` of `v` to a unit multiple of
`v_T`. -/
def StabilizesLine (σ : MatrixRepresentation G m) (v : m → k)
    {B : GroupScheme (Spec (CommRingCat.of k))} (b : B ⟶ G) : Prop :=
  ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X),
    x ∈ (SubgroupFunctor.range b).carrier T →
      ∃ a : Γ(T.left, ⊤)ˣ,
        (σ.pointMatrix T x : Matrix m m Γ(T.left, ⊤)) *ᵥ (fun i => scalarMap T (v i)) =
          (a : Γ(T.left, ⊤)) • fun i => scalarMap T (v i)

/-- If the fibers of `q` lie in cosets of `B` and `B` stabilizes the line of `v`, then the fibers
of `q` stabilize the line of `v`. -/
theorem fibersStabilizeLine_of_fibersInCosets {σ : MatrixRepresentation G m} {v : m → k}
    {B : GroupScheme (Spec (CommRingCat.of k))} {b : B ⟶ G}
    {Q : Over (Spec (CommRingCat.of k))} {q : G.X ⟶ Q} (hq : FibersInCosets q b)
    (hs : StabilizesLine σ v b) : FibersStabilizeLine σ v q :=
  fun T g h hgh => hs T (g⁻¹ * h) (hq T g h hgh)

/-- A common eigenline of two representations gives an eigenline of their tensor product. -/
theorem StabilizesLine.tensor {m' : Type} [Fintype m'] [DecidableEq m']
    {σ : MatrixRepresentation G m} {σ' : MatrixRepresentation G m'} {v : m → k} {w : m' → k}
    {B : GroupScheme (Spec (CommRingCat.of k))} {b : B ⟶ G}
    (hs : StabilizesLine σ v b) (hs' : StabilizesLine σ' w b) :
    StabilizesLine (σ.tensor σ') (fun p => v p.1 * w p.2) b := by
  intro T x hx
  obtain ⟨a, ha⟩ := hs T x hx
  obtain ⟨a', ha'⟩ := hs' T x hx
  refine ⟨a * a', ?_⟩
  have hvw : (fun p : m × m' => scalarMap T (v p.1 * w p.2)) =
      fun p => scalarMap T (v p.1) * scalarMap T (w p.2) := by
    funext p
    exact map_mul _ _ _
  rw [hvw, MatrixRepresentation.tensor_pointMatrix,
    GeneralLinear.kroneckerHom_mulVec m m' _ _ (fun i => scalarMap T (v i))
      (fun j => scalarMap T (w j)), ha, ha']
  funext p
  simp only [Pi.smul_apply, smul_eq_mul, Units.val_mul]
  ring

omit [DecidableEq m] in
/-- The matrix of a rational point has the entries of its point matrix, read in `k`. -/
theorem rationalMatrix_coe [DecidableEq m] (σ : MatrixRepresentation G m)
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :
    (σ.rationalMatrix g : Matrix m m k) =
      (σ.pointMatrix _ g : Matrix m m Γ((Over.mk (𝟙 (Spec (CommRingCat.of k)))).left, ⊤)).map
        (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom :=
  rfl

/-- On rational points the dual representation is the inverse transpose. -/
theorem rationalMatrix_dual (ρ : MatrixRepresentation G m)
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :
    (ρ.dual.rationalMatrix g : Matrix m m k) =
      ((ρ.rationalMatrix g⁻¹ : GL m k) : Matrix m m k)ᵀ := by
  rw [map_inv, rationalMatrix_coe, MatrixRepresentation.dual_pointMatrix,
    GeneralLinear.matrixContragredient_coe]
  ext i l
  rfl

/-- On rational points the tensor representation is the Kronecker product. -/
theorem rationalMatrix_tensor {m' : Type} [Fintype m'] [DecidableEq m']
    (ρ : MatrixRepresentation G m) (σ : MatrixRepresentation G m')
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :
    ((ρ.tensor σ).rationalMatrix g : Matrix (m × m') (m × m') k) =
      (ρ.rationalMatrix g : Matrix m m k) ⊗ₖ (σ.rationalMatrix g : Matrix m' m' k) := by
  ext p p'
  rw [rationalMatrix_coe, map_apply, MatrixRepresentation.tensor_pointMatrix_entry, map_mul]
  rfl

/-- The dual orbit vector is the orbit of `w₀` under the dual representation. -/
theorem dualOrbitVec_rationalMatrix (ρ : MatrixRepresentation G m) (w₀ : m → k)
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :
    dualOrbitVec ρ.rationalMatrix w₀ g = (ρ.dual.rationalMatrix g : Matrix m m k) *ᵥ w₀ := by
  rw [rationalMatrix_dual, mulVec_transpose]
  rfl

/-- The tensor orbit vector is the orbit of `e ⊗ w₀` under the tensor of `ρ` with its dual. -/
theorem tensorOrbitVec_rationalMatrix (ρ : MatrixRepresentation G m) (e w₀ : m → k)
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :
    tensorOrbitVec ρ.rationalMatrix e w₀ g =
      ((ρ.tensor ρ.dual).rationalMatrix g : Matrix (m × m) (m × m) k) *ᵥ
        fun p => e p.1 * w₀ p.2 := by
  rw [rationalMatrix_tensor]
  funext p
  rw [← GeneralLinear.kroneckerHom_coe,
    GeneralLinear.kroneckerHom_mulVec m m _ _ e w₀, ← dualOrbitVec_rationalMatrix]
  rfl

variable [IsAlgClosed k] [LocallyOfFiniteType G.X.hom]
variable {Q : Over (Spec (CommRingCat.of k))} (q : G.X ⟶ Q)
  [Flat q.left] [Surjective q.left] [QuasiCompact q.left] [IsProper Q.hom]

/-- **Closed orbit of a line.** -/
theorem isClosedOrbit_orbitVec (ρ : MatrixRepresentation G m) {e : m → k} (he : e ≠ 0)
    (hq : FibersStabilizeLine ρ e q) : IsClosedOrbit (orbitVec ρ.rationalMatrix e) :=
  isClosedOrbit_of_isProper ρ he q hq

/-- **Closed orbit of a dual line.** -/
theorem isClosedOrbit_dualOrbitVec (ρ : MatrixRepresentation G m) {w₀ : m → k} (hw₀ : w₀ ≠ 0)
    (hq : FibersStabilizeLine ρ.dual w₀ q) : IsClosedOrbit (dualOrbitVec ρ.rationalMatrix w₀) := by
  have h := isClosedOrbit_of_isProper ρ.dual hw₀ q hq
  rwa [show dualOrbitVec ρ.rationalMatrix w₀ = fun g =>
    (ρ.dual.rationalMatrix g : Matrix m m k) *ᵥ w₀ from funext (dualOrbitVec_rationalMatrix ρ w₀)]

/-- **Closed orbit of the tensor of a line and a dual line.** -/
theorem isClosedOrbit_tensorOrbitVec (ρ : MatrixRepresentation G m) {e w₀ : m → k} (he : e ≠ 0)
    (hw₀ : w₀ ≠ 0) (hq : FibersStabilizeLine (ρ.tensor ρ.dual) (fun p => e p.1 * w₀ p.2) q) :
    IsClosedOrbit (tensorOrbitVec ρ.rationalMatrix e w₀) := by
  have hne : (fun p : m × m => e p.1 * w₀ p.2) ≠ 0 := by
    obtain ⟨i, hi⟩ : ∃ i, e i ≠ 0 := by
      by_contra hall
      push Not at hall
      exact he (funext hall)
    obtain ⟨l, hl⟩ : ∃ l, w₀ l ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hw₀ (funext hall)
    intro h0
    exact mul_ne_zero hi hl (congrFun h0 (i, l))
  have h := isClosedOrbit_of_isProper (ρ.tensor ρ.dual) hne q hq
  rwa [show tensorOrbitVec ρ.rationalMatrix e w₀ = fun g =>
    ((ρ.tensor ρ.dual).rationalMatrix g : Matrix (m × m) (m × m) k) *ᵥ
      fun p => e p.1 * w₀ p.2 from funext (tensorOrbitVec_rationalMatrix ρ e w₀)]

end Langlands.GroupScheme.FlagCore
