import Langlands.Shimura.Coefficients.Algebraic
import Langlands.Shimura.Unitary.Adelic
import Langlands.Global.FiniteAdeleSplit
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.Topology.Algebra.Group.Units

/-! # Points of a similitude group over products of coefficient rings

The named point groups `σ.Points S` are functorial in the coefficient ring,
are invariant under continuous algebra isomorphisms, and split over a product
`S × T` of coefficient rings. For rational finite adeles this gives
`GG(A_f) ≃ₜ* GG(∏_{v ∣ n} ℚ_v) × GG(A_f^{(n)})`. See `PointsSplit.md`.
-/

noncomputable section

universe u v w z

namespace Langlands.Shimura.AlgebraInvolution

open scoped TensorProduct

variable {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
variable (σ : AlgebraInvolution R A)

section Functoriality

variable {S : Type w} {T : Type z} {U : Type*}
variable [CommRing S] [Algebra R S] [CommRing T] [Algebra R T] [CommRing U] [Algebra R U]

theorem pointsMap_id : σ.pointsMap (AlgHom.id R S) = MonoidHom.id (σ.Points S) := by
  apply MonoidHom.ext
  intro x
  apply Subtype.ext
  apply Prod.ext
  · apply Units.ext
    change changeCoefficients (AlgHom.id R S) (x.1.1 : S ⊗[R] A) = x.1.1
    rw [changeCoefficients_id]
    rfl
  · apply Units.ext
    rfl

theorem pointsMap_comp (f : S →ₐ[R] T) (g : T →ₐ[R] U) :
    σ.pointsMap (g.comp f) = (σ.pointsMap g).comp (σ.pointsMap f) := by
  apply MonoidHom.ext
  intro x
  apply Subtype.ext
  apply Prod.ext
  · apply Units.ext
    change changeCoefficients (g.comp f) (x.1.1 : S ⊗[R] A) =
      changeCoefficients g (changeCoefficients f (x.1.1 : S ⊗[R] A))
    rw [changeCoefficients_comp]
    rfl
  · apply Units.ext
    rfl

theorem pointsMap_apply_apply (f : S →ₐ[R] T) (g : T →ₐ[R] U) (x : σ.Points S) :
    σ.pointsMap g (σ.pointsMap f x) = σ.pointsMap (g.comp f) x := by
  rw [pointsMap_comp]
  rfl

/-- An algebra isomorphism of coefficient rings induces an isomorphism of point groups. -/
def pointsEquiv (f : S ≃ₐ[R] T) : σ.Points S ≃* σ.Points T where
  toFun := σ.pointsMap f.toAlgHom
  invFun := σ.pointsMap f.symm.toAlgHom
  left_inv x := by
    rw [pointsMap_apply_apply,
      show f.symm.toAlgHom.comp f.toAlgHom = AlgHom.id R S from AlgHom.ext f.symm_apply_apply,
      pointsMap_id]
    rfl
  right_inv x := by
    rw [pointsMap_apply_apply,
      show f.toAlgHom.comp f.symm.toAlgHom = AlgHom.id R T from AlgHom.ext f.apply_symm_apply,
      pointsMap_id]
    rfl
  map_mul' := _root_.map_mul _

@[simp] theorem pointsEquiv_apply (f : S ≃ₐ[R] T) (x : σ.Points S) :
    σ.pointsEquiv f x = σ.pointsMap f.toAlgHom x := rfl

@[simp] theorem pointsEquiv_symm_apply (f : S ≃ₐ[R] T) (x : σ.Points T) :
    (σ.pointsEquiv f).symm x = σ.pointsMap f.symm.toAlgHom x := rfl

/-- A continuous algebra isomorphism of topological coefficient rings induces an
isomorphism of topological point groups. -/
def pointsContinuousEquiv [TopologicalSpace S] [IsTopologicalRing S]
    [TopologicalSpace T] [IsTopologicalRing T] [Module.Finite R A] (f : S ≃A[R] T) :
    σ.Points S ≃ₜ* σ.Points T :=
  { σ.pointsEquiv f.toAlgEquiv with
    continuous_toFun := by exact σ.continuous_pointsMap f.toAlgEquiv.toAlgHom f.continuous
    continuous_invFun := by exact σ.continuous_pointsMap f.toAlgEquiv.symm.toAlgHom f.symm.continuous }

@[simp] theorem pointsContinuousEquiv_apply [TopologicalSpace S] [IsTopologicalRing S]
    [TopologicalSpace T] [IsTopologicalRing T] [Module.Finite R A] (f : S ≃A[R] T)
    (x : σ.Points S) :
    σ.pointsContinuousEquiv f x = σ.pointsMap f.toAlgEquiv.toAlgHom x := rfl

end Functoriality

section Product

variable (S : Type w) (T : Type z) [CommRing S] [Algebra R S] [CommRing T] [Algebra R T]

/-- Scalar extension to a product of coefficient rings is the product of the scalar
extensions; its components are the coefficient changes along the two projections
(`prodTensorEquiv_apply`). -/
def prodTensorEquiv : (S × T) ⊗[R] A ≃ₐ[R] (S ⊗[R] A) × (T ⊗[R] A) :=
  (Algebra.TensorProduct.comm R (S × T) A).trans
    ((Algebra.TensorProduct.prodRight R R A S T).trans
      (AlgEquiv.prodCongr (Algebra.TensorProduct.comm R A S) (Algebra.TensorProduct.comm R A T)))

variable {S T}

theorem prodTensorEquiv_apply (x : (S × T) ⊗[R] A) :
    prodTensorEquiv S T x =
      (changeCoefficients (AlgHom.fst R S T) x, changeCoefficients (AlgHom.snd R S T) x) := by
  induction x using TensorProduct.inductionOn with
  | tmul s a => rfl
  | add x y hx hy => rw [map_add, hx, hy, map_add, map_add]; rfl

theorem prodTensorEquiv_baseChange (x : (S × T) ⊗[R] A) :
    prodTensorEquiv S T (σ.baseChange (S × T) x) =
      (σ.baseChange S (prodTensorEquiv S T x).1, σ.baseChange T (prodTensorEquiv S T x).2) := by
  rw [prodTensorEquiv_apply, prodTensorEquiv_apply, changeCoefficients_involution,
    changeCoefficients_involution]

theorem prodTensorEquiv_algebraMap (c : S × T) :
    prodTensorEquiv (R := R) (A := A) S T (algebraMap (S × T) ((S × T) ⊗[R] A) c) =
      (algebraMap S (S ⊗[R] A) c.1, algebraMap T (T ⊗[R] A) c.2) := by
  rw [prodTensorEquiv_apply, changeCoefficients_scalar, changeCoefficients_scalar]
  rfl

variable (S T)

/-- Coefficient change along the first projection, semilinear over that projection. -/
def fstTensorSemilinear : (S × T) ⊗[R] A →ₛₗ[RingHom.fst S T] S ⊗[R] A where
  toFun := changeCoefficients (AlgHom.fst R S T)
  map_add' := map_add _
  map_smul' c x := by
    change changeCoefficients (AlgHom.fst R S T) (c • x) =
      c.1 • changeCoefficients (AlgHom.fst R S T) x
    rw [Algebra.smul_def c x, _root_.map_mul, changeCoefficients_scalar, ← Algebra.smul_def]
    rfl

/-- Coefficient change along the second projection, semilinear over that projection. -/
def sndTensorSemilinear : (S × T) ⊗[R] A →ₛₗ[RingHom.snd S T] T ⊗[R] A where
  toFun := changeCoefficients (AlgHom.snd R S T)
  map_add' := map_add _
  map_smul' c x := by
    change changeCoefficients (AlgHom.snd R S T) (c • x) =
      c.2 • changeCoefficients (AlgHom.snd R S T) x
    rw [Algebra.smul_def c x, _root_.map_mul, changeCoefficients_scalar, ← Algebra.smul_def]
    rfl

section Topology

variable [TopologicalSpace S] [IsTopologicalRing S] [TopologicalSpace T] [IsTopologicalRing T]

/-- For a finite `R`-algebra `A`, the product decomposition of the scalar extension is continuous
for the module topologies. -/
theorem continuous_prodTensorEquiv [Module.Finite R A] :
    letI : TopologicalSpace ((S × T) ⊗[R] A) := moduleTopology (S × T) ((S × T) ⊗[R] A)
    letI : TopologicalSpace (S ⊗[R] A) := moduleTopology S (S ⊗[R] A)
    letI : TopologicalSpace (T ⊗[R] A) := moduleTopology T (T ⊗[R] A)
    Continuous (prodTensorEquiv (R := R) (A := A) S T) := by
  let : TopologicalSpace ((S × T) ⊗[R] A) := moduleTopology (S × T) ((S × T) ⊗[R] A)
  let : TopologicalSpace (S ⊗[R] A) := moduleTopology S (S ⊗[R] A)
  let : TopologicalSpace (T ⊗[R] A) := moduleTopology T (T ⊗[R] A)
  rw [show ⇑(prodTensorEquiv (R := R) (A := A) S T) = fun x =>
      (changeCoefficients (A := A) (AlgHom.fst R S T) x,
        changeCoefficients (A := A) (AlgHom.snd R S T) x) from
    funext prodTensorEquiv_apply]
  exact (continuous_changeCoefficients _ continuous_fst).prodMk
    (continuous_changeCoefficients _ continuous_snd)

omit [IsTopologicalRing S] [IsTopologicalRing T] in
/-- The inverse of the product decomposition of the scalar extension is continuous for the module
topologies: each component projection is a quotient map, and the two partial inverses are
multiplication by the idempotents `(1, 0)` and `(0, 1)`. -/
theorem continuous_prodTensorEquiv_symm :
    letI : TopologicalSpace ((S × T) ⊗[R] A) := moduleTopology (S × T) ((S × T) ⊗[R] A)
    letI : TopologicalSpace (S ⊗[R] A) := moduleTopology S (S ⊗[R] A)
    letI : TopologicalSpace (T ⊗[R] A) := moduleTopology T (T ⊗[R] A)
    Continuous (prodTensorEquiv (R := R) (A := A) S T).symm := by
  let : TopologicalSpace ((S × T) ⊗[R] A) := moduleTopology (S × T) ((S × T) ⊗[R] A)
  let : TopologicalSpace (S ⊗[R] A) := moduleTopology S (S ⊗[R] A)
  let : TopologicalSpace (T ⊗[R] A) := moduleTopology T (T ⊗[R] A)
  have : IsModuleTopology (S × T) ((S × T) ⊗[R] A) := ⟨rfl⟩
  have : IsModuleTopology S (S ⊗[R] A) := ⟨rfl⟩
  have : IsModuleTopology T (T ⊗[R] A) := ⟨rfl⟩
  have := IsModuleTopology.toContinuousAdd (S × T) ((S × T) ⊗[R] A)
  set E := prodTensorEquiv (R := R) (A := A) S T
  have hfst (z : (S × T) ⊗[R] A) : fstTensorSemilinear (A := A) S T z = (E z).1 :=
    (congrArg Prod.fst (prodTensorEquiv_apply z)).symm
  have hsnd (z : (S × T) ⊗[R] A) : sndTensorSemilinear (A := A) S T z = (E z).2 :=
    (congrArg Prod.snd (prodTensorEquiv_apply z)).symm
  have hq₁ : Topology.IsQuotientMap (fstTensorSemilinear (A := A) S T) :=
    IsModuleTopology.isQuotientMap_of_surjectiveₛₗ (by exact isOpenQuotientMap_fst) _
      fun x => ⟨E.symm (x, 0), by rw [hfst, E.apply_symm_apply]⟩
  have hq₂ : Topology.IsQuotientMap (sndTensorSemilinear (A := A) S T) :=
    IsModuleTopology.isQuotientMap_of_surjectiveₛₗ (by exact isOpenQuotientMap_snd) _
      fun y => ⟨E.symm (0, y), by rw [hsnd, E.apply_symm_apply]⟩
  have h₁ : Continuous fun x : S ⊗[R] A => E.symm (x, 0) := by
    rw [hq₁.continuous_iff]
    have : (fun x : S ⊗[R] A => E.symm (x, 0)) ∘ fstTensorSemilinear (A := A) S T =
        fun z => ((1, 0) : S × T) • z := by
      funext z
      apply E.injective
      rw [Function.comp_apply, E.apply_symm_apply, hfst, Algebra.smul_def ((1, 0) : S × T) z,
        _root_.map_mul, prodTensorEquiv_algebraMap]
      ext <;> simp only [Prod.fst_mul, Prod.snd_mul, _root_.map_one, map_zero, one_mul, zero_mul]
    rw [this]
    exact continuous_const_smul _
  have h₂ : Continuous fun y : T ⊗[R] A => E.symm (0, y) := by
    rw [hq₂.continuous_iff]
    have : (fun y : T ⊗[R] A => E.symm (0, y)) ∘ sndTensorSemilinear (A := A) S T =
        fun z => ((0, 1) : S × T) • z := by
      funext z
      apply E.injective
      rw [Function.comp_apply, E.apply_symm_apply, hsnd, Algebra.smul_def ((0, 1) : S × T) z,
        _root_.map_mul, prodTensorEquiv_algebraMap]
      ext <;> simp only [Prod.fst_mul, Prod.snd_mul, _root_.map_one, map_zero, one_mul, zero_mul]
    rw [this]
    exact continuous_const_smul _
  rw [show ⇑E.symm = fun p => E.symm (p.1, 0) + E.symm (0, p.2) by
    funext p
    rw [← map_add]
    simp]
  exact (h₁.comp continuous_fst).add (h₂.comp continuous_snd)

end Topology

variable {S T}

theorem changeCoefficients_fst_prodTensorEquiv_symm (p : (S ⊗[R] A) × (T ⊗[R] A)) :
    changeCoefficients (AlgHom.fst R S T) ((prodTensorEquiv S T).symm p) = p.1 := by
  have h := congrArg Prod.fst (prodTensorEquiv_apply ((prodTensorEquiv (R := R) (A := A) S T).symm p))
  rw [AlgEquiv.apply_symm_apply] at h
  exact h.symm

theorem changeCoefficients_snd_prodTensorEquiv_symm (p : (S ⊗[R] A) × (T ⊗[R] A)) :
    changeCoefficients (AlgHom.snd R S T) ((prodTensorEquiv S T).symm p) = p.2 := by
  have h := congrArg Prod.snd (prodTensorEquiv_apply ((prodTensorEquiv (R := R) (A := A) S T).symm p))
  rw [AlgEquiv.apply_symm_apply] at h
  exact h.symm

/-- The point with coefficients in `S × T` whose components are a given pair of points. -/
def prodPoint (x : (σ.baseChange S).similitudes) (y : (σ.baseChange T).similitudes) :
    σ.Points (S × T) :=
  ⟨(Units.map (prodTensorEquiv (R := R) (A := A) S T).symm.toMonoidHom
      (MulEquiv.prodUnits.symm (x.1.1, y.1.1)),
    MulEquiv.prodUnits.symm (x.1.2, y.1.2)), by
      rw [(σ.baseChange (S × T)).mem_similitudes_iff]
      apply (prodTensorEquiv (R := R) (A := A) S T).injective
      change prodTensorEquiv S T ((prodTensorEquiv S T).symm
            (((x.1.1 : (S ⊗[R] A)ˣ) : S ⊗[R] A), ((y.1.1 : (T ⊗[R] A)ˣ) : T ⊗[R] A)) *
          σ.baseChange (S × T) ((prodTensorEquiv S T).symm
            (((x.1.1 : (S ⊗[R] A)ˣ) : S ⊗[R] A), ((y.1.1 : (T ⊗[R] A)ˣ) : T ⊗[R] A)))) =
        prodTensorEquiv S T (algebraMap (S × T) _ (((x.1.2 : Sˣ) : S), ((y.1.2 : Tˣ) : T)))
      rw [_root_.map_mul, prodTensorEquiv_baseChange, AlgEquiv.apply_symm_apply,
        prodTensorEquiv_algebraMap]
      exact Prod.ext (((σ.baseChange S).mem_similitudes_iff x.1).mp x.2)
        (((σ.baseChange T).mem_similitudes_iff y.1).mp y.2)⟩

theorem prodPoint_one : σ.prodPoint (S := S) (T := T) 1 1 = 1 := by
  apply Subtype.ext
  apply Prod.ext
  · apply Units.ext
    change (prodTensorEquiv (R := R) (A := A) S T).symm (1, 1) = 1
    exact _root_.map_one _
  · apply Units.ext
    rfl

theorem prodPoint_mul (x x' : (σ.baseChange S).similitudes)
    (y y' : (σ.baseChange T).similitudes) :
    σ.prodPoint (x * x') (y * y') = σ.prodPoint x y * σ.prodPoint x' y' := by
  apply Subtype.ext
  apply Prod.ext
  · apply Units.ext
    change (prodTensorEquiv (R := R) (A := A) S T).symm
        (((x.1.1 : (S ⊗[R] A)ˣ) : S ⊗[R] A) * ((x'.1.1 : (S ⊗[R] A)ˣ) : S ⊗[R] A),
          ((y.1.1 : (T ⊗[R] A)ˣ) : T ⊗[R] A) * ((y'.1.1 : (T ⊗[R] A)ˣ) : T ⊗[R] A)) =
      (prodTensorEquiv S T).symm
          (((x.1.1 : (S ⊗[R] A)ˣ) : S ⊗[R] A), ((y.1.1 : (T ⊗[R] A)ˣ) : T ⊗[R] A)) *
        (prodTensorEquiv S T).symm
          (((x'.1.1 : (S ⊗[R] A)ˣ) : S ⊗[R] A), ((y'.1.1 : (T ⊗[R] A)ˣ) : T ⊗[R] A))
    rw [← _root_.map_mul]
    rfl
  · apply Units.ext
    rfl

theorem pointsMap_fst_prodPoint (x : (σ.baseChange S).similitudes)
    (y : (σ.baseChange T).similitudes) :
    σ.pointsMap (AlgHom.fst R S T) (σ.prodPoint x y) = x := by
  apply Subtype.ext
  apply Prod.ext
  · apply Units.ext
    exact changeCoefficients_fst_prodTensorEquiv_symm _
  · apply Units.ext
    rfl

theorem pointsMap_snd_prodPoint (x : (σ.baseChange S).similitudes)
    (y : (σ.baseChange T).similitudes) :
    σ.pointsMap (AlgHom.snd R S T) (σ.prodPoint x y) = y := by
  apply Subtype.ext
  apply Prod.ext
  · apply Units.ext
    exact changeCoefficients_snd_prodTensorEquiv_symm _
  · apply Units.ext
    rfl

theorem prodPoint_pointsMap (z : σ.Points (S × T)) :
    σ.prodPoint (σ.pointsMap (AlgHom.fst R S T) z) (σ.pointsMap (AlgHom.snd R S T) z) = z := by
  apply Subtype.ext
  apply Prod.ext
  · apply Units.ext
    change (prodTensorEquiv (R := R) (A := A) S T).symm
        (changeCoefficients (AlgHom.fst R S T) (((z.1.1 : ((S × T) ⊗[R] A)ˣ)) : (S × T) ⊗[R] A),
          changeCoefficients (AlgHom.snd R S T) (((z.1.1 : ((S × T) ⊗[R] A)ˣ)) :
            (S × T) ⊗[R] A)) = z.1.1
    rw [← prodTensorEquiv_apply, AlgEquiv.symm_apply_apply]
  · apply Units.ext
    rfl

variable (S T)

/-- Points with coefficients in `S × T` built from a pair of points. -/
def prodPointsInv : σ.Points S × σ.Points T →* σ.Points (S × T) where
  toFun y := σ.prodPoint y.1 y.2
  map_one' := σ.prodPoint_one
  map_mul' x y := σ.prodPoint_mul x.1 y.1 x.2 y.2

/-- The point group with coefficients in a product of coefficient rings is the product of the
point groups, through the coefficient changes along the two projections. -/
def prodPointsEquiv : σ.Points (S × T) ≃* σ.Points S × σ.Points T where
  toFun x := (σ.pointsMap (AlgHom.fst R S T) x, σ.pointsMap (AlgHom.snd R S T) x)
  invFun := σ.prodPointsInv S T
  left_inv x := σ.prodPoint_pointsMap x
  right_inv y := Prod.ext (σ.pointsMap_fst_prodPoint y.1 y.2) (σ.pointsMap_snd_prodPoint y.1 y.2)
  map_mul' x y := Prod.ext (_root_.map_mul _ x y) (_root_.map_mul _ x y)

@[simp] theorem prodPointsEquiv_apply_fst (x : σ.Points (S × T)) :
    (σ.prodPointsEquiv S T x).1 = σ.pointsMap (AlgHom.fst R S T) x := rfl

@[simp] theorem prodPointsEquiv_apply_snd (x : σ.Points (S × T)) :
    (σ.prodPointsEquiv S T x).2 = σ.pointsMap (AlgHom.snd R S T) x := rfl

theorem prodPointsEquiv_symm_apply (y : σ.Points S × σ.Points T) :
    (σ.prodPointsEquiv S T).symm y = σ.prodPointsInv S T y := rfl

/-- The multiplier of the point built from a pair is the pair of multipliers. -/
theorem multiplier_prodPointsInv (y : σ.Points S × σ.Points T) :
    Points.multiplier σ (S × T) (σ.prodPointsInv S T y) =
      MulEquiv.prodUnits.symm (Points.multiplier σ S y.1, Points.multiplier σ T y.2) := rfl

variable [TopologicalSpace S] [IsTopologicalRing S] [TopologicalSpace T] [IsTopologicalRing T]

omit [IsTopologicalRing S] [IsTopologicalRing T] in
/-- Building a point from a pair of points is continuous. -/
theorem continuous_prodPointsInv [Module.Finite R A] : Continuous (σ.prodPointsInv S T) := by
  let : TopologicalSpace ((S × T) ⊗[R] A) := moduleTopology (S × T) ((S × T) ⊗[R] A)
  let : TopologicalSpace (S ⊗[R] A) := moduleTopology S (S ⊗[R] A)
  let : TopologicalSpace (T ⊗[R] A) := moduleTopology T (T ⊗[R] A)
  have hS : Continuous fun x : σ.Points S => (Subtype.val x : (S ⊗[R] A)ˣ × Sˣ) :=
    continuous_subtype_val
  have hT : Continuous fun x : σ.Points T => (Subtype.val x : (T ⊗[R] A)ˣ × Tˣ) :=
    continuous_subtype_val
  have h₁ : Continuous fun y : σ.Points S × σ.Points T =>
      (((Subtype.val y.1 : (S ⊗[R] A)ˣ × Sˣ).1, (Subtype.val y.2 : (T ⊗[R] A)ˣ × Tˣ).1) :
        (S ⊗[R] A)ˣ × (T ⊗[R] A)ˣ) :=
    (continuous_fst.comp (hS.comp continuous_fst)).prodMk
      (continuous_fst.comp (hT.comp continuous_snd))
  have h₂ : Continuous fun y : σ.Points S × σ.Points T =>
      (((Subtype.val y.1 : (S ⊗[R] A)ˣ × Sˣ).2, (Subtype.val y.2 : (T ⊗[R] A)ˣ × Tˣ).2) :
        Sˣ × Tˣ) :=
    (continuous_snd.comp (hS.comp continuous_fst)).prodMk
      (continuous_snd.comp (hT.comp continuous_snd))
  refine Continuous.subtype_mk (Continuous.prodMk ?_ ?_) _
  · exact (Continuous.units_map _ (continuous_prodTensorEquiv_symm S T)).comp
      (Homeomorph.prodUnits.symm.continuous.comp h₁)
  · exact Homeomorph.prodUnits.symm.continuous.comp h₂

/-- The splitting of the point group over a product of topological coefficient rings, as an
isomorphism of topological groups. -/
def prodPointsContinuousEquiv [Module.Finite R A] :
    σ.Points (S × T) ≃ₜ* σ.Points S × σ.Points T :=
  { σ.prodPointsEquiv S T with
    continuous_toFun := (σ.continuous_pointsMap _ continuous_fst).prodMk
      (σ.continuous_pointsMap _ continuous_snd)
    continuous_invFun := σ.continuous_prodPointsInv S T }

@[simp] theorem prodPointsContinuousEquiv_apply [Module.Finite R A] (x : σ.Points (S × T)) :
    σ.prodPointsContinuousEquiv S T x =
      (σ.pointsMap (AlgHom.fst R S T) x, σ.pointsMap (AlgHom.snd R S T) x) := rfl

end Product

section Rational

open Langlands.Global
open scoped NumberField

variable {A : Type v} [Ring A] [Algebra ℚ A]
variable (σ : AlgebraInvolution ℚ A) (n : ℕ)

/-- The points with coefficients in the product of the completions of `ℚ` at the finite places
whose prime ideal contains `n`. -/
abbrev DividingPoints :=
  σ.Points (Π v : {v : FinitePlace ℚ // (n : 𝓞 ℚ) ∈ v.asIdeal}, FiniteCompletion ℚ v.1)

/-- The points with coefficients in the prime-to-`n` finite adeles. -/
abbrev PrimeToPoints := σ.Points (PrimeToFiniteAdeles n)

variable [Module.Finite ℚ A]

/-- For `n ≠ 0`, the finite adelic points split as the points at the places whose prime ideal
contains `n` times the prime-to-`n` points. -/
def finiteAdelicPointsSplit (hn : n ≠ 0) :
    σ.FiniteAdelicPoints ≃ₜ* σ.DividingPoints n × σ.PrimeToPoints n :=
  (σ.pointsContinuousEquiv (ratFiniteAdelesSplit n hn)).trans (σ.prodPointsContinuousEquiv _ _)

theorem finiteAdelicPointsSplit_apply_fst (hn : n ≠ 0) (g : σ.FiniteAdelicPoints) :
    (σ.finiteAdelicPointsSplit n hn g).1 =
      σ.pointsMap ((AlgHom.fst ℚ _ _).comp (ratFiniteAdelesSplit n hn).toAlgEquiv.toAlgHom) g :=
  σ.pointsMap_apply_apply _ _ g

theorem finiteAdelicPointsSplit_apply_snd (hn : n ≠ 0) (g : σ.FiniteAdelicPoints) :
    (σ.finiteAdelicPointsSplit n hn g).2 =
      σ.pointsMap (primeToFiniteRestriction n).toAlgHom g :=
  σ.pointsMap_apply_apply _ _ g

/-- Evaluation of the points over `Π_{v ∣ n} ℚ_v` at one of these places. -/
def dividingLocalMap (v : {v : FinitePlace ℚ // (n : 𝓞 ℚ) ∈ v.asIdeal}) :
    σ.DividingPoints n →ₜ* σ.Points (FiniteCompletion ℚ v.1) where
  toMonoidHom := σ.pointsMap
    (Pi.evalAlgHom ℚ (fun v : {v : FinitePlace ℚ // (n : 𝓞 ℚ) ∈ v.asIdeal} ↦
      FiniteCompletion ℚ v.1) v)
  continuous_toFun := σ.continuous_pointsMap _ (continuous_apply v)

/-- The local component at a place whose prime ideal contains `n` of the first factor of the
splitting is the published local evaluation `finiteLocalMap`. -/
theorem dividingLocalMap_finiteAdelicPointsSplit (hn : n ≠ 0)
    (v : {v : FinitePlace ℚ // (n : 𝓞 ℚ) ∈ v.asIdeal}) (g : σ.FiniteAdelicPoints) :
    σ.dividingLocalMap n v (σ.finiteAdelicPointsSplit n hn g).1 = σ.finiteLocalMap v.1 g := by
  have h : (Pi.evalAlgHom ℚ (fun v : {v : FinitePlace ℚ // (n : 𝓞 ℚ) ∈ v.asIdeal} ↦
      FiniteCompletion ℚ v.1) v).comp
        ((AlgHom.fst ℚ _ _).comp (ratFiniteAdelesSplit n hn).toAlgEquiv.toAlgHom) =
      finiteEvaluation v.1 :=
    AlgHom.ext fun _ ↦ rfl
  change σ.pointsMap _ (σ.finiteAdelicPointsSplit n hn g).1 = σ.pointsMap _ g
  rw [finiteAdelicPointsSplit_apply_fst, pointsMap_apply_apply, h]

/-- The splitting sends the diagonal image of a rational point to its diagonal images. -/
theorem finiteAdelicPointsSplit_diagonal (hn : n ≠ 0) (g : σ.similitudes) :
    σ.finiteAdelicPointsSplit n hn (σ.finiteAdelicDiagonal g) =
      (σ.diagonalPoints _ g, σ.diagonalPoints _ g) := by
  apply Prod.ext
  · exact (finiteAdelicPointsSplit_apply_fst σ n hn _).trans (σ.pointsMap_diagonalPoints _ g)
  · exact (finiteAdelicPointsSplit_apply_snd σ n hn _).trans (σ.pointsMap_diagonalPoints _ g)

end Rational

end Langlands.Shimura.AlgebraInvolution
