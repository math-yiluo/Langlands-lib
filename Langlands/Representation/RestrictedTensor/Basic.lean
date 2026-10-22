import Mathlib.LinearAlgebra.PiTensorProduct.Basic
import Mathlib.Algebra.Colimit.DirectLimit
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# Algebraic restricted tensor products

The finite stages and their transition maps are the construction in
Flath, *Decomposition of representations into tensor products*, §2, pp. 180–181.
-/

noncomputable section
open scoped Classical TensorProduct

universe uK uI uV uW

namespace Langlands.RestrictedTensor

variable (K : Type uK) [Field K]
variable {ι : Type uI} (V : ι → Type uV)
variable [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]

/-- The tensor product of the factors in a finite set. -/
abbrev Stage (S : Finset ι) := PiTensorProduct K (fun i : S => V i)

variable {K V}

/-- Extend a finite tuple by the reference vectors. Values of `e` on `S` are unused. -/
def extend (e : ∀ i, V i) {S T : Finset ι} (v : ∀ i : S, V i) (j : T) : V j :=
  if h : j.1 ∈ S then v ⟨j.1, h⟩ else e j.1

omit [∀ i, AddCommGroup (V i)] in
private theorem extend_update (e : ∀ i, V i) {S T : Finset ι}
    [DecidableEq S] [DecidableEq T] (h : S ⊆ T)
    (v : ∀ i : S, V i) (i : S) (a : V i) :
    extend e (T := T) (Function.update v i a) =
      Function.update (extend e v) ⟨i.1, h i.2⟩ a := by
  classical
  funext j
  by_cases hji : j.1 = i.1
  · obtain ⟨j, hj⟩ := j
    dsimp at hji
    subst j
    simp [extend]
  · have hn : j ≠ (⟨i.1, h i.2⟩ : T) := fun h' => hji (congrArg Subtype.val h')
    simp only [Function.update_of_ne hn, extend]
    split_ifs with hj
    · have hn' : (⟨j.1, hj⟩ : S) ≠ i := fun h' => hji (congrArg Subtype.val h')
      exact Function.update_of_ne hn' _ _
    · rfl

/-- The multilinear map that adjoins the missing reference vectors. -/
def transitionMultilinear (e : ∀ i, V i) {S T : Finset ι} (h : S ⊆ T) :
    MultilinearMap K (fun i : S => V i) (Stage K V T) where
  toFun v := PiTensorProduct.tprod K (extend e v)
  map_update_add' := by
    intro _ v i a b
    classical
    rw [extend_update e h, extend_update e h, extend_update e h]
    exact (PiTensorProduct.tprod K).map_update_add _ _ _ _
  map_update_smul' := by
    intro _ v i c a
    classical
    rw [extend_update e h, extend_update e h]
    exact (PiTensorProduct.tprod K).map_update_smul _ _ _ _

/-- The finite-stage transition map. -/
def transition (e : ∀ i, V i) {S T : Finset ι} (h : S ⊆ T) :
    Stage K V S →ₗ[K] Stage K V T :=
  PiTensorProduct.lift (transitionMultilinear e h)

@[simp]
theorem transition_tprod (e : ∀ i, V i) {S T : Finset ι} (h : S ⊆ T)
    (v : ∀ i : S, V i) :
    transition (K := K) e h (PiTensorProduct.tprod K v) =
      PiTensorProduct.tprod K (extend e v) :=
  PiTensorProduct.lift.tprod _

omit [∀ i, AddCommGroup (V i)] in
@[simp]
theorem extend_self (e : ∀ i, V i) {S : Finset ι} (v : ∀ i : S, V i) :
    extend e (T := S) v = v := by
  classical
  funext i
  simp [extend, i.2]

omit [∀ i, AddCommGroup (V i)] in
theorem extend_extend (e : ∀ i, V i) {S T U : Finset ι} (h : S ⊆ T)
    (v : ∀ i : S, V i) :
    extend e (T := U) (extend e (T := T) v) = extend e v := by
  classical
  funext i
  by_cases hi : i.1 ∈ S
  · simp [extend, hi, h hi]
  · simp [extend, hi]

@[simp]
theorem transition_self (e : ∀ i, V i) (S : Finset ι) :
    transition (K := K) e (S := S) (Finset.Subset.refl S) = LinearMap.id := by
  ext v
  simp

theorem transition_comp (e : ∀ i, V i) {S T U : Finset ι}
    (hST : S ⊆ T) (hTU : T ⊆ U) :
    (transition (K := K) e hTU).comp (transition e hST) =
      transition e (hST.trans hTU) := by
  ext v
  simp [extend_extend e hST]

/-- Split the indices in `T` into `S` and the indices newly adjoined to `S`. -/
def splitIndex {S T : Finset ι} (h : S ⊆ T) :
    S ⊕ {i : T // i.1 ∉ S} ≃ T where
  toFun := Sum.elim (fun i => ⟨i.1, h i.2⟩) Subtype.val
  invFun i := if hi : i.1 ∈ S then Sum.inl ⟨i.1, hi⟩ else Sum.inr ⟨i, hi⟩
  left_inv := by
    intro i
    cases i with
    | inl i => simp [i.2]
    | inr i => simp [i.2]
  right_inv := by intro i; dsimp only; split_ifs <;> rfl

/-- Separate an arbitrary finite subfamily from a finite tensor stage. -/
def splitStage {S T : Finset ι} (h : S ⊆ T) :
    Stage K V T ≃ₗ[K]
      (Stage K V S ⊗[K] PiTensorProduct K (fun i : {i : T // i.1 ∉ S} => V i.1)) :=
  (PiTensorProduct.reindex K (fun i : T => V i) (splitIndex h).symm).trans
    (PiTensorProduct.tmulEquivDep K (fun i => V (splitIndex h i))).symm

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem splitStage_tprod {S T : Finset ι} (h : S ⊆ T) (v : ∀ i : T, V i) :
    splitStage (K := K) (V := V) h (PiTensorProduct.tprod K v) =
      (PiTensorProduct.tprod K (fun i : S => v ⟨i.1, h i.2⟩)) ⊗ₜ[K]
        (PiTensorProduct.tprod K (fun i : {i : T // i.1 ∉ S} => v i.1)) := by
  dsimp only [splitStage, LinearEquiv.trans_apply]
  have hr := PiTensorProduct.reindex_tprod (R := K) (s := fun i : T => V i)
    (splitIndex h).symm v
  rw [hr]
  exact PiTensorProduct.tmulEquivDep_symm_apply K _ _

/-- Contract the newly adjoined factors using specified linear functionals. -/
def retractStage {S T : Finset ι} (h : S ⊆ T)
    (φ : ∀ i : {i : T // i.1 ∉ S}, V i.1 →ₗ[K] K) :
    Stage K V T →ₗ[K] Stage K V S :=
  (TensorProduct.rid K (Stage K V S)).toLinearMap ∘ₗ
    (TensorProduct.map LinearMap.id
      (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra K _ K).compLinearMap φ))) ∘ₗ
    (splitStage h).toLinearMap

@[simp]
theorem retractStage_tprod {S T : Finset ι} (h : S ⊆ T)
    (φ : ∀ i : {i : T // i.1 ∉ S}, V i.1 →ₗ[K] K) (v : ∀ i : T, V i) :
    retractStage h φ (PiTensorProduct.tprod K v) =
      (∏ i : {i : T // i.1 ∉ S}, φ i (v i.1)) •
        PiTensorProduct.tprod K (fun i : S => v ⟨i.1, h i.2⟩) := by
  simp [retractStage]

theorem retractStage_transition (e : ∀ i, V i) {S T : Finset ι} (h : S ⊆ T)
    (φ : ∀ i : {i : T // i.1 ∉ S}, V i.1 →ₗ[K] K)
    (hφ : ∀ i, φ i (e i.1) = 1) :
    (retractStage h φ).comp (transition e h) = LinearMap.id := by
  ext v
  change retractStage h φ (transition e h (PiTensorProduct.tprod K v)) =
    PiTensorProduct.tprod K v
  rw [transition_tprod, retractStage_tprod]
  have hp : (∏ i : {i : T // i.1 ∉ S}, φ i (extend e v i.1)) = 1 := by
    apply Finset.prod_eq_one
    intro i _
    simpa only [extend, dite_eq_right i.2] using hφ i
  rw [hp, one_smul]
  congr 1
  funext i
  simp [extend, i.2]

/-- Over a field, adjoining nonzero vectors gives an injective transition. -/
theorem transition_injective (e : ∀ i, V i) {S T : Finset ι} (h : S ⊆ T)
    (he : ∀ i ∈ T, i ∉ S → e i ≠ 0) :
    Function.Injective (transition (K := K) e h) := by
  have hφ (i : {i : T // i.1 ∉ S}) :
      ∃ φ : V i.1 →ₗ[K] K, φ (e i.1) = 1 :=
    Module.Projective.exists_dual_eq_one K (he i.1 i.1.2 i.2)
  choose φ hφ using hφ
  have hi : Function.LeftInverse (retractStage h φ) (transition e h) :=
    fun x => LinearMap.congr_fun (retractStage_transition e h φ hφ) x
  exact hi.injective

/-- The directed index set of finite sets containing the exceptional set. -/
abbrev Index (E : Finset ι) := {S : Finset ι // E ⊆ S}

instance (E : Finset ι) : Nonempty (Index E) := ⟨⟨E, le_rfl⟩⟩

instance (E : Finset ι) : IsDirectedOrder (Index E) where
  directed S T :=
    ⟨⟨S.1 ∪ T.1, S.2.trans Finset.subset_union_left⟩,
      Finset.subset_union_left, Finset.subset_union_right⟩

variable (K V)

/-- The transition system on finite sets containing `E`. -/
def systemMap (E : Finset ι) (e : ∀ i, V i) (S T : Index E) (h : S ≤ T) :
    Stage K V S.1 →ₗ[K] Stage K V T.1 :=
  transition e h

instance (E : Finset ι) (e : ∀ i, V i) :
    DirectedSystem (fun S : Index E => Stage K V S.1) (systemMap K V E e · · ·) where
  map_self := by intro S x; simp [systemMap]
  map_map := by
    intro U T S hST hTU x
    exact LinearMap.congr_fun (transition_comp e hST hTU) x

/-- The actual algebraic direct limit of the finite tensor products. -/
abbrev Space (E : Finset ι) (e : ∀ i, V i) :=
  DirectLimit (fun S : Index E => Stage K V S.1) (systemMap K V E e)

/-- The universal linear map from a finite tensor stage. -/
def of (E : Finset ι) (e : ∀ i, V i) (S : Index E) :
    Stage K V S.1 →ₗ[K] Space K V E e :=
  DirectLimit.Module.of K (Index E) _ (systemMap K V E e) S

variable {K V}

@[simp]
theorem of_transition (E : Finset ι) (e : ∀ i, V i) {S T : Index E}
    (h : S ≤ T) (x : Stage K V S.1) :
    of K V E e T (transition e h x) = of K V E e S x :=
  DirectLimit.Module.of_f

/-- Equality of representatives means equality after transition to a common finite stage. -/
theorem of_eq_iff (E : Finset ι) (e : ∀ i, V i) {S T : Index E}
    (x : Stage K V S.1) (y : Stage K V T.1) :
    of K V E e S x = of K V E e T y ↔
      ∃ (U : Index E) (hSU : S ≤ U) (hTU : T ≤ U),
        transition e hSU x = transition e hTU y :=
  Quotient.eq

theorem exists_of (E : Finset ι) (e : ∀ i, V i) (x : Space K V E e) :
    ∃ (S : Index E) (y : Stage K V S.1), x = of K V E e S y :=
  DirectLimit.exists_eq_mk _ x

/-- Nonzero reference vectors ensure that each original finite stage embeds in the limit. -/
theorem of_injective (E : Finset ι) (e : ∀ i, V i) (he : ∀ i ∉ E, e i ≠ 0)
    (S : Index E) : Function.Injective (of K V E e S) :=
  DirectLimit.mk_injective (systemMap K V E e) (fun A _B h => transition_injective e h
    (fun i _ hi => he i (fun hiE => hi (A.2 hiE)))) S

variable {W : Type uW} [AddCommGroup W] [Module K W]

/-- Descend a compatible family of linear maps through the actual quotient. -/
def lift (E : Finset ι) (e : ∀ i, V i)
    (f : ∀ S : Index E, Stage K V S.1 →ₗ[K] W)
    (hf : ∀ (S T : Index E) (h : S ≤ T) x, f T (transition e h x) = f S x) :
    Space K V E e →ₗ[K] W :=
  DirectLimit.Module.lift K (Index E) _ (systemMap K V E e) f hf

@[simp]
theorem lift_of (E : Finset ι) (e : ∀ i, V i)
    (f : ∀ S : Index E, Stage K V S.1 →ₗ[K] W)
    (hf : ∀ (S T : Index E) (h : S ≤ T) x, f T (transition e h x) = f S x)
    (S : Index E) (x : Stage K V S.1) :
    lift E e f hf (of K V E e S x) = f S x := rfl

@[ext]
theorem hom_ext {E : Finset ι} {e : ∀ i, V i}
    {f g : Space K V E e →ₗ[K] W}
    (h : ∀ (S : Index E) x, f (of K V E e S x) = g (of K V E e S x)) : f = g := by
  apply LinearMap.ext
  intro x
  obtain ⟨S, y, rfl⟩ := exists_of E e x
  exact h S y

/-- An elementary tensor specified on a finite stage, with reference vectors elsewhere. -/
def pure (E : Finset ι) (e : ∀ i, V i) (S : Index E) (v : ∀ i : S.1, V i) :
    Space K V E e :=
  of K V E e S (PiTensorProduct.tprod K v)

@[simp]
theorem pure_extend (E : Finset ι) (e : ∀ i, V i) {S T : Index E}
    (h : S ≤ T) (v : ∀ i : S.1, V i) :
    pure E e T (extend e v) = pure (K := K) E e S v := by
  unfold pure
  rw [← transition_tprod e h, of_transition]

/-- Elementary tensors generate the restricted tensor product under sums and scalar multiples. -/
@[elab_as_elim]
theorem induction {E : Finset ι} {e : ∀ i, V i} {P : Space K V E e → Prop}
    (hpure : ∀ (S : Index E) v, P (pure E e S v))
    (hadd : ∀ x y, P x → P y → P (x + y))
    (hsmul : ∀ (a : K) x, P x → P (a • x)) (x : Space K V E e) : P x := by
  obtain ⟨S, y, rfl⟩ := exists_of E e x
  induction y using PiTensorProduct.induction_on with
  | smul_tprod a v =>
    simpa only [map_smul, pure] using hsmul a (pure E e S v) (hpure S v)
  | add x y hx hy =>
    simpa only [map_add] using hadd _ _ hx hy

theorem span_pure (E : Finset ι) (e : ∀ i, V i) :
    Submodule.span K {x : Space K V E e |
      ∃ S : Index E, ∃ v : ∀ i : S.1, V i, pure E e S v = x} = ⊤ := by
  apply Submodule.eq_top_iff'.mpr
  intro x
  induction x using induction with
  | hpure S v => exact Submodule.subset_span ⟨S, v, rfl⟩
  | hadd x y hx hy => exact Submodule.add_mem _ hx hy
  | hsmul a x hx => exact Submodule.smul_mem _ a hx

variable (V)

/-- Prescribed nonzero reference vectors only outside the finite exceptional set. -/
structure ReferenceVectors (E : Finset ι) where
  vector : ∀ i, i ∉ E → V i
  nonzero : ∀ i hi, vector i hi ≠ 0

namespace ReferenceVectors

variable {V} {E : Finset ι}

/-- Fill the unused exceptional coordinates with zero. No nonzero vector is required there. -/
def family (r : ReferenceVectors V E) (i : ι) : V i :=
  if hi : i ∈ E then 0 else r.vector i hi

@[simp]
theorem family_of_not_mem (r : ReferenceVectors V E) {i : ι} (hi : i ∉ E) :
    r.family i = r.vector i hi := by simp [family, hi]

theorem family_nonzero (r : ReferenceVectors V E) (i : ι) (hi : i ∉ E) :
    r.family i ≠ 0 := by simpa only [family_of_not_mem r hi] using r.nonzero i hi

end ReferenceVectors

variable (K)

/-- Flath's algebraic restricted tensor product, constructed as an actual directed limit. -/
abbrev Product (E : Finset ι) (r : ReferenceVectors V E) : Type (max uK uI uV) :=
  Space K V E r.family

/-- Every finite stage containing the exceptional set embeds into the restricted product. -/
theorem reference_of_injective (E : Finset ι) (r : ReferenceVectors V E) (S : Index E) :
    Function.Injective (of K V E r.family S) :=
  of_injective E r.family r.family_nonzero S

end Langlands.RestrictedTensor
