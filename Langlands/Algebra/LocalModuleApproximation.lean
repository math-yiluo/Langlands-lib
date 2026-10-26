import Langlands.Algebra.LocalApproximationCokernel
import Mathlib.Algebra.FiveLemma
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Data.Fintype.Order
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-! # Constructions of local module approximation systems -/

open scoped TensorProduct Matrix

universe uI uA uB uE uF uR uS uS' uM uN

namespace Langlands.Algebra

section lifts

variable {ι : Type uI} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
  {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]
  [IsLocalRing R] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]

namespace LocalAlgebraSystem

variable (D : LocalAlgebraSystem.{uI, uA, uB} ι R S)

/-- Every element of `S` comes from a component when the algebra colimit map is onto. -/
theorem exists_algι_eq (hD : Function.Surjective D.algebraColimitMap) (s : S) :
    ∃ i, ∃ x : D.alg i, D.algι i x = s := by
  obtain ⟨z, rfl⟩ := hD s
  obtain ⟨i, x, rfl⟩ := Ring.DirectLimit.exists_of z
  exact ⟨i, x, (D.algebraColimitMap_of i x).symm⟩

/-- Every element of `R` comes from a component when the base colimit map is onto. -/
theorem exists_baseι_eq (hD : Function.Surjective D.baseColimitMap) (r : R) :
    ∃ i, ∃ x : D.base i, D.baseι i x = r := by
  obtain ⟨z, rfl⟩ := hD r
  obtain ⟨i, x, rfl⟩ := Ring.DirectLimit.exists_of z
  exact ⟨i, x, (D.baseColimitMap_of i x).symm⟩

/-- A finite family of elements of `S` comes from one component. -/
theorem exists_algι_eq_fun (hD : Function.Surjective D.algebraColimitMap) {κ : Type*}
    [Finite κ] (s : κ → S) : ∃ i, ∃ x : κ → D.alg i, ∀ k, D.algι i (x k) = s k := by
  choose i x hx using fun k ↦ D.exists_algι_eq hD (s k)
  obtain ⟨j, hj⟩ := Finite.exists_le i
  exact ⟨j, fun k ↦ D.algMap (i k) j (hj k) (x k), fun k ↦ by rw [D.algι_compat, hx]⟩

/-- An algebra component element killed in `S` is killed by some transition. -/
theorem exists_algMap_eq_zero (hD : Function.Injective D.algebraColimitMap) {i : ι}
    (x : D.alg i) (hx : D.algι i x = 0) : ∃ j, ∃ h : i ≤ j, D.algMap i j h x = 0 := by
  have h0 : Ring.DirectLimit.of D.alg (fun i j h ↦ D.algMap i j h) i x = 0 :=
    hD (by rw [algebraColimitMap_of, hx, map_zero])
  exact Ring.DirectLimit.of.zero_exact h0

/-- A base component element killed in `R` is killed by some transition. -/
theorem exists_baseMap_eq_zero (hD : Function.Injective D.baseColimitMap) {i : ι}
    (x : D.base i) (hx : D.baseι i x = 0) : ∃ j, ∃ h : i ≤ j, D.baseMap i j h x = 0 := by
  have h0 : Ring.DirectLimit.of D.base (fun i j h ↦ D.baseMap i j h) i x = 0 :=
    hD (by rw [baseColimitMap_of, hx, map_zero])
  exact Ring.DirectLimit.of.zero_exact h0

/-- A finite family of algebra component elements killed in `S` is killed by one transition. -/
theorem exists_algMap_eq_zero_fun (hD : Function.Injective D.algebraColimitMap) {κ : Type*}
    [Finite κ] {i : ι} (x : κ → D.alg i) (hx : ∀ k, D.algι i (x k) = 0) :
    ∃ j, ∃ h : i ≤ j, ∀ k, D.algMap i j h (x k) = 0 := by
  choose j hij hj using fun k ↦ D.exists_algMap_eq_zero hD (x k) (hx k)
  obtain ⟨l, hl⟩ := Finite.exists_le (fun o : Option κ ↦ o.elim i j)
  refine ⟨l, hl none, fun k ↦ ?_⟩
  have hkl : j k ≤ l := hl (some k)
  rw [← DirectedSystem.map_map' D.algMap (hij k) hkl, hj, map_zero]

end LocalAlgebraSystem

end lifts

section tail

variable {ι : Type uI} [Preorder ι] [IsDirectedOrder ι]

/-- The indices above a fixed index form a nonempty preorder. -/
instance tailIndex_nonempty (i₀ : ι) : Nonempty {j : ι // i₀ ≤ j} := ⟨⟨i₀, le_rfl⟩⟩

/-- The indices above a fixed index form a directed preorder. -/
instance tailIndex_isDirectedOrder (i₀ : ι) : IsDirectedOrder {j : ι // i₀ ≤ j} where
  directed a b := by
    obtain ⟨c, hac, hbc⟩ := exists_ge_ge a.1 b.1
    exact ⟨⟨c, a.2.trans hac⟩, hac, hbc⟩

/-- A bijective ring direct-limit comparison stays bijective after restriction to a tail. -/
theorem ringDirectLimit_lift_tail_bijective [Nonempty ι] {A : ι → Type uA}
    [∀ i, CommRing (A i)] (f : ∀ i j, i ≤ j → A i →+* A j)
    [DirectedSystem A fun i j h ↦ f i j h] {T : Type uR} [CommRing T] (g : ∀ i, A i →+* T)
    (hg : ∀ i j h a, g j (f i j h a) = g i a)
    (hbij : Function.Bijective (Ring.DirectLimit.lift A (fun i j h ↦ f i j h) T g hg))
    (i₀ : ι) :
    Function.Bijective (Ring.DirectLimit.lift (fun j : {j : ι // i₀ ≤ j} ↦ A j.1)
      (fun j k h ↦ f j.1 k.1 h) T (fun j ↦ g j.1) (fun j k h a ↦ hg j.1 k.1 h a)) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz
    induction z using Ring.DirectLimit.induction_on with
    | ih j a =>
      rw [Ring.DirectLimit.lift_of] at hz
      have h0 : Ring.DirectLimit.of A (fun i j h ↦ f i j h) j.1 a = 0 :=
        hbij.1 (by rw [Ring.DirectLimit.lift_of, hz, map_zero])
      obtain ⟨k, hjk, hk⟩ := Ring.DirectLimit.of.zero_exact h0
      have hof : Ring.DirectLimit.of (fun j : {j : ι // i₀ ≤ j} ↦ A j.1)
          (fun j k h ↦ f j.1 k.1 h) ⟨k, j.2.trans hjk⟩ (f j.1 k hjk a) =
          Ring.DirectLimit.of (fun j : {j : ι // i₀ ≤ j} ↦ A j.1)
            (fun j k h ↦ f j.1 k.1 h) j a :=
        Ring.DirectLimit.of_f (G := fun j : {j : ι // i₀ ≤ j} ↦ A j.1)
          (f := fun j k h ↦ f j.1 k.1 h) (i := j) (j := ⟨k, j.2.trans hjk⟩) hjk a
      rw [← hof, hk, map_zero]
  · intro t
    obtain ⟨z, rfl⟩ := hbij.2 t
    induction z using Ring.DirectLimit.induction_on with
    | ih i a =>
      obtain ⟨k, hik, hk⟩ := exists_ge_ge i i₀
      refine ⟨Ring.DirectLimit.of _ _ (⟨k, hk⟩ : {j : ι // i₀ ≤ j}) (f i k hik a), ?_⟩
      rw [Ring.DirectLimit.lift_of, Ring.DirectLimit.lift_of, hg]

variable [Nonempty ι] {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]
  [IsLocalRing R] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]

namespace LocalAlgebraSystem

variable (D : LocalAlgebraSystem.{uI, uA, uB} ι R S)

/-- The restriction of a local algebra system to the indices above `i₀`, with the same
components, transitions and cocone maps. -/
def tail (i₀ : ι) : LocalAlgebraSystem.{uI, uA, uB} {j : ι // i₀ ≤ j} R S where
  base j := D.base j.1
  alg j := D.alg j.1
  structure_local j := D.structure_local j.1
  baseMap j k h := D.baseMap j.1 k.1 h
  algMap j k h := D.algMap j.1 k.1 h
  base_directed :=
    { map_self := by
        intro j x
        exact DirectedSystem.map_self' D.baseMap x
      map_map := by
        intro k j i hij hjk x
        exact DirectedSystem.map_map' D.baseMap hij hjk x }
  alg_directed :=
    { map_self := by
        intro j x
        exact DirectedSystem.map_self' D.algMap x
      map_map := by
        intro k j i hij hjk x
        exact DirectedSystem.map_map' D.algMap hij hjk x }
  baseMap_local j k h := D.baseMap_local j.1 k.1 h
  algMap_local j k h := D.algMap_local j.1 k.1 h
  map_comm j k h r := D.map_comm j.1 k.1 h r
  baseι j := D.baseι j.1
  algι j := D.algι j.1
  baseι_local j := D.baseι_local j.1
  algι_local j := D.algι_local j.1
  baseι_compat j k h r := D.baseι_compat j.1 k.1 h r
  algι_compat j k h s := D.algι_compat j.1 k.1 h s
  ι_comm j r := D.ι_comm j.1 r

/-- Restriction to a tail preserves the four approximation clauses. -/
theorem tail_isApproximation (hD : D.IsApproximation) (i₀ : ι) :
    (D.tail i₀).IsApproximation :=
  ⟨⟨ringDirectLimit_lift_tail_bijective D.baseMap D.baseι D.baseι_compat hD.1.1 i₀,
      ringDirectLimit_lift_tail_bijective D.algMap D.algι D.algι_compat hD.1.2 i₀⟩,
    fun j ↦ hD.2.1 j.1, fun j ↦ hD.2.2.1 j.1, fun j k h ↦ hD.2.2.2 j.1 k.1 h⟩

end LocalAlgebraSystem

end tail

section transport

variable {ι : Type uI} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
  {R : Type uR} {S : Type uS} {S' : Type uS'} [CommRing R] [CommRing S] [CommRing S']
  [IsLocalRing R] [IsLocalRing S] [IsLocalRing S'] [Algebra R S] [Algebra R S']
  [IsLocalHom (algebraMap R S)] [IsLocalHom (algebraMap R S')]

namespace LocalAlgebraSystem

variable (D : LocalAlgebraSystem.{uI, uA, uB} ι R S') (e : S' ≃ₐ[R] S)

/-- The same diagram of local rings, with the algebra cocone composed with an `R`-algebra
equivalence of cocone rings. -/
def mapAlgEquiv : LocalAlgebraSystem.{uI, uA, uB} ι R S where
  base := D.base
  alg := D.alg
  structure_local := D.structure_local
  baseMap := D.baseMap
  algMap := D.algMap
  base_directed := D.base_directed
  alg_directed := D.alg_directed
  baseMap_local := D.baseMap_local
  algMap_local := D.algMap_local
  map_comm := D.map_comm
  baseι := D.baseι
  algι i := (e : S' →+* S).comp (D.algι i)
  baseι_local := D.baseι_local
  algι_local i := by
    have := D.algι_local i
    refine ⟨fun a ha ↦ IsUnit.of_map (D.algι i) a ?_⟩
    have := ha.map (e.symm : S →+* S')
    simpa using this
  baseι_compat := D.baseι_compat
  algι_compat i j h s := congrArg e (D.algι_compat i j h s)
  ι_comm i r := by
    change e (D.algι i (algebraMap (D.base i) (D.alg i) r)) = algebraMap R S (D.baseι i r)
    rw [D.ι_comm, AlgEquiv.commutes]

/-- Transport of the algebra cocone along an algebra equivalence preserves approximation. -/
theorem mapAlgEquiv_isApproximation (hD : D.IsApproximation) :
    (D.mapAlgEquiv e).IsApproximation := by
  refine ⟨⟨hD.1.1, ?_⟩, hD.2.1, hD.2.2.1, hD.2.2.2⟩
  have heq : (D.mapAlgEquiv e).algebraColimitMap = (e : S' →+* S).comp D.algebraColimitMap := by
    ext i x
    exact ((D.mapAlgEquiv e).algebraColimitMap_of i x).trans
      (congrArg e (D.algebraColimitMap_of i x).symm)
  rw [heq]
  exact e.bijective.comp hD.1.2

end LocalAlgebraSystem

end transport

section modules

variable {ι : Type uI} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
  {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]
  [IsLocalRing R] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]

namespace LocalModuleSystem

variable {D : LocalAlgebraSystem.{uI, uA, uB} ι R S} {M : Type uM} [AddCommGroup M] [Module S M]
  (E : LocalModuleSystem.{uI, uA, uB, uE} D M)

/-- Every target element comes from a component when the additive colimit map is onto. -/
theorem exists_ιM_eq (hE : Function.Surjective E.moduleColimitMap) (m : M) :
    ∃ i, ∃ x : E.obj i, E.ιM i x = m := by
  obtain ⟨z, rfl⟩ := hE m
  induction z using AddCommGroup.DirectLimit.induction_on with
  | ih i x => exact ⟨i, x, (E.moduleColimitMap_of i x).symm⟩

/-- A component element killed in the target is killed by a transition when the additive
colimit map is injective. -/
theorem exists_map_eq_zero (hE : Function.Injective E.moduleColimitMap) {i : ι} (x : E.obj i)
    (hx : E.ιM i x = 0) : ∃ j, ∃ h : i ≤ j, E.map i j h x = 0 := by
  let := Classical.decEq ι
  have h0 : AddCommGroup.DirectLimit.of E.obj
      (fun i j h ↦ (E.map i j h).toAddMonoidHom) i x = 0 :=
    hE (by rw [moduleColimitMap_of, hx, map_zero])
  have : DirectedSystem E.obj fun i j h ↦ (E.map i j h).toAddMonoidHom := E.directed
  exact AddCommGroup.DirectLimit.of.zero_exact i x h0

/-- The additive colimit map is bijective when every target element comes from a component
and every component element killed in the target dies at a later stage. -/
theorem moduleColimitMap_bijective_of (hsurj : ∀ m, ∃ i, ∃ x : E.obj i, E.ιM i x = m)
    (hinj : ∀ i (x : E.obj i), E.ιM i x = 0 → ∃ j, ∃ h : i ≤ j, E.map i j h x = 0) :
    Function.Bijective E.moduleColimitMap := by
  let := Classical.decEq ι
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz
    induction z using AddCommGroup.DirectLimit.induction_on with
    | ih i x =>
      rw [moduleColimitMap_of] at hz
      obtain ⟨j, h, hj⟩ := hinj i x hz
      rw [← AddCommGroup.DirectLimit.of_f h x]
      exact (congrArg _ hj).trans (map_zero _)
  · intro m
    obtain ⟨i, x, rfl⟩ := hsurj m
    exact ⟨_, E.moduleColimitMap_of i x⟩

variable {M' : Type uN} [AddCommGroup M'] [Module S M']

/-- The same module diagram, with its cocone composed with a linear equivalence of targets. -/
def mapLinearEquiv (e : M ≃ₗ[S] M') : LocalModuleSystem.{uI, uA, uB, uE} D M' where
  obj := E.obj
  map := E.map
  directed := E.directed
  ιM i := e.toLinearMap.comp (E.ιM i)
  ιM_compat i j h m := congrArg e (E.ιM_compat i j h m)

/-- Transport of the module cocone along a linear equivalence preserves approximation. -/
theorem mapLinearEquiv_isApproximation (e : M ≃ₗ[S] M') (hE : E.IsApproximation) :
    (E.mapLinearEquiv e).IsApproximation := by
  refine ⟨⟨hE.1.1, (E.mapLinearEquiv e).moduleColimitMap_bijective_of (fun m ↦ ?_)
    (fun i x hx ↦ ?_)⟩, hE.2.1, hE.2.2.1, hE.2.2.2.1, hE.2.2.2.2.1, hE.2.2.2.2.2⟩
  · obtain ⟨i, x, hx⟩ := E.exists_ιM_eq hE.1.2.2 (e.symm m)
    refine ⟨i, x, ?_⟩
    change e (E.ιM i x) = m
    rw [hx, LinearEquiv.apply_symm_apply]
  · have hx' : e (E.ιM i x) = 0 := hx
    exact E.exists_map_eq_zero hE.1.2.1 x (e.map_eq_zero_iff.mp hx')

end LocalModuleSystem

namespace LocalAlgebraSystem

variable (D : LocalAlgebraSystem.{uI, uA, uB} ι R S) (κ : Type uE)

/-- The free module systems `κ → D.alg i`, with coordinatewise transitions and cocone maps
into `κ → S`. -/
def freeSystem : LocalModuleSystem.{uI, uA, uB, max uE uB} D (κ → S) where
  obj i := κ → D.alg i
  map i j h :=
    { toFun := fun v k ↦ D.algMap i j h (v k)
      map_add' := fun v w ↦ funext fun k ↦ map_add _ _ _
      map_smul' := fun s v ↦ funext fun k ↦ map_mul _ _ _ }
  directed :=
    { map_self := by
        intro i v
        funext k
        exact DirectedSystem.map_self' D.algMap (v k)
      map_map := by
        intro k j i hij hjk v
        funext l
        exact DirectedSystem.map_map' D.algMap hij hjk (v l) }
  ιM i :=
    { toFun := fun v k ↦ D.algι i (v k)
      map_add' := fun v w ↦ funext fun k ↦ map_add _ _ _
      map_smul' := fun s v ↦ funext fun k ↦ map_mul _ _ _ }
  ιM_compat i j h v := funext fun k ↦ D.algι_compat i j h (v k)

variable {κ}

/-- Finite free systems have bijective additive colimit maps over a ring colimit. -/
theorem freeSystem_moduleColimitMap_bijective [Finite κ]
    (hD : Function.Bijective D.algebraColimitMap) :
    Function.Bijective (D.freeSystem κ).moduleColimitMap := by
  refine (D.freeSystem κ).moduleColimitMap_bijective_of (fun v ↦ ?_) (fun i v hv ↦ ?_)
  · obtain ⟨i, x, hx⟩ := D.exists_algι_eq_fun hD.2 v
    exact ⟨i, x, funext hx⟩
  · obtain ⟨j, h, hj⟩ := D.exists_algMap_eq_zero_fun hD.1 v (fun k ↦ congrFun hv k)
    exact ⟨j, h, funext hj⟩

/-- The tensor transitions of finite free systems are bijective. -/
theorem freeSystem_moduleBaseChangeMap_bijective [Finite κ] {i j : ι} (h : i ≤ j) :
    Function.Bijective ((D.freeSystem κ).moduleBaseChangeMap h) := by
  classical
  have := Fintype.ofFinite κ
  let := (D.algMap i j h).toAlgebra
  have heq : ∀ x, (D.freeSystem κ).moduleBaseChangeMap h x =
      TensorProduct.piScalarRight (D.alg i) (D.alg j) (D.alg j) κ x := by
    intro x
    induction x with
    | tmul s v =>
      rw [LocalModuleSystem.moduleBaseChangeMap_tmul]
      refine Eq.trans ?_ ((TensorProduct.piScalarRight_apply (D.alg i) (D.alg j) (D.alg j) κ _).trans
        (TensorProduct.piScalarRightHom_tmul (D.alg i) (D.alg j) (D.alg j) κ s
          (show κ → D.alg i from v))).symm
      funext k
      change s * D.algMap i j h (v k) = D.algMap i j h (v k) * s
      exact mul_comm _ _
    | add x y hx hy =>
      exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)
  have hfun : ⇑((D.freeSystem κ).moduleBaseChangeMap h) =
      ⇑(TensorProduct.piScalarRight (D.alg i) (D.alg j) (D.alg j) κ) := funext heq
  rw [hfun]
  exact (TensorProduct.piScalarRight (D.alg i) (D.alg j) (D.alg j) κ).bijective

/-- Finite free systems over a ring approximation satisfy all six module clauses. -/
theorem freeSystem_isApproximation [Finite κ] (hD : D.IsApproximation) :
    (D.freeSystem κ).IsApproximation :=
  ⟨⟨hD.1, D.freeSystem_moduleColimitMap_bijective hD.1.2⟩, hD.2.1, hD.2.2.1,
    fun i ↦ by change Module.Finite (D.alg i) (κ → D.alg i); infer_instance, hD.2.2.2,
    fun _ _ h ↦ D.freeSystem_moduleBaseChangeMap_bijective h⟩

variable {ν : Type uF}

/-- Compatible component matrices give a compatible map of free systems over the matrix
map of the cocone ring. -/
def matrixMap [Fintype κ] (A : ∀ i, Matrix ν κ (D.alg i))
    (hA : ∀ i j h, (A i).map (D.algMap i j h) = A j) (B : Matrix ν κ S)
    (hB : ∀ i, (A i).map (D.algι i) = B) :
    LocalModuleSystem.CompatibleMap (D.freeSystem κ) (D.freeSystem ν) B.mulVecLin where
  component i := (A i).mulVecLin
  map_comm i j h v := by
    funext l
    have hl := RingHom.map_mulVec (D.algMap i j h) (A i) (show κ → D.alg i from v) l
    rw [hA] at hl
    exact hl.symm
  ιM_comm i v := by
    funext l
    have hl := RingHom.map_mulVec (D.algι i) (A i) (show κ → D.alg i from v) l
    rw [hB] at hl
    exact hl

end LocalAlgebraSystem

namespace LocalModuleSystem.CompatibleMap

variable {D : LocalAlgebraSystem.{uI, uA, uB} ι R S}
  {M : Type uM} {N : Type uN} [AddCommGroup M] [AddCommGroup N] [Module S M] [Module S N]
  {E : LocalModuleSystem.{uI, uA, uB, uE} D M}
  {F : LocalModuleSystem.{uI, uA, uB, uF} D N} {f : M →ₗ[S] N}
  (φ : CompatibleMap E F f)

/-- The cokernel system has bijective tensor transitions when those of the source are onto
and those of the target are bijective. -/
theorem cokernelSystem_moduleBaseChangeMap_bijective {i j : ι} (h : i ≤ j)
    (hE : Function.Surjective (E.moduleBaseChangeMap h))
    (hF : Function.Bijective (F.moduleBaseChangeMap h)) :
    Function.Bijective (φ.cokernelSystem.moduleBaseChangeMap h) := by
  let := (D.algMap i j h).toAlgebra
  refine LinearMap.bijective_of_surjective_of_bijective_of_right_exact
    ((φ.component i).baseChange (D.alg j))
    ((LinearMap.range (φ.component i)).mkQ.baseChange (D.alg j))
    (φ.component j) (LinearMap.range (φ.component j)).mkQ
    (E.moduleBaseChangeMap h) (F.moduleBaseChangeMap h) (φ.cokernelSystem.moduleBaseChangeMap h)
    ?_ ?_ ?_ (LinearMap.exact_map_mkQ_range _) hE hF ?_ (Submodule.mkQ_surjective _)
  · refine LinearMap.ext fun x ↦ ?_
    induction x with
    | tmul s m =>
      simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul, moduleBaseChangeMap_tmul,
        map_smul, φ.map_comm]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  · refine LinearMap.ext fun x ↦ ?_
    induction x with
    | tmul s n =>
      simp only [LinearMap.comp_apply, moduleBaseChangeMap_tmul, map_smul]
      rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  · exact lTensor_exact (D.alg j) (LinearMap.exact_map_mkQ_range _)
      (Submodule.mkQ_surjective _)
  · exact LinearMap.lTensor_surjective (D.alg j) (Submodule.mkQ_surjective _)

/-- Components of the cokernel system are finite when those of the target system are. -/
theorem cokernelSystem_finite (i : ι) [Module.Finite (D.alg i) (F.obj i)] :
    Module.Finite (D.alg i) (φ.cokernelSystem.obj i) := by
  change Module.Finite (D.alg i) (F.obj i ⧸ LinearMap.range (φ.component i))
  infer_instance

/-- The cokernel of a compatible map of approximation systems is an approximation system,
provided its additive colimit comparison is bijective. -/
theorem cokernelSystem_isApproximation (hφ : φ.IsApproximation)
    (hC : Function.Bijective φ.cokernelSystem.moduleColimitMap) :
    φ.cokernelSystem.IsApproximation := by
  obtain ⟨hE, hF⟩ := hφ
  refine ⟨⟨hF.1.1, hC⟩, hF.2.1, hF.2.2.1, fun i ↦ ?_, hF.2.2.2.2.1, fun i j h ↦
      φ.cokernelSystem_moduleBaseChangeMap_bijective h (hE.2.2.2.2.2 i j h).2
        (hF.2.2.2.2.2 i j h)⟩
  have := hF.2.2.2.1 i
  exact φ.cokernelSystem_finite i

end LocalModuleSystem.CompatibleMap

end modules

/-- A finitely presented module is the cokernel of a matrix between finite free modules. -/
theorem exists_matrix_presentation (S : Type uS) (M : Type uM) [CommRing S] [AddCommGroup M]
    [Module S M] [Module.FinitePresentation S M] :
    ∃ (n m : ℕ) (A : Matrix (Fin n) (Fin m) S),
      Nonempty (((Fin n → S) ⧸ LinearMap.range A.mulVecLin) ≃ₗ[S] M) := by
  obtain ⟨n, K, e, hK⟩ := Module.FinitePresentation.exists_fin S M
  obtain ⟨m, g, hg⟩ := K.fg_iff_exists_fin_linearMap.mp hK
  refine ⟨n, m, LinearMap.toMatrix' g, ⟨(Submodule.quotEquivOfEq _ _ ?_).trans e.symm⟩⟩
  rw [← Matrix.toLin'_apply', Matrix.toLin'_toMatrix', hg]

end Langlands.Algebra
