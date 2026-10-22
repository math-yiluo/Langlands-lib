import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.PiTensorProduct.Finite
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RingTheory.SimpleModule.Basic
import Langlands.Representation.Tensor.Finite
import Langlands.Representation.Jacquet.Coinvariants

/-!
# Irreducibility, admissibility and Jacquet vanishing of finite external tensors

For a finite family of representations over a field, the actual external tensor
product `FiniteTensor.external` is irreducible when every factor is irreducible
with only scalar self-intertwiners, is admissible when every factor is admissible,
and has zero coinvariants for a product subgroup as soon as one factor does.
-/

noncomputable section

open scoped TensorProduct
open Function Module

namespace Langlands.FiniteTensor

universe uk uI uG uV uW uX uA

variable {k : Type uk} [Field k]

section Density

variable {G : Type uG} [Group G] {W : Type uW} [AddCommGroup W] [Module k W]

/-- Jacobson density for an irreducible representation whose self-intertwiners
are scalars: every linear endomorphism agrees with the action of some group
algebra element on any finite set of vectors. -/
theorem exists_asAlgebraHom_eq_on (σ : Representation k G W) [σ.IsIrreducible]
    (hS : ∀ φ : σ.IntertwiningMap σ,
      ∃ c : k, φ = c • Representation.IntertwiningMap.id σ)
    (f : W →ₗ[k] W) (s : Finset W) :
    ∃ r : MonoidAlgebra k G, ∀ w ∈ s, σ.asAlgebraHom r w = f w := by
  let f' : Module.End (Module.End (MonoidAlgebra k G) σ.asModule) σ.asModule :=
    { toFun := fun m => σ.asModuleEquiv.symm (f (σ.asModuleEquiv m))
      map_add' := fun m m' => by simp
      map_smul' := by
        intro φ m
        obtain ⟨c, hc⟩ := hS
          ((Representation.IntertwiningMap.equivLinearMapAsModule σ σ).symm φ)
        have hφ : ∀ m : σ.asModule,
            φ m = σ.asModuleEquiv.symm (c • σ.asModuleEquiv m) := fun m =>
          congrArg (fun ψ : σ.IntertwiningMap σ => ψ m) hc
        change σ.asModuleEquiv.symm (f (σ.asModuleEquiv (φ m))) =
          φ (σ.asModuleEquiv.symm (f (σ.asModuleEquiv m)))
        rw [hφ, hφ]
        simp }
  obtain ⟨r, hr⟩ := jacobson_density f' s
  exact ⟨r, fun w hw => (hr w hw).symm⟩

end Density

section Slots

variable {ι : Type uI} [Fintype ι] [DecidableEq ι]
variable {V : ι → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]

/-- A linear endomorphism in one slot and identities in all other slots. -/
abbrev slot (j : ι) (T : V j →ₗ[k] V j) : ∀ i, V i →ₗ[k] V i :=
  update (fun _ => LinearMap.id) j T

omit [Fintype ι] in
theorem slot_apply_update (j : ι) (T : V j →ₗ[k] V j) (v : ∀ i, V i) (w : V j) :
    (fun i => slot j T i (update v j w i)) = update v j (T w) := by
  funext i
  by_cases hi : i = j
  · subst hi
    simp [slot]
  · simp [slot, hi]

omit [Fintype ι] in
theorem map_slot_tprod_update (j : ι) (T : V j →ₗ[k] V j) (v : ∀ i, V i) (w : V j) :
    PiTensorProduct.map (slot j T) (PiTensorProduct.tprod k (update v j w)) =
      PiTensorProduct.tprod k (update v j (T w)) := by
  rw [PiTensorProduct.map_tprod, slot_apply_update]

/-- A property preserved by every one-slot factor of a tensor map is
preserved by the whole tensor map. -/
theorem map_induction (f : ∀ i, V i →ₗ[k] V i) (P : (⨂[k] i, V i) → Prop)
    (h : ∀ j y, P y → P (PiTensorProduct.map (slot j (f j)) y))
    (x : ⨂[k] i, V i) (hx : P x) : P (PiTensorProduct.map f x) := by
  have key : ∀ S : Finset ι, ∀ y, P y →
      P (PiTensorProduct.map (fun i => if i ∈ S then f i else LinearMap.id) y) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro y hy
      simpa [PiTensorProduct.map_id] using hy
    | insert a S ha ih =>
      intro y hy
      have hfam : (fun i => if i ∈ insert a S then f i else LinearMap.id) =
          fun i => (if i ∈ S then f i else LinearMap.id) ∘ₗ slot a (f a) i := by
        funext i
        by_cases hi : i = a
        · subst hi
          simp [slot, ha]
        · simp [slot, hi]
      rw [hfam, PiTensorProduct.map_comp, LinearMap.comp_apply]
      exact ih _ (h a y hy)
  simpa using key Finset.univ x hx

omit [Fintype ι] in
/-- Splitting off one slot turns a one-slot tensor map into `lTensor`. -/
theorem split_map_slot (j : ι) (T : V j →ₗ[k] V j) (x : ⨂[k] i, V i) :
    PiTensorProduct.equivPiTensorComplSingletonTensor k V j
        (PiTensorProduct.map (slot j T) x) =
      LinearMap.lTensor _ T (PiTensorProduct.equivPiTensorComplSingletonTensor k V j x) := by
  have h : (PiTensorProduct.equivPiTensorComplSingletonTensor k V j).toLinearMap ∘ₗ
        PiTensorProduct.map (slot j T) =
      LinearMap.lTensor _ T ∘ₗ
        (PiTensorProduct.equivPiTensorComplSingletonTensor k V j).toLinearMap := by
    ext v
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, comp_apply,
      PiTensorProduct.map_tprod, LinearEquiv.coe_coe,
      PiTensorProduct.equivPiTensorComplSingletonTensor_tprod, LinearMap.lTensor_tmul]
    congr 1
    · congr 1
      funext i
      have hi : (i : ι) ≠ j := i.property
      simp [slot, hi]
    · simp [slot]
  exact LinearMap.congr_fun h x

/-- In `X ⊗ W`, a vector fixed by `lTensor` of a family of maps is fixed by
`lTensor` of any map fixing all vectors fixed by that family. -/
theorem lTensor_eq_of_forall_fixed {X : Type uX} [AddCommGroup X] [Module k X]
    {W : Type uW} [AddCommGroup W] [Module k W] {A : Type uA}
    (T : A → W →ₗ[k] W) (π : W →ₗ[k] W) (hπ : ∀ w, (∀ a, T a w = w) → π w = w)
    (y : X ⊗[k] W) (hy : ∀ a, LinearMap.lTensor X (T a) y = y) :
    LinearMap.lTensor X π y = y := by
  classical
  let b := Basis.ofVectorSpace k X
  let c := Basis.ofVectorSpace k W
  let Φ : Basis.ofVectorSpaceIndex k X → X ⊗[k] W →ₗ[k] W := fun κ =>
    (TensorProduct.lid k W).toLinearMap ∘ₗ LinearMap.rTensor W (b.coord κ)
  have hΦ : ∀ κ (S : W →ₗ[k] W) z, Φ κ (LinearMap.lTensor X S z) = S (Φ κ z) := by
    intro κ S z
    induction z with
    | tmul x w => simp [Φ]
    | add z z' hz hz' => rw [map_add, map_add, hz, hz', map_add, map_add]
  have hrepr : ∀ κ μ (z : X ⊗[k] W),
      (b.tensorProduct c).repr z (κ, μ) = c.repr (Φ κ z) μ := by
    intro κ μ z
    induction z with
    | tmul x w =>
      simp [Φ, Basis.tensorProduct_repr_tmul_apply, mul_comm]
    | add z z' hz hz' => simp only [map_add, Finsupp.add_apply, hz, hz']
  have hfix : ∀ κ, π (Φ κ y) = Φ κ y := fun κ =>
    hπ _ (fun a => by rw [← hΦ, hy a])
  rw [← sub_eq_zero]
  refine (b.tensorProduct c).ext_elem_iff.mpr ?_
  rintro ⟨κ, μ⟩
  rw [hrepr, map_sub, hΦ, hfix, sub_self]
  simp

omit [Fintype ι] in
/-- One-slot version of `lTensor_eq_of_forall_fixed` in an indexed tensor. -/
theorem map_slot_eq_of_forall_fixed (j : ι) {A : Type uA} (T : A → V j →ₗ[k] V j)
    (π : V j →ₗ[k] V j) (hπ : ∀ w, (∀ a, T a w = w) → π w = w)
    (x : ⨂[k] i, V i) (hx : ∀ a, PiTensorProduct.map (slot j (T a)) x = x) :
    PiTensorProduct.map (slot j π) x = x := by
  apply (PiTensorProduct.equivPiTensorComplSingletonTensor k V j).injective
  rw [split_map_slot]
  exact lTensor_eq_of_forall_fixed T π hπ _ (fun a => by rw [← split_map_slot, hx a])

/-- A vector fixed slotwise by families of maps is fixed by the tensor product
of maps fixing their common fixed vectors. -/
theorem map_eq_of_forall_fixed {A : ι → Type uA} (T : ∀ i, A i → V i →ₗ[k] V i)
    (π : ∀ i, V i →ₗ[k] V i) (hπ : ∀ i w, (∀ a, T i a w = w) → π i w = w)
    (x : ⨂[k] i, V i) (hx : ∀ j a, PiTensorProduct.map (slot j (T j a)) x = x) :
    PiTensorProduct.map π x = x :=
  map_induction π (fun y => y = x) (fun j y hy => by
      subst hy
      exact map_slot_eq_of_forall_fixed j (T j) (π j) (hπ j) _ (hx j)) x rfl

end Slots

section External

variable {ι : Type uI} [Fintype ι] [DecidableEq ι]
variable {V : ι → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
variable {H : ι → Type uG} [∀ i, Group (H i)]

omit [Fintype ι] in
/-- A coordinate element of the product group acts in its own slot only. -/
theorem external_mulSingle (ρ : ∀ i, Representation k (H i) (V i)) (j : ι) (h : H j) :
    external ρ (Pi.mulSingle j h) = PiTensorProduct.map (slot j (ρ j h)) := by
  change PiTensorProduct.map (fun i => ρ i (Pi.mulSingle j h i)) = _
  congr 1
  funext i
  by_cases hi : i = j
  · subst hi
    simp [slot]
  · simp [slot, hi, Module.End.one_eq_id]

omit [Fintype ι] in
/-- Subrepresentations are stable under group algebra elements acting in one slot. -/
theorem map_slot_asAlgebraHom_mem (ρ : ∀ i, Representation k (H i) (V i))
    (U : Subrepresentation (external ρ)) (j : ι) (a : MonoidAlgebra k (H j))
    (x : ⨂[k] i, V i) (hx : x ∈ U) :
    PiTensorProduct.map (slot j ((ρ j).asAlgebraHom a)) x ∈ U := by
  induction a using MonoidAlgebra.induction_linear with
  | zero =>
    have h0 : PiTensorProduct.map (slot j (0 : V j →ₗ[k] V j)) = 0 :=
      (PiTensorProduct.mapMultilinear k V V).map_update_zero _ j
    rw [map_zero, h0, LinearMap.zero_apply]
    exact U.toSubmodule.zero_mem
  | add a a' ha ha' =>
    rw [map_add, slot, PiTensorProduct.map_update_add, LinearMap.add_apply]
    exact U.toSubmodule.add_mem ha ha'
  | single g c =>
    rw [Representation.asAlgebraHom_single, slot, PiTensorProduct.map_update_smul,
      LinearMap.smul_apply, ← slot, ← external_mulSingle]
    exact U.toSubmodule.smul_mem c (U.apply_mem_toSubmodule _ hx)

/-- Subrepresentations are stable under tensor products of group algebra actions. -/
theorem map_asAlgebraHom_mem (ρ : ∀ i, Representation k (H i) (V i))
    (U : Subrepresentation (external ρ)) (r : ∀ i, MonoidAlgebra k (H i))
    (x : ⨂[k] i, V i) (hx : x ∈ U) :
    PiTensorProduct.map (fun i => (ρ i).asAlgebraHom (r i)) x ∈ U :=
  map_induction _ (· ∈ U) (fun j y hy => map_slot_asAlgebraHom_mem ρ U j (r j) y hy) x hx

/-- The external tensor product of irreducible factors with scalar
self-intertwiners is irreducible. -/
theorem isIrreducible_external (ρ : ∀ i, Representation k (H i) (V i))
    [∀ i, (ρ i).IsIrreducible]
    (hS : ∀ i, ∀ φ : (ρ i).IntertwiningMap (ρ i),
      ∃ c : k, φ = c • Representation.IntertwiningMap.id (ρ i)) :
    (external ρ).IsIrreducible := by
  classical
  let b := fun i => Basis.ofVectorSpace k (V i)
  let Bt := Basis.piTensorProduct b
  have hne : ∃ x : ⨂[k] i, V i, x ≠ 0 := by
    have hp : ∀ i, Nonempty (Basis.ofVectorSpaceIndex k (V i)) := fun i => by
      have : Nontrivial (V i) :=
        IsSimpleModule.nontrivial (MonoidAlgebra k (H i)) (ρ i).asModule
      exact (b i).index_nonempty
    exact ⟨Bt (fun i => Classical.choice (hp i)), Bt.ne_zero _⟩
  have hmain : ∀ U : Subrepresentation (external ρ), ∀ x ∈ U, x ≠ 0 → U = ⊤ := by
    intro U x hxU hx0
    obtain ⟨p, hp⟩ : ∃ p, Bt.repr x p ≠ 0 := by
      by_contra h
      push Not at h
      exact hx0 (Bt.ext_elem_iff.mpr (fun q => by simp [h q]))
    have htprod : ∀ u : ∀ i, V i, PiTensorProduct.tprod k u ∈ U := by
      intro u
      let f : ∀ i, V i →ₗ[k] V i := fun i => ((b i).coord (p i)).smulRight (u i)
      have hf : PiTensorProduct.map f x = Bt.repr x p • PiTensorProduct.tprod k u := by
        have hmap : PiTensorProduct.map f =
            (Bt.coord p).smulRight (PiTensorProduct.tprod k u) := by
          ext v
          simp [f, Bt, Basis.piTensorProduct_repr_tprod_apply, MultilinearMap.map_smul_univ]
        rw [hmap]
        rfl
      let s : ∀ i, Finset (V i) := fun i => (Bt.repr x).support.image (fun q => b i (q i))
      have hr : ∀ i, ∃ r : MonoidAlgebra k (H i), ∀ w ∈ s i,
          (ρ i).asAlgebraHom r w = f i w :=
        fun i => exists_asAlgebraHom_eq_on (ρ i) (hS i) (f i) (s i)
      choose r hr using hr
      have hagree : PiTensorProduct.map (fun i => (ρ i).asAlgebraHom (r i)) x =
          PiTensorProduct.map f x := by
        rw [← Bt.linearCombination_repr x, Finsupp.linearCombination_apply,
          map_finsuppSum, map_finsuppSum]
        refine Finsupp.sum_congr (fun q hq => ?_)
        rw [map_smul, map_smul, Basis.piTensorProduct_apply, PiTensorProduct.map_tprod,
          PiTensorProduct.map_tprod]
        congr 2
        funext i
        exact hr i _ (Finset.mem_image_of_mem _ hq)
      have hmem : PiTensorProduct.map f x ∈ U :=
        hagree ▸ map_asAlgebraHom_mem ρ U r x hxU
      rw [hf] at hmem
      have h := U.toSubmodule.smul_mem (Bt.repr x p)⁻¹ hmem
      rwa [smul_smul, inv_mul_cancel₀ hp, one_smul] at h
    apply Subrepresentation.ext
    apply eq_top_iff.mpr
    rw [← PiTensorProduct.span_tprod_eq_top]
    exact Submodule.span_le.mpr (by rintro _ ⟨u, rfl⟩; exact htprod u)
  obtain ⟨x0, hx0⟩ := hne
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h => hx0 ?_⟩, eq_bot_or_eq_top := fun U => ?_ }
  · have hx : x0 ∈ (⊤ : Subrepresentation (external ρ)) := Submodule.mem_top
    rw [← h] at hx
    exact (Submodule.mem_bot k).mp hx
  · by_cases hU : ∃ x ∈ U, x ≠ 0
    · obtain ⟨x, hx, hx0⟩ := hU
      exact Or.inr (hmain U x hx hx0)
    · left
      push Not at hU
      apply Subrepresentation.ext
      exact (Submodule.eq_bot_iff _).mpr hU

/-- Fixed vectors of a product subgroup lie in the tensor product of the
factorwise fixed vectors. -/
theorem fixedVectors_external_le (ρ : ∀ i, Representation k (H i) (V i))
    (K : ∀ i, Subgroup (H i)) :
    fixedVectors (external ρ) (Subgroup.pi Set.univ K) ≤
      LinearMap.range (PiTensorProduct.map fun i => (fixedVectors (ρ i) (K i)).subtype) := by
  intro x hx
  have hfix : ∀ g ∈ Subgroup.pi Set.univ K, external ρ g x = x := fun g hg => hx ⟨g, hg⟩
  have hcompl : ∀ i, ∃ C : Submodule k (V i), IsCompl (fixedVectors (ρ i) (K i)) C :=
    fun i => Submodule.exists_isCompl _
  choose C hC using hcompl
  let p : ∀ i, V i →ₗ[k] fixedVectors (ρ i) (K i) := fun i =>
    Submodule.projectionOnto _ (C i) (hC i)
  let π : ∀ i, V i →ₗ[k] V i := fun i => (fixedVectors (ρ i) (K i)).subtype ∘ₗ p i
  have hx' : PiTensorProduct.map π x = x := by
    refine map_eq_of_forall_fixed (A := fun i => K i) (fun i a => ρ i a) π ?_ x ?_
    · intro i w hw
      have hmem : w ∈ fixedVectors (ρ i) (K i) := fun a => hw a
      simp [π, p, Submodule.projectionOnto_apply_of_mem_left (hC i) hmem]
    · intro j a
      rw [← external_mulSingle]
      exact hfix _ ((Subgroup.mulSingle_mem_pi j (a : H j)).mpr (fun _ => a.property))
  refine ⟨PiTensorProduct.map p x, ?_⟩
  rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
  exact hx'

/-- Coinvariants vanish exactly when every vector is a relation. -/
theorem subsingleton_coinvariants_iff {G : Type uG} [Group G]
    {W : Type uW} [AddCommGroup W] [Module k W]
    (σ : Representation k G W) (N : Subgroup G) :
    Subsingleton (Jacquet.Coinvariants σ N) ↔ ∀ w, w ∈ Jacquet.relations σ N := by
  constructor
  · intro h w
    rw [← Jacquet.mk_eq_zero]
    exact Subsingleton.elim _ _
  · intro h
    refine ⟨fun a b => ?_⟩
    obtain ⟨v, rfl⟩ := Jacquet.mk_surjective σ N a
    obtain ⟨w, rfl⟩ := Jacquet.mk_surjective σ N b
    rw [(Jacquet.mk_eq_zero σ N v).mpr (h v), (Jacquet.mk_eq_zero σ N w).mpr (h w)]

omit [Fintype ι] in
/-- If one factor has zero coinvariants for its subgroup, the external tensor
product has zero coinvariants for the product subgroup. -/
theorem coinvariants_external_subsingleton (ρ : ∀ i, Representation k (H i) (V i))
    (N : ∀ i, Subgroup (H i)) (j : ι)
    (hj : Subsingleton (Jacquet.Coinvariants (ρ j) (N j))) :
    Subsingleton (Jacquet.Coinvariants (external ρ) (Subgroup.pi Set.univ N)) := by
  rw [subsingleton_coinvariants_iff] at hj ⊢
  have htprod : ∀ v : ∀ i, V i, PiTensorProduct.tprod k v ∈
      Jacquet.relations (external ρ) (Subgroup.pi Set.univ N) := by
    intro v
    let e : V j →ₗ[k] ⨂[k] i, V i := (PiTensorProduct.tprod k).toLinearMap v j
    have hle : Jacquet.relations (ρ j) (N j) ≤
        (Jacquet.relations (external ρ) (Subgroup.pi Set.univ N)).comap e := by
      rw [Jacquet.relations_eq_span]
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨⟨n, w⟩, rfl⟩
      have hn : Pi.mulSingle j (n : H j) ∈ Subgroup.pi Set.univ N :=
        (Subgroup.mulSingle_mem_pi j _).mpr (fun _ => n.property)
      have h := Jacquet.sub_mem_relations (external ρ) (Subgroup.pi Set.univ N) ⟨_, hn⟩ (e w)
      have he : e (ρ j n w) = external ρ (Pi.mulSingle j (n : H j)) (e w) := by
        simp only [e, MultilinearMap.toLinearMap_apply, external_mulSingle,
          map_slot_tprod_update]
      change e (ρ j n w - w) ∈ Jacquet.relations (external ρ) (Subgroup.pi Set.univ N)
      rw [map_sub, he]
      exact h
    have h := hle (hj (v j))
    simpa [e, MultilinearMap.toLinearMap_apply] using h
  intro x
  have hx : x ∈ Submodule.span k (Set.range (PiTensorProduct.tprod k (s := V))) := by
    rw [PiTensorProduct.span_tprod_eq_top]
    exact Submodule.mem_top
  exact (Submodule.span_le.mpr (by rintro _ ⟨v, rfl⟩; exact htprod v)) hx

variable [∀ i, TopologicalSpace (H i)]

/-- Finite external tensor products of admissible factors are admissible. -/
theorem isAdmissible_external (ρ : ∀ i, Representation k (H i) (V i))
    (hρ : ∀ i, IsAdmissible (ρ i)) : IsAdmissible (external ρ) := by
  refine ⟨isSmooth_external ρ (fun i => (hρ i).1), fun K => ?_⟩
  let K' : ∀ i, OpenSubgroup (H i) := fun i =>
    K.comap (MonoidHom.mulSingle H i) (continuous_mulSingle i)
  have hle : Subgroup.pi Set.univ (fun i => (K' i).toSubgroup) ≤ K.toSubgroup := by
    intro g hg
    exact Subgroup.pi_mem_of_mulSingle_mem g (fun i => hg i (Set.mem_univ i))
  have hfix : fixedVectors (external ρ) K.toSubgroup ≤
      fixedVectors (external ρ) (Subgroup.pi Set.univ fun i => (K' i).toSubgroup) := by
    intro x hx g
    exact hx ⟨g, hle g.property⟩
  have : ∀ i, Module.Finite k (fixedVectors (ρ i) (K' i).toSubgroup) :=
    fun i => (hρ i).2 (K' i)
  exact Submodule.finiteDimensional_of_le (hfix.trans (fixedVectors_external_le ρ _))

end External

end Langlands.FiniteTensor
