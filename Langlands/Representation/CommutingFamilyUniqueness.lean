import Langlands.Representation.RestrictedTensor.CyclicEvaluation
import Langlands.Representation.RestrictedTensor.Maps
import Langlands.Representation.Tensor.FiniteProperties
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Uniqueness for commuting families of isotypic local actions

Let `σ i` (`i : ι`) be pairwise commuting actions of monoids `G i` on a vector space `V`,
jointly irreducible, and let `σ' i` be such a family on `V'`. If at every index both are
isotypic of the type of one irreducible representation `τ i` with scalar self-intertwiners,
and for almost all `i` the vectors of `τ i` fixed by a set `H i` form at most a line while every
vector of `V` and of `V'` is fixed by `H i` for almost all `i`, then `V` and `V'` are
isomorphic by a linear isomorphism intertwining every `σ i` with `σ' i`.
-/

noncomputable section
open scoped Classical TensorProduct

namespace Langlands.CommutingFamily

open Langlands.RestrictedTensor Langlands.RestrictedTensor.CyclicEvaluation

universe uk uI uG uV uV' uW uX

/-! ## Jacobson density for monoid representations -/

section Density

variable {k : Type uk} [Field k] {G : Type uG} [Monoid G]
  {W : Type uW} [AddCommGroup W] [Module k W]

/-- Jacobson density for an irreducible monoid representation whose self-intertwiners are
scalars: every linear endomorphism agrees with the action of some monoid algebra element on
any finite set of vectors. -/
theorem exists_asAlgebraHom_eq_on (τ : Representation k G W) [τ.IsIrreducible]
    (hS : ∀ φ : τ.IntertwiningMap τ,
      ∃ c : k, φ = c • Representation.IntertwiningMap.id τ)
    (f : W →ₗ[k] W) (s : Finset W) :
    ∃ r : MonoidAlgebra k G, ∀ w ∈ s, τ.asAlgebraHom r w = f w := by
  let f' : Module.End (Module.End (MonoidAlgebra k G) τ.asModule) τ.asModule :=
    { toFun := fun m => τ.asModuleEquiv.symm (f (τ.asModuleEquiv m))
      map_add' := fun m m' => by simp
      map_smul' := by
        intro φ m
        obtain ⟨c, hc⟩ := hS
          ((Representation.IntertwiningMap.equivLinearMapAsModule τ τ).symm φ)
        have hφ : ∀ m : τ.asModule,
            φ m = τ.asModuleEquiv.symm (c • τ.asModuleEquiv m) := fun m =>
          congrArg (fun ψ : τ.IntertwiningMap τ => ψ m) hc
        change τ.asModuleEquiv.symm (f (τ.asModuleEquiv (φ m))) =
          φ (τ.asModuleEquiv.symm (f (τ.asModuleEquiv m)))
        rw [hφ, hφ]
        simp }
  obtain ⟨r, hr⟩ := jacobson_density f' s
  exact ⟨r, fun w hw => (hr w hw).symm⟩

end Density

/-! ## Irreducibility of finite tensor products under slot actions -/

section Tensor

variable {k : Type uk} [Field k] {J : Type uI} [Fintype J] [DecidableEq J]
  {H : J → Type uG} [∀ j, Monoid (H j)]
  {X : J → Type uX} [∀ j, AddCommGroup (X j)] [∀ j, Module k (X j)]

open FiniteTensor Module

omit [Fintype J] in
/-- A subspace stable under every one-slot monoid action is stable under one-slot monoid
algebra actions. -/
theorem map_slot_asAlgebraHom_mem (ρ : ∀ j, Representation k (H j) (X j))
    (U : Submodule k (⨂[k] j, X j))
    (hU : ∀ j (g : H j), ∀ x ∈ U, PiTensorProduct.map (slot j (ρ j g)) x ∈ U)
    (j : J) (a : MonoidAlgebra k (H j)) (x : ⨂[k] j, X j) (hx : x ∈ U) :
    PiTensorProduct.map (slot j ((ρ j).asAlgebraHom a)) x ∈ U := by
  induction a using MonoidAlgebra.induction_linear with
  | zero =>
    have h0 : PiTensorProduct.map (slot j (0 : X j →ₗ[k] X j)) = 0 :=
      (PiTensorProduct.mapMultilinear k X X).map_update_zero _ j
    rw [map_zero, h0, LinearMap.zero_apply]
    exact U.zero_mem
  | add a a' ha ha' =>
    rw [map_add, slot, PiTensorProduct.map_update_add, LinearMap.add_apply]
    exact U.add_mem ha ha'
  | single g c =>
    rw [Representation.asAlgebraHom_single, slot, PiTensorProduct.map_update_smul,
      LinearMap.smul_apply, ← slot]
    exact U.smul_mem c (hU j g x hx)

/-- A nonzero subspace of a finite tensor product of irreducible monoid representations with
scalar self-intertwiners, stable under every one-slot action, is everything. -/
theorem eq_top_of_slot_stable (ρ : ∀ j, Representation k (H j) (X j))
    [∀ j, (ρ j).IsIrreducible]
    (hS : ∀ j, ∀ φ : (ρ j).IntertwiningMap (ρ j),
      ∃ c : k, φ = c • Representation.IntertwiningMap.id (ρ j))
    (U : Submodule k (⨂[k] j, X j))
    (hU : ∀ j (g : H j), ∀ x ∈ U, PiTensorProduct.map (slot j (ρ j g)) x ∈ U)
    (x : ⨂[k] j, X j) (hxU : x ∈ U) (hx0 : x ≠ 0) : U = ⊤ := by
  let b := fun j => Basis.ofVectorSpace k (X j)
  let Bt := Basis.piTensorProduct b
  obtain ⟨p, hp⟩ : ∃ p, Bt.repr x p ≠ 0 := by
    by_contra h
    push Not at h
    exact hx0 (Bt.ext_elem_iff.mpr (fun q => by simp [h q]))
  have htprod : ∀ u : ∀ j, X j, PiTensorProduct.tprod k u ∈ U := by
    intro u
    let f : ∀ j, X j →ₗ[k] X j := fun j => ((b j).coord (p j)).smulRight (u j)
    have hf : PiTensorProduct.map f x = Bt.repr x p • PiTensorProduct.tprod k u := by
      have hmap : PiTensorProduct.map f =
          (Bt.coord p).smulRight (PiTensorProduct.tprod k u) := by
        ext v
        simp [f, Bt, Basis.piTensorProduct_repr_tprod_apply, MultilinearMap.map_smul_univ]
      rw [hmap]
      rfl
    let s : ∀ j, Finset (X j) := fun j => (Bt.repr x).support.image (fun q => b j (q j))
    have hr : ∀ j, ∃ r : MonoidAlgebra k (H j), ∀ w ∈ s j,
        (ρ j).asAlgebraHom r w = f j w :=
      fun j => exists_asAlgebraHom_eq_on (ρ j) (hS j) (f j) (s j)
    choose r hr using hr
    have hagree : PiTensorProduct.map (fun j => (ρ j).asAlgebraHom (r j)) x =
        PiTensorProduct.map f x := by
      rw [← Bt.linearCombination_repr x, Finsupp.linearCombination_apply,
        map_finsuppSum, map_finsuppSum]
      refine Finsupp.sum_congr (fun q hq => ?_)
      rw [map_smul, map_smul, Basis.piTensorProduct_apply, PiTensorProduct.map_tprod,
        PiTensorProduct.map_tprod]
      congr 2
      funext j
      exact hr j _ (Finset.mem_image_of_mem _ hq)
    have hmem : PiTensorProduct.map f x ∈ U :=
      hagree ▸ map_induction _ (· ∈ U)
        (fun j y hy => map_slot_asAlgebraHom_mem ρ U hU j (r j) y hy) x hxU
    rw [hf] at hmem
    have h := U.smul_mem (Bt.repr x p)⁻¹ hmem
    rwa [smul_smul, inv_mul_cancel₀ hp, one_smul] at h
  apply eq_top_iff.mpr
  rw [← PiTensorProduct.span_tprod_eq_top]
  exact Submodule.span_le.mpr (by rintro _ ⟨u, rfl⟩; exact htprod u)

end Tensor

/-! ## Injectivity of cyclic evaluation for commuting monoid actions -/

section Injective

variable {k : Type uk} [Field k] {ι : Type uI} {G : ι → Type uG} [∀ i, Monoid (G i)]
  {V : Type uV} [AddCommGroup V] [Module k V]
  (σ : ∀ i, Representation k (G i) V) (hσ : Commuting σ) (v : V)

/-- The cyclic subrepresentation of `σ i` generated by `v`. -/
abbrev factorRep (i : ι) : Representation k (G i) (Factor σ v i) :=
  (Langlands.Cyclic.orbitSpan (σ i) v).toRepresentation

/-- The coordinate action on a finite stage is the one-slot tensor map. -/
theorem coordinateAction_eq_slot (S : Finset ι) (i : S) (g : G i) :
    coordinateAction σ v S i g =
      PiTensorProduct.map (FiniteTensor.slot i (factorRep σ v i g)) := rfl

include hσ in
/-- If every cyclic factor of a nonzero vector is irreducible with scalar self-intertwiners,
every finite cyclic evaluation is injective. -/
theorem evalStage_injective (hv : v ≠ 0)
    (hirr : ∀ i, (factorRep σ v i).IsIrreducible)
    (hscalar : ∀ i, ∀ f : (factorRep σ v i).IntertwiningMap (factorRep σ v i),
      ∃ c : k, f = c • Representation.IntertwiningMap.id _)
    (S : Finset ι) : Function.Injective (evalStage σ hσ v S) := by
  rw [← LinearMap.ker_eq_bot]
  by_contra hne
  obtain ⟨x, hxk, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have : ∀ i : S, (factorRep σ v i).IsIrreducible := fun i => hirr i
  have htop := eq_top_of_slot_stable (J := S) (fun i : S => factorRep σ v i)
    (fun i => hscalar i) (LinearMap.ker (evalStage σ hσ v S)) ?_ x hxk hx0
  · have hmem : PiTensorProduct.tprod k (fun i : S => Langlands.Cyclic.generator (σ i) v) ∈
        LinearMap.ker (evalStage σ hσ v S) := htop ▸ Submodule.mem_top
    rw [LinearMap.mem_ker, evalStage_generator] at hmem
    exact hv hmem
  · intro j g y hy
    rw [LinearMap.mem_ker] at hy ⊢
    have h := LinearMap.congr_fun (evalStage_coordinateAction σ hσ v S j g) y
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hy, map_zero,
      coordinateAction_eq_slot] at h
    exact h

include hσ in
/-- Injectivity passes from finite stages to the restricted tensor product. -/
theorem eval_injective (hv : v ≠ 0)
    (hirr : ∀ i, (factorRep σ v i).IsIrreducible)
    (hscalar : ∀ i, ∀ f : (factorRep σ v i).IntertwiningMap (factorRep σ v i),
      ∃ c : k, f = c • Representation.IntertwiningMap.id _)
    (E : Finset ι) : Function.Injective (eval σ hσ v E) := by
  intro x y hxy
  have hz : x - y = 0 := by
    obtain ⟨S, z, hz⟩ := exists_of E (fun i => Langlands.Cyclic.generator (σ i) v) (x - y)
    have he : evalStage σ hσ v S.1 z = 0 := by
      rw [← eval_of, ← hz, map_sub, hxy, sub_self]
    have hz0 : z = 0 := evalStage_injective σ hσ v hv hirr hscalar S.1 (by simpa using he)
    rw [hz, hz0, map_zero]
  exact sub_eq_zero.mp hz

end Injective

/-! ## One index: isotypic representations -/

section Local

variable {k : Type uk} [Field k] {G : Type uG} [Monoid G]
  {W : Type uW} [AddCommGroup W] [Module k W]
  {V : Type uV} [AddCommGroup V] [Module k V]
  {X : Type uX} [AddCommGroup X] [Module k X]

open Module

/-- Intertwining maps intertwine the monoid algebra actions. -/
theorem intertwining_asAlgebraHom {τ : Representation k G W} {σ : Representation k G V}
    (f : τ.IntertwiningMap σ) (a : MonoidAlgebra k G) (w : W) :
    f (τ.asAlgebraHom a w) = σ.asAlgebraHom a (f w) := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
  | single g c =>
    simp only [Representation.asAlgebraHom_single, LinearMap.smul_apply, map_smul,
      Representation.IntertwiningMap.isIntertwining]

/-- An irreducible representation has a nonzero vector. -/
theorem exists_ne_zero_of_irreducible (τ : Representation k G W) [τ.IsIrreducible] :
    ∃ w : W, w ≠ 0 := by
  by_contra h
  push Not at h
  apply (bot_ne_top : (⊥ : Subrepresentation τ) ≠ ⊤)
  apply le_antisymm bot_le
  intro w _
  exact (Submodule.mem_bot k).mpr (h w)

/-- Every vector of an irreducible representation is obtained from any nonzero vector by the
monoid algebra. -/
theorem exists_asAlgebraHom_apply_eq (τ : Representation k G W) [τ.IsIrreducible] {w : W}
    (hw : w ≠ 0) (u : W) : ∃ a : MonoidAlgebra k G, τ.asAlgebraHom a w = u := by
  have htop : Langlands.Cyclic.orbitSpan τ w = ⊤ := by
    refine (eq_bot_or_eq_top (Langlands.Cyclic.orbitSpan τ w)).resolve_left fun h => hw ?_
    have hmem := Langlands.Cyclic.mem_orbitSpan τ w
    rw [h] at hmem
    exact (Submodule.mem_bot k).mp hmem
  have hu : u ∈ LinearMap.range (Langlands.Cyclic.algebraEvaluation τ w) := by
    rw [Langlands.Cyclic.range_algebraEvaluation, htop]
    exact Submodule.mem_top
  obtain ⟨a, ha⟩ := LinearMap.mem_range.mp hu
  exact ⟨a, ha⟩

/-- An intertwining map from an irreducible representation that is nonzero at one vector is
injective. -/
theorem injective_of_apply_ne_zero {τ : Representation k G W} {σ : Representation k G V}
    [τ.IsIrreducible] (f : τ.IntertwiningMap σ) {w : W} (h : f w ≠ 0) :
    Function.Injective f :=
  (Representation.IsIrreducible.injective_or_eq_zero f).resolve_right (by rintro rfl; exact h rfl)

/-- Irreducibility is transported by an equivalence of representations. -/
theorem isIrreducible_of_equiv {τ : Representation k G W} {ρ : Representation k G X}
    (e : τ.Equiv ρ) (h : τ.IsIrreducible) : ρ.IsIrreducible := by
  rw [Representation.irreducible_iff_isSimpleModule_asModule] at h ⊢
  exact (LinearMap.isSimpleModule_iff_of_bijective
    (Representation.IntertwiningMap.equivLinearMapAsModule τ ρ e.toIntertwiningMap)
    e.bijective).mp h

/-- Scalar self-intertwiners are transported by an equivalence of representations. -/
theorem scalar_of_equiv {τ : Representation k G W} {ρ : Representation k G X}
    (e : τ.Equiv ρ)
    (hS : ∀ φ : τ.IntertwiningMap τ,
      ∃ c : k, φ = c • Representation.IntertwiningMap.id τ)
    (φ : ρ.IntertwiningMap ρ) : ∃ c : k, φ = c • Representation.IntertwiningMap.id ρ := by
  obtain ⟨c, hc⟩ := hS (e.symm.toIntertwiningMap.comp (φ.comp e.toIntertwiningMap))
  refine ⟨c, Representation.IntertwiningMap.ext (LinearMap.ext fun y => ?_)⟩
  have h := congrArg (fun ψ : τ.IntertwiningMap τ => e (ψ (e.symm y))) hc
  simp only [Representation.IntertwiningMap.comp_apply,
    Representation.Equiv.coe_toIntertwiningMap, Representation.Equiv.apply_symm_apply,
    Representation.IntertwiningMap.smul_apply, Representation.IntertwiningMap.id_apply,
    map_smul] at h
  simpa using h

/-- `x` is the value at `w` of an intertwining map from `τ` to `σ`. -/
def IsImage (τ : Representation k G W) (σ : Representation k G V) (w : W) (x : V) : Prop :=
  ∃ f : τ.IntertwiningMap σ, f w = x

/-- Being an image is preserved by linear maps commuting with the action. -/
theorem IsImage.of_commute {τ : Representation k G W} {σ : Representation k G V} {w : W}
    {x : V} (h : IsImage τ σ w x) (T : V →ₗ[k] V)
    (hT : ∀ (g : G) (y : V), T (σ g y) = σ g (T y)) : IsImage τ σ w (T x) := by
  obtain ⟨f, rfl⟩ := h
  exact ⟨(LinearMap.intertwiningMap_of_isIntertwiningMap σ σ T hT).comp f, rfl⟩

/-- Relations satisfied by an image of a nonzero vector are satisfied by every image of the
same vector of `τ`. -/
theorem IsImage.annihilator_le {τ : Representation k G W} {σ : Representation k G V}
    {σ' : Representation k G X} [τ.IsIrreducible] {u : W} {x : V} {y : X}
    (hx : IsImage τ σ u x) (hx0 : x ≠ 0) (hy : IsImage τ σ' u y) (a : MonoidAlgebra k G)
    (ha : σ.asAlgebraHom a x = 0) : σ'.asAlgebraHom a y = 0 := by
  obtain ⟨f, rfl⟩ := hx
  obtain ⟨f', rfl⟩ := hy
  rw [← intertwining_asAlgebraHom] at ha ⊢
  have h0 : τ.asAlgebraHom a u = 0 :=
    injective_of_apply_ne_zero f hx0 (by rw [ha, map_zero])
  rw [h0, map_zero]

/-- An image of `w` under an intertwining map from an irreducible `τ`, if nonzero, generates
a cyclic subrepresentation equivalent to `τ`. -/
theorem nonempty_equiv_orbitSpan (τ : Representation k G W) (σ : Representation k G V)
    [τ.IsIrreducible] {w : W} {x : V} (h : IsImage τ σ w x) (hx : x ≠ 0) :
    Nonempty (τ.Equiv (Langlands.Cyclic.orbitSpan σ x).toRepresentation) := by
  obtain ⟨f, rfl⟩ := h
  have hw : w ≠ 0 := by rintro rfl; exact hx (map_zero f)
  have hf := injective_of_apply_ne_zero f hx
  have hmem : ∀ u, f u ∈ (Langlands.Cyclic.orbitSpan σ (f w)).toSubmodule := by
    intro u
    obtain ⟨a, rfl⟩ := exists_asAlgebraHom_apply_eq τ hw u
    rw [intertwining_asAlgebraHom, ← Langlands.Cyclic.range_algebraEvaluation]
    exact LinearMap.mem_range.mpr ⟨a, rfl⟩
  let g : W →ₗ[k] (Langlands.Cyclic.orbitSpan σ (f w)).toSubmodule :=
    LinearMap.codRestrict _ f.toLinearMap hmem
  have hg : Function.Bijective g := by
    refine ⟨fun u u' huu => hf (congrArg Subtype.val huu), fun y => ?_⟩
    have hy : (y : V) ∈ LinearMap.range (Langlands.Cyclic.algebraEvaluation σ (f w)) := by
      rw [Langlands.Cyclic.range_algebraEvaluation]
      exact y.2
    obtain ⟨a, ha⟩ := LinearMap.mem_range.mp hy
    refine ⟨τ.asAlgebraHom a w, Subtype.ext ?_⟩
    change f (τ.asAlgebraHom a w) = (y : V)
    rw [intertwining_asAlgebraHom, ← ha]
    rfl
  refine ⟨Representation.Equiv.mk (LinearEquiv.ofBijective g hg) fun h => ?_⟩
  ext u
  change f (τ h u) = σ h (f u)
  exact Representation.IntertwiningMap.isIntertwining _ _ f h u

/-- The linear map sending an intertwining map to its underlying linear map. -/
def toLinearMapₗ (τ : Representation k G W) (σ : Representation k G V) :
    τ.IntertwiningMap σ →ₗ[k] W →ₗ[k] V where
  toFun f := f.toLinearMap
  map_add' f g := by ext; simp
  map_smul' c f := by ext; simp

/-- Evaluation `f ⊗ w ↦ f w` on the tensor product of the intertwining space with `W`. -/
def evalHom (τ : Representation k G W) (σ : Representation k G V) :
    τ.IntertwiningMap σ ⊗[k] W →ₗ[k] V :=
  TensorProduct.lift (toLinearMapₗ τ σ)

@[simp] theorem evalHom_tmul (τ : Representation k G W) (σ : Representation k G V)
    (f : τ.IntertwiningMap σ) (w : W) : evalHom τ σ (f ⊗ₜ w) = f w := by
  simp [evalHom, toLinearMapₗ]

/-- Evaluation intertwines the monoid algebra action on the second tensor factor. -/
theorem evalHom_lTensor (τ : Representation k G W) (σ : Representation k G V)
    (a : MonoidAlgebra k G) (t : τ.IntertwiningMap σ ⊗[k] W) :
    evalHom τ σ (LinearMap.lTensor _ (τ.asAlgebraHom a) t) =
      σ.asAlgebraHom a (evalHom τ σ t) := by
  induction t using TensorProduct.inductionOn with
  | tmul f w => simp [intertwining_asAlgebraHom]
  | add t t' ht ht' => rw [map_add, map_add, ht, ht', map_add, map_add]

theorem evalHom_lTensor_single (τ : Representation k G W) (σ : Representation k G V)
    (g : G) (t : τ.IntertwiningMap σ ⊗[k] W) :
    evalHom τ σ (LinearMap.lTensor _ (τ g) t) = σ g (evalHom τ σ t) := by
  simpa [Representation.asAlgebraHom_single_one] using
    evalHom_lTensor τ σ (MonoidAlgebra.single g 1) t

/-- `lTensor` written in the coordinates of a basis of the second factor. -/
theorem lTensor_eq_sum {M : Type*} [AddCommGroup M] [Module k M] {κ : Type*} [DecidableEq κ]
    (c : Basis κ k W) (g : W →ₗ[k] W) (t : M ⊗[k] W) :
    LinearMap.lTensor M g t =
      (TensorProduct.equivFinsuppOfBasisRight c t).sum fun j m => m ⊗ₜ g (c j) := by
  conv_lhs => rw [← (TensorProduct.equivFinsuppOfBasisRight c).symm_apply_apply t,
    TensorProduct.equivFinsuppOfBasisRight_symm_apply]
  rw [map_finsuppSum]
  simp only [LinearMap.lTensor_tmul]

theorem lTensor_smulRight {M : Type*} [AddCommGroup M] [Module k M] (φ : W →ₗ[k] k) (w : W)
    (z : M ⊗[k] W) :
    LinearMap.lTensor M (φ.smulRight w) z =
      TensorProduct.rid k M (LinearMap.lTensor M φ z) ⊗ₜ w := by
  induction z using TensorProduct.inductionOn with
  | tmul m u =>
    simp only [LinearMap.lTensor_tmul, LinearMap.smulRight_apply, TensorProduct.rid_tmul,
      TensorProduct.smul_tmul]
  | add z z' hz hz' => rw [map_add, hz, hz', map_add, map_add, TensorProduct.add_tmul]

/-- Density in `M ⊗ W`: a nonzero tensor is moved by the monoid algebra, acting on `W`, to a
nonzero pure tensor. -/
theorem exists_lTensor_eq_tmul (τ : Representation k G W) [τ.IsIrreducible]
    (hS : ∀ φ : τ.IntertwiningMap τ,
      ∃ c : k, φ = c • Representation.IntertwiningMap.id τ)
    {M : Type*} [AddCommGroup M] [Module k M] (t : M ⊗[k] W) (ht : t ≠ 0) :
    ∃ (a : MonoidAlgebra k G) (m : M) (w : W), m ≠ 0 ∧ w ≠ 0 ∧
      LinearMap.lTensor M (τ.asAlgebraHom a) t = m ⊗ₜ w := by
  let c := Basis.ofVectorSpace k W
  obtain ⟨j₀, hj₀⟩ : ∃ j, TensorProduct.equivFinsuppOfBasisRight c t j ≠ 0 := by
    by_contra h
    push Not at h
    apply ht
    apply (TensorProduct.equivFinsuppOfBasisRight (M := M) c).injective
    ext j
    simp [h j]
  obtain ⟨a, ha⟩ := exists_asAlgebraHom_eq_on τ hS ((c.coord j₀).smulRight (c j₀))
    ((TensorProduct.equivFinsuppOfBasisRight c t).support.image c)
  refine ⟨a, _, c j₀, hj₀, c.ne_zero j₀, ?_⟩
  calc LinearMap.lTensor M (τ.asAlgebraHom a) t =
        LinearMap.lTensor M ((c.coord j₀).smulRight (c j₀)) t := by
        rw [lTensor_eq_sum c, lTensor_eq_sum c]
        exact Finsupp.sum_congr fun j hj => by rw [ha (c j) (Finset.mem_image_of_mem c hj)]
    _ = _ := by rw [lTensor_smulRight, TensorProduct.equivFinsuppOfBasisRight_apply]

variable (τ : Representation k G W) (σ : Representation k G V) [τ.IsIrreducible]
  (hS : ∀ φ : τ.IntertwiningMap τ, ∃ c : k, φ = c • Representation.IntertwiningMap.id τ)

include hS in
/-- A nonzero value of the evaluation map is moved by the monoid algebra to a nonzero image
`f w`. -/
theorem exists_asAlgebraHom_evalHom_eq (t : τ.IntertwiningMap σ ⊗[k] W) (ht : t ≠ 0) :
    ∃ (a : MonoidAlgebra k G) (f : τ.IntertwiningMap σ) (w : W), f w ≠ 0 ∧
      σ.asAlgebraHom a (evalHom τ σ t) = f w := by
  obtain ⟨a, f, w, hf, hw, h⟩ := exists_lTensor_eq_tmul τ hS t ht
  refine ⟨a, f, w, ?_, ?_⟩
  · have hinj := (Representation.IsIrreducible.injective_or_eq_zero f).resolve_right hf
    exact fun h0 => hw (hinj (by rw [h0, map_zero]))
  · rw [← evalHom_lTensor, h, evalHom_tmul]

include hS in
theorem evalHom_injective : Function.Injective (evalHom τ σ) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro t ht
  by_contra ht0
  obtain ⟨a, f, w, hfw, h⟩ := exists_asAlgebraHom_evalHom_eq τ σ hS t ht0
  rw [LinearMap.mem_ker.mp ht, map_zero] at h
  exact hfw h.symm

omit [τ.IsIrreducible] in
theorem evalHom_surjective
    (hiso : ⨆ f : τ.IntertwiningMap σ, LinearMap.range f.toLinearMap = ⊤) :
    Function.Surjective (evalHom τ σ) := by
  rw [← LinearMap.range_eq_top, eq_top_iff, ← hiso]
  refine iSup_le fun f => ?_
  intro v hv
  obtain ⟨w, rfl⟩ := LinearMap.mem_range.mp hv
  exact LinearMap.mem_range.mpr ⟨f ⊗ₜ w, evalHom_tmul τ σ f w⟩

include hS in
/-- In a `τ`-isotypic representation, every nonzero vector is moved by the monoid algebra to a
nonzero image of any prescribed nonzero vector of `τ`. -/
theorem exists_isImage
    (hiso : ⨆ f : τ.IntertwiningMap σ, LinearMap.range f.toLinearMap = ⊤)
    {x : V} (hx : x ≠ 0) {w₁ : W} (hw₁ : w₁ ≠ 0) :
    ∃ a : MonoidAlgebra k G, σ.asAlgebraHom a x ≠ 0 ∧ IsImage τ σ w₁ (σ.asAlgebraHom a x) := by
  obtain ⟨t, rfl⟩ := evalHom_surjective τ σ hiso x
  have ht : t ≠ 0 := by rintro rfl; exact hx (map_zero _)
  obtain ⟨a, f, w, hfw, h⟩ := exists_asAlgebraHom_evalHom_eq τ σ hS t ht
  have hw : w ≠ 0 := by rintro rfl; exact hfw (map_zero f)
  have hinj := injective_of_apply_ne_zero f hfw
  obtain ⟨b, hb⟩ := exists_asAlgebraHom_apply_eq τ hw w₁
  have key : σ.asAlgebraHom (b * a) (evalHom τ σ t) = f w₁ := by
    rw [map_mul, Module.End.mul_apply, h, ← intertwining_asAlgebraHom, hb]
  refine ⟨b * a, ?_, f, key.symm⟩
  rw [key]
  exact fun h0 => hw₁ (hinj (by rw [h0, map_zero]))

include hS in
/-- If the vectors of `τ` fixed by `H` lie on the line through `w₀`, every vector of an
isotypic `σ` fixed by `H` is an image of `w₀`. -/
theorem isImage_of_fixed
    (hiso : ⨆ f : τ.IntertwiningMap σ, LinearMap.range f.toLinearMap = ⊤)
    (H : Set G) (w₀ : W) (hw₀ : ∀ w : W, (∀ h ∈ H, τ h w = w) → ∃ c : k, w = c • w₀)
    (x : V) (hx : ∀ h ∈ H, σ h x = x) : IsImage τ σ w₀ x := by
  obtain ⟨t, rfl⟩ := evalHom_surjective τ σ hiso x
  have hfix : ∀ h : H, LinearMap.lTensor _ (τ h) t = t := fun h =>
    evalHom_injective τ σ hS (by rw [evalHom_lTensor_single, hx h h.2])
  obtain ⟨φ, hφ⟩ : ∃ φ : W →ₗ[k] k, ∀ c : k, φ (c • w₀) • w₀ = c • w₀ := by
    by_cases h0 : w₀ = 0
    · exact ⟨0, fun c => by simp [h0]⟩
    · obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one k h0
      exact ⟨φ, fun c => by simp [hφ]⟩
  have hπ := FiniteTensor.lTensor_eq_of_forall_fixed (fun h : H => τ h) (φ.smulRight w₀)
    (fun w hw => by
      obtain ⟨c, rfl⟩ := hw₀ w (fun h hh => hw ⟨h, hh⟩)
      rw [LinearMap.smulRight_apply]
      exact hφ c) t hfix
  refine ⟨TensorProduct.rid k _ (LinearMap.lTensor _ φ t), ?_⟩
  rw [← evalHom_tmul τ σ, ← lTensor_smulRight, hπ]

end Local

/-! ## The family: selection of a factorizable vector and the global map -/

section Global

variable {k : Type uk} [Field k] {ι : Type uI} {G : ι → Type uG} [∀ i, Monoid (G i)]
  {V : Type uV} [AddCommGroup V] [Module k V] {V' : Type uV'} [AddCommGroup V'] [Module k V']
  {W : ι → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module k (W i)]

/-- Joint irreducibility of a family of actions: the space is nonzero and every subspace
stable under all the actions is `⊥` or `⊤`. -/
def IsJointlyIrreducible (σ : ∀ i, Representation k (G i) V) : Prop :=
  Nontrivial V ∧ ∀ U : Submodule k V, (∀ i (g : G i), ∀ v ∈ U, σ i g v ∈ U) → U = ⊥ ∨ U = ⊤

theorem exists_finset_of_eventually {p : ι → Prop} (h : ∀ᶠ i in Filter.cofinite, p i) :
    ∃ E : Finset ι, ∀ i ∉ E, p i :=
  ⟨(Filter.eventually_cofinite.mp h).toFinset, fun i hi => by
    by_contra hc
    exact hi ((Set.Finite.mem_toFinset _).mpr hc)⟩

variable (σ : ∀ i, Representation k (G i) V) (hσ : Commuting σ)

include hσ in
theorem asAlgebraHom_commute {i j : ι} (hij : i ≠ j) (a : MonoidAlgebra k (G i)) (g : G j)
    (v : V) : (σ i).asAlgebraHom a (σ j g v) = σ j g ((σ i).asAlgebraHom a v) := by
  have h := LinearMap.congr_fun (algebra_commute σ hσ hij a (MonoidAlgebra.single g 1)).eq v
  simpa only [Module.End.mul_apply, Representation.asAlgebraHom_single_one] using h

/-- Acting by `g ∈ G i` after a finite product inserts `g` at coordinate `i`. -/
theorem single_mul_algebraProduct (S : Finset ι) (a : ∀ i, MonoidAlgebra k (G i)) (i : ι)
    (g : G i) :
    σ i g * algebraProduct σ hσ S a = algebraProduct σ hσ (insert i S)
      (Function.update a i (MonoidAlgebra.single g 1 * if i ∈ S then a i else 1)) := by
  set b := Function.update a i (MonoidAlgebra.single g 1 * if i ∈ S then a i else 1) with hb
  have hbj : ∀ j, j ≠ i → b j = a j := fun j hj => Function.update_of_ne hj _ _
  by_cases hi : i ∈ S
  · have hbi : b i = MonoidAlgebra.single g 1 * a i := by simp [b, hi]
    have hcongr : algebraProduct σ hσ (S.erase i) b = algebraProduct σ hσ (S.erase i) a :=
      algebraProduct_congr σ hσ (fun j hj => hbj j (Finset.ne_of_mem_erase hj))
    have hcomm := (commute_algebraProduct σ hσ (S.erase i) (Finset.notMem_erase i S)
      (MonoidAlgebra.single g 1) a).eq
    rw [Representation.asAlgebraHom_single_one] at hcomm
    rw [Finset.insert_eq_of_mem hi, algebraProduct_erase_right σ hσ S i hi a,
      algebraProduct_erase_right σ hσ S i hi b, hcongr, hbi, map_mul,
      Representation.asAlgebraHom_single_one, ← mul_assoc, ← mul_assoc, hcomm]
  · have hbi : b i = MonoidAlgebra.single g 1 := by simp [b, hi]
    rw [algebraProduct_insert σ hσ S i hi b, hbi, Representation.asAlgebraHom_single_one,
      algebraProduct_congr σ hσ (a := b) (b := a)
        (fun j hj => hbj j (fun h => hi (h ▸ hj)))]

theorem apply_algebraProduct (S : Finset ι) (a : ∀ i, MonoidAlgebra k (G i)) (i : ι)
    (g : G i) (v : V) :
    σ i g (algebraProduct σ hσ S a v) = algebraProduct σ hσ (insert i S)
      (Function.update a i (MonoidAlgebra.single g 1 * if i ∈ S then a i else 1)) v := by
  rw [← single_mul_algebraProduct σ hσ S a i g, Module.End.mul_apply]

/-- In a jointly irreducible space the vectors `algebraProduct S a x` span everything. -/
theorem span_algebraProduct_eq_top (hirr : IsJointlyIrreducible σ) {x : V} (hx : x ≠ 0) :
    Submodule.span k (Set.range fun p : Finset ι × (∀ i, MonoidAlgebra k (G i)) =>
      algebraProduct σ hσ p.1 p.2 x) = ⊤ := by
  have hstab : ∀ i (g : G i), ∀ v ∈ Submodule.span k
      (Set.range fun p : Finset ι × (∀ i, MonoidAlgebra k (G i)) => algebraProduct σ hσ p.1 p.2 x),
      σ i g v ∈ Submodule.span k
        (Set.range fun p : Finset ι × (∀ i, MonoidAlgebra k (G i)) =>
          algebraProduct σ hσ p.1 p.2 x) := by
    intro i g v hv
    have hle : Submodule.span k (Set.range fun p : Finset ι × (∀ i, MonoidAlgebra k (G i)) =>
        algebraProduct σ hσ p.1 p.2 x) ≤
        (Submodule.span k (Set.range fun p : Finset ι × (∀ i, MonoidAlgebra k (G i)) =>
          algebraProduct σ hσ p.1 p.2 x)).comap (σ i g) := by
      rw [Submodule.span_le]
      rintro _ ⟨⟨S, a⟩, rfl⟩
      exact Submodule.subset_span ⟨(insert i S,
        Function.update a i (MonoidAlgebra.single g 1 * if i ∈ S then a i else 1)),
        (apply_algebraProduct σ hσ S a i g x).symm⟩
    exact hle hv
  rcases hirr.2 _ hstab with h | h
  · exfalso
    have hmem : x ∈ Submodule.span k (Set.range fun p : Finset ι × (∀ i, MonoidAlgebra k (G i)) =>
        algebraProduct σ hσ p.1 p.2 x) :=
      Submodule.subset_span ⟨(∅, fun _ => 1), by simp⟩
    rw [h] at hmem
    exact hx ((Submodule.mem_bot k).mp hmem)
  · exact h

include hσ in
/-- Selection: starting from a nonzero vector that is an image (with side condition `P`) at
all but finitely many indices, the commuting monoid algebras produce a nonzero vector that is an
image at every index. -/
theorem exists_isImage_everywhere (τ : ∀ i, Representation k (G i) (W i))
    [∀ i, (τ i).IsIrreducible]
    (hS : ∀ i, ∀ φ : (τ i).IntertwiningMap (τ i),
      ∃ c : k, φ = c • Representation.IntertwiningMap.id (τ i))
    (hiso : ∀ i, ⨆ f : (τ i).IntertwiningMap (σ i), LinearMap.range f.toLinearMap = ⊤)
    (P : ∀ i, W i → Prop) (hP : ∀ i, ∃ w, w ≠ 0 ∧ P i w) (E : Finset ι) :
    ∀ x : V, x ≠ 0 → (∀ i ∉ E, ∃ w, P i w ∧ IsImage (τ i) (σ i) w x) →
      ∃ x' : V, x' ≠ 0 ∧ ∀ i, ∃ w, P i w ∧ IsImage (τ i) (σ i) w x' := by
  induction E using Finset.induction_on with
  | empty => exact fun x hx h => ⟨x, hx, fun i => h i (Finset.notMem_empty i)⟩
  | @insert i E hi ih =>
    intro x hx h
    obtain ⟨w₁, hw₁, hP₁⟩ := hP i
    obtain ⟨a, ha0, ha⟩ := exists_isImage (τ i) (σ i) (hS i) (hiso i) hx hw₁
    refine ih _ ha0 fun j hj => ?_
    by_cases hji : j = i
    · subst hji
      exact ⟨w₁, hP₁, ha⟩
    · obtain ⟨w, hPw, hw⟩ := h j (by simp [hji, hj])
      exact ⟨w, hPw, hw.of_commute _ fun g y => asAlgebraHom_commute σ hσ (Ne.symm hji) a g y⟩

variable (σ' : ∀ i, Representation k (G i) V') (hσ' : Commuting σ')

/-- The map of cyclic factors `σ i (a) x ↦ σ' i (a) y`. -/
def transfer (x : V) (y : V') (i : ι) : Factor σ x i →ₗ[k] Factor σ' y i :=
  (Langlands.Cyclic.presentation (σ' i) y).comp (presentationSection σ x i)

theorem transfer_presentation {x : V} {y : V'}
    (hann : ∀ i (a : MonoidAlgebra k (G i)),
      (σ i).asAlgebraHom a x = 0 → (σ' i).asAlgebraHom a y = 0)
    (i : ι) (a : MonoidAlgebra k (G i)) :
    transfer σ σ' x y i (Langlands.Cyclic.presentation (σ i) x a) =
      Langlands.Cyclic.presentation (σ' i) y a := by
  apply Subtype.ext
  simp only [transfer, LinearMap.comp_apply, Langlands.Cyclic.presentation_val]
  have hb := presentationSection_eval σ x i (Langlands.Cyclic.presentation (σ i) x a)
  rw [Langlands.Cyclic.presentation_val] at hb
  have h := hann i (presentationSection σ x i (Langlands.Cyclic.presentation (σ i) x a) - a)
    (by rw [map_sub, LinearMap.sub_apply, hb, sub_self])
  rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at h
  exact h

theorem transfer_generator {x : V} {y : V'}
    (hann : ∀ i (a : MonoidAlgebra k (G i)),
      (σ i).asAlgebraHom a x = 0 → (σ' i).asAlgebraHom a y = 0) (i : ι) :
    transfer σ σ' x y i (Langlands.Cyclic.generator (σ i) x) =
      Langlands.Cyclic.generator (σ' i) y := by
  have h1 : Langlands.Cyclic.generator (σ i) x = Langlands.Cyclic.presentation (σ i) x 1 :=
    Subtype.ext (by simp)
  have h2 : Langlands.Cyclic.generator (σ' i) y = Langlands.Cyclic.presentation (σ' i) y 1 :=
    Subtype.ext (by simp)
  rw [h1, transfer_presentation σ σ' hann, h2]

include hσ hσ' in
/-- If the cyclic factors of `x` are irreducible with scalar self-intertwiners and every
relation of `x` at every index is a relation of `y`, then `algebraProduct S a x ↦
algebraProduct S a y` is a well-defined linear map. -/
theorem exists_map_algebraProduct (hirr : IsJointlyIrreducible σ) {x : V} (hx : x ≠ 0)
    (y : V') (hfac : ∀ i, (factorRep σ x i).IsIrreducible)
    (hsc : ∀ i, ∀ f : (factorRep σ x i).IntertwiningMap (factorRep σ x i),
      ∃ c : k, f = c • Representation.IntertwiningMap.id _)
    (hann : ∀ i (a : MonoidAlgebra k (G i)),
      (σ i).asAlgebraHom a x = 0 → (σ' i).asAlgebraHom a y = 0) :
    ∃ Φ : V →ₗ[k] V', ∀ (S : Finset ι) (a : ∀ i, MonoidAlgebra k (G i)),
      Φ (algebraProduct σ hσ S a x) = algebraProduct σ' hσ' S a y := by
  have hpure : ∀ (S : Finset ι) (a : ∀ i, MonoidAlgebra k (G i)),
      eval σ hσ x ∅ (RestrictedTensor.pure ∅ (fun i => Langlands.Cyclic.generator (σ i) x)
        ⟨S, Finset.empty_subset S⟩ (fun i => Langlands.Cyclic.presentation (σ i) x (a i))) =
        algebraProduct σ hσ S a x := by
    intro S a
    rw [RestrictedTensor.pure, eval_of, evalStage_presentation]
  have hsurj : Function.Surjective (eval σ hσ x ∅) := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← span_algebraProduct_eq_top σ hσ hirr hx,
      Submodule.span_le]
    rintro _ ⟨⟨S, a⟩, rfl⟩
    exact ⟨_, hpure S a⟩
  let e := LinearEquiv.ofBijective (eval σ hσ x ∅)
    ⟨eval_injective σ hσ x hx hfac hsc ∅, hsurj⟩
  refine ⟨(eval σ' hσ' y ∅).comp ((mapWithBound ∅ ∅
    (fun i => Langlands.Cyclic.generator (σ i) x) (fun i => Langlands.Cyclic.generator (σ' i) y)
    (transfer σ σ' x y) ∅ subset_rfl (fun i _ => transfer_generator σ σ' hann i)).comp
    e.symm.toLinearMap), fun S a => ?_⟩
  have he : e.symm (algebraProduct σ hσ S a x) =
      RestrictedTensor.pure ∅ (fun i => Langlands.Cyclic.generator (σ i) x) ⟨S, Finset.empty_subset S⟩
        (fun i => Langlands.Cyclic.presentation (σ i) x (a i)) := by
    rw [LinearEquiv.symm_apply_eq]
    exact (hpure S a).symm
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, he,
    mapWithBound_pure_of_subset _ _ _ _ _ _ _ _ _ (Finset.empty_subset S)]
  simp only [transfer_presentation σ σ' hann]
  rw [RestrictedTensor.pure, eval_of, evalStage_presentation]

include hσ hσ' in
/-- **Uniqueness for commuting families of isotypic local actions.** Let `σ i` and `σ' i` be
pairwise commuting jointly irreducible families of monoid actions on `V` and `V'`. Suppose that
at every index both are isotypic of the type of one irreducible `τ i` with scalar
self-intertwiners, that for almost all `i` the vectors of `τ i` fixed by `H i` lie on a line,
and that every vector of `V` and of `V'` is fixed by `H i` for almost all `i`. Then some linear
isomorphism `V ≃ V'` intertwines `σ i` with `σ' i` for every `i`. -/
theorem exists_linearEquiv_of_isotypic (hirr : IsJointlyIrreducible σ)
    (hirr' : IsJointlyIrreducible σ') (τ : ∀ i, Representation k (G i) (W i))
    [∀ i, (τ i).IsIrreducible]
    (hS : ∀ i, ∀ φ : (τ i).IntertwiningMap (τ i),
      ∃ c : k, φ = c • Representation.IntertwiningMap.id (τ i))
    (hiso : ∀ i, ⨆ f : (τ i).IntertwiningMap (σ i), LinearMap.range f.toLinearMap = ⊤)
    (hiso' : ∀ i, ⨆ f : (τ i).IntertwiningMap (σ' i), LinearMap.range f.toLinearMap = ⊤)
    (H : ∀ i, Set (G i))
    (hsph : ∀ᶠ i in Filter.cofinite, ∃ w₀ : W i,
      ∀ w : W i, (∀ h ∈ H i, τ i h w = w) → ∃ c : k, w = c • w₀)
    (hsm : ∀ v : V, ∀ᶠ i in Filter.cofinite, ∀ h ∈ H i, σ i h v = v)
    (hsm' : ∀ v : V', ∀ᶠ i in Filter.cofinite, ∀ h ∈ H i, σ' i h v = v) :
    ∃ Φ : V ≃ₗ[k] V', ∀ i (g : G i) (v : V), Φ (σ i g v) = σ' i g (Φ v) := by
  have : Nontrivial V := hirr.1
  have : Nontrivial V' := hirr'.1
  -- a nonzero vector whose cyclic factors are all copies of the `τ i`
  obtain ⟨x₀, hx₀⟩ := exists_ne (0 : V)
  obtain ⟨E, hE⟩ := exists_finset_of_eventually (hsph.and (hsm x₀))
  obtain ⟨x, hx, hxim⟩ := exists_isImage_everywhere σ hσ τ hS hiso (fun _ _ => True)
    (fun i => (exists_ne_zero_of_irreducible (τ i)).imp fun w hw => ⟨hw, trivial⟩) E x₀ hx₀
    (fun i hi => by
      obtain ⟨⟨w₀, hw₀⟩, hfix⟩ := hE i hi
      exact ⟨w₀, trivial, isImage_of_fixed (τ i) (σ i) (hS i) (hiso i) (H i) w₀ hw₀ x₀ hfix⟩)
  choose w _ hw using hxim
  have hw0 : ∀ i, w i ≠ 0 := by
    intro i h0
    obtain ⟨f, hf⟩ := hw i
    rw [h0, map_zero] at hf
    exact hx hf.symm
  -- a nonzero vector of `V'` satisfying every relation of `x`
  obtain ⟨y₀, hy₀⟩ := exists_ne (0 : V')
  obtain ⟨E', hE'⟩ := exists_finset_of_eventually ((hsph.and (hsm x)).and (hsm' y₀))
  obtain ⟨y, hy, hyim⟩ := exists_isImage_everywhere σ' hσ' τ hS hiso'
    (fun i u => IsImage (τ i) (σ i) u x) (fun i => ⟨w i, hw0 i, hw i⟩) E' y₀ hy₀
    (fun i hi => by
      obtain ⟨⟨⟨w₀, hw₀⟩, hfx⟩, hfy⟩ := hE' i hi
      exact ⟨w₀, isImage_of_fixed (τ i) (σ i) (hS i) (hiso i) (H i) w₀ hw₀ x hfx,
        isImage_of_fixed (τ i) (σ' i) (hS i) (hiso' i) (H i) w₀ hw₀ y₀ hfy⟩)
  have hann : ∀ i (a : MonoidAlgebra k (G i)),
      (σ i).asAlgebraHom a x = 0 → (σ' i).asAlgebraHom a y = 0 := by
    intro i a ha
    obtain ⟨u, hux, huy⟩ := hyim i
    exact hux.annihilator_le hx huy a ha
  have hfac : ∀ i, (factorRep σ x i).IsIrreducible := fun i =>
    isIrreducible_of_equiv (nonempty_equiv_orbitSpan (τ i) (σ i) (hw i) hx).some inferInstance
  have hsc : ∀ i, ∀ f : (factorRep σ x i).IntertwiningMap (factorRep σ x i),
      ∃ c : k, f = c • Representation.IntertwiningMap.id _ := fun i =>
    scalar_of_equiv (nonempty_equiv_orbitSpan (τ i) (σ i) (hw i) hx).some (hS i)
  -- the global map and its properties
  obtain ⟨Φ, hΦ⟩ := exists_map_algebraProduct σ hσ σ' hσ' hirr hx y hfac hsc hann
  have hequiv : ∀ i (g : G i), Φ ∘ₗ σ i g = σ' i g ∘ₗ Φ := by
    intro i g
    refine LinearMap.ext_on_range (span_algebraProduct_eq_top σ hσ hirr hx) fun p => ?_
    obtain ⟨S, a⟩ := p
    simp only [LinearMap.comp_apply]
    rw [apply_algebraProduct σ hσ, hΦ, hΦ, apply_algebraProduct σ' hσ']
  have hcomm : ∀ i (g : G i) (v : V), Φ (σ i g v) = σ' i g (Φ v) := fun i g v =>
    LinearMap.congr_fun (hequiv i g) v
  have hΦx : Φ x = y := by simpa using hΦ ∅ (fun _ => 1)
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot]
    rcases hirr.2 (LinearMap.ker Φ) (fun i g v hv => by
      rw [LinearMap.mem_ker] at hv ⊢
      rw [hcomm, hv, map_zero]) with h | h
    · exact h
    · exfalso
      have hmem : x ∈ LinearMap.ker Φ := by rw [h]; exact Submodule.mem_top
      rw [LinearMap.mem_ker, hΦx] at hmem
      exact hy hmem
  have hsurj : Function.Surjective Φ := by
    rw [← LinearMap.range_eq_top]
    rcases hirr'.2 (LinearMap.range Φ) (fun i g v hv => by
      obtain ⟨u, rfl⟩ := LinearMap.mem_range.mp hv
      exact LinearMap.mem_range.mpr ⟨σ i g u, hcomm i g u⟩) with h | h
    · exfalso
      have hmem : y ∈ LinearMap.range Φ := LinearMap.mem_range.mpr ⟨x, hΦx⟩
      rw [h] at hmem
      exact hy ((Submodule.mem_bot k).mp hmem)
    · exact h
  exact ⟨LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩, hcomm⟩

end Global

end Langlands.CommutingFamily
