import Langlands.Representation.CommutingFamilyUniqueness
import Langlands.Representation.Archimedean.GKModuleDensity
import Langlands.Automorphic.OperatorSubquotientLocalComponentStatement
import Mathlib.Algebra.FreeMonoid.Basic

/-!
# Representations of free monoids given by generators

A family of linear operators `act a` (`a : α`) on a vector space `V` defines a representation
`rep act` of the free monoid on `α`. This module relates the properties used by
`Langlands.CommutingFamily.exists_linearEquiv_of_isotypic` for such representations to
properties of the generators, and specializes them to two kinds of families:

* the elements of a monoid acting through a representation `ρ` (`act = ⇑ρ`);
* a `(𝔤, K)`-module `(V, ρ, π)`, the generators being the elements of `K` and of `𝔤`, indexed by
  a type `Γ` that maps onto `K ⊕ 𝔤` (`gkGenerators dec ρ π`, `gkRep dec ρ π`).

Main results:

* `rep_comm`, `rep_mem`, `isIrreducible_rep`, `scalar_rep`, `intertwiningMap`,
  `map_generator`, `comm_of_rep`: commutation, stable subspaces, irreducibility, scalar
  self-intertwiners and intertwining maps are detected on the generators.
* `nonempty_equiv_of_isotypic`: if a nonzero representation `σ` is isotypic both for an
  irreducible `ρ` and for an irreducible `τ` with scalar self-intertwiners, then `ρ` and `τ`
  are equivalent. `exists_fixed_line_of_equiv`: fixed lines are transported along
  equivalences.
* `IsCommonType`, `isCommonType_monoid`, `isCommonType_gk`: a representation is a common
  isotypic type of two others, with scalar self-intertwiners; for monoid representations and
  for `(𝔤, K)`-modules this follows from irreducibility once the first of the two
  representations is also isotypic of a type with scalar self-intertwiners (for instance an
  admissible one).
-/

noncomputable section

open scoped Classical

set_option autoImplicit false

namespace Langlands.FreeMonoidGenerators

universe uk uα uβ uG uV uV' uW uX uK uL uΓ

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ### Generators -/

section Generators

variable {k : Type uk} [Field k] {α : Type uα} {β : Type uβ}
  {V : Type uV} [AddCommGroup V] [Module k V] {V' : Type uV'} [AddCommGroup V'] [Module k V']
  {W : Type uW} [AddCommGroup W] [Module k W]

/-- The representation of the free monoid on `α` in which the generator `a` acts by
`act a`. -/
abbrev rep (act : α → Module.End k V) : Representation k (FreeMonoid α) V :=
  FreeMonoid.lift act

theorem rep_of (act : α → Module.End k V) (a : α) : rep act (FreeMonoid.of a) = act a :=
  rfl

/-- Words act by operators commuting with `T` when the generators do. -/
theorem rep_commute {act : α → Module.End k V} {T : Module.End k V}
    (h : ∀ a, Commute (act a) T) (g : FreeMonoid α) : Commute (rep act g) T := by
  induction g using FreeMonoid.inductionOn' with
  | one => rw [map_one]; exact Commute.one_left T
  | of_mul a g ih => rw [map_mul, rep_of]; exact (h a).mul_left ih

/-- Two free-monoid representations commute when their generators commute. -/
theorem rep_comm {act : α → Module.End k V} {act' : β → Module.End k V}
    (h : ∀ a b x, act a (act' b x) = act' b (act a x)) (g : FreeMonoid α)
    (g' : FreeMonoid β) (x : V) : rep act g (rep act' g' x) = rep act' g' (rep act g x) := by
  have hgen : ∀ a b, Commute (act a) (act' b) := fun a b => LinearMap.ext (h a b)
  have hc : Commute (rep act g) (rep act' g') :=
    rep_commute (fun a => (rep_commute (fun b => (hgen a b).symm) g').symm) g
  exact LinearMap.congr_fun hc.eq x

/-- A subspace stable under the generators is stable under every word. -/
theorem rep_mem {act : α → Module.End k V} {U : Submodule k V}
    (h : ∀ a, ∀ x ∈ U, act a x ∈ U) (g : FreeMonoid α) : ∀ x ∈ U, rep act g x ∈ U := by
  induction g using FreeMonoid.inductionOn' with
  | one => intro x hx; rw [map_one]; exact hx
  | of_mul a g ih =>
    intro x hx
    rw [map_mul, Module.End.mul_apply, rep_of]
    exact h a _ (ih x hx)

/-- A linear map intertwining the generators intertwines every word. -/
theorem rep_map {act : α → Module.End k W} {act' : α → Module.End k V} (f : W →ₗ[k] V)
    (h : ∀ a w, f (act a w) = act' a (f w)) (g : FreeMonoid α) (w : W) :
    f (rep act g w) = rep act' g (f w) := by
  induction g using FreeMonoid.inductionOn' generalizing w with
  | one => rw [map_one, map_one]; rfl
  | of_mul a g ih =>
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, rep_of, rep_of, h, ih]

/-- The intertwining map of free-monoid representations given by a linear map intertwining
the generators. -/
def intertwiningMap {act : α → Module.End k W} {act' : α → Module.End k V} (f : W →ₗ[k] V)
    (h : ∀ a w, f (act a w) = act' a (f w)) : (rep act).IntertwiningMap (rep act') :=
  f.intertwiningMap_of_isIntertwiningMap _ _ (rep_map f h)

theorem intertwiningMap_toLinearMap {act : α → Module.End k W} {act' : α → Module.End k V}
    (f : W →ₗ[k] V) (h : ∀ a w, f (act a w) = act' a (f w)) :
    (intertwiningMap f h).toLinearMap = f :=
  rfl

/-- An intertwining map of free-monoid representations intertwines the generators. -/
theorem map_generator {act : α → Module.End k W} {act' : α → Module.End k V}
    (φ : (rep act).IntertwiningMap (rep act')) (a : α) (w : W) :
    φ (act a w) = act' a (φ w) :=
  Representation.IntertwiningMap.isIntertwining _ _ φ (FreeMonoid.of a) w

/-- A linear map commuting with every word commutes with the generators. -/
theorem comm_of_rep {act : α → Module.End k V} {act' : α → Module.End k V'} (Φ : V →ₗ[k] V')
    (h : ∀ (g : FreeMonoid α) (x : V), Φ (rep act g x) = rep act' g (Φ x)) (a : α) (x : V) :
    Φ (act a x) = act' a (Φ x) :=
  h (FreeMonoid.of a) x

/-- **Irreducibility from the generators.** If `W` is nonzero and every subspace stable under
the generators is `⊥` or `⊤`, the free-monoid representation is irreducible. -/
theorem isIrreducible_rep [Nontrivial W] {act : α → Module.End k W}
    (h : ∀ U : Submodule k W, (∀ a, ∀ w ∈ U, act a w ∈ U) → U = ⊥ ∨ U = ⊤) :
    (rep act).IsIrreducible := by
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h0 => ?_⟩, eq_bot_or_eq_top := fun S => ?_ }
  · have h1 : (⊥ : Submodule k W) = ⊤ := congrArg Subrepresentation.toSubmodule h0
    exact bot_ne_top h1
  · rcases h S.toSubmodule (fun a w hw => S.apply_mem_toSubmodule (FreeMonoid.of a) hw) with
      h1 | h1
    · exact Or.inl (Subrepresentation.ext h1)
    · exact Or.inr (Subrepresentation.ext h1)

/-- **Scalar self-intertwiners from the generators.** If every linear map commuting with the
generators is a scalar, every self-intertwiner of the free-monoid representation is a
scalar. -/
theorem scalar_rep {act : α → Module.End k W}
    (hS : ∀ T : Module.End k W, (∀ a w, T (act a w) = act a (T w)) →
      ∃ c : k, ∀ w, T w = c • w)
    (φ : (rep act).IntertwiningMap (rep act)) :
    ∃ c : k, φ = c • Representation.IntertwiningMap.id (rep act) := by
  obtain ⟨c, hc⟩ := hS φ.toLinearMap (map_generator φ)
  refine ⟨c, Representation.IntertwiningMap.ext (LinearMap.ext fun w => ?_)⟩
  show φ w = (c • Representation.IntertwiningMap.id (rep act)) w
  rw [Representation.IntertwiningMap.smul_apply, Representation.IntertwiningMap.id_apply]
  exact hc w

end Generators

/-! ### Spanning families of linear maps -/

section Span

variable {k : Type uk} [Field k] {V : Type uV} [AddCommGroup V] [Module k V]
  {W : Type uW} [AddCommGroup W] [Module k W]

/-- If every map of a spanning family of maps `W → V` occurs in a second family, the second
family spans as well. -/
theorem iSup_range_eq_top_of_forall_exists {ι : Sort*} {κ : Sort*} (u : ι → W →ₗ[k] V)
    (u' : κ → W →ₗ[k] V) (h : ⨆ i, LinearMap.range (u i) = ⊤)
    (hu : ∀ i, ∃ j, u' j = u i) : ⨆ j, LinearMap.range (u' j) = ⊤ := by
  refine eq_top_iff.mpr ?_
  rw [← h]
  refine iSup_le fun i => ?_
  obtain ⟨j, hj⟩ := hu i
  rw [← hj]
  exact le_iSup (fun j => LinearMap.range (u' j)) j

end Span

/-! ### Isotypic representations of the same type -/

section Equivalence

variable {k : Type uk} [Field k] {G : Type uG} [Monoid G]
  {V : Type uV} [AddCommGroup V] [Module k V] {V' : Type uV'} [AddCommGroup V'] [Module k V']
  {W : Type uW} [AddCommGroup W] [Module k W] {X : Type uX} [AddCommGroup X] [Module k X]

/-- A nonzero representation spanned by the images of the intertwining maps from `ρ` receives
a nonzero intertwining map from `ρ`. -/
theorem exists_apply_ne_zero_of_isotypic [Nontrivial V] (ρ : Representation k G X)
    (σ : Representation k G V)
    (h : ⨆ f : ρ.IntertwiningMap σ, LinearMap.range f.toLinearMap = ⊤) :
    ∃ (f : ρ.IntertwiningMap σ) (u : X), f u ≠ 0 := by
  by_contra hne
  have hne' : ∀ (f : ρ.IntertwiningMap σ) (u : X), f u = 0 := fun f u =>
    by_contra fun hfu => hne ⟨f, u, hfu⟩
  have hle : (⨆ f : ρ.IntertwiningMap σ, LinearMap.range f.toLinearMap) ≤ ⊥ :=
    iSup_le fun f => by
      rintro _ ⟨u, rfl⟩
      exact (Submodule.mem_bot k).mpr (hne' f u)
  rw [h] at hle
  exact bot_ne_top (eq_bot_iff.mpr hle).symm

/-- **Two isotypic types of one representation are equivalent.** If a nonzero representation
`σ` is `ρ`-isotypic and `τ`-isotypic for irreducible `ρ` and `τ`, and the self-intertwiners of
`τ` are scalars, then `ρ` and `τ` are equivalent. -/
theorem nonempty_equiv_of_isotypic [Nontrivial V] (ρ : Representation k G X)
    (τ : Representation k G W) (σ : Representation k G V) [ρ.IsIrreducible] [τ.IsIrreducible]
    (hS : ∀ φ : τ.IntertwiningMap τ, ∃ c : k, φ = c • Representation.IntertwiningMap.id τ)
    (hρ : ⨆ f : ρ.IntertwiningMap σ, LinearMap.range f.toLinearMap = ⊤)
    (hτ : ⨆ f : τ.IntertwiningMap σ, LinearMap.range f.toLinearMap = ⊤) :
    Nonempty (ρ.Equiv τ) := by
  obtain ⟨f, u, hfu⟩ := exists_apply_ne_zero_of_isotypic ρ σ hρ
  obtain ⟨w₁, hw₁⟩ := CommutingFamily.exists_ne_zero_of_irreducible τ
  obtain ⟨a, hax, him⟩ := CommutingFamily.exists_isImage τ σ hS hτ hfu hw₁
  have himρ : CommutingFamily.IsImage ρ σ (ρ.asAlgebraHom a u) (σ.asAlgebraHom a (f u)) :=
    ⟨f, CommutingFamily.intertwining_asAlgebraHom f a u⟩
  exact ⟨(CommutingFamily.nonempty_equiv_orbitSpan ρ σ himρ hax).some.trans
    (CommutingFamily.nonempty_equiv_orbitSpan τ σ him hax).some.symm⟩

/-- Fixed lines are transported along an equivalence: if the vectors of `τ` fixed by the
elements of `K` lie on a line, so do those of an equivalent `ρ`. -/
theorem exists_fixed_line_of_equiv {ρ : Representation k G X} {τ : Representation k G W}
    (e : ρ.Equiv τ) (K : Set G)
    (h : ∃ w₀ : W, ∀ w : W, (∀ g ∈ K, τ g w = w) → ∃ c : k, w = c • w₀) :
    ∃ x₀ : X, ∀ x : X, (∀ g ∈ K, ρ g x = x) → ∃ c : k, x = c • x₀ := by
  obtain ⟨w₀, hw₀⟩ := h
  refine ⟨e.symm w₀, fun x hx => ?_⟩
  obtain ⟨c, hc⟩ := hw₀ (e x) fun g hg =>
    (Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g x).symm.trans
      (congrArg e (hx g hg))
  refine ⟨c, ?_⟩
  calc x = e.symm (e x) := (e.symm_apply_apply x).symm
    _ = e.symm (c • w₀) := by rw [hc]
    _ = c • e.symm w₀ := map_smul e.symm c w₀

/-- `τ` is a common isotypic type of `σ` and `σ'`: it is irreducible with scalar
self-intertwiners, and both `σ` and `σ'` are `τ`-isotypic. -/
def IsCommonType (τ : Representation k G W) (σ : Representation k G V)
    (σ' : Representation k G V') : Prop :=
  τ.IsIrreducible ∧
    (∀ φ : τ.IntertwiningMap τ, ∃ c : k, φ = c • Representation.IntertwiningMap.id τ) ∧
    (⨆ f : τ.IntertwiningMap σ, LinearMap.range f.toLinearMap = ⊤) ∧
    ⨆ f : τ.IntertwiningMap σ', LinearMap.range f.toLinearMap = ⊤

end Equivalence

/-! ### Monoid representations -/

section Monoid

variable {k : Type uk} [Field k] {G : Type uG} [Monoid G]
  {V : Type uV} [AddCommGroup V] [Module k V] {V' : Type uV'} [AddCommGroup V'] [Module k V']
  {W : Type uW} [AddCommGroup W] [Module k W] {X : Type uX} [AddCommGroup X] [Module k X]

/-- An intertwining map of monoid representations intertwines the free-monoid
representations. -/
def ofIntertwiningMap {ρ : Representation k G W} {σ : Representation k G V}
    (f : ρ.IntertwiningMap σ) : (rep ⇑ρ).IntertwiningMap (rep ⇑σ) :=
  intertwiningMap f.toLinearMap fun g w => Representation.IntertwiningMap.isIntertwining _ _ f g w

/-- An intertwining map of the free-monoid representations is an intertwining map of the
monoid representations. -/
def toIntertwiningMap {ρ : Representation k G W} {σ : Representation k G V}
    (φ : (rep ⇑ρ).IntertwiningMap (rep ⇑σ)) : ρ.IntertwiningMap σ :=
  φ.toLinearMap.intertwiningMap_of_isIntertwiningMap _ _ (map_generator φ)

theorem iSup_range_rep_eq_top {ρ : Representation k G W} {σ : Representation k G V}
    (h : ⨆ f : ρ.IntertwiningMap σ, LinearMap.range f.toLinearMap = ⊤) :
    ⨆ f : (rep ⇑ρ).IntertwiningMap (rep ⇑σ), LinearMap.range f.toLinearMap = ⊤ :=
  iSup_range_eq_top_of_forall_exists _ _ h fun f => ⟨ofIntertwiningMap f, rfl⟩

theorem isIrreducible_rep_coe (ρ : Representation k G W) [ρ.IsIrreducible] :
    (rep ⇑ρ).IsIrreducible := by
  obtain ⟨w, hw⟩ := CommutingFamily.exists_ne_zero_of_irreducible ρ
  have : Nontrivial W := ⟨⟨w, 0, hw⟩⟩
  refine isIrreducible_rep fun U hU => ?_
  let R : Subrepresentation ρ := ⟨U, fun g _ hx => hU g _ hx⟩
  rcases eq_bot_or_eq_top R with h | h
  · exact Or.inl (congrArg Subrepresentation.toSubmodule h)
  · exact Or.inr (congrArg Subrepresentation.toSubmodule h)

theorem scalar_rep_coe {ρ : Representation k G W}
    (hS : ∀ φ : ρ.IntertwiningMap ρ, ∃ c : k, φ = c • Representation.IntertwiningMap.id ρ)
    (φ : (rep ⇑ρ).IntertwiningMap (rep ⇑ρ)) :
    ∃ c : k, φ = c • Representation.IntertwiningMap.id (rep ⇑ρ) := by
  refine scalar_rep (fun T hT => ?_) φ
  obtain ⟨c, hc⟩ := hS (T.intertwiningMap_of_isIntertwiningMap ρ ρ hT)
  refine ⟨c, fun w => ?_⟩
  have h := congrArg (fun ψ : ρ.IntertwiningMap ρ => ψ w) hc
  simp only [Representation.IntertwiningMap.smul_apply,
    Representation.IntertwiningMap.id_apply] at h
  exact h

/-- **Monoid representations.** Let `σ` be nonzero and `τ`-isotypic for an irreducible `τ`
with scalar self-intertwiners. If `σ` and `σ'` are `ρ`-isotypic for an irreducible `ρ`, then
`rep ⇑ρ` is a common isotypic type of `rep ⇑σ` and `rep ⇑σ'`, and `ρ` is equivalent to `τ`. -/
theorem isCommonType_monoid [Nontrivial V] (ρ : Representation k G X) [ρ.IsIrreducible]
    (τ : Representation k G W) [τ.IsIrreducible]
    (hS : ∀ φ : τ.IntertwiningMap τ, ∃ c : k, φ = c • Representation.IntertwiningMap.id τ)
    (σ : Representation k G V) (σ' : Representation k G V')
    (hτ : ⨆ f : τ.IntertwiningMap σ, LinearMap.range f.toLinearMap = ⊤)
    (hρ : ⨆ f : ρ.IntertwiningMap σ, LinearMap.range f.toLinearMap = ⊤)
    (hρ' : ⨆ f : ρ.IntertwiningMap σ', LinearMap.range f.toLinearMap = ⊤) :
    IsCommonType (rep ⇑ρ) (rep ⇑σ) (rep ⇑σ') ∧ Nonempty (ρ.Equiv τ) := by
  obtain ⟨e⟩ := nonempty_equiv_of_isotypic ρ τ σ hS hρ hτ
  exact ⟨⟨isIrreducible_rep_coe ρ, scalar_rep_coe (CommutingFamily.scalar_of_equiv e.symm hS),
    iSup_range_rep_eq_top hρ, iSup_range_rep_eq_top hρ'⟩, ⟨e⟩⟩

end Monoid

/-! ### `(𝔤, K)`-modules -/

section GK

variable {K : Type uK} [Group K] {L : Type uL} [LieRing L] [LieAlgebra ℂ L]
  {Γ : Type uΓ} (dec : Γ → K ⊕ L)
  {V : Type uV} [AddCommGroup V] [Module ℂ V] {V' : Type uV'} [AddCommGroup V'] [Module ℂ V']
  {W : Type uW} [AddCommGroup W] [Module ℂ W] {X : Type uX} [AddCommGroup X] [Module ℂ X]

/-- The generators of a `(𝔤, K)`-module `(V, ρ, π)` indexed by a type `Γ` decoded into
`K ⊕ 𝔤` by `dec`: the generator `a` acts by `ρ k` if `dec a = k ∈ K` and by `π X` if
`dec a = X ∈ 𝔤`. (In the application `Γ` is `K ⊕ 𝔤` lifted to a larger universe.) -/
def gkGenerators (ρ : Representation ℂ K V) (π : L →ₗ⁅ℂ⁆ Module.End ℂ V) (a : Γ) :
    Module.End ℂ V :=
  Sum.elim (fun k => ρ k) (fun X => π X) (dec a)

/-- The free-monoid representation of a `(𝔤, K)`-module. -/
abbrev gkRep (ρ : Representation ℂ K V) (π : L →ₗ⁅ℂ⁆ Module.End ℂ V) :
    Representation ℂ (FreeMonoid Γ) V :=
  rep (gkGenerators dec ρ π)

variable {dec}

theorem gkGenerators_of_eq_inl (ρ : Representation ℂ K V) (π : L →ₗ⁅ℂ⁆ Module.End ℂ V)
    {a : Γ} {k : K} (h : dec a = Sum.inl k) : gkGenerators dec ρ π a = ρ k := by
  rw [gkGenerators, h, Sum.elim_inl]

theorem gkGenerators_of_eq_inr (ρ : Representation ℂ K V) (π : L →ₗ⁅ℂ⁆ Module.End ℂ V)
    {a : Γ} {X : L} (h : dec a = Sum.inr X) : gkGenerators dec ρ π a = π X := by
  rw [gkGenerators, h, Sum.elim_inr]

/-- Maps of `(𝔤, K)`-modules intertwine the generators. -/
theorem gkGenerators_map {ρ : Representation ℂ K X} {π : L →ₗ⁅ℂ⁆ Module.End ℂ X}
    {ρ' : Representation ℂ K V} {π' : L →ₗ⁅ℂ⁆ Module.End ℂ V} {f : X →ₗ[ℂ] V}
    (hf : f ∈ Archimedean.gkHoms ρ π ρ' π') (a : Γ) (x : X) :
    f (gkGenerators dec ρ π a x) = gkGenerators dec ρ' π' a (f x) := by
  rcases h : dec a with k | Y
  · rw [gkGenerators_of_eq_inl ρ π h, gkGenerators_of_eq_inl ρ' π' h]
    exact hf.1 k x
  · rw [gkGenerators_of_eq_inr ρ π h, gkGenerators_of_eq_inr ρ' π' h]
    exact hf.2 Y x

/-- Isotypy of `(𝔤, K)`-modules gives isotypy of the free-monoid representations. -/
theorem iSup_range_gk_eq_top {ρ : Representation ℂ K X} {π : L →ₗ⁅ℂ⁆ Module.End ℂ X}
    {ρ' : Representation ℂ K V} {π' : L →ₗ⁅ℂ⁆ Module.End ℂ V}
    (h : Archimedean.IsGKIsotypic ρ π ρ' π') :
    ⨆ f : (gkRep dec ρ π).IntertwiningMap (gkRep dec ρ' π'),
      LinearMap.range f.toLinearMap = ⊤ := by
  have h₁ : ⨆ f : Archimedean.gkHoms ρ π ρ' π', LinearMap.range (f : X →ₗ[ℂ] V) = ⊤ :=
    (iSup_subtype' (p := fun f => f ∈ Archimedean.gkHoms ρ π ρ' π')
      (f := fun f _ => LinearMap.range f)).symm.trans h
  exact iSup_range_eq_top_of_forall_exists
    (fun f : Archimedean.gkHoms ρ π ρ' π' => (f : X →ₗ[ℂ] V))
    (fun g : (gkRep dec ρ π).IntertwiningMap (gkRep dec ρ' π') => g.toLinearMap) h₁
    fun f => ⟨intertwiningMap (f : X →ₗ[ℂ] V) (gkGenerators_map f.2), rfl⟩

variable (hdec : Function.Surjective dec)
include hdec

theorem isIrreducible_gk {ρ : Representation ℂ K X} {π : L →ₗ⁅ℂ⁆ Module.End ℂ X}
    (h : Archimedean.IsIrreducibleGKModule ρ π) : (gkRep dec ρ π).IsIrreducible := by
  have : Nontrivial X := h.1
  refine isIrreducible_rep fun U hU => h.2 U (fun k x hx => ?_) (fun Y x hx => ?_)
  · obtain ⟨a, ha⟩ := hdec (Sum.inl k)
    have hmem := hU a x hx
    rwa [gkGenerators_of_eq_inl ρ π ha] at hmem
  · obtain ⟨a, ha⟩ := hdec (Sum.inr Y)
    have hmem := hU a x hx
    rwa [gkGenerators_of_eq_inr ρ π ha] at hmem

theorem scalar_gk [TopologicalSpace K] {ρ : Representation ℂ K X}
    {π : L →ₗ⁅ℂ⁆ Module.End ℂ X} (hyp : Archimedean.GKModuleDensity.Hyp ρ π)
    (φ : (gkRep dec ρ π).IntertwiningMap (gkRep dec ρ π)) :
    ∃ c : ℂ, φ = c • Representation.IntertwiningMap.id _ := by
  refine scalar_rep (fun T hT => Archimedean.GKModuleDensity.exists_eq_scalar hyp T
    (fun k x => ?_) (fun Y x => ?_)) φ
  · obtain ⟨a, ha⟩ := hdec (Sum.inl k)
    have h := hT a x
    rwa [gkGenerators_of_eq_inl ρ π ha] at h
  · obtain ⟨a, ha⟩ := hdec (Sum.inr Y)
    have h := hT a x
    rwa [gkGenerators_of_eq_inr ρ π ha] at h

/-- **`(𝔤, K)`-modules.** Let `(V, ρQ, πQ)` be nonzero and `(ρA, πA)`-isotypic for an
irreducible admissible `(𝔤, K)`-module `(ρA, πA)` satisfying the hypotheses of
`GKModuleDensity`. If `(ρQ, πQ)` and `(ρQ', πQ')` are `(ρ, π)`-isotypic for an irreducible
`(ρ, π)`, then the free-monoid representation of `(ρ, π)` is a common isotypic type of those of
`(ρQ, πQ)` and `(ρQ', πQ')`. -/
theorem isCommonType_gk [TopologicalSpace K] [Nontrivial V]
    {ρ : Representation ℂ K X} {π : L →ₗ⁅ℂ⁆ Module.End ℂ X}
    (hirr : Archimedean.IsIrreducibleGKModule ρ π)
    {ρA : Representation ℂ K W} {πA : L →ₗ⁅ℂ⁆ Module.End ℂ W}
    (hyp : Archimedean.GKModuleDensity.Hyp ρA πA)
    {ρQ : Representation ℂ K V} {πQ : L →ₗ⁅ℂ⁆ Module.End ℂ V}
    {ρQ' : Representation ℂ K V'} {πQ' : L →ₗ⁅ℂ⁆ Module.End ℂ V'}
    (hA : Archimedean.IsGKIsotypic ρA πA ρQ πQ) (hQ : Archimedean.IsGKIsotypic ρ π ρQ πQ)
    (hQ' : Archimedean.IsGKIsotypic ρ π ρQ' πQ') :
    IsCommonType (gkRep dec ρ π) (gkRep dec ρQ πQ) (gkRep dec ρQ' πQ') := by
  have := isIrreducible_gk hdec hirr
  have := isIrreducible_gk hdec hyp.irreducible
  obtain ⟨e⟩ := nonempty_equiv_of_isotypic (gkRep dec ρ π) (gkRep dec ρA πA) (gkRep dec ρQ πQ)
    (scalar_gk hdec hyp) (iSup_range_gk_eq_top hQ) (iSup_range_gk_eq_top hA)
  exact ⟨isIrreducible_gk hdec hirr, CommutingFamily.scalar_of_equiv e.symm (scalar_gk hdec hyp),
    iSup_range_gk_eq_top hQ, iSup_range_gk_eq_top hQ'⟩

end GK

end Langlands.FreeMonoidGenerators
