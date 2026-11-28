import Langlands.Weil.Representation.Restriction
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.DenseEmbedding

/-!
# Restriction of continuous representations along a map with dense image

Let `E` be a Hausdorff topological field, `G` a monoid with a topology and `φ : H →* G` a
monoid homomorphism with dense image. For representations of `G` on `E`-vector spaces whose
action map is continuous for the module topology on the endomorphisms, the conditions "`f`
intertwines at `g`", "`ρ g` preserves the subspace `U`" and "a matrix entry of `ρ g` lies in
the closed set `S`" cut out closed subsets of `G`. A closed set containing the image of `φ` is
all of `G`, so restriction along `φ` preserves and reflects intertwiners, isomorphism,
subrepresentations, irreducibility and closed conditions on matrix entries.
-/

noncomputable section

universe uE uG uH uV uW

namespace Langlands.Representation

variable {E : Type uE} [Field E] [TopologicalSpace E]
  {G : Type uG} [TopologicalSpace G] {H : Type uH} [Monoid H]
  {V : Type uV} [AddCommGroup V] [Module E V]
  {W : Type uW} [AddCommGroup W] [Module E W]

/-- If the coordinates of two families of vectors against every linear functional depend
continuously on the parameter, the set of parameters where the two families agree is closed. -/
theorem isClosed_setOf_eq_of_continuous_dual [T2Space E] {α β : G → W}
    (hα : ∀ ψ : Module.Dual E W, Continuous fun g => ψ (α g))
    (hβ : ∀ ψ : Module.Dual E W, Continuous fun g => ψ (β g)) :
    IsClosed {g | α g = β g} := by
  have h : {g | α g = β g} = ⋂ ψ : Module.Dual E W, {g | ψ (α g) = ψ (β g)} := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    refine ⟨fun h ψ => by rw [h], fun h => ?_⟩
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff E]
    intro ψ
    rw [map_sub, sub_eq_zero]
    exact h ψ
  rw [h]
  exact isClosed_iInter fun ψ => isClosed_eq (hα ψ) (hβ ψ)

variable [IsTopologicalRing E] [Monoid G]
  [TopologicalSpace (Module.End E V)] [IsModuleTopology E (Module.End E V)]

/-- A matrix coefficient `g ↦ ψ (ρ g v)` of a representation whose action map is continuous
for the module topology on the endomorphisms is continuous. -/
theorem continuous_dual_apply {ρ : Representation E G V} (hρ : Continuous ρ)
    (ψ : Module.Dual E V) (v : V) : Continuous fun g => ψ (ρ g v) :=
  (IsModuleTopology.continuous_of_linearMap (ψ ∘ₗ LinearMap.applyₗ v)).comp hρ

/-- For a basis `b` and a closed set `S` of scalars, the elements whose matrix entry `(i, j)`
lies in `S` form a closed set. -/
theorem isClosed_setOf_repr_mem {ρ : Representation E G V} (hρ : Continuous ρ)
    {ι : Type*} (b : Module.Basis ι E V) {S : Set E} (hS : IsClosed S) (i j : ι) :
    IsClosed {g | b.repr (ρ g (b j)) i ∈ S} :=
  hS.preimage (continuous_dual_apply hρ (b.coord i) (b j))

/-- Along a homomorphism with dense image, if the matrix entries of a continuous
representation in a basis lie in a closed set on the image, they lie in it everywhere. -/
theorem repr_mem_of_denseRange (φ : H →* G) (hφ : DenseRange φ) {ρ : Representation E G V}
    (hρ : Continuous ρ) {ι : Type*} (b : Module.Basis ι E V) {S : Set E} (hS : IsClosed S)
    (hb : ∀ h i j, b.repr (ρ (φ h) (b j)) i ∈ S) (g : G) (i j : ι) :
    b.repr (ρ g (b j)) i ∈ S :=
  hφ.induction_on (p := fun g => b.repr (ρ g (b j)) i ∈ S) g
    (isClosed_setOf_repr_mem hρ b hS i j) fun h => hb h i j

variable [T2Space E]

/-- The elements at which a linear map intertwines two continuous representations form a
closed set. -/
theorem isClosed_setOf_intertwines [TopologicalSpace (Module.End E W)]
    [IsModuleTopology E (Module.End E W)] {ρ : Representation E G V} {σ : Representation E G W}
    (hρ : Continuous ρ) (hσ : Continuous σ) (f : V →ₗ[E] W) :
    IsClosed {g | ∀ v, f (ρ g v) = σ g (f v)} := by
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun v => isClosed_setOf_eq_of_continuous_dual
    (fun ψ => continuous_dual_apply hρ (ψ ∘ₗ f) v) (fun ψ => continuous_dual_apply hσ ψ (f v))

/-- The elements whose action preserves a given subspace form a closed set. -/
theorem isClosed_setOf_mapsTo {ρ : Representation E G V} (hρ : Continuous ρ)
    (U : Submodule E V) : IsClosed {g | ∀ v ∈ U, ρ g v ∈ U} := by
  have h : {g | ∀ v ∈ U, ρ g v ∈ U} =
      ⋂ v ∈ U, ⋂ ψ ∈ U.dualAnnihilator, {g | ψ (ρ g v) = 0} := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    exact forall₂_congr fun v _ =>
      (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff U (ρ g v)).symm
  rw [h]
  exact isClosed_biInter fun v _ => isClosed_biInter fun ψ _ =>
    isClosed_eq (continuous_dual_apply hρ ψ v) continuous_const

variable (φ : H →* G)

/-- Along a homomorphism with dense image, a linear map intertwines two continuous
representations if and only if it intertwines their restrictions. -/
theorem intertwines_iff_of_denseRange [TopologicalSpace (Module.End E W)]
    [IsModuleTopology E (Module.End E W)] (hφ : DenseRange φ) {ρ : Representation E G V}
    {σ : Representation E G W} (hρ : Continuous ρ) (hσ : Continuous σ) (f : V →ₗ[E] W) :
    (∀ g v, f (ρ g v) = σ g (f v)) ↔ ∀ h v, f (ρ (φ h) v) = σ (φ h) (f v) :=
  ⟨fun hf h => hf (φ h), fun hf g =>
    hφ.induction_on (p := fun g => ∀ v, f (ρ g v) = σ g (f v)) g
      (isClosed_setOf_intertwines hρ hσ f) hf⟩

/-- Along a homomorphism with dense image, a subspace is stable under a continuous
representation if and only if it is stable under its restriction. -/
theorem mapsTo_iff_of_denseRange (hφ : DenseRange φ) {ρ : Representation E G V}
    (hρ : Continuous ρ) (U : Submodule E V) :
    (∀ g, ∀ v ∈ U, ρ g v ∈ U) ↔ ∀ h, ∀ v ∈ U, ρ (φ h) v ∈ U :=
  ⟨fun hU h => hU (φ h), fun hU g =>
    hφ.induction_on (p := fun g => ∀ v ∈ U, ρ g v ∈ U) g (isClosed_setOf_mapsTo hρ U) hU⟩

/-- Along a homomorphism with dense image, two continuous representations are equivalent if
and only if their restrictions are. -/
theorem nonempty_equiv_iff_of_denseRange [TopologicalSpace (Module.End E W)]
    [IsModuleTopology E (Module.End E W)] (hφ : DenseRange φ) {ρ : Representation E G V}
    {σ : Representation E G W} (hρ : Continuous ρ) (hσ : Continuous σ) :
    Nonempty (ρ.Equiv σ) ↔ Nonempty (Representation.Equiv (ρ.comp φ) (σ.comp φ)) := by
  constructor
  · rintro ⟨e⟩
    exact ⟨Representation.Equiv.mk e.toLinearEquiv fun h => e.isIntertwining' (φ h)⟩
  · rintro ⟨e⟩
    have he : ∀ h v, e.toLinearEquiv (ρ (φ h) v) = σ (φ h) (e.toLinearEquiv v) :=
      fun h v => LinearMap.congr_fun (e.isIntertwining' h) v
    have hG := (intertwines_iff_of_denseRange φ hφ hρ hσ e.toLinearEquiv.toLinearMap).2 he
    exact ⟨Representation.Equiv.mk e.toLinearEquiv fun g => LinearMap.ext fun v => hG g v⟩

/-- Along a homomorphism with dense image, the subrepresentations of a continuous
representation are exactly those of its restriction: the same subspaces, with the same
order. -/
def subrepresentationOrderIsoOfDenseRange (hφ : DenseRange φ) {ρ : Representation E G V}
    (hρ : Continuous ρ) : Subrepresentation ρ ≃o Subrepresentation (ρ.comp φ) where
  toFun U := ⟨U.toSubmodule, fun h _ hv => U.apply_mem_toSubmodule (φ h) hv⟩
  invFun U := ⟨U.toSubmodule, fun g =>
    ((mapsTo_iff_of_denseRange φ hφ hρ U.toSubmodule).2
      fun h _ hv => U.apply_mem_toSubmodule h hv) g⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-- Along a homomorphism with dense image, a continuous representation is irreducible if and
only if its restriction is. -/
theorem isIrreducible_comp_iff_of_denseRange (hφ : DenseRange φ) {ρ : Representation E G V}
    (hρ : Continuous ρ) : ρ.IsIrreducible ↔ Representation.IsIrreducible (ρ.comp φ) :=
  OrderIso.isSimpleOrder_iff (subrepresentationOrderIsoOfDenseRange φ hφ hρ)

end Langlands.Representation

namespace Langlands.FiniteRepresentation

variable {E : Type uE} [Field E] [TopologicalSpace E] [IsTopologicalRing E] [T2Space E]
  {G : Type uG} [Monoid G] [TopologicalSpace G] {H : Type uH} [Monoid H] (φ : H →* G)

/-- Along a homomorphism with dense image, two finite-dimensional representations whose
action maps are continuous for the module topology on the endomorphisms are isomorphic if and
only if their restrictions are. -/
theorem isIsomorphic_restrict_iff_of_denseRange (hφ : DenseRange φ)
    {A B : FiniteRepresentation.{uE, uG, uV} E G}
    (hA : letI : TopologicalSpace (Module.End E A) := moduleTopology E (Module.End E A)
      Continuous A.representation)
    (hB : letI : TopologicalSpace (Module.End E B) := moduleTopology E (Module.End E B)
      Continuous B.representation) :
    IsIsomorphic A B ↔ IsIsomorphic (restrict φ A) (restrict φ B) := by
  let : TopologicalSpace (Module.End E A) := moduleTopology E (Module.End E A)
  have : IsModuleTopology E (Module.End E A) := ⟨rfl⟩
  let : TopologicalSpace (Module.End E B) := moduleTopology E (Module.End E B)
  have : IsModuleTopology E (Module.End E B) := ⟨rfl⟩
  exact Representation.nonempty_equiv_iff_of_denseRange φ hφ hA hB

/-- Along a homomorphism with dense image, a finite-dimensional representation whose action
map is continuous for the module topology on the endomorphisms is irreducible if and only if
its restriction is. -/
theorem isIrreducible_restrict_iff_of_denseRange (hφ : DenseRange φ)
    {A : FiniteRepresentation.{uE, uG, uV} E G}
    (hA : letI : TopologicalSpace (Module.End E A) := moduleTopology E (Module.End E A)
      Continuous A.representation) :
    A.representation.IsIrreducible ↔ (restrict φ A).representation.IsIrreducible := by
  let : TopologicalSpace (Module.End E A) := moduleTopology E (Module.End E A)
  have : IsModuleTopology E (Module.End E A) := ⟨rfl⟩
  exact Representation.isIrreducible_comp_iff_of_denseRange φ hφ hA

end Langlands.FiniteRepresentation
