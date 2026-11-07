import Mathlib.Algebra.Module.LocalizedModule.Int
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
import Mathlib.RingTheory.Localization.BaseChange
import Langlands.Shimura.DefiniteFormsDoubleCoset

/-!
# Lattice-valued forms on definite similitude groups

Harris, *Galois properties of cohomological automorphic forms on GL(n)*, 1999, p. 307-308, takes
a `K_ℓ`-stable lattice `𝓛_W` over the ring of integers `𝒪` of `L_ℓ` in the coefficients of `ρ`
and states a natural isomorphism `𝒜_ℓ(GJ, 𝓛_W, K) ⊗_𝒪 L_ℓ ≅ 𝒜_ℓ(GJ, ρ, K)(L_ℓ)`; for trivial
`ρ` the lattice is `𝒪 ⊂ L_ℓ`. This file proves this isomorphism when `L_ℓ` is replaced by any
localization `S` of a commutative ring `O` and the double coset space `GJ(ℚ)\GJ(𝔸^f)/K` is
finite.

## Main definitions

* `scalarFormsMap ι K ρ ρL j hj`: for a `K`-equivariant `O`-linear map `j : V → W`, the map
  `f ↦ j ∘ f` from the forms for `ρL` to the forms for `ρ`.
* `isLocalizedModule_scalarFormsMap`: if `j` is injective and is the localization of `V` at a
  submonoid `M` of `O`, and there are finitely many double cosets, then so is `scalarFormsMap`.
* `formsBaseChangeEquiv`: the resulting `S ⊗[O] forms ι K ρL ≃ₗ[S] forms ι K ρ`,
  `s ⊗ f ↦ s • (j ∘ f)`, for `S` the localization of `O` at `M`.
* `DefiniteForms.IsStableLattice`: Harris's `K_ℓ`-stable `𝒪`-lattice `𝓛_W` in `W(S)`, with
  the action `DefiniteForms.latticeRep` of `K_ℓ` on it.
* `DefiniteForms.latticeFormsEquiv`: Harris's isomorphism
  `𝒜_ℓ(GJ, 𝓛_W, K) ⊗_𝒪 S ≅ 𝒜_ℓ(GJ, ρ, K)(S)`, in the order `S ⊗[O] _`.
* `DefiniteForms.trivialLatticeFormsEquiv`: its trivial case
  `𝒜_ℓ(GJ, 𝒪, K) ⊗_𝒪 S ≅ 𝒜_ℓ(GJ, K)(S)`, for trivial coefficients.
-/

noncomputable section

namespace Langlands.Shimura.EquivariantForms

open scoped TensorProduct

universe uO uS w t uΓ uG

section Lattice

variable {O : Type uO} [CommRing O] (M : Submonoid O) {S : Type uS} [CommRing S] [Algebra O S]
  [IsLocalization M S] {Γ : Type uΓ} {G : Type uG} [Group Γ] [Group G] (ι : Γ →* G)
  (K : Subgroup G) {W : Type w} [AddCommGroup W] [Module S W] [Module O W]
  [IsScalarTower O S W] (ρ : Representation S K W) {V : Type t} [AddCommGroup V] [Module O V]
  (ρL : Representation O K V) (j : V →ₗ[O] W) (hj : ∀ (k : K) (v : V), j (ρL k v) = ρ k (j v))

/-- The map `f ↦ j ∘ f` from the forms for `ρL` to the forms for `ρ`, for a `K`-equivariant
`O`-linear map `j`. -/
def scalarFormsMap : forms ι K ρL →ₗ[O] forms ι K ρ where
  toFun f := ⟨fun g => j (f.1 g), fun γ g => congrArg j (f.2.1 γ g),
    fun g k => (congrArg j (f.2.2 g k)).trans (hj _ _)⟩
  map_add' f₁ f₂ := Subtype.ext (funext fun g => map_add j (f₁.1 g) (f₂.1 g))
  map_smul' c f := Subtype.ext (funext fun g => map_smul j c (f.1 g))

@[simp]
lemma scalarFormsMap_apply_coe (f : forms ι K ρL) (g : G) :
    (scalarFormsMap ι K ρ ρL j hj f).1 g = j (f.1 g) :=
  rfl

include M in
/-- If `j` is injective and identifies `W` with the localization of `V` at `M`, and `ι Γ \ G / K`
is finite, then `f ↦ j ∘ f` identifies the forms for `ρ` with the localization at `M` of the
forms for `ρL`. -/
theorem isLocalizedModule_scalarFormsMap [Finite (DoubleCosets ι K)] [IsLocalizedModule M j]
    (hinj : Function.Injective j) : IsLocalizedModule M (scalarFormsMap ι K ρ ρL j hj) where
  map_units s := by
    rw [← (Algebra.lsmul O (A := S) O (forms ι K ρ)).commutes]
    exact (IsLocalization.map_units S s).map _
  surj F := by
    obtain ⟨s, hs⟩ := IsLocalizedModule.exist_integer_multiples_of_finite M j
      (fun x : DoubleCosets ι K => F.1 x.out)
    choose v hv using hs
    have hinv : ∀ x, v x ∈ Representation.invariants
        (ρL.comp (doubleCosetStabilizer ι K x.out).subtype) := by
      intro x
      refine (Representation.mem_invariants _ _).2 fun k => hinj ?_
      change j (ρL k (v x)) = j (v x)
      rw [hj, hv, (ρ k).map_smul_of_tower]
      congr 1
      exact (Representation.mem_invariants _ _).1 (apply_mem_invariants F x.out) k
    refine ⟨⟨(doubleCosetEquiv ι K ρL).symm (fun x => ⟨v x, hinv x⟩), s⟩, ?_⟩
    apply (doubleCosetEquiv ι K ρ).injective
    refine funext fun x => Subtype.ext ?_
    rw [doubleCosetEquiv_apply_coe, doubleCosetEquiv_apply_coe, scalarFormsMap_apply_coe]
    have := congrArg (fun φ => (φ x).1)
      ((doubleCosetEquiv ι K ρL).apply_symm_apply (fun x => ⟨v x, hinv x⟩))
    simp only [doubleCosetEquiv_apply_coe] at this
    rw [this, hv]
    rfl
  exists_of_eq {f₁ f₂} h := ⟨1, by
    rw [one_smul, one_smul]
    exact Subtype.ext (funext fun g => hinj (congrArg (fun F => F.1 g) h))⟩

variable [Finite (DoubleCosets ι K)] [IsLocalizedModule M j]

/-- Under the hypotheses of `isLocalizedModule_scalarFormsMap`, the forms for `ρ` are the base change
from `O` to `S` of the forms for `ρL`: `S ⊗[O] forms ι K ρL ≃ forms ι K ρ`,
`s ⊗ f ↦ s • (j ∘ f)`. -/
def formsBaseChangeEquiv (hinj : Function.Injective j) :
    S ⊗[O] forms ι K ρL ≃ₗ[S] forms ι K ρ :=
  haveI := isLocalizedModule_scalarFormsMap M ι K ρ ρL j hj hinj
  (IsLocalizedModule.isBaseChange M S (scalarFormsMap ι K ρ ρL j hj)).equiv

/-- `formsBaseChangeEquiv` sends `s ⊗ f` to `g ↦ s • j (f g)`. -/
lemma formsBaseChangeEquiv_tmul (hinj : Function.Injective j) (s : S) (f : forms ι K ρL)
    (g : G) : (formsBaseChangeEquiv M ι K ρ ρL j hj hinj (s ⊗ₜ f)).1 g = s • j (f.1 g) := by
  have := isLocalizedModule_scalarFormsMap M ι K ρ ρL j hj hinj
  rw [formsBaseChangeEquiv, IsBaseChange.equiv_tmul]
  rfl

end Lattice

end Langlands.Shimura.EquivariantForms

namespace Langlands.Shimura.DefiniteForms

open Langlands.Global Langlands.Shimura.EquivariantForms
open scoped TensorProduct

universe u v w uO

variable {A : Type v} [Ring A] [Algebra ℚ A] (σ : AlgebraInvolution ℚ A) [Module.Finite ℚ A]
  (ℓ : FinitePlace ℚ)

section Lattice

variable {L : Type u} [Field L] [Algebra ℚ L] {W : Type w} [AddCommGroup W] [Module L W]
  (ρ : (σ.baseChange L).AlgebraicRepresentation W) {S : Type u} [CommRing S] [Algebra ℚ S]
  [Algebra L S] (φ : FiniteCompletion ℚ ℓ →ₐ[ℚ] S) (K : Subgroup σ.FiniteAdelicPoints)
  {O : Type uO} [CommRing O] [Algebra O S]

/-- Harris's `K_ℓ`-stable `𝒪`-lattice `𝓛_W` in `W(S)` (1999, p. 307): an `O`-submodule of
`W(S) = S ⊗[L] W` that is finitely generated over `O`, spans `W(S)` over `S`, and is stable under
`ρ(k_ℓ)` for every `k_ℓ ∈ K_ℓ`. -/
structure IsStableLattice (𝓛 : Submodule O (S ⊗[L] W)) : Prop where
  fg : 𝓛.FG
  span_eq_top : Submodule.span S (𝓛 : Set (S ⊗[L] W)) = ⊤
  mem : ∀ (k : localLevel σ ℓ K), ∀ v ∈ 𝓛, localRep σ ℓ ρ φ K k v ∈ 𝓛

variable {σ ℓ ρ φ K} {𝓛 : Submodule O (S ⊗[L] W)}

/-- The action of `K_ℓ` on a `K_ℓ`-stable lattice `𝓛_W` by restriction of `ρ`. -/
def latticeRep (h : IsStableLattice σ ℓ ρ φ K 𝓛) : Representation O (localLevel σ ℓ K) 𝓛 where
  toFun k := ((localRep σ ℓ ρ φ K k).restrictScalars O).restrict (h.mem k)
  map_one' := by ext; simp
  map_mul' k₁ k₂ := by
    ext v
    change localRep σ ℓ ρ φ K (k₁ * k₂) v = localRep σ ℓ ρ φ K k₁ (localRep σ ℓ ρ φ K k₂ v)
    rw [map_mul]
    rfl

@[simp]
lemma latticeRep_apply_coe (h : IsStableLattice σ ℓ ρ φ K 𝓛) (k : localLevel σ ℓ K) (v : 𝓛) :
    (latticeRep h k v : S ⊗[L] W) = localRep σ ℓ ρ φ K k v :=
  rfl

variable (M : Submonoid O) [IsLocalization M S]

include M in
/-- If `S` is the localization of `O` at `M`, then the inclusion of a lattice `𝓛_W` into `W(S)`
is the localization of `𝓛_W` at `M`. -/
theorem IsStableLattice.isLocalizedModule (h : IsStableLattice σ ℓ ρ φ K 𝓛) :
    IsLocalizedModule M 𝓛.subtype where
  map_units s := by
    rw [← (Algebra.lsmul O (A := S) O (S ⊗[L] W)).commutes]
    exact (IsLocalization.map_units S s).map _
  surj x := by
    have hx : x ∈ Submodule.span S (𝓛 : Set (S ⊗[L] W)) := h.span_eq_top ▸ Submodule.mem_top
    obtain ⟨y, hy, z, rfl⟩ := (IsLocalization.mem_span_iff (M := M)).1 hx
    rw [Submodule.span_eq] at hy
    refine ⟨⟨⟨y, hy⟩, z⟩, ?_⟩
    change (z : O) • (IsLocalization.mk' S 1 z • y) = y
    rw [← IsScalarTower.algebraMap_smul S (z : O), smul_smul, IsLocalization.mk'_spec', map_one,
      one_smul]
  exists_of_eq {v₁ v₂} hv := ⟨1, by rw [one_smul, one_smul]; exact Subtype.ext hv⟩

variable [Finite (DoubleCosets σ.finiteAdelicDiagonal K)]

/-- Harris's natural isomorphism `𝒜_ℓ(GJ, 𝓛_W, K) ⊗_𝒪 L_ℓ ≅ 𝒜_ℓ(GJ, ρ, K)(L_ℓ)` (1999, p. 308),
for `S` the localization of `O` at `M` (for instance `L_ℓ` and its ring of integers `𝒪`), a
`K_ℓ`-stable `O`-lattice `𝓛_W` in `W(S)`, and finitely many double cosets `GJ(ℚ)\GJ(𝔸^f)/K`:
`s ⊗ f ↦ s • f`. -/
def latticeFormsEquiv (h : IsStableLattice σ ℓ ρ φ K 𝓛) :
    S ⊗[O] ellModuleForms σ ℓ K (V := 𝓛) (latticeRep h) ≃ₗ[S] ellAdicForms σ ρ ℓ φ K :=
  haveI := h.isLocalizedModule M
  (formsBaseChangeEquiv (V := 𝓛) (W := S ⊗[L] W) M σ.finiteAdelicDiagonal K
    ((localRep σ ℓ ρ φ K).comp (localLevelMap σ ℓ K)) ((latticeRep h).comp (localLevelMap σ ℓ K))
    𝓛.subtype (fun _ _ => rfl) 𝓛.injective_subtype :)

/-- `latticeFormsEquiv` sends `s ⊗ f` to `g ↦ s • f g`. -/
lemma latticeFormsEquiv_tmul (h : IsStableLattice σ ℓ ρ φ K 𝓛) (s : S)
    (f : ellModuleForms σ ℓ K (V := 𝓛) (latticeRep h)) (g : σ.FiniteAdelicPoints) :
    (latticeFormsEquiv M h (s ⊗ₜ f)).1 g = s • (f.1 g : S ⊗[L] W) := by
  have := h.isLocalizedModule M
  unfold latticeFormsEquiv
  exact (formsBaseChangeEquiv_tmul (V := 𝓛) (W := S ⊗[L] W) M σ.finiteAdelicDiagonal K
    ((localRep σ ℓ ρ φ K).comp (localLevelMap σ ℓ K)) ((latticeRep h).comp (localLevelMap σ ℓ K))
    𝓛.subtype (fun _ _ => rfl) 𝓛.injective_subtype s f g :)

end Lattice

section Trivial

variable (K : Subgroup σ.FiniteAdelicPoints) {O : Type uO} [CommRing O] (M : Submonoid O)
  {S : Type u} [CommRing S] [Algebra O S] [IsLocalization M S]
  [Finite (DoubleCosets σ.finiteAdelicDiagonal K)]

/-- Harris's trivial case (1999, p. 308): for the lattice `𝒪` in `L_ℓ`,
`𝒜_ℓ(GJ, 𝒪, K) ⊗_𝒪 L_ℓ ≅ 𝒜_ℓ(GJ, K)(L_ℓ)`, `s ⊗ f ↦ s • f`, with both sides the forms of
`ellModuleForms` for the trivial action of `K_ℓ`, for `S` the localization of `O` at `M` with
`O → S` injective and finitely many double cosets `GJ(ℚ)\GJ(𝔸^f)/K`. -/
def trivialLatticeFormsEquiv (hinj : Function.Injective (algebraMap O S)) :
    S ⊗[O] ellModuleForms σ ℓ K (Representation.trivial O (localLevel σ ℓ K) O) ≃ₗ[S]
      ellModuleForms σ ℓ K (Representation.trivial S (localLevel σ ℓ K) S) :=
  formsBaseChangeEquiv M σ.finiteAdelicDiagonal K
    ((Representation.trivial S (localLevel σ ℓ K) S).comp (localLevelMap σ ℓ K))
    ((Representation.trivial O (localLevel σ ℓ K) O).comp (localLevelMap σ ℓ K))
    (Algebra.linearMap O S) (fun _ _ => rfl) hinj

/-- `trivialLatticeFormsEquiv` sends `s ⊗ f` to `g ↦ s * f g`. -/
lemma trivialLatticeFormsEquiv_tmul (hinj : Function.Injective (algebraMap O S)) (s : S)
    (f : ellModuleForms σ ℓ K (Representation.trivial O (localLevel σ ℓ K) O))
    (g : σ.FiniteAdelicPoints) :
    (trivialLatticeFormsEquiv σ ℓ K M hinj (s ⊗ₜ f)).1 g = s * algebraMap O S (f.1 g) :=
  formsBaseChangeEquiv_tmul M σ.finiteAdelicDiagonal K _ _ (Algebra.linearMap O S)
    (fun _ _ => rfl) hinj s f g

end Trivial

end Langlands.Shimura.DefiniteForms
