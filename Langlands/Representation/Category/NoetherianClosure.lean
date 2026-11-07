import Langlands.Representation.Category.Abelian
import Langlands.Representation.Category.SmoothCoproducts
import Langlands.Representation.CompactCoefficient.GroupTransport
import Langlands.Representation.Filtration.ObjectDefinitions
import Mathlib.RingTheory.Noetherian.Basic

/-! # Closure properties of Noetherian group-algebra modules of representations

A representation `ρ` of a monoid `G` over a commutative ring `k` is Noetherian here when
its group-algebra module `ρ.asModule` is a Noetherian `k[G]`-module. This module proves
that this property passes to sources of injective intertwiners, targets of surjective
intertwiners, extensions, representations with a finite filtration whose graded quotients
are Noetherian, finite direct sums, and pullbacks along surjective monoid homomorphisms.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory
open scoped MonoidAlgebra

namespace Langlands.NoetherianRepresentation

universe uR uG uH uI uU uV uW

section Representation

variable {k : Type uR} [CommRing k] {G : Type uG} [Monoid G]
  {U : Type uU} {V : Type uV} {W : Type uW}
  [AddCommGroup U] [Module k U] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]

/-- The source of an injective intertwiner into a Noetherian representation is Noetherian. -/
theorem of_injective {ρ : Representation k G V} {σ : Representation k G W}
    (f : ρ.IntertwiningMap σ) (hf : Function.Injective f)
    [IsNoetherian k[G] σ.asModule] : IsNoetherian k[G] ρ.asModule :=
  isNoetherian_of_injective (Representation.IntertwiningMap.equivLinearMapAsModule ρ σ f) hf

/-- The target of a surjective intertwiner out of a Noetherian representation is
Noetherian. -/
theorem of_surjective {ρ : Representation k G V} {σ : Representation k G W}
    (f : ρ.IntertwiningMap σ) (hf : Function.Surjective f)
    [IsNoetherian k[G] ρ.asModule] : IsNoetherian k[G] σ.asModule :=
  isNoetherian_of_surjective (Representation.IntertwiningMap.equivLinearMapAsModule ρ σ f)
    (LinearMap.range_eq_top.mpr hf)

/-- Equivalent representations are Noetherian together. -/
theorem of_equiv {ρ : Representation k G V} {σ : Representation k G W} (e : ρ.Equiv σ)
    [IsNoetherian k[G] ρ.asModule] : IsNoetherian k[G] σ.asModule :=
  of_surjective e.toIntertwiningMap e.toLinearEquiv.surjective

/-- Extensions: if `i : ρ → σ` and `q : σ → τ` are intertwiners with `ker q ⊆ range i`
and `ρ`, `τ` are Noetherian, then `σ` is Noetherian. Neither injectivity of `i`, nor
surjectivity of `q`, nor `q ∘ i = 0` is assumed. -/
theorem of_extension {ρ : Representation k G U} {σ : Representation k G V}
    {τ : Representation k G W} (i : ρ.IntertwiningMap σ) (q : σ.IntertwiningMap τ)
    (hexact : ∀ v, q v = 0 → ∃ u, i u = v)
    [IsNoetherian k[G] ρ.asModule] [IsNoetherian k[G] τ.asModule] :
    IsNoetherian k[G] σ.asModule := by
  let i' := Representation.IntertwiningMap.equivLinearMapAsModule ρ σ i
  let q' := Representation.IntertwiningMap.equivLinearMapAsModule σ τ q
  rw [isNoetherian_iff_submodule_quotient (LinearMap.ker q')]
  constructor
  · have hle : LinearMap.ker q' ≤ LinearMap.range i' := by
      intro v hv
      obtain ⟨u, hu⟩ := hexact v (LinearMap.mem_ker.mp hv)
      exact ⟨u, hu⟩
    exact isNoetherian_of_le hle
  · exact isNoetherian_of_linearEquiv q'.quotKerEquivRange.symm

/-- Pullback along a surjective monoid homomorphism `f` does not change the invariant
subspaces: the `k[G]`-submodules of `ρ.asModule` and the `k[H]`-submodules of
`(ρ.comp f).asModule` are the same subspaces of `V`. -/
def compSubmoduleOrderIso {H : Type uH} [Monoid H] (ρ : Representation k G V)
    (f : H →* G) (hf : Function.Surjective f) :
    Submodule k[G] ρ.asModule ≃o Submodule k[H] (Representation.asModule (ρ.comp f)) :=
  Subrepresentation.subrepresentationSubmoduleOrderIso.symm.trans
    ((show Subrepresentation ρ ≃o Subrepresentation (ρ.comp f) from
      { toFun := fun S => ⟨S.toSubmodule, fun h _ hv => S.apply_mem_toSubmodule (f h) hv⟩
        invFun := fun S => ⟨S.toSubmodule, fun g _ hv => by
          obtain ⟨h, rfl⟩ := hf g
          exact S.apply_mem_toSubmodule h hv⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_rel_iff' := Iff.rfl }).trans
      Subrepresentation.subrepresentationSubmoduleOrderIso)

/-- The submodule corresponding to `N` has the same vectors as `N`. -/
@[simp]
theorem mem_compSubmoduleOrderIso {H : Type uH} [Monoid H] (ρ : Representation k G V)
    (f : H →* G) (hf : Function.Surjective f) (N : Submodule k[G] ρ.asModule) (v : V) :
    v ∈ compSubmoduleOrderIso ρ f hf N ↔ v ∈ N :=
  Iff.rfl

/-- Pullback along a surjective monoid homomorphism preserves and reflects Noetherianity:
both group-algebra modules have the same invariant subspaces. -/
theorem comp_surjective_iff {H : Type uH} [Monoid H] (ρ : Representation k G V)
    (f : H →* G) (hf : Function.Surjective f) :
    IsNoetherian k[G] ρ.asModule ↔ IsNoetherian k[H] (Representation.asModule (ρ.comp f)) := by
  let e := compSubmoduleOrderIso ρ f hf
  rw [isNoetherian_iff, isNoetherian_iff]
  exact ⟨fun _ => e.symm.strictMono.wellFoundedGT, fun _ => e.strictMono.wellFoundedGT⟩

/-- A finite direct sum of Noetherian representations is Noetherian. -/
theorem directSum {ι : Type uI} [Finite ι] {V : ι → Type uV}
    [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)] (ρ : ∀ i, Representation k G (V i))
    [∀ i, IsNoetherian k[G] (ρ i).asModule] :
    IsNoetherian k[G] (Representation.directSum ρ).asModule := by
  classical
  let π : ∀ i, (Representation.directSum ρ).IntertwiningMap (ρ i) := fun i =>
    { toLinearMap := DirectSum.component k ι V i
      isIntertwining' := fun _ => by
        ext v
        rfl }
  let f : (Representation.directSum ρ).asModule →ₗ[k[G]] ∀ i, (ρ i).asModule :=
    LinearMap.pi fun i =>
      Representation.IntertwiningMap.equivLinearMapAsModule _ (ρ i) (π i)
  refine isNoetherian_of_injective f fun x y hxy => ?_
  exact DirectSum.ext_component k fun i => congrFun hxy i

/-- A representation with a finite filtration by subrepresentations whose graded
quotients are all Noetherian is Noetherian. -/
theorem of_objectRepFiltration {A : Rep.{uV} k G} {n : ℕ} (s : ObjectRepFiltration A n)
    (hgr : ∀ i, IsNoetherian k[G] (s.gradedRepresentation i).ρ.asModule) :
    IsNoetherian k[G] A.ρ.asModule := by
  have hstep : ∀ m (hm : m < n + 1),
      IsNoetherian k[G] (s.subrepresentation ⟨m, hm⟩).toRepresentation.asModule := by
    intro m
    induction m with
    | zero =>
      intro hm
      have hbot : s.subrepresentation ⟨0, hm⟩ = ⊥ := s.subrepresentation_zero
      have : Subsingleton (s.subrepresentation ⟨0, hm⟩).toRepresentation.asModule := by
        constructor
        rintro ⟨a, ha⟩ ⟨b, hb⟩
        apply Subtype.ext
        change a = b
        rw [hbot] at ha hb
        rw [(Submodule.mem_bot k).1 ha, (Submodule.mem_bot k).1 hb]
      infer_instance
    | succ m ih =>
      intro hm
      let i : Fin n := ⟨m, by omega⟩
      have : IsNoetherian k[G] (s.subrepresentation i.castSucc).toRepresentation.asModule :=
        ih (by omega)
      have := hgr i
      let incl : (s.subrepresentation i.castSucc).toRepresentation.IntertwiningMap
          (s.subrepresentation i.succ).toRepresentation :=
        { toLinearMap := Submodule.inclusion
            (s.monotone_subrepresentation (Fin.castSucc_le_succ i))
          isIntertwining' := fun _ => rfl }
      exact of_extension (ρ := (s.subrepresentation i.castSucc).toRepresentation)
        incl (s.gradedProjection i).hom
        (by
          intro v hv
          have hmem := (Submodule.Quotient.mk_eq_zero _).1 hv
          exact ⟨⟨v, hmem⟩, rfl⟩)
  have htop := hstep n (Nat.lt_succ_self n)
  have hlast : s.subrepresentation ⟨n, Nat.lt_succ_self n⟩ = ⊤ := s.subrepresentation_last
  let f : A.ρ.IntertwiningMap (s.subrepresentation ⟨n, Nat.lt_succ_self n⟩).toRepresentation :=
    { toLinearMap :=
        { toFun := fun v => ⟨v, by rw [hlast]; trivial⟩
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      isIntertwining' := fun _ => rfl }
  exact of_injective f fun v w h => congrArg Subtype.val h

end Representation

end Langlands.NoetherianRepresentation

namespace Langlands.SmoothRep

open Langlands.NoetherianRepresentation

universe uG uH uI uV

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- The source of a monomorphism of smooth representations into a Noetherian one is
Noetherian. -/
theorem isNoetherian_of_mono {A B : SmoothRep.{0, uG, uV} ℂ G} (f : A ⟶ B) [Mono f]
    [IsNoetherian ℂ[G] B.representation.asModule] :
    IsNoetherian ℂ[G] A.representation.asModule :=
  of_injective (hom f) ((mono_iff_injective f).mp inferInstance)

/-- The target of an epimorphism of smooth representations out of a Noetherian one is
Noetherian. -/
theorem isNoetherian_of_epi {A B : SmoothRep.{0, uG, uV} ℂ G} (f : A ⟶ B) [Epi f]
    [IsNoetherian ℂ[G] A.representation.asModule] :
    IsNoetherian ℂ[G] B.representation.asModule :=
  of_surjective (hom f) ((epi_iff_surjective f).mp inferInstance)

/-- A finite direct sum of Noetherian smooth representations is Noetherian. -/
theorem isNoetherian_directSum {ι : Type uI} [DecidableEq ι] [Finite ι]
    (A : ι → SmoothRep.{0, uG, max uI uV} ℂ G)
    [∀ i, IsNoetherian ℂ[G] (A i).representation.asModule] :
    IsNoetherian ℂ[G] (directSum A).representation.asModule :=
  NoetherianRepresentation.directSum fun i => (A i).representation

/-- A smooth representation admitting an injective intertwiner into a finite direct sum of
Noetherian smooth representations is finitely generated over the group algebra. -/
theorem finite_of_injective_directSum {ι : Type uI} [DecidableEq ι] [Finite ι]
    (A : ι → SmoothRep.{0, uG, max uI uV} ℂ G)
    [∀ i, IsNoetherian ℂ[G] (A i).representation.asModule]
    {E : SmoothRep.{0, uG, max uI uV} ℂ G}
    (f : E.representation.IntertwiningMap (directSum A).representation)
    (hf : Function.Injective f) :
    Module.Finite ℂ[G] E.representation.asModule :=
  haveI := isNoetherian_directSum A
  haveI := of_injective f hf
  inferInstance

/-- Pullback along a topological group isomorphism preserves and reflects
Noetherianity. -/
theorem isNoetherian_pullback_iff {H : Type uH} [Group H] [TopologicalSpace H]
    (e : H ≃ₜ* G) (A : SmoothRep.{0, uG, uV} ℂ G) :
    IsNoetherian ℂ[H] (pullback e A).representation.asModule ↔
      IsNoetherian ℂ[G] A.representation.asModule :=
  (comp_surjective_iff A.representation e.toMonoidHom e.surjective).symm

end Langlands.SmoothRep
