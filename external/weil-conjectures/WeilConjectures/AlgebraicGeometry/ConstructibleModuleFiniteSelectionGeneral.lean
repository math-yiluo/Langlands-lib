/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.ConstructibleModuleSupportGeneral
import WeilConjectures.AlgebraicGeometry.ConstructibleModuleSubobjectNoetherian
import WeilConjectures.Topology.SpectralConstructibleFiniteIntersection
import WeilConjectures.AlgebraicGeometry.Sites.StalkwiseCokernel

/-! # Finite selection over a Noetherian coefficient ring

Source: Stacks Project, Tag 09Z6 (3), finite selection using constructible supports.
-/

@[expose] public section

universe u w

open CategoryTheory Limits
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

private noncomputable def jointMap {Λ : Type (u + 1)} [CommRing Λ]
    {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (L : Type w) (G : L → Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (φ : ∀ l : L, F ⟶ G l) (S : Finset L) :
    F ⟶ ⨁ fun l : S => G l.1 :=
  biproduct.lift (fun l : S => φ l.1)

private theorem failure_locus_constructible
    (Λ : Type (u + 1)) [CommRing Λ] [IsNoetherianRing Λ]
    (X : Scheme.{u}) [IsNoetherian X]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsConstructibleSheaf F]
    (L : Type w) (G : L → Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (φ : ∀ l : L, F ⟶ G l) (S : Finset L) :
    Topology.IsConstructible {x : X | ¬ Function.Injective
      (((pointSmallEtale (X.algClosurePoint x)).sheafFiber
        (A := ModuleCat.{u + 1} Λ)).map (jointMap F L G φ S))} := by
  let f := jointMap F L G φ S
  let K : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) := kernel f
  let : PreservesColimitsOfSize.{u, u}
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, u + 1, u, u} Λ
  have hK : IsConstructibleSheaf K := by
    apply constructible_of_mono_noetherian (kernel.ι f)
  let U : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⥤
      Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
    sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
  obtain ⟨_, hzero, hc⟩ := constructibleModuleSupport_general (X := X) K
  let H := U.obj K
  have hsupp : etaleSheafSupport H = {x : X |
      ¬ IsZero ((pointSmallEtale (X.algClosurePoint x)).sheafFiber.obj H)} := by
    ext x
    constructor
    · intro hx hz
      exact (hzero x _ (X.algClosurePoint x) (X.algClosurePoint_base x default) hz) hx
    · intro hz
      refine ⟨AlgebraicClosure (X.residueField x), inferInstance, inferInstance,
        X.algClosurePoint x, by simp, ?_⟩
      exact fun h => hz h
  have heq : {x : X | ¬ Function.Injective
      (((pointSmallEtale (X.algClosurePoint x)).sheafFiber
        (A := ModuleCat.{u + 1} Λ)).map f)} = etaleSheafSupport H := by
    rw [hsupp]
    ext x
    let P := pointSmallEtale (X.algClosurePoint x)
    let Q := P.sheafFiber (A := ModuleCat.{u + 1} Λ)
    let e := P.sheafFiberCompIso.{u, u, u + 1, u + 1, u + 1, u + 2, u + 2}
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
    have he : IsZero (Q.obj K) ↔ IsZero (P.sheafFiber.obj H) := by
      have hf : IsZero (Q.obj K) ↔
          IsZero ((P.sheafFiber ⋙ forget₂ (ModuleCat.{u + 1} Λ)
            AddCommGrpCat.{u + 1}).obj K) := by
        rw [ModuleCat.isZero_iff_subsingleton, AddCommGrpCat.isZero_iff_subsingleton]
        rfl
      exact hf.trans (e.app K).isZero_iff.symm
    have hk : IsZero (Q.obj K) ↔ Function.Injective (Q.map f) := by
      let ek := PreservesKernel.iso Q f
      change IsZero (Q.obj (kernel f)) ↔ Function.Injective (Q.map f)
      rw [ek.isZero_iff]
      exact (Preadditive.mono_iff_isZero_kernel _).symm.trans
        (ModuleCat.mono_iff_injective _)
    change (¬ Function.Injective (Q.map f)) ↔ ¬ IsZero (P.sheafFiber.obj H)
    rw [← hk, he]
  rw [heq]
  exact hc

/-- A family containing an injective map at every geometric stalk of a constructible
module sheaf has a finite subfamily whose joint map is monomorphic.
Source: Stacks Project, Tag 09Z6 (3), using constructible-topology compactness.
(blueprint: new-lem-weil-pbc-noetherian-module-finite-selection).

Proof: For each finite family, its joint kernel is a subobject of the constructible
source, hence constructible over the Noetherian coefficient ring. Exactness of stalks
identifies the support of this kernel with the failure locus of injectivity at the
residue-field algebraic-closure points. These loci are constructible. Their total
intersection is empty, since at each point a singleton family is already injective.
Compactness of the constructible topology gives finitely many families with empty
intersection of failure loci. Their union is injective at every test stalk, by
projection to each selected family. Conservativity of the geometric stalks makes
its joint map mono. Reindex its finite index set by `Fin n`. The empty scheme and
empty index set require no separate choices. -/
theorem exists_mono_biproduct_of_constructible_module_stalk_injective_general
    (Λ : Type (u + 1)) [CommRing Λ] [IsNoetherianRing Λ]
    (X : Scheme.{u}) [IsNoetherian X]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsConstructibleSheaf F]
    (L : Type w) (G : L → Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (φ : ∀ l : L, F ⟶ G l)
    (hφ : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X),
      ∃ l : L, Function.Injective
        (((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).map (φ l))) :
    ∃ (n : ℕ) (l : Fin n → L), Mono (biproduct.lift (fun i : Fin n ↦ φ (l i))) := by
  classical
  let E (S : Finset L) : Set X := {x : X | ¬ Function.Injective
    (((pointSmallEtale (X.algClosurePoint x)).sheafFiber
      (A := ModuleCat.{u + 1} Λ)).map (jointMap F L G φ S))}
  have hE (S : Finset L) : Topology.IsConstructible (E S) :=
    failure_locus_constructible Λ X F L G φ S
  have hEmpty : (⋂ S : Finset L, E S) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨l, hl⟩ := hφ _ (X.algClosurePoint x)
    apply Set.mem_iInter.mp hx {l}
    let Q := (pointSmallEtale (X.algClosurePoint x)).sheafFiber
      (A := ModuleCat.{u + 1} Λ)
    have hm : Mono (Q.map (φ l)) := (ModuleCat.mono_iff_injective _).mpr hl
    have he : jointMap F L G φ {l} ≫
        biproduct.π (fun j : ({l} : Finset L) => G j.val) ⟨l, by simp⟩ = φ l := by
      simp [jointMap]
    have : Mono (Q.map (jointMap F L G φ {l})) := by
      apply mono_of_mono_fac (h := Q.map (φ l))
        (g := Q.map (jointMap F L G φ {l}))
        (f := Q.map (biproduct.π (fun j : ({l} : Finset L) => G j.val)
          ⟨l, by simp⟩))
      exact (Q.map_comp _ _).symm.trans (congrArg Q.map he)
    exact (ModuleCat.mono_iff_injective _).mp this
  have : SpectralSpace X := {}
  obtain ⟨A, hA⟩ := finite_subfamily_iInter_eq_empty_of_isConstructible X
    (Finset L) E hE hEmpty
  let S : Finset L := A.biUnion id
  have hm : Mono (jointMap F L G φ S) := by
    constructor
    intro Z a b hab
    apply sheafHom_ext_of_sheafFiber_map_algClosurePoint
    intro x
    obtain ⟨K, hK, hxK⟩ : ∃ K ∈ A, x ∉ E K := by
      by_contra hn
      have hx : x ∈ ⋂ K ∈ A, E K := by
        simp only [Set.mem_iInter]
        intro K hK
        by_contra hxK
        exact hn ⟨K, hK, hxK⟩
      rw [hA] at hx
      exact hx
    have hKS : K ⊆ S := fun l hl => Finset.mem_biUnion.mpr ⟨K, hK, hl⟩
    let p : (⨁ fun l : S => G l.val) ⟶ ⨁ fun l : K => G l.val :=
      biproduct.lift (fun l : K => biproduct.π (fun j : S => G j.val)
        ⟨l.val, hKS l.property⟩)
    have hp : jointMap F L G φ S ≫ p = jointMap F L G φ K := by
      apply biproduct.hom_ext
      intro l
      simp [p, jointMap]
    let Q := (pointSmallEtale (X.algClosurePoint x)).sheafFiber
      (A := ModuleCat.{u + 1} Λ)
    have hinj : Function.Injective (Q.map (jointMap F L G φ K)) := not_not.mp hxK
    have : Mono (Q.map (jointMap F L G φ K)) :=
      (ModuleCat.mono_iff_injective _).mpr hinj
    apply (cancel_mono (Q.map (jointMap F L G φ K))).mp
    rw [← Q.map_comp, ← Q.map_comp, ← hp, ← Category.assoc,
      ← Category.assoc, hab]
  let e := Fintype.equivFin S
  let l : Fin (Fintype.card S) → L := fun i => (e.symm i).val
  have hn : Mono (biproduct.lift (fun i : Fin (Fintype.card S) => φ (l i))) := by
    constructor
    intro Z a b hab
    apply (cancel_mono (jointMap F L G φ S)).mp
    apply biproduct.hom_ext
    intro j
    have he := congrArg (fun f => f ≫
      biproduct.π (fun i : Fin (Fintype.card S) => G (l i)) (e j)) hab
    simp only [Category.assoc, biproduct.lift_π] at he
    change a ≫ φ ((e.symm (e j)).val) = b ≫ φ ((e.symm (e j)).val) at he
    rw [e.symm_apply_apply] at he
    simpa only [jointMap, Category.assoc, biproduct.lift_π] using he
  exact ⟨Fintype.card S, l, hn⟩

end AlgebraicGeometry.Scheme
