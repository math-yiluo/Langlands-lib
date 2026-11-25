/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.GroupTheory.Torsion
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.CategoryTheory.Abelian.Exact

/-!
# The map on sheaf cohomology induced by an exact functor

Sheaf cohomology `CategoryTheory.Sheaf.H F n` is the `Ext`-group in degree `n` from the
constant sheaf `ℤ` to `F`. An exact functor `G` between two categories of abelian sheaves
therefore induces a map on cohomology as soon as it is compatible with the constant sheaves:
push an `Ext`-class forward along `G` and precompose with the comparison of constant sheaves.

## Main definitions

- `CategoryTheory.Sheaf.IsTorsion`: a sheaf of abelian groups every section of which is locally
  torsion.
- `CategoryTheory.Sheaf.H.mapFunctor`: the map `H F n →+ H (G.obj F) n` on sheaf cohomology
  induced by an exact functor `G` together with an isomorphism `e` between the constant
  sheaf `ℤ` on the target site and the image under `G` of the constant sheaf `ℤ` on the
  source site.

## Main statements

- `CategoryTheory.Sheaf.H.mapFunctor_map`: the induced map is natural in the sheaf.
- `CategoryTheory.Sheaf.H.mapFunctor_bijective`: it is bijective as soon as `G` is fully
  faithful and preserves injective objects, and the source category of sheaves has enough
  injective objects.
- `CategoryTheory.Sheaf.subsingleton_H_one_of_surjective`: `H¹(F) = 0` as soon as, for every
  short exact sequence `0 → F → E → Q → 0`, every global section of `Q` lifts to `E`.
- `CategoryTheory.Sheaf.H.exact_δ_map` and `CategoryTheory.Sheaf.H.exact_map_map`: exactness of
  the long exact cohomology sequence `Γ(S.X₃) → H¹(S.X₁) → H¹(S.X₂)` and
  `Hⁿ(S.X₁) → Hⁿ(S.X₂) → Hⁿ(S.X₃)` of a short exact sequence of abelian sheaves.
- `CategoryTheory.Sheaf.H.δSucc`, `CategoryTheory.Sheaf.H.exact_map_δSucc` and
  `CategoryTheory.Sheaf.H.exact_δSucc_map`: the connecting homomorphism `Hⁿ(S.X₃) → Hⁿ⁺¹(S.X₁)`
  and the exactness of the long exact cohomology sequence around it.
- `CategoryTheory.Sheaf.H.quotientRangeAddEquiv`: for a short exact sequence
  `0 → F → I → Q → 0` with `H¹(I) = 0`, the connecting homomorphism identifies `H¹(F)` with
  the cokernel of `Γ(I) → Γ(Q)`.
- `CategoryTheory.Sheaf.exists_shortExact_injective_addEquiv_H_one`: such a sequence exists
  with `I` injective.
- `CategoryTheory.Sheaf.H.connecting`: the connecting homomorphism `Hⁿ(S.X₃) → Hⁿ⁺¹(S.X₁)` of a
  short exact sequence, natural (`CategoryTheory.Sheaf.H.map_connecting`) and with kernel the
  image of `Hⁿ(S.X₂)` (`CategoryTheory.Sheaf.H.connecting_eq_zero_iff`).
- `CategoryTheory.Sheaf.functorHZeroIso`: `H⁰` is the functor of sections over a terminal
  object.
- `CategoryTheory.Sheaf.H.bijective_map_of_isIso`: an isomorphism of sheaves induces bijections on
  cohomology.
-/

@[expose] public section

universe w' w v' v u' u

namespace CategoryTheory

open Abelian Limits AddCommGrpCat

/-- A sheaf of abelian groups is *torsion* if every section is locally torsion: each section
`s` over `U` restricts to an element of finite order on the members of a covering sieve of `U`.
On a site with enough points this means that all stalks are torsion groups [Stacks 03SA],
see `CategoryTheory.Sheaf.isTorsion_iff_isAddTorsion_sheafFiber`.

The sections themselves need not be torsion: on the small étale site sections over an infinite
disjoint union are infinite products, so a sheaf all of whose groups of sections are torsion
is killed by a single integer. That stronger condition is
`CategoryTheory.Sheaf.IsTorsion.of_forall_isAddTorsion`'s hypothesis. -/
def Sheaf.IsTorsion {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (F : Sheaf J AddCommGrpCat.{w}) : Prop :=
  ∀ ⦃U : Cᵒᵖ⦄ (s : F.obj.obj U), ∃ S ∈ J U.unop,
    ∀ ⦃V : C⦄ ⦃f : V ⟶ U.unop⦄, S f → IsOfFinAddOrder (F.obj.map f.op s)

/-- A sheaf of abelian groups all of whose groups of sections are torsion groups is torsion. -/
lemma Sheaf.IsTorsion.of_forall_isAddTorsion {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {F : Sheaf J AddCommGrpCat.{w}}
    (h : ∀ U, IsAddTorsion (F.obj.obj U)) : F.IsTorsion :=
  fun U _ ↦ ⟨⊤, J.top_mem U.unop, fun _ _ _ ↦ h _ _⟩

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
variable [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
variable [HasSheafify K AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf K AddCommGrpCat.{w})]
variable (G : Sheaf J AddCommGrpCat.{w} ⥤ Sheaf K AddCommGrpCat.{w})
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (e : (constantSheaf K AddCommGrpCat.{w}).obj (of (ULift ℤ)) ≅
    G.obj ((constantSheaf J AddCommGrpCat.{w}).obj (of (ULift ℤ))))

namespace Sheaf

variable (F : Sheaf J AddCommGrpCat.{w}) (n : ℕ)

/-- The map on sheaf cohomology induced by an exact functor `G` between two categories of
abelian sheaves, together with an isomorphism `e` between the constant sheaf `ℤ` on the
target site and the image under `G` of the constant sheaf `ℤ` on the source site: an
`Ext`-class is pushed forward along `G` and then precomposed with `e`. -/
noncomputable def H.mapFunctor : H F n →+ H (G.obj F) n :=
  (Ext.precompAddEquiv e _ n).toAddMonoidHom.comp (G.mapExtAddHom _ F n)

lemma H.mapFunctor_apply (x : H F n) :
    H.mapFunctor G e F n x = (Ext.mk₀ e.hom).comp (x.mapExactFunctor G) (zero_add n) :=
  rfl

section Naturality

variable {F}

/-- The map induced on sheaf cohomology by an exact functor is natural in the sheaf: the
square

```
   H F n ──────H.mapFunctor G e F n──────→ H (G.obj F) n
     │                                          │
     │ H.map φ n                                │ H.map (G.map φ) n
     ↓                                          ↓
   H F' n ─────H.mapFunctor G e F' n─────→ H (G.obj F') n
```

commutes. -/
lemma H.mapFunctor_map {F' : Sheaf J AddCommGrpCat.{w}} (φ : F ⟶ F') (x : H F n) :
    H.mapFunctor G e F' n (H.map φ n x) =
      H.map (G.map φ) n (H.mapFunctor G e F n x) := by
  simp only [H.mapFunctor_apply, H.map_apply, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_mk₀]
  exact (Ext.comp_assoc _ _ _ (zero_add n) (add_zero n) (by omega)).symm

end Naturality

/-- If moreover `G` is fully faithful and preserves injective objects, and the source
category of sheaves has enough injective objects, then the induced map on sheaf cohomology
is bijective. -/
theorem H.mapFunctor_bijective [G.Full] [G.Faithful]
    [EnoughInjectives (Sheaf J AddCommGrpCat.{w})] [G.PreservesInjectiveObjects] :
    Function.Bijective (H.mapFunctor G e F n) :=
  (Ext.precompAddEquiv e _ n).bijective.comp
    (Functor.mapExt_bijective_of_preservesInjectiveObjects G _ F n)

end Sheaf

section VanishingH1

open Opposite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{w})]

/-- **`H¹` vanishes when global sections lift.** Let `T` be a terminal object, so that global
sections are sections over `T`. If for every short exact sequence `0 → F → E → Q → 0` of
abelian sheaves every global section of `Q` lifts to a global section of `E`, then
`H¹(F) = 0`.

In torsor language: the fibre of `E → Q` over a global section of `Q` is an `F`-torsor, which
is trivial exactly when the section lifts; every class in `H¹(F) = Ext¹(ℤ, F)` arises this way
from an embedding of `F` into an injective sheaf. This is the half of the classification of
`H¹` by torsors that is needed for vanishing results.
(blueprint: `lemma-cohomology-multiplicative-group--3`, vanishing direction) -/
theorem Sheaf.subsingleton_H_one_of_surjective (F : Sheaf J AddCommGrpCat.{w}) {T : C}
    (hT : IsTerminal T)
    (h : ∀ ⦃E Q : Sheaf J AddCommGrpCat.{w}⦄ (ι : F ⟶ E) (π : E ⟶ Q) (w : ι ≫ π = 0),
      (ShortComplex.mk ι π w).ShortExact → Function.Surjective (π.hom.app (op T))) :
    Subsingleton (H F 1) := by
  let S := ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F)) (cokernel.condition _)
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  obtain ⟨y, rfl⟩ :=
    Ext.covariant_sequence_exact₁ _ hS x (Ext.eq_zero_of_injective _) (zero_add 1)
  obtain ⟨t, ht⟩ := h S.f S.g S.zero hS (H.equiv₀ S.X₃ hT y)
  have hy : ((H.equiv₀ S.X₂ hT).symm t).comp (Ext.mk₀ S.g) (add_zero 0) = y := by
    rw [← H.map_apply, H.equiv₀_symm_naturality, ht, AddEquiv.symm_apply_apply]
  rw [← hy, Ext.comp_assoc _ _ _ (add_zero 0) (zero_add 1) (zero_add 1), hS.comp_extClass,
    Ext.comp_zero]

end VanishingH1

section HOneCokernel

open Opposite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
  {S : ShortComplex (Sheaf J AddCommGrpCat.{w})} (hS : S.ShortExact) {T : C} (hT : IsTerminal T)

/-- The connecting homomorphism `Γ(S.X₃) → H¹(S.X₁)` of a short exact sequence of abelian
sheaves, where global sections are sections over a terminal object `T`. -/
noncomputable def Sheaf.H.δSections : S.X₃.obj.obj (op T) →+ H S.X₁ 1 :=
  (hS.extClass.postcomp _ (zero_add 1)).comp (H.equiv₀ S.X₃ hT).symm.toAddMonoidHom

lemma Sheaf.H.δ_apply (s : S.X₃.obj.obj (op T)) :
    H.δSections hS hT s = ((H.equiv₀ S.X₃ hT).symm s).comp hS.extClass (zero_add 1) :=
  rfl

/-- The kernel of the connecting homomorphism `Γ(S.X₃) → H¹(S.X₁)` consists of the global
sections of `S.X₃` which lift to `S.X₂`. -/
lemma Sheaf.H.ker_δ : (H.δSections hS hT).ker = (S.g.hom.app (op T)).hom.range := by
  ext s
  rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_range, H.δ_apply]
  constructor
  · intro h
    obtain ⟨x, hx⟩ := Ext.covariant_sequence_exact₃ _ hS _ (zero_add 1) h
    refine ⟨H.equiv₀ S.X₂ hT x, (H.equiv₀ S.X₃ hT).symm.injective ?_⟩
    rw [← H.equiv₀_symm_naturality, AddEquiv.symm_apply_apply, H.map_apply, hx]
  · rintro ⟨x, rfl⟩
    rw [← H.equiv₀_symm_naturality, H.map_apply, Ext.comp_assoc _ _ _ (add_zero 0) (zero_add 1)
      (zero_add 1), hS.comp_extClass, Ext.comp_zero]

/-- The long exact cohomology sequence is exact at `H¹(S.X₁)`: the kernel of
`H¹(S.X₁) → H¹(S.X₂)` is the image of the connecting homomorphism `Γ(S.X₃) → H¹(S.X₁)`. -/
lemma Sheaf.H.exact_δ_map : Function.Exact (H.δSections hS hT) (H.map S.f 1) := by
  intro x
  constructor
  · intro hx
    obtain ⟨y, rfl⟩ := Ext.covariant_sequence_exact₁ _ hS x hx (zero_add 1)
    exact ⟨H.equiv₀ _ hT y, by rw [H.δ_apply, AddEquiv.symm_apply_apply]⟩
  · rintro ⟨y, rfl⟩
    rw [H.δ_apply, H.map_apply, Ext.comp_assoc _ _ _ (zero_add 1) (add_zero 1) (zero_add 1),
      hS.extClass_comp, Ext.comp_zero]

include hS in
/-- The long exact cohomology sequence is exact at `Hⁿ(S.X₂)`: the kernel of
`Hⁿ(S.X₂) → Hⁿ(S.X₃)` is the image of `Hⁿ(S.X₁) → Hⁿ(S.X₂)`. -/
lemma Sheaf.H.exact_map_map (n : ℕ) : Function.Exact (H.map S.f n) (H.map S.g n) := by
  intro x
  constructor
  · exact Ext.covariant_sequence_exact₂ _ hS x
  · rintro ⟨y, rfl⟩
    rw [← H.map_comp_apply, S.zero, H.map_apply, Ext.mk₀_zero, Ext.comp_zero]

/-- The connecting homomorphism `Γ(S.X₃) → H¹(S.X₁)` is surjective when `H¹(S.X₂) = 0`. -/
lemma Sheaf.H.surjective_δ [Subsingleton (H S.X₂ 1)] : Function.Surjective (H.δSections hS hT) := by
  intro x
  obtain ⟨y, rfl⟩ := Ext.covariant_sequence_exact₁ _ hS x (Subsingleton.elim _ _) (zero_add 1)
  exact ⟨H.equiv₀ S.X₃ hT y, by rw [H.δ_apply, AddEquiv.symm_apply_apply]⟩

/-- For a short exact sequence `0 → F → I → Q → 0` of abelian sheaves with `H¹(I) = 0`, the
connecting homomorphism identifies `H¹(F)` with the cokernel of `Γ(I) → Γ(Q)`. -/
noncomputable def Sheaf.H.quotientRangeAddEquiv [Subsingleton (H S.X₂ 1)] :
    S.X₃.obj.obj (op T) ⧸ (S.g.hom.app (op T)).hom.range ≃+ H S.X₁ 1 :=
  (QuotientAddGroup.quotientAddEquivOfEq (H.ker_δ hS hT)).symm.trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _ (H.surjective_δ hS hT))

/-- **`H¹` as a cokernel of global sections.** Every abelian sheaf `F` on a site with a
terminal object `T` sits in a short exact sequence `0 → F → I → Q → 0` with `I` injective,
hence with `H^q(I) = 0` for `q ≥ 1`, and the connecting homomorphism then identifies `H¹(F)`
with the cokernel of `d_T : Γ(I) → Γ(Q)`.

The blueprint takes for `I` the Godement sheaf of `F`, which is flasque; here `I` is an
injective sheaf, which has the same two properties used later: it is acyclic, and every
equivariant map from a torsor into it exists (see
`CategoryTheory.Sheaf.Torsor.exists_quotientEquiv_H_one`).
(blueprint: `lem-galois-flasque`) -/
theorem Sheaf.exists_shortExact_injective_addEquiv_H_one (hT : IsTerminal T)
    [EnoughInjectives (Sheaf J AddCommGrpCat.{w})] (F : Sheaf J AddCommGrpCat.{w}) :
    ∃ (I Q : Sheaf J AddCommGrpCat.{w}) (ι : F ⟶ I) (d : I ⟶ Q) (w : ι ≫ d = 0),
      (ShortComplex.mk ι d w).ShortExact ∧ Injective I ∧ (∀ q, Subsingleton (H I (q + 1))) ∧
      Nonempty (H F 1 ≃+ Q.obj.obj (op T) ⧸ (d.hom.app (op T)).hom.range) := by
  let S := ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F)) (cokernel.condition _)
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
  exact ⟨S.X₂, S.X₃, S.f, S.g, S.zero, hS, inferInstance, fun _ ↦ inferInstance,
    ⟨(H.quotientRangeAddEquiv hS hT).symm⟩⟩


end HOneCokernel

section Connecting

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
  {S : ShortComplex (Sheaf J AddCommGrpCat.{w})} (hS : S.ShortExact)

/-- The connecting homomorphism `Hⁿ(S.X₃) → Hⁿ⁺¹(S.X₁)` of the long exact cohomology sequence
of a short exact sequence of abelian sheaves: composition with the extension class of `S`. -/
noncomputable def Sheaf.H.δSucc (n : ℕ) : H S.X₃ n →+ H S.X₁ (n + 1) :=
  hS.extClass.postcomp _ rfl

lemma Sheaf.H.δSucc_apply (n : ℕ) (x : H S.X₃ n) : H.δSucc hS n x = x.comp hS.extClass rfl :=
  rfl

/-- In degree `0`, the connecting homomorphism `H⁰(S.X₃) → H¹(S.X₁)` is the connecting
homomorphism `CategoryTheory.Sheaf.H.δSections` on global sections. -/
lemma Sheaf.H.δSucc_zero {T : C} (hT : Limits.IsTerminal T) (x : H S.X₃ 0) :
    H.δSucc hS 0 x = H.δSections hS hT (H.equiv₀ S.X₃ hT x) := by
  rw [H.δ_apply, AddEquiv.symm_apply_apply]
  rfl

/-- The long exact cohomology sequence is exact at `Hⁿ(S.X₃)`: the kernel of the connecting
homomorphism `Hⁿ(S.X₃) → Hⁿ⁺¹(S.X₁)` is the image of `Hⁿ(S.X₂) → Hⁿ(S.X₃)`. -/
lemma Sheaf.H.exact_map_δSucc (n : ℕ) : Function.Exact (H.map S.g n) (H.δSucc hS n) :=
  (ShortComplex.ab_exact_iff_function_exact _).1 (Ext.covariant_sequence_exact₃' _ hS n _ rfl)

/-- The long exact cohomology sequence is exact at `Hⁿ⁺¹(S.X₁)`: the kernel of
`Hⁿ⁺¹(S.X₁) → Hⁿ⁺¹(S.X₂)` is the image of the connecting homomorphism. -/
lemma Sheaf.H.exact_δSucc_map (n : ℕ) : Function.Exact (H.δSucc hS n) (H.map S.f (n + 1)) :=
  (ShortComplex.ab_exact_iff_function_exact _).1 (Ext.covariant_sequence_exact₁' _ hS n _ rfl)

/-- The connecting homomorphism is natural in the short exact sequence. -/
lemma Sheaf.H.map_δSucc {S' : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (hS' : S'.ShortExact) (φ : S ⟶ S') (n : ℕ) (x : H S.X₃ n) :
    H.map φ.τ₁ (n + 1) (H.δSucc hS n x) = H.δSucc hS' n (H.map φ.τ₃ n x) := by
  rw [H.δSucc_apply, H.δSucc_apply, H.map_apply, H.map_apply,
    Ext.comp_assoc_of_third_deg_zero, hS.extClass_naturality hS' φ,
    Ext.comp_assoc_of_second_deg_zero]

/-- The connecting homomorphism `Hⁿ(S.X₃) → Hⁿ⁺¹(S.X₁)` is surjective when
`Hⁿ⁺¹(S.X₂) = 0`. -/
lemma Sheaf.H.δSucc_surjective (n : ℕ) [Subsingleton (H S.X₂ (n + 1))] :
    Function.Surjective (H.δSucc hS n) := by
  intro x
  obtain ⟨y, rfl⟩ := Ext.covariant_sequence_exact₁ _ hS x (Subsingleton.elim _ _) rfl
  exact ⟨y, rfl⟩

/-- The connecting homomorphism `Hⁿ(S.X₃) → Hⁿ⁺¹(S.X₁)`, as a morphism between the values of
the cohomology functors `CategoryTheory.Sheaf.functorH`. -/
noncomputable def Sheaf.functorHδ (n : ℕ) :
    (functorH.{w'} J n).obj S.X₃ ⟶ (functorH.{w'} J (n + 1)).obj S.X₁ :=
  AddCommGrpCat.ofHom (H.δSucc hS n)

lemma Sheaf.functorHδ_apply (n : ℕ) (x : H S.X₃ n) : functorHδ hS n x = H.δSucc hS n x :=
  rfl

@[reassoc]
lemma Sheaf.functorHδ_naturality (n : ℕ) {S' : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (hS' : S'.ShortExact) (φ : S ⟶ S') :
    functorHδ hS n ≫ (functorH.{w'} J (n + 1)).map φ.τ₁ =
      (functorH.{w'} J n).map φ.τ₃ ≫ functorHδ hS' n := by
  ext x
  exact H.map_δSucc hS hS' φ n x

lemma Sheaf.functorHδ_eq_zero_iff (n : ℕ) (x : H S.X₃ n) :
    functorHδ hS n x = 0 ↔ x ∈ ((functorH.{w'} J n).map S.g).hom.range :=
  ((H.exact_map_δSucc hS n) x).trans (by rfl)

lemma Sheaf.functorHδ_surjective (n : ℕ) [Subsingleton (H S.X₂ (n + 1))] :
    Function.Surjective (functorHδ hS n) :=
  H.δSucc_surjective hS n

end Connecting


section Zero

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w} (Sheaf J AddCommGrpCat.{w})] {T : C}
  (hT : IsTerminal T)

/-- `H⁰` is the functor of sections over a terminal object. -/
noncomputable def Sheaf.functorHZeroIso :
    functorH.{w} J 0 ≅ sheafToPresheaf J AddCommGrpCat.{w} ⋙
      (evaluation Cᵒᵖ AddCommGrpCat.{w}).obj (Opposite.op T) :=
  NatIso.ofComponents (fun F ↦ (H.equiv₀ F hT).toAddCommGrpIso) fun φ ↦ by
    ext x
    exact (H.equiv₀_naturality (hT := hT) φ x).symm

end Zero

/-- The map induced on sheaf cohomology by `m • f` is `m` times the map induced by `f`. -/
lemma Sheaf.H.map_nsmul_apply {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
    {F G : Sheaf J AddCommGrpCat.{w}} (f : F ⟶ G) (m n : ℕ) (x : H F n) :
    H.map (m • f) n x = m • H.map f n x := by
  induction m with
  | zero => rw [zero_smul, zero_smul, H.map_apply, Ext.mk₀_zero, Ext.comp_zero]
  | succ m ih => rw [succ_nsmul, succ_nsmul, H.map_add_apply, ih]

/-- An isomorphism of sheaves induces a bijection on cohomology. -/
lemma Sheaf.H.bijective_map_of_isIso {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
    {F G : Sheaf J AddCommGrpCat.{w}} (f : F ⟶ G) [IsIso f] (n : ℕ) :
    Function.Bijective (H.map f n) :=
  Function.bijective_iff_has_inverse.2 ⟨H.map (inv f) n,
    fun x ↦ by rw [← H.map_comp_apply, IsIso.hom_inv_id, H.map_id_apply],
    fun x ↦ by rw [← H.map_comp_apply, IsIso.inv_hom_id, H.map_id_apply]⟩

end CategoryTheory
