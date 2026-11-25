/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.Hilbert90
public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.Mathlib.RingTheory.Etale.Field
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.FieldTheory.KrullTopology
import WeilConjectures.AlgebraicGeometry.Sites.FiniteGaloisGermRepresentative
import WeilConjectures.AlgebraicGeometry.Sites.FiniteGaloisInvariantGermDescent

/-!
# A section representing an invariant geometric germ

## References

* Stacks Project, Tag 04JM, direct proof, applied over a finite separable field
* Stacks Project, the direct proof of Lemma 59.56.5, applied after restricting the sheaf to `Spec L`
-/

@[expose] public section

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

attribute [local instance] Algebra.Etale.of_finite_of_isSeparable

/-- A germ in the geometric fibre of `F` invariant under the fixing subgroup of a finite
separable extension `L / K`, for a given Galois action on the fibre, is represented by a section
of `F` over `Spec L`. -/
theorem exists_fieldSection_of_invariant_germ
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω]
    (s : Spec (.of Ω) ⟶ Spec (.of K))
    (hs : s = Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
    (F : Sheaf (Spec (.of K)).smallEtaleTopology (Type (max (u + 1) v)))
    (action : MulAction Gal(Ks/K) ((pointSmallEtale s).sheafFiber.obj F))
    (haction : ∀ (g : Gal(Ks/K)) (τ : Ω ≃ₐ[K] Ω),
      (algebraMap Ks Ω).comp g.toRingHom =
        τ.toRingHom.comp (algebraMap Ks Ω) →
      ∀ (X : (Spec (.of K)).Etale) (x x' : (pointSmallEtale s).fiber.obj X),
      x'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ x.left →
      ∀ (z : F.obj.obj (op X)),
      action.smul g ((pointSmallEtale s).toPresheafFiber X x F.obj z) =
        (pointSmallEtale s).toPresheafFiber X x' F.obj z)
    (L : IntermediateField K Ks) [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (x : (pointSmallEtale s).fiber.obj (etaleSpec K L))
    (hx : x.left = Spec.map
      (CommRingCat.ofHom ((algebraMap Ks Ω).comp L.subtype)))
    (m : (pointSmallEtale s).sheafFiber.obj F)
    (hm : ∀ g ∈ L.fixingSubgroup, action.smul g m = m) :
    ∃ z : F.obj.obj (op (etaleSpec K L)),
      (pointSmallEtale s).toPresheafFiber (etaleSpec K L) x F.obj z = m := by
  obtain ⟨E, hLE, y, hy, z, hz⟩ :=
    exists_finiteGalois_germ_representative K Ks Ω s hs F L m
  have hinj : Function.Injective
      ((pointSmallEtale s).toPresheafFiber (etaleSpec K E.toIntermediateField) y F.obj) := by
    intro z z' h
    obtain ⟨Y, f, y', _, hf⟩ :=
      ((pointSmallEtale s).toPresheafFiber_eq_iff' (P := F.obj)
        (etaleSpec K E.toIntermediateField) y z z').mp h
    have hcov : Sieve.ofArrows _ (fun _ : Unit ↦ f) ∈
        (Spec (.of K)).smallEtaleTopology (etaleSpec K E.toIntermediateField) := by
      rw [ofArrows_mem_smallEtaleTopology_iff]
      ext a
      simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
      exact ⟨(), y'.left (default : Spec (.of Ω)),
        @Subsingleton.elim (Spec (.of E.toIntermediateField)) _ _ _⟩
    have hsheaf : Presieve.IsSheafFor F.obj (Presieve.singleton f) := by
      rw [← Presieve.ofArrows_pUnit.{0}, Presieve.isSheafFor_iff_generate]
      exact ((isSheaf_iff_isSheaf_of_type _ _).mp F.property) _ hcov
    exact (Presieve.isSeparatedFor_singleton.mp hsheaf.isSeparatedFor) hf
  have hfixed : ∀ g ∈ L.fixingSubgroup,
      action.smul g ((pointSmallEtale s).toPresheafFiber (etaleSpec K E) y F.obj z) =
        (pointSmallEtale s).toPresheafFiber (etaleSpec K E) y F.obj z := by
    simpa only [hz] using hm
  obtain ⟨w, hw⟩ := exists_fieldSection_of_finiteGalois_invariant_representative
    K Ks Ω s F action haction L x hx E hLE y hy z hinj hfixed
  exact ⟨w, hw.trans hz⟩

end AlgebraicGeometry.Scheme
