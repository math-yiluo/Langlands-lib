/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
import WeilConjectures.Topology.SheafIsomorphismLocalOpenCover
import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Isomorphisms of quasi-coherent modules detected on an affine open cover

Source: Stacks Project, Schemes, Tags 01IA and 01IB, and Sheaves, Tag 04TN;
used in Morphisms, Tag 01SB
(blueprint: lem-weil-pbc-quasi-coherent-iso-on-affine-cover).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- A morphism of quasi-coherent modules is an isomorphism if its maps on sections over an
arbitrary affine open cover are bijective.

Source: Stacks Project, Schemes, Tags 01IA and 01IB, Sheaves, Tag 04TN;
used in Morphisms, Tag 01SB
(blueprint: lem-weil-pbc-quasi-coherent-iso-on-affine-cover).

Proof (the node's four steps):
1. For each affine open `W a`, put `R = Γ(Y, W a)`. Choose an isomorphism
   `h : Spec R ≅ W a` inducing the identity on global sections. This follows from
   `def-pc-scheme` and `def-weil-affine-spectrum`. Compose with the inclusion into `Y`.
   By `lem-weil-pbc-module-restriction-open-immersion-colimits`, restriction along this
   open immersion is functorial and preserves quasi-coherence (`pqf-def-coherent`).
   The restricted morphism's global sections map is precisely `φ.app (W a)` as an
   `R`-linear map, since the chosen chart induces the identity on `R`.
2. By `lem-weil-pbc-affine-tilde-gamma-adjunction`, the counits for the two restricted
   quasi-coherent modules are isomorphisms. Their naturality identifies the restricted
   morphism with the composite of the inverse source counit, the tilde of its global
   sections map, and the target counit. Naturality also follows from the adjunction's
   Hom bijection: both composites correspond to that same global sections map.
   Bijectivity gives an `R`-linear inverse; the tilde functor sends it to an inverse.
   Thus the morphism restricted to `Spec R` is an isomorphism.
3. Restrict back along `h` inverse. Restriction is a functor by
   `lem-weil-pbc-module-restriction-open-immersion-colimits`, so preserves this
   isomorphism. On every open inside `W a`, the composite chart is the inclusion into
   `Y`, with the usual structure-sheaf action and the original components of `φ`.
   Thus this is exactly the restriction to `W a`, as in
   `def-weil-pbc-module-finite-type-presentation`.
4. The local inverses on the `W a` agree on overlaps, being inverses of the same
   restricted morphism. By `lem-weil-pbc-sheaf-isomorphism-local-open-cover` (Tag 04TN),
   they glue to a global inverse of `φ`. -/
theorem Hom.isIso_of_bijective_on_affine_open_cover {Y : Scheme.{u}} {F G : Y.Modules}
    [F.IsQuasicoherent] [G.IsQuasicoherent] (φ : F ⟶ G) {A : Type u}
    (W : A → Y.Opens) (hcover : ⨆ a, W a = ⊤) (haffine : ∀ a : A, IsAffineOpen (W a))
    (hbijective : ∀ a : A, Function.Bijective (φ.app (W a))) : IsIso φ := by
  have affine_iso {R : CommRingCat.{u}} {M N : (Spec R).Modules}
      [M.IsQuasicoherent] [N.IsQuasicoherent] (α : M ⟶ N)
      (hα : Function.Bijective (α.app ⊤)) : IsIso α := by
    have : IsIso ((moduleSpecΓFunctor (R := R)).map α) :=
      (ConcreteCategory.isIso_iff_bijective _).2 hα
    have : IsIso ((tilde.functor R).map ((moduleSpecΓFunctor (R := R)).map α)) :=
      inferInstance
    have : IsIso ((tilde.adjunction (R := R)).counit.app N) :=
      inferInstanceAs (IsIso N.fromTildeΓ)
    have hn := (tilde.adjunction (R := R)).counit.naturality α
    dsimp only [Functor.id_map, Functor.comp_map] at hn
    have : IsIso (M.fromTildeΓ ≫ α) := by
      change IsIso ((tilde.adjunction (R := R)).counit.app M ≫ α)
      rw [← hn]
      infer_instance
    exact (isIso_comp_left_iff M.fromTildeΓ α).1 this
  apply (sheaf_module_isIso_iff_isIso_over_open_cover Y.toRingedSpace A W hcover F G φ).2
  intro a
  let f := (haffine a).fromSpec
  have htop : f ''ᵁ (⊤ : (Spec Γ(Y, W a)).Opens) = W a := by
    ext x
    simp [f]
  have hα : IsIso ((restrictFunctor f).map φ) := by
    apply affine_iso
    change Function.Bijective (φ.app (f ''ᵁ ⊤))
    rw [htop]
    exact hbijective a
  have : IsIso ((restrictFunctor (haffine a).isoSpec.hom).map
      ((restrictFunctor f).map φ)) := inferInstance
  have e : restrictFunctor (W a).ι ≅
      restrictFunctor f ⋙ restrictFunctor (haffine a).isoSpec.hom :=
    (restrictFunctorCongr (haffine a).isoSpec_hom_fromSpec).symm ≪≫
      restrictFunctorComp _ _
  have : IsIso ((restrictFunctor (W a).ι).map φ) := by
    apply (NatIso.isIso_map_iff e φ).2
    change IsIso ((restrictFunctor (haffine a).isoSpec.hom).map
      ((restrictFunctor f).map φ))
    infer_instance
  have : IsIso ((overEquiv (W a)).functor.map (φ.over (W a))) := by
    exact (NatIso.isIso_map_iff (overFunctorEquiv (W a)) φ).2 inferInstance
  exact isIso_of_reflects_iso (φ.over (W a)) (overEquiv (W a)).functor

end AlgebraicGeometry.Scheme.Modules
