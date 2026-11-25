/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.CoherentGenericPointClosedDescent
import WeilConjectures.AlgebraicGeometry.CoherentIntegralGenericIdealMap
import WeilConjectures.AlgebraicGeometry.ClosedPushforwardStalks
import WeilConjectures.AlgebraicGeometry.CoherentLocalIsomorphism
import WeilConjectures.AlgebraicGeometry.FinitePushforwardCoherent
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # A coherent ideal inclusion near a generic point

Source: Stacks Project, Cohomology of Schemes, Lemma 01YE
(`coherent.tex`, label `lemma-prepare-filter-irreducible`)
(blueprint: lem-weil-pbc-coherent-generic-point-ideal-inclusion).
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
namespace AlgebraicGeometry
namespace Scheme
namespace Modules
noncomputable section

/-- Closed pushforward preserves invertibility of a stalk map at a source point. -/
private theorem pushforward_stalk_isIso {X Z : Scheme.{w}} (i : Z ⟶ X)
    [IsClosedImmersion i] {A B : Z.Modules} (χ : A ⟶ B) (z : Z)
    [IsIso ((RingedSpace.moduleStalkFunctor Z.toRingedSpace z).map χ)] :
    IsIso ((RingedSpace.moduleStalkFunctor X.toRingedSpace (i.base z)).map
      ((pushforward i).map χ)) := by
  have hA := closedImmersion_pushforward_stalks i i.isClosedEmbedding A
  have hB := closedImmersion_pushforward_stalks i i.isClosedEmbedding B
  let cA := ConcreteCategory.hom (TopCat.Presheaf.stalkPushforward Ab i.base A.presheaf z)
  let cB := ConcreteCategory.hom (TopCat.Presheaf.stalkPushforward Ab i.base B.presheaf z)
  let f := (RingedSpace.moduleStalkFunctor X.toRingedSpace (i.base z)).map
    ((pushforward i).map χ)
  let g := (RingedSpace.moduleStalkFunctor Z.toRingedSpace z).map χ
  have hca : Function.Bijective cA := (hA.2.1 z).1
  have hcb : Function.Bijective cB := (hB.2.1 z).1
  have hg : Function.Bijective g := ConcreteCategory.bijective_of_isIso g
  have comm (a) : cB (f a) = g (cA a) := by
    exact congr($(hA.2.2 B χ z) a)
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      apply hca.1
      apply hg.1
      rw [← comm, ← comm, hab]
    · intro b
      obtain ⟨a, ha⟩ := hg.2 (cB b)
      obtain ⟨a', ha'⟩ := hca.2 a
      refine ⟨a', hcb.1 ?_⟩
      rw [comm, ha', ha]
  exact (ConcreteCategory.isIso_iff_bijective f).mpr hf

/-- A coherent module whose generic stalk is killed by the ambient maximal ideal contains
an injective pushforward of a finite direct sum of a coherent ideal on the integral closed
subscheme, and this inclusion is an isomorphism on an ambient neighbourhood of that point.

Source: Stacks Project, Cohomology of Schemes, Lemma 01YE
(`coherent.tex`, label `lemma-prepare-filter-irreducible`)
(blueprint: lem-weil-pbc-coherent-generic-point-ideal-inclusion).

Proof (the seven steps of the node):
1. The closed subscheme Z is Noetherian by lem-weil-pbc-immersion-base-change-lft and
   pqf-lem-locnoeth-lft, and compactness of a closed subset. Its defining ideal J is
   coherent by pqf-lem-coherent-ft-locnoeth and
   lem-weil-pbc-coherent-kernel-cokernel-locnoeth. The closed immersion gives a surjective
   local-ring map at the generic point with kernel J_ξ, by
   lem-weil-pbc-closed-pushforward-stalks, lem-weil-pbc-locally-surjective-iff-stalks and
   lem-weil-pbc-module-stalk-exact. Its target is a field by
   lem-weil-pbc-integral-scheme-ideal-generic-stalk, so J_ξ is the maximal ideal.
2. Use lem-weil-pbc-sections-annihilated-by-ideal to form F', the sections killed by J.
   This is a coherent submodule by lem-weil-pbc-coherent-kernel-cokernel-locnoeth, with
   F'_ξ = F_ξ by the annihilation hypothesis. By lem-weil-pbc-coherent-local-isomorphism
   its inclusion is an isomorphism on W₁ containing ξ. The equality J F' = 0 follows
   from lem-weil-pbc-ideal-module-product-stalk and lem-weil-pbc-module-iso-on-stalks.
3. By lem-weil-pbc-closed-immersion-coherent-equivalence, write F' ≅ i_* G for a coherent
   module G on Z. Identify its generic stalk by lem-weil-pbc-closed-pushforward-stalks.
4. The generic stalk G_η is finite-dimensional over the generic local field, by
   pqf-def-coherent and lem-weil-pbc-locally-surjective-iff-stalks. Set r to its dimension.
   Extend a stalk isomorphism from O_Z^{⊕ r} using lem-weil-pbc-coherent-stalk-map-extends
   to a map φ on U containing η. By lem-weil-pbc-coherent-local-isomorphism it is an
   isomorphism on a smaller V containing η.
5. Form the ideal I_T of the reduced complement T = Z ∖ U by
   lem-weil-pbc-reduced-induced-closed-subscheme. Lemma lem-weil-pbc-coherent-homs-over-open
   extends φ to χ : (I_T^n)^{⊕ r} → G for some n. Put I = I_T^n; it is coherent by
   lem-weil-pbc-ideal-times-quasi-coherent-affine-sections and
   lem-weil-pbc-coherent-kernel-cokernel-locnoeth. The identification
   I O_Z^{⊕ r} = I^{⊕ r} follows by the finite-sum tensor formula of
   def-pur-sheaf-tensor-product. The map χ remains an isomorphism on V.
6. The kernel K of χ has zero generic stalk by lem-weil-pbc-module-stalk-exact. Its
   coordinate images in O_Z are quasi-coherent ideals by
   lem-weil-pbc-quasi-coherent-module-cokernel-image, with zero generic stalks. They
   vanish by lem-weil-pbc-integral-scheme-ideal-generic-stalk, so K = 0 and χ is injective.
7. Compose i_* χ with i_* G ≅ F' and F' ↪ F. Sectionwise pushforward preserves its
   injectivity (lem-weil-pbc-closed-pushforward-stalks). Since i is a closed embedding,
   W₂ = X ∖ i(Z ∖ V) is open, contains ξ, and has inverse image V. The composite is an
   isomorphism on W = W₁ ∩ W₂, as required.
-/
theorem coherent_generic_point_ideal_inclusion {X Z : Scheme.{w}} [IsNoetherian X]
    (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
    (F : X.Modules)
    (hF : AlgebraicGeometry.RingedSpace.IsCoherent X.toRingedSpace F)
    (hkill : ∀ a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (i.base (genericPoint Z))),
      ∀ x : (RingedSpace.moduleStalkFunctor X.toRingedSpace (i.base (genericPoint Z))).obj F,
        a • x = 0) :
    ∃ (r : ℕ) (I : Z.IdealSheafData),
      AlgebraicGeometry.RingedSpace.IsCoherent Z.toRingedSpace I.toModules ∧
      ∃ (α : (pushforward i).obj (∐ fun _ : Fin r => I.toModules) ⟶ F),
        Mono α ∧
        ∃ (W : X.Opens), i.base (genericPoint Z) ∈ W ∧
          IsIso ((SheafOfModules.overFunctor X.ringCatSheaf W).map α)
    := by
  have : IsNoetherian Z := isNoetherian_of_locallyOfFiniteType i
  obtain ⟨G, hG, β, hβ, hβstalk⟩ := coherent_generic_point_closed_descent i F hF hkill
  obtain ⟨r, I, hI, hsum, χ, hχ, hχstalk⟩ := coherent_integral_generic_ideal_map Z G hG
  have : Mono β := hβ
  have : Mono χ := hχ
  have : IsIso ((RingedSpace.moduleStalkFunctor X.toRingedSpace
    (i.base (genericPoint Z))).map β) := hβstalk
  have : IsIso ((RingedSpace.moduleStalkFunctor Z.toRingedSpace
    (genericPoint Z)).map χ) := hχstalk
  let α := (pushforward i).map χ ≫ β
  have : Mono α := inferInstance
  have : IsIso ((RingedSpace.moduleStalkFunctor X.toRingedSpace
      (i.base (genericPoint Z))).map ((pushforward i).map χ)) :=
    pushforward_stalk_isIso i χ (genericPoint Z)
  have hαstalk : Function.Bijective ((RingedSpace.moduleStalkFunctor X.toRingedSpace
      (i.base (genericPoint Z))).map α) := by
    dsimp only [α]
    rw [Functor.map_comp]
    exact ConcreteCategory.bijective_of_isIso _
  have hsource := (isCoherent_pushforward_of_isFinite i _ hsum).1
  obtain ⟨W, hW, hαW⟩ :=
    (coherent_local_isomorphism X F _ hF hsource α (i.base (genericPoint Z))).2.2.2 hαstalk
  exact ⟨r, I, hI, α, inferInstance, W, hW, hαW⟩

end
end Modules
end Scheme
end AlgebraicGeometry
