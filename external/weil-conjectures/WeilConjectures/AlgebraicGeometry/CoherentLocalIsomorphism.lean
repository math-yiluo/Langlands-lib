/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeSubKernel
import WeilConjectures.Topology.FiniteTypeSurjectiveNearStalk

/-!
# Local isomorphism criterion for coherent modules

Source: Stacks Project, Cohomology of Schemes, Lemma 01Y3
(blueprint: lem-weil-pbc-coherent-local-isomorphism).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry
universe u
namespace AlgebraicGeometry
noncomputable section

private theorem epi_over_of_local_lifts (X : RingedSpace.{u})
    {G F : SheafOfModules.{u} (moduleRings X)} (φ : G ⟶ F) (U : Opens X)
    (h : ∀ (W : Opens X), W ≤ U → ∀ t : F.val.obj (.op W),
      ∃ (I : Type u) (V : I → Opens X) (hV : ∀ i, V i ≤ W)
        (g : ∀ i, G.val.obj (.op (V i))), (⨆ i, V i) = W ∧
          ∀ i, φ.val.app (.op (V i)) (g i) =
            F.val.map (homOfLE (hV i)).op t) : Epi (φ.over U) := by
  let T := SheafOfModules.toSheaf.{u} ((moduleRings X).over U)
  have hl : CategoryTheory.Presheaf.IsLocallySurjective
      ((Opens.grothendieckTopology X).over U) (T.map (φ.over U)).hom := by
    constructor
    intro W t
    change Sieve.overEquiv W _ ∈ Opens.grothendieckTopology X W.left
    intro x hx
    obtain ⟨I, V, hV, g, hc, hg⟩ := h W.left (leOfHom W.hom) t
    have hx' : x ∈ ⨆ i, V i := by rw [hc]; exact hx
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx'
    refine ⟨V i, homOfLE (hV i), ?_, hi⟩
    rw [Sieve.overEquiv_iff]
    exact ⟨g i, hg i⟩
  have : Epi (T.map (φ.over U)) :=
    CategoryTheory.Sheaf.epi_of_isLocallySurjective _
  exact T.epi_of_epi_map inferInstance

private theorem finiteType_zero_near (X : RingedSpace.{u})
    (F : SheafOfModules.{u} (moduleRings X)) [F.IsFiniteType] (x : X)
    (hz : IsZero ((RingedSpace.moduleStalkFunctor X x).obj F)) :
    ∃ U : Opens X, x ∈ U ∧ IsZero (F.over U) := by
  have hs : Function.Surjective
      ((RingedSpace.moduleStalkFunctor X x).map (0 : F ⟶ F)) := by
    have : Subsingleton ((RingedSpace.moduleStalkFunctor X x).obj F) :=
      ModuleCat.isZero_iff_subsingleton.mp hz
    intro t
    exact ⟨0, Subsingleton.elim _ _⟩
  obtain ⟨U, hx, hU⟩ :=
    RingedSpace.exists_surjective_neighbourhood_of_surjective_stalk X (0 : F ⟶ F) x hs
  have he := epi_over_of_local_lifts X (0 : F ⟶ F) U hU
  refine ⟨U, hx, ?_⟩
  have : Epi (0 : F.over U ⟶ F.over U) := he
  exact IsZero.of_epi_zero (F.over U) (F.over U)

/-- At a point of a locally Noetherian scheme, a morphism of coherent modules has
zero, injective, surjective, or bijective stalk behaviour on a neighbourhood.
Source: Stacks Project, Cohomology of Schemes, Lemma 01Y3
(blueprint: lem-weil-pbc-coherent-local-isomorphism).
Proof:
1. By `pqf-def-coherent`, both modules are of finite type, in the sense of
   `def-weil-pbc-module-finite-type-presentation`. The kernel of `φ` is computed
   sectionwise (`situation-conventions`), so its restriction vanishes
   exactly when every section map of `φ` on that neighbourhood is injective.
   The locally Noetherian hypothesis is retained from the source but is unused.
2. For (3), apply `lem-weil-pbc-module-finite-type-surjective-on-stalk` (Modules,
   01B8) to `φ`, since its target is of finite type.
3. A finite-type module with zero stalk vanishes near the point (Modules, 01B9):
   apply 01B8 to the zero map into it; local surjectivity says every section is
   locally zero, and the sheaf axiom makes it zero. Apply this to `F` for (1).
4. For (2), `lem-weil-pbc-coherent-finite-type-sub-kernel` makes `Ker φ` finite
   type. Evaluation preserves kernels, so the kernel inclusion is sectionwise
   injective; Mathlib makes its stalk map injective too. Its composite with the
   injective `φₓ` is zero, so cancellation makes it zero. A zero monomorphism has
   zero source. Step 3 makes the kernel vanish near `x`; evaluation of the exact
   kernel sequence then makes every section map injective there.
5. For (4), intersect the neighbourhoods from (2) and (3). A target section has
   local preimages by sheaf surjectivity; injectivity makes them agree on overlaps,
   so they glue. Every section map is thus bijective. Their inverses are linear
   and commute with restriction, giving an inverse morphism of module sheaves.
   Lean packages this gluing in balancedness of the abelian module-sheaf category.
-/
theorem coherent_local_isomorphism (X : Scheme.{u}) [IsLocallyNoetherian X]
    (F G : SheafOfModules (moduleRings X.toLocallyRingedSpace.toRingedSpace))
    (hF : RingedSpace.IsCoherent X.toLocallyRingedSpace.toRingedSpace F)
    (hG : RingedSpace.IsCoherent X.toLocallyRingedSpace.toRingedSpace G)
    (φ : G ⟶ F) (x : X) :
    (IsZero ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F) →
      ∃ U : X.Opens, x ∈ U ∧ IsZero (F.over U)) ∧
    (Function.Injective ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map φ) →
      ∃ U : X.Opens, x ∈ U ∧
        ∀ (V : X.Opens), V ≤ U →
          Function.Injective (ConcreteCategory.hom (φ.val.app (.op V)))) ∧
    (Function.Surjective ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map φ) →
      ∃ U : X.Opens, x ∈ U ∧
        Epi ((SheafOfModules.overFunctor
          (moduleRings X.toLocallyRingedSpace.toRingedSpace) U).map φ)) ∧
    (Function.Bijective ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map φ) →
      ∃ U : X.Opens, x ∈ U ∧
        IsIso ((SheafOfModules.overFunctor
          (moduleRings X.toLocallyRingedSpace.toRingedSpace) U).map φ)) := by
  have : F.IsFiniteType := hF.1
  have hs (h : Function.Surjective
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map φ)) :=
    RingedSpace.exists_surjective_neighbourhood_of_surjective_stalk
      X.toRingedSpace φ x h
  have hi (h : Function.Injective
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map φ)) :
      ∃ U : X.Opens, x ∈ U ∧ ∀ V : X.Opens, V ≤ U →
        Function.Injective (ConcreteCategory.hom (φ.val.app (.op V))) := by
    have : (kernel φ).IsFiniteType :=
      (RingedSpace.coherent_finiteType_submodule_kernel X.toRingedSpace).2 G F φ hG.1 hF
    have hm : Mono ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map φ) :=
      (ModuleCat.mono_iff_injective _).mpr h
    -- Sectionwise kernel inclusions stay injective after taking germs.
    have hm' : Mono ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map
        (kernel.ι φ)) := by
      apply (ModuleCat.mono_iff_injective _).mpr
      refine TopCat.Presheaf.stalkFunctor_map_injective_of_app_injective
        (f := (PresheafOfModules.toPresheaf _).map (kernel.ι φ).val) ?_ x
      intro W
      let EW := SheafOfModules.evaluation.{u} (moduleRings X.toRingedSpace) (.op W)
      exact (ModuleCat.mono_iff_injective (EW.map (kernel.ι φ))).mp
        (Functor.map_mono EW _)
    have hk : (RingedSpace.moduleStalkFunctor X.toRingedSpace x).map (kernel.ι φ) = 0 :=
      zero_of_comp_mono _ (by rw [← Functor.map_comp, kernel.condition, Functor.map_zero])
    have hz : IsZero ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj (kernel φ)) :=
      IsZero.of_mono_eq_zero _ hk
    obtain ⟨U, hx, hU⟩ := finiteType_zero_near X.toRingedSpace (kernel φ) x hz
    refine ⟨U, hx, ?_⟩
    intro V hV
    apply (ModuleCat.mono_iff_injective _).mp
    let E := SheafOfModules.evaluation.{u} (moduleRings X.toRingedSpace) (.op V)
    have : E.PreservesZeroMorphisms := ⟨fun _ _ ↦ rfl⟩
    have hzV : IsZero (E.obj (kernel φ)) := by
      let EU := SheafOfModules.evaluation.{u} ((moduleRings X.toRingedSpace).over U)
        (.op (Over.mk (homOfLE hV)))
      have : EU.PreservesZeroMorphisms := ⟨fun _ _ ↦ rfl⟩
      exact Functor.map_isZero EU hU
    have hzι : E.map (kernel.ι φ) = 0 := hzV.eq_zero_of_src _
    have heV := (ShortComplex.kernelSequence_exact φ).map_of_mono_of_preservesKernel E
      inferInstance inferInstance
    exact heV.mono_g hzι
  refine ⟨finiteType_zero_near X.toRingedSpace F x, hi, ?_, ?_⟩
  · intro h
    obtain ⟨U, hx, hU⟩ := hs h
    exact ⟨U, hx, epi_over_of_local_lifts X.toRingedSpace φ U hU⟩
  · intro h
    obtain ⟨U₁, hx₁, h₁⟩ := hi h.1
    obtain ⟨U₂, hx₂, h₂⟩ := hs h.2
    refine ⟨U₁ ⊓ U₂, ⟨hx₁, hx₂⟩, ?_⟩
    have : Epi (φ.over (U₁ ⊓ U₂)) :=
      epi_over_of_local_lifts X.toRingedSpace φ (U₁ ⊓ U₂)
        (fun W hW ↦ h₂ W (hW.trans inf_le_right))
    have : Mono (φ.over (U₁ ⊓ U₂)) := by
      constructor
      intro Z a b hab
      ext W z
      apply h₁ W.unop.left ((leOfHom W.unop.hom).trans inf_le_left)
      exact congrArg (fun f ↦ f.val.app W z) hab
    -- The category of module sheaves is abelian, hence balanced.
    exact isIso_of_mono_of_epi _

end
end AlgebraicGeometry
