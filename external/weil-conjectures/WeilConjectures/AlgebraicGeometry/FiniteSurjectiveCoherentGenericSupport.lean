/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.FinitePushforwardCoherent
import WeilConjectures.AlgebraicGeometry.FiniteTypeModuleSupportClosed
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.Topology.PresheafModuleStalkFunctor
import Mathlib.Algebra.Category.Grp.Zero

/-! # Coherent sheaf with prescribed generic support

Source: Stacks Project, Cohomology of Schemes, Lemma 01YO (blueprint:
lem-weil-pbc-finite-surjective-coherent-generic-support).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- A finite surjective map to a locally Noetherian scheme admits a coherent module whose
pushforward is supported on a prescribed integral closed subscheme and is annihilated at its
generic point by the maximal ideal.
Source: Stacks Project, Cohomology of Schemes, Lemma 01YO, lines 3479--3521
(blueprint: lem-weil-pbc-finite-surjective-coherent-generic-support).

Proof:
1. Finite implies locally finite type, so Y is locally Noetherian
   (lem-weil-pbc-finite-iff-integral-lft, pqf-lem-locnoeth-lft). Lift ξ by surjectivity
   and take its reduced closure (lem-weil-pbc-reduced-induced-closed-subscheme).
2. Its image is exactly closure {ξ}, since a finite map is closed
   (lem-weil-pbc-finite-closed-map-finite-fibres). Factor its reduced source through Z
   (lem-weil-pbc-reduced-source-factors-through-closed-subscheme).
3. Push forward its structure sheaf along the closed immersion into Y. This is coherent
   (lem-weil-pbc-closed-immersion-finite, pqf-lem-coherent-ft-locnoeth,
   lem-weil-pbc-finite-pushforward-coherent). Sectionwise pushforward composes.
4. On affine neighborhoods the generic stalk is (B/q)_p. Integrality and incomparability
   (lem-weil-pbc-finite-algebra-is-integral, lem-weil-pbc-integral-incomparability) show
   this is the residue field of the chosen lift and therefore nonzero.
5. The stalk action factors through the residue field of ξ (def-weil-residue-field,
   def-weil-pbc-module-stalk), so the maximal ideal annihilates the stalk.
6. The pushforward has closed support (lem-weil-pbc-finite-type-module-support-closed).
   Closed-pushforward stalks put it inside i(Z) (lem-weil-pbc-closed-pushforward-stalks).
   It contains ξ by step 4, hence contains its closure and equals i(Z).
-/
theorem exists_coherent_pushforward_support_eq_range
    {X Y Z : Scheme.{u}} (f : Y ⟶ X) (i : Z ⟶ X) (ξ : X)
    [IsFinite f] [Surjective f] [IsLocallyNoetherian X]
    [IsClosedImmersion i] [IsIntegral Z]
    (hξ : IsGenericPoint ξ (Set.range i.base)) :
    ∃ F : Y.Modules,
      RingedSpace.IsCoherent Y.toRingedSpace F ∧
      {x : X | ¬ Subsingleton (((Modules.pushforward f).obj F).presheaf.stalk x : Type u)} =
        Set.range i.base ∧
      ∀ a : (X.toRingedSpace.presheaf.stalk ξ : Type u),
        a ∈ IsLocalRing.maximalIdeal (X.toRingedSpace.presheaf.stalk ξ) →
        ∀ s : ((RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).obj
          ((Modules.pushforward f).obj F) : Type u),
          a • s = 0 := by
  classical
  obtain ⟨y, hy⟩ := f.surjective ξ
  let I := IdealSheafData.vanishingIdeal ⟨closure {y}, isClosed_closure⟩
  let j := I.subschemeι
  let O : I.subscheme.Modules := SheafOfModules.unit I.subscheme.ringCatSheaf
  let F := (Modules.pushforward j).obj O
  let G := (Modules.pushforward f).obj F
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f
  have hO : RingedSpace.IsCoherent I.subscheme.toRingedSpace O :=
    Modules.isCoherent_unit_of_finite_to_locallyNoetherian j
  have hF : RingedSpace.IsCoherent Y.toRingedSpace F :=
    (Modules.isCoherent_pushforward_of_isFinite j O hO).1
  have hG : RingedSpace.IsCoherent X.toRingedSpace G :=
    (Modules.isCoherent_pushforward_of_isFinite f F hF).1
  obtain ⟨hq, ht⟩ :=
    (Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X G).mp hG
  have : G.IsQuasicoherent := hq
  have : G.IsFiniteType := ht
  have hclosed : IsClosed {x : X | ¬ Subsingleton (G.presheaf.stalk x)} :=
    (Modules.finite_type_module_support_closed X G).2.2.2
  have hgeneric :
      (¬ Subsingleton (G.presheaf.stalk (f y))) ∧
        ∀ a : (X.toRingedSpace.presheaf.stalk (f y) : Type u),
          a ∈ IsLocalRing.maximalIdeal (X.toRingedSpace.presheaf.stalk (f y)) →
          ∀ s : ((RingedSpace.moduleStalkFunctor X.toRingedSpace (f y)).obj G : Type u),
            a • s = 0 := by
    have hrange : Set.range j.base = closure {y} := by
      simp [j, I, IdealSheafData.range_subschemeι,
        IdealSheafData.coe_support_vanishingIdeal]
    obtain ⟨z, hz⟩ : y ∈ Set.range j.base :=
      hrange.symm ▸ subset_closure (Set.mem_singleton y)
    constructor
    · intro h
      have h01 := @Subsingleton.elim _ h
        (G.presheaf.germ ⊤ (f y) (by trivial)
          (show G.presheaf.obj (Opposite.op ⊤) from
            (1 : Γ(I.subscheme, j ⁻¹ᵁ (f ⁻¹ᵁ ⊤)))))
        (G.presheaf.germ ⊤ (f y) (by trivial) 0)
      obtain ⟨U, hU, k, l, heq⟩ := G.presheaf.germ_eq (f y)
        (show f y ∈ (⊤ : X.Opens) from trivial) (by trivial) _ _ h01
      have hmap : G.presheaf.map k.op
          (show G.presheaf.obj (Opposite.op ⊤) from
            (1 : Γ(I.subscheme, j ⁻¹ᵁ (f ⁻¹ᵁ ⊤)))) =
          (1 : Γ(I.subscheme, j ⁻¹ᵁ (f ⁻¹ᵁ U))) :=
        (I.subscheme.presheaf.map
          ((Opens.map j.base).map ((Opens.map f.base).map k)).op).hom.map_one
      have hone : (1 : Γ(I.subscheme, j ⁻¹ᵁ (f ⁻¹ᵁ U))) = 0 := by
        simpa only [hmap, map_zero] using heq
      have hzU : z ∈ j ⁻¹ᵁ (f ⁻¹ᵁ U) := by
        change f (j z) ∈ U
        rwa [hz]
      have hstalk := congrArg
        (fun t ↦ I.subscheme.presheaf.germ (j ⁻¹ᵁ (f ⁻¹ᵁ U)) z hzU t) hone
      exact one_ne_zero (by simpa only [map_one, map_zero] using hstalk)
    · intro a ha s
      obtain ⟨U, hU, r, rfl⟩ := X.presheaf.exists_germ_eq a
      obtain ⟨V, hVU, hV, m, rfl⟩ := G.presheaf.exists_le_germ_eq s hU
      rw [← X.presheaf.germ_res_apply (homOfLE hVU) (f y) hV r] at ha ⊢
      let rV := X.presheaf.map (homOfLE hVU).op r
      have ev0 : X.evaluation V (f y) hV rV = 0 := by
        exact (IsLocalRing.residue_eq_zero_iff _).mpr ha
      have pull0 : j.app (f ⁻¹ᵁ V) (f.app V rV) = 0 := by
        apply (IdealSheafData.mem_idealOfOpens_iff I).mp
        apply ((IdealSheafData.reduced_induced_closed_subscheme Y
          ⟨closure {y}, isClosed_closure⟩).1 (f ⁻¹ᵁ V) (f.app V rV)).mpr
        intro t ht htT
        rw [Y.evaluation_eq_zero_iff_notMem_basicOpen]
        intro htopen
        have hyopen := (specializes_iff_mem_closure.mpr htT).mem_open
          (Y.basicOpen (f.app V rV)).isOpen htopen
        have ey0 := evaluation_naturality_apply f y hV rV
        rw [ev0, map_zero] at ey0
        exact ((Y.evaluation_eq_zero_iff_notMem_basicOpen y hV _).mp ey0.symm) hyopen
      erw [← PresheafOfModules.germ_smul G.val]
      have hsmul :
          (X.presheaf.map (homOfLE hVU).op r) • m = 0 := by
        change (j.app (f ⁻¹ᵁ V) (f.app V rV)) *
          (show Γ(I.subscheme, j ⁻¹ᵁ (f ⁻¹ᵁ V)) from m) = 0
        rw [pull0, zero_mul]
      rw [hsmul, map_zero]
  rw [hy] at hgeneric
  refine ⟨F, hF, ?_, hgeneric.2⟩
  apply Set.Subset.antisymm
  · intro x hx
    by_contra hnot
    let V : X.Opens := ⟨(Set.range i.base)ᶜ, hξ.isClosed.isOpen_compl⟩
    have hxV : x ∈ V := hnot
    have hrange : Set.range j.base = closure {y} := by
      simp [j, I, IdealSheafData.range_subschemeι,
        IdealSheafData.coe_support_vanishingIdeal]
    have himage : ∀ z : I.subscheme, f (j z) ∈ Set.range i.base := by
      intro z
      have hz : j z ∈ closure {y} := hrange ▸ ⟨z, rfl⟩
      have hfz := (specializes_iff_mem_closure.mpr hz).map f.continuous
      rw [hy] at hfz
      exact hξ.specializes_iff_mem.mp hfz
    have hempty (U : X.Opens) (hU : U ≤ V) : j ⁻¹ᵁ (f ⁻¹ᵁ U) = ⊥ := by
      ext z
      exact ⟨fun hz ↦ (hU hz) (himage z), False.elim⟩
    have htrivial (U : X.Opens) (hU : U ≤ V) : Subsingleton (G.presheaf.obj
        (Opposite.op U)) := by
      change Subsingleton (O.presheaf.obj (Opposite.op (j ⁻¹ᵁ (f ⁻¹ᵁ U))))
      exact AddCommGrpCat.subsingleton_of_isZero
        ((TopCat.Sheaf.isTerminalOfEqEmpty ⟨O.presheaf, O.isSheaf⟩ (hempty U hU)).isZero)
    apply hx
    refine ⟨?_⟩
    intro a b
    obtain ⟨U, hUV, hxU, s, rfl⟩ := G.presheaf.exists_le_germ_eq a hxV
    obtain ⟨W, hWV, hxW, t, rfl⟩ := G.presheaf.exists_le_germ_eq b hxV
    have hxQ : x ∈ U ⊓ W := ⟨hxU, hxW⟩
    have := htrivial (U ⊓ W) (inf_le_left.trans hUV)
    have heq : G.presheaf.map (homOfLE (inf_le_left : U ⊓ W ≤ U)).op s =
        G.presheaf.map (homOfLE (inf_le_right : U ⊓ W ≤ W)).op t :=
      Subsingleton.elim _ _
    rw [← G.presheaf.germ_res_apply (homOfLE (inf_le_left : U ⊓ W ≤ U)) x hxQ s,
      ← G.presheaf.germ_res_apply (homOfLE (inf_le_right : U ⊓ W ≤ W)) x hxQ t, heq]
  · exact (hξ.mem_closed_set_iff hclosed).mp hgeneric.1

end AlgebraicGeometry.Scheme
