/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Topology.ContinuousMap.Algebra

import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# Sections of a finite constant pro-etale sheaf

Source: Bhatt--Scholze, *The pro-etale topology for schemes*, Lemma 4.2.12,
printed p. 30 (blueprint: lem-pur-proetale-finite-constant-sections).

For a finite commutative ring with its discrete topology, sections of the constant
ring sheaf on the small pro-etale site are continuous functions on the underlying
scheme. The comparison is normalized on constant sections and is natural for
morphisms in the site.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private def continuousRingPresheaf (X : Scheme.{u}) (A : Type (u + 1))
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] : X.ProEtᵒᵖ ⥤ RingCat.{u + 1} where
  obj V := RingCat.of C(V.unop.left, A)
  map h := RingCat.ofHom
    (ContinuousMap.compRightAlgHom A A h.unop.left.base.hom).toRingHom
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

private def constantToContinuous (X : Scheme.{u}) (A : Type (u + 1))
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    (Functor.const X.ProEtᵒᵖ).obj (RingCat.of A) ⟶ continuousRingPresheaf X A where
  app V := RingCat.ofHom (ContinuousMap.C : A →+* C(V.unop.left, A))
  naturality _ _ h := by ext; rfl

private theorem continuousRingPresheaf_isSheaf (X : Scheme.{u}) (A : Type (u + 1))
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    Presheaf.IsSheaf (Scheme.ProEt.topology X) (continuousRingPresheaf X A) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget (Scheme.ProEt.topology X)
    (continuousRingPresheaf X A) (forget RingCat.{u + 1})]
  exact (Scheme.ProEt.forget X ⋙ Over.forget X).op_comp_isSheaf_of_isSheaf
    (Scheme.ProEt.topology X) Scheme.proetaleTopology (continuousMapPresheaf A)
    ((isSheaf_fpqcTopology_continuousMapPresheaf A).of_le
      Scheme.proetaleTopology_le_fpqcTopology)

private theorem constantToContinuous_locallyInjective
    (X : Scheme.{u}) (A : Type (u + 1))
    [CommRing A] [TopologicalSpace A] [DiscreteTopology A] :
    Presheaf.IsLocallyInjective (Scheme.ProEt.topology X) (constantToContinuous X A) where
  equalizerSieve_mem {V} a b h := by
    classical
    by_cases he : IsEmpty V.unop.left
    · let _ := he
      exact (Scheme.ProEt.topology X).superset_covering bot_le
        (Scheme.ProEt.bot_mem_topology V.unop)
    · obtain ⟨x⟩ := not_isEmpty_iff.mp he
      have hab : a = b := congrArg (fun f : C(V.unop.left, A) ↦ f x) h
      subst b
      simp

private theorem constantToContinuous_locallySurjective
    (X : Scheme.{u}) (A : Type (u + 1))
    [CommRing A] [TopologicalSpace A] [DiscreteTopology A] :
    Presheaf.IsLocallySurjective (Scheme.ProEt.topology X) (constantToContinuous X A) where
  imageSieve_mem {V} f := by
    classical
    change C(V.left, A) at f
    let U (x : V.left) : V.left.Opens :=
      ⟨f ⁻¹' {f x}, (isOpen_discrete {f x}).preimage f.continuous⟩
    let W (x : V.left) : X.ProEt := Scheme.ProEt.mk ((U x).ι ≫ V.hom)
    let i (x : V.left) : W x ⟶ V :=
      MorphismProperty.Over.homMk (U x).ι rfl
    have hm : Presieve.ofArrows W i ∈ Scheme.ProEt.precoverage X V := by
      change (Presieve.ofArrows W i).map (Scheme.ProEt.forget X ⋙ Over.forget X) ∈
        Scheme.proetalePrecoverage V.left
      rw [Presieve.map_ofArrows]
      apply Scheme.zariskiPrecoverage_le_propQCPrecoverage
      rw [Scheme.ofArrows_mem_precoverage_iff]
      refine ⟨?_, ?_⟩
      · intro x
        exact ⟨x, ⟨⟨x, rfl⟩, rfl⟩⟩
      · intro x
        change IsOpenImmersion (U x).ι
        infer_instance
    apply (Scheme.ProEt.topology X).superset_covering _
      (Precoverage.generate_mem_toGrothendieck hm)
    rw [Sieve.generate_le_iff]
    rintro Y g ⟨x⟩
    refine ⟨f x, ?_⟩
    apply ContinuousMap.ext
    intro y
    exact y.property.symm

/-- Sections of a finite constant pro-etale ring sheaf are continuous functions.

Source: Bhatt--Scholze, *The pro-etale topology for schemes*, Lemma 4.2.12,
printed p. 30 (blueprint: lem-pur-proetale-finite-constant-sections).
The proof constructs the sheaf of continuous functions, proves that the map from
the constant presheaf is locally bijective using the finite discrete fibres, and
then applies sheafification. Pointwise ring operations give ring equivalences;
the same construction sends each constant section to the corresponding constant
function and commutes with restriction by precomposition. The argument includes
empty and disconnected objects and uses no quasi-compactness assumption.
-/
theorem proEtale_finite_constant_sections
    (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] :
    ∃ θ : ∀ V : X.ProEt,
      RingEquiv
        (↑(((constantSheaf (Scheme.ProEt.topology X) RingCat.{u + 1}).obj
          (RingCat.of A)).obj.obj (Opposite.op V)))
        C(V.left, A),
      (∀ (V : X.ProEt) (a : A),
        θ V (((toSheafify (Scheme.ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of A))).app
            (Opposite.op V)) a) = ContinuousMap.const V.left a) ∧
      (∀ {V W : X.ProEt} (h : W ⟶ V)
        (s : (((constantSheaf (Scheme.ProEt.topology X) RingCat.{u + 1}).obj
          (RingCat.of A)).obj.obj (Opposite.op V))),
        θ W (((constantSheaf (Scheme.ProEt.topology X) RingCat.{u + 1}).obj
          (RingCat.of A)).obj.map h.op s) =
          (θ V s).comp h.left.base.hom) := by
  let J := Scheme.ProEt.topology X
  let P := (Functor.const X.ProEtᵒᵖ).obj (RingCat.of A)
  let F := continuousRingPresheaf X A
  let φ := constantToContinuous X A
  have hF : Presheaf.IsSheaf J F := continuousRingPresheaf_isSheaf X A
  have : Presheaf.IsLocallyInjective J φ := constantToContinuous_locallyInjective X A
  have : Presheaf.IsLocallySurjective J φ := constantToContinuous_locallySurjective X A
  have : IsIso ((presheafToSheaf J RingCat.{u + 1}).map φ) :=
    (J.W_iff φ).mp (J.W_of_isLocallyBijective φ)
  have : IsIso (sheafifyMap J φ) := inferInstance
  let e : sheafify J P ≅ F := asIso (sheafifyMap J φ) ≪≫ (isoSheafify J hF).symm
  have he : toSheafify J P ≫ e.hom = φ := by
    dsimp [e]
    rw [← Category.assoc, ← toSheafify_naturality]
    simp only [toSheafify_naturality, isoSheafify_inv, Category.assoc,
      sheafifyMap_sheafifyLift, toSheafify_sheafifyLift]
    exact Category.comp_id φ
  refine ⟨fun V ↦ (e.app (op V)).ringCatIsoToRingEquiv, ?_, ?_⟩
  · intro V a
    exact congrArg (fun k ↦ (k.app (op V)) a) he
  · intro V W h s
    exact NatTrans.naturality_apply e.hom h.op s

end AlgebraicGeometry
