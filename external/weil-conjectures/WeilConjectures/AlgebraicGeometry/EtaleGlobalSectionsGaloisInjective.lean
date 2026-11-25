/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.KrullTopology
public import WeilConjectures.RepresentationTheory.DiscreteContinuousRep
public import Mathlib.RepresentationTheory.Invariants
import Mathlib.Algebra.Category.Grp.FilteredColimits

/-!
# Global sections under the abelian Galois stalk equivalence

Source: Stacks Project, Etale Cohomology, Tag 04JM, lemma-global-sections-point.
(blueprint: lem-sc-etale-global-sections-galois-invariants).
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

/-- The canonical terminal germ map, transported through the supplied stalk
isomorphism, is injective.

Source: Stacks Project, Tag 04JM, lemma-global-sections-point.
(blueprint: aux-etale-global-sections-injective).

Proof: Equality of germs is witnessed on a common pointed etale neighbourhood.
Its structural map to Spec K is an etale surjection: its image is nonempty and
Spec K has one point. It therefore covers the terminal object. The separatedness
part of the sheaf condition makes restriction along this cover injective.
The two terminal sections are equal. Transport through the additive stalk
isomorphism preserves and reflects equality. -/
theorem etaleGlobalSections_galoisInvariants_injective
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [IsAlgClosed Ω]
    (T : (Spec (.of K)).Etale) (hT : Limits.IsTerminal T)
    (E : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1} ≌
      Rep.DiscreteContinuousRep.{0, u, u + 1} ℤ (Gal(Ks/K)))
    (i : E.functor ⋙ ObjectProperty.ι _ ⋙ Rep.RepToAction ℤ (Gal(Ks/K)) ⋙
      Action.forget (ModuleCat.{u + 1} ℤ) (Gal(Ks/K)) ⋙
      forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat ≅
      (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).sheafFiber)
    (x : (pointSmallEtale
      (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).fiber.obj T)
    : ∀ F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1},
      Function.Injective (fun z : F.obj.obj (op T) ↦ (i.inv.app F) ((pointSmallEtale
        (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).toPresheafFiber T x F.obj z)) := by
  classical
  have : Limits.PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    Limits.preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  intro F a b h
  let p := pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
  have hg : p.toPresheafFiber T x F.obj a = p.toPresheafFiber T x F.obj b := by
    exact (ConcreteCategory.bijective_of_isIso (i.inv.app F)).1 h
  obtain ⟨Y, f, y, _, hf⟩ := (p.toPresheafFiber_eq_iff' T x a b).mp hg
  let U : (Spec (.of K)).Etale :=
    MorphismProperty.Over.mk ⊤ (𝟙 (Spec (.of K))) (by infer_instance)
  let r : T ⟶ U := MorphismProperty.Over.homMk T.hom
  let j := hT.from U
  have hj : T.hom ≫ j.left = 𝟙 T.left :=
    congrArg (fun q : T ⟶ T ↦ q.left) (hT.hom_ext (r ≫ j) (𝟙 T))
  have hsub : Subsingleton T.left := ⟨fun c d ↦ by
    have hc := congrArg (fun q : T.left ⟶ T.left ↦ q c) hj
    have hd := congrArg (fun q : T.left ⟶ T.left ↦ q d) hj
    have hb : T.hom c = T.hom d := by
      exact @Subsingleton.elim (Spec (.of K)) _ _ _
    exact hc.symm.trans ((congrArg j.left hb).trans hd)⟩
  have hcov : Sieve.ofArrows _ (fun _ : Unit ↦ f) ∈
      (Spec (.of K)).smallEtaleTopology T := by
    rw [ofArrows_mem_smallEtaleTopology_iff]
    ext c
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    exact ⟨(), y.left (default : Spec (.of Ω)), hsub.elim _ _⟩
  let Fset := F.obj ⋙ CategoryTheory.forget AddCommGrpCat
  have hsheaf : Presieve.IsSheafFor Fset (Presieve.singleton f) := by
    rw [← Presieve.ofArrows_pUnit.{0}, Presieve.isSheafFor_iff_generate]
    exact ((isSheaf_iff_isSheaf_of_type _ _).mp
      ((Presheaf.isSheaf_iff_isSheaf_forget _ _ _).mp F.property)) _ hcov
  exact (Presieve.isSeparatedFor_singleton.mp hsheaf.isSeparatedFor) hf

end AlgebraicGeometry.Scheme
