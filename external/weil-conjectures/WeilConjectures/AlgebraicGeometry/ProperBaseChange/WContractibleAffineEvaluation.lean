/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.RingTheory.ProperBaseChange.IndPrincipalZariski
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import WeilConjectures.RingTheory.ProEtale.WeaklyEtale
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.WContractibleCoverSection
import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Evaluation at a w-contractible affine pro-etale object

## References

* Stacks Project, Tags 0981, 098F and 098H
* Sites, Tags 090K and 090L
* Stacks Project, Tag 098H, disjoint-cover gluing argument
* Stacks Project, Tags 0981 and 098H, implication (1) to (2), adapted to the small site over `X`
-/

@[expose] public section

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.ProEt

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The sheaf axiom glues arbitrary sections on disjoint covering subobjects.
The only compatibility on distinct components is over an empty test scheme. -/
private theorem exists_glue_of_disjoint
    {X : Scheme.{u}} (F : Sheaf (topology X) (Type (max (u + 1) v)))
    {W : X.ProEt} {I : Type u} (V : I → X.ProEt) (ι : ∀ i, V i ⟶ W)
    (hcov : Presieve.ofArrows V ι ∈ precoverage X W)
    (hmono : ∀ i, Mono (ι i))
    (hdisj : ∀ i j, i ≠ j →
      Disjoint (Set.range (ι i).left.base) (Set.range (ι j).left.base))
    (x : ∀ i, F.obj.obj (op (V i))) :
    ∃ z : F.obj.obj (op W), ∀ i, F.obj.map (ι i).op z = x i := by
  classical
  have hsh : (Presieve.ofArrows V ι).IsSheafFor F.obj :=
    (Presieve.isSheafFor_iff_generate _).mpr
      ((isSheaf_iff_isSheaf_of_type _ _).mp F.property _
        (Precoverage.generate_mem_toGrothendieck hcov))
  rw [Presieve.isSheafFor_arrows_iff] at hsh
  have hcompat : ∀ (i j : I) (Q : X.ProEt) (a : Q ⟶ V i) (b : Q ⟶ V j),
      a ≫ ι i = b ≫ ι j → F.obj.map a.op (x i) = F.obj.map b.op (x j) := by
    intro i j Q a b hab
    by_cases hij : i = j
    · subst j
      have := hmono i
      obtain rfl : a = b := (cancel_mono (ι i)).mp hab
      rfl
    · have : IsEmpty Q.left := ⟨fun q ↦ by
        have hq := congrArg (fun m ↦ m.left.base q) hab
        change ((ι i).left ((a.left) q)) = ((ι j).left ((b.left) q)) at hq
        exact Set.disjoint_left.mp (hdisj i j hij)
          ⟨a.left q, rfl⟩ ⟨b.left q, hq.symm⟩⟩
      have : Unique (F.obj.obj (op Q)) :=
        Limits.Types.isTerminalEquivUnique _ (F.isTerminalOfBotCover Q (bot_mem_topology Q))
      exact Subsingleton.elim _ _
  obtain ⟨z, hz, -⟩ := hsh x hcompat
  exact ⟨z, hz⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Evaluation at `Spec A` sends every epimorphism of sheaves of sets on the full small
pro-etale site to a surjection, provided every faithfully flat weakly etale ring map
out of `A` has a ring retraction. -/
theorem surjective_app_of_affine_ring_retractions
    (X : Scheme.{u}) (A : Type u) [CommRing A]
    (f : Spec (CommRingCat.of A) ⟶ X) [WeaklyEtale f]
    (hA : ∀ (B : Type u) [CommRing B] (φ : A →+* B),
      φ.FaithfullyFlat → φ.WeaklyEtale →
        ∃ r : B →+* A, r.comp φ = RingHom.id A)
    (F G : Sheaf (topology X) (Type (max (u + 1) v)))
    (α : F ⟶ G) [Epi α] :
    Function.Surjective (α.hom.app (op (ProEt.mk f))) := by
  classical
  -- A covering sieve contains a small pro-etale covering family.
  have : (precoverage X).HasIsos := by dsimp [precoverage]; infer_instance
  have : (precoverage X).IsStableUnderComposition := by
    dsimp [precoverage]; infer_instance
  have : (precoverage X).IsStableUnderBaseChange := by
    dsimp [precoverage]; infer_instance
  have : Precoverage.Small.{u} (precoverage X) := by
    dsimp [precoverage, Scheme.proetalePrecoverage]; infer_instance
  have : Sheaf.IsLocallySurjective α :=
    (Sheaf.isLocallySurjective_iff_epi α).mpr inferInstance
  intro s
  have hS : Presheaf.imageSieve α.hom s ∈ topology X (ProEt.mk f) :=
    Presheaf.imageSieve_mem (topology X) α.hom (U := op (ProEt.mk f)) s
  obtain ⟨R, hR, hle⟩ :=
    (Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition
      (J := precoverage X)).mp hS
  obtain ⟨E, rfl⟩ := (Precoverage.mem_iff_exists_zeroHypercover (J := precoverage X)).mp hR
  let D := E.restrictIndexOfSmall.{u}
  have hlocal (i : D.I₀) :
      ∃ t : F.obj.obj (op (D.X i)),
        α.hom.app _ t = G.obj.map (D.f i).op s :=
    hle _ _ ⟨Precoverage.ZeroHypercover.Small.restrictFun E i⟩
  choose t ht using hlocal
  have hcover : Presieve.ofArrows (fun i ↦ (D.X i).left)
      (fun i ↦ (D.f i).left) ∈ Scheme.proetalePrecoverage (Spec (.of A)) := by
    have hd := D.mem₀
    change (Presieve.ofArrows D.X D.f).map (ProEt.forget X ⋙ Over.forget X) ∈
      Scheme.proetalePrecoverage (Spec (.of A)) at hd
    rw [Presieve.map_ofArrows] at hd
    exact hd
  -- The geometric section lemma uses the equivalent algebra formulation.
  have hsplit (B : Type u) [CommRing B] [Algebra A B]
      (hff : Module.FaithfullyFlat A B) (hwe : Algebra.WeaklyEtale A B) :
      ∃ r : B →+* A, r.comp (algebraMap A B) = RingHom.id A :=
    hA B (algebraMap A B) (RingHom.faithfullyFlat_algebraMap_iff.mpr hff)
      (RingHom.weaklyEtale_algebraMap_iff.mpr hwe)
  obtain ⟨σ, hσ⟩ := exists_section_proetaleCover_of_ring_retractions A hsplit
    D.I₀ (fun i ↦ (D.X i).left) (fun i ↦ (D.f i).left) hcover
  let p := Limits.Sigma.desc (fun i ↦ (D.f i).left)
  change σ ≫ p = 𝟙 _ at hσ
  have hp : WeaklyEtale p := by
    apply IsZariskiLocalAtSource.sigmaDesc (P := @WeaklyEtale)
    intro i
    exact Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ hcover ⟨i⟩
  -- Glue on the covering coproduct before pulling back along its section.
  let W : X.ProEt := ProEt.mk (p ≫ f)
  let π : W ⟶ ProEt.mk f := MorphismProperty.Over.homMk p rfl trivial
  let ι : ∀ i, D.X i ⟶ W := fun i ↦
    MorphismProperty.Over.homMk (Limits.Sigma.ι (fun i ↦ (D.X i).left) i)
      (by
        change Limits.Sigma.ι (fun i ↦ (D.X i).left) i ≫ p ≫ f = (D.X i).hom
        dsimp only [p]
        rw [Limits.Sigma.ι_comp_desc_assoc]
        exact MorphismProperty.Over.w (D.f i)) trivial
  have hιcov : Presieve.ofArrows D.X ι ∈ precoverage X W := by
    change (Presieve.ofArrows D.X ι).map (ProEt.forget X ⋙ Over.forget X) ∈
      Scheme.proetalePrecoverage W.left
    rw [Presieve.map_ofArrows]
    exact Scheme.zariskiPrecoverage_le_propQCPrecoverage _
      (sigmaOpenCover (fun i ↦ (D.X i).left)).mem₀
  have hιmono (i : D.I₀) : Mono (ι i) := by
    apply (ProEt.forget X ⋙ Over.forget X).mono_of_mono_map
    change Mono (Limits.Sigma.ι (fun i ↦ (D.X i).left) i)
    infer_instance
  have hιdisj (i j : D.I₀) (hij : i ≠ j) :
      Disjoint (Set.range (ι i).left.base) (Set.range (ι j).left.base) :=
    TopologicalSpace.Opens.coe_disjoint.mpr
      (disjoint_opensRange_sigmaι (fun i ↦ (D.X i).left) i j hij)
  obtain ⟨z, hz⟩ := exists_glue_of_disjoint F D.X ι hιcov hιmono hιdisj t
  let τ : ProEt.mk f ⟶ W := MorphismProperty.Over.homMk σ
    (by change σ ≫ p ≫ f = f; rw [← Category.assoc, hσ, Category.id_comp]) trivial
  have hτ : τ ≫ π = 𝟙 _ := MorphismProperty.Over.Hom.ext hσ
  have hιπ (i : D.I₀) : ι i ≫ π = D.f i :=
    MorphismProperty.Over.Hom.ext (Limits.Sigma.ι_comp_desc _ _)
  have himage : α.hom.app (op W) z = G.obj.map π.op s := by
    have hsep := ((isSheaf_iff_isSheaf_of_type _ _).mp G.property).isSeparated
      _ (Precoverage.generate_mem_toGrothendieck hιcov)
    apply hsep.ext
    rintro Q g ⟨Q', a, b, ⟨i⟩, rfl⟩
    simp only [op_comp, G.obj.map_comp, types_comp_apply]
    rw [← NatTrans.naturality_apply, hz, ht]
    simp only [← types_comp_apply, ← G.obj.map_comp, ← op_comp, hιπ]
  refine ⟨F.obj.map τ.op z, ?_⟩
  rw [NatTrans.naturality_apply, himage, ← types_comp_apply,
    ← G.obj.map_comp, ← op_comp, hτ, op_id, G.obj.map_id]
  rfl

end AlgebraicGeometry.Scheme.ProEt
