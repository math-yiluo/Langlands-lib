/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.IdealPowerTorsionFunctor
public import Mathlib.Algebra.Homology.LocalCohomology
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import WeilConjectures.Algebra.Homology.ExtInjectiveResolutionComparison
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-! # Quotient Hom complexes and the torsion subcomplex

Source: Stacks Project, Tag 0954, proof of Lemma 47.8.2.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace ModuleCat

private def homDiagram {R : Type u} [CommRing R] (J : Ideal R) (N : ModuleCat.{u} R) :
    (ℕᵒᵖ)ᵒᵖ ⥤ ModuleCat.{u} R :=
  (((localCohomology.ringModIdeals (localCohomology.idealPowersDiagram J)).op ⋙
    linearCoyoneda R (ModuleCat.{u} R)).flip).obj N

set_option backward.isDefEq.respectTransparency false in
private def evalOne {R : Type u} [CommRing R] (J : Ideal R) (N : ModuleCat.{u} R)
    (n : (ℕᵒᵖ)ᵒᵖ) :
    (homDiagram J N).obj n ⟶ ModuleCat.of R (Ideal.primaryComponent N J) :=
  ModuleCat.ofHom
    { toFun := fun f ↦ ⟨f.hom (1 : R ⧸ J ^ n.unop.unop), by
        apply (Ideal.primaryComponent_mem N J _).mpr
        refine ⟨n.unop.unop, ?_⟩
        rw [Submodule.mem_torsionBySet_iff]
        intro a
        rw [← f.hom.map_smul]
        have h : (a : R) • (1 : R ⧸ J ^ n.unop.unop) = 0 := by
          simpa [Algebra.smul_def] using
            (Ideal.Quotient.eq_zero_iff_mem (I := J ^ n.unop.unop)).mpr a.property
        rw [h, map_zero]⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

private def evalCocone {R : Type u} [CommRing R] (J : Ideal R)
    (N : ModuleCat.{u} R) : Cocone (homDiagram J N) where
  pt := ModuleCat.of R (Ideal.primaryComponent N J)
  ι :=
    { app := evalOne J N
      naturality := by
        intro n m f
        ext g
        apply Subtype.ext
        rfl }

set_option backward.isDefEq.respectTransparency false in
private theorem evalOne_injective {R : Type u} [CommRing R] (J : Ideal R)
    (N : ModuleCat.{u} R) (n : (ℕᵒᵖ)ᵒᵖ) :
    Function.Injective (evalOne J N n) := by
  intro f g h
  have he : f.hom (1 : R ⧸ J ^ n.unop.unop) =
      g.hom (1 : R ⧸ J ^ n.unop.unop) := congrArg Subtype.val h
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hx : Ideal.Quotient.mk (J ^ n.unop.unop) a =
      a • (1 : R ⧸ J ^ n.unop.unop) := by simp [Algebra.smul_def]
  change f.hom (Ideal.Quotient.mk (J ^ n.unop.unop) a) =
    g.hom (Ideal.Quotient.mk (J ^ n.unop.unop) a)
  rw [hx, f.hom.map_smul, g.hom.map_smul, he]

private theorem evalOne_surjective {R : Type u} [CommRing R] (J : Ideal R)
    (N : ModuleCat.{u} R) (x : Ideal.primaryComponent N J) :
    ∃ (n : (ℕᵒᵖ)ᵒᵖ) (f : (homDiagram J N).obj n), evalOne J N n f = x := by
  obtain ⟨n, hn⟩ := (Ideal.primaryComponent_mem N J x.val).mp x.property
  rw [Submodule.mem_torsionBySet_iff] at hn
  let f : R ⧸ J ^ n →ₗ[R] N := (J ^ n).liftQ
    (LinearMap.toSpanSingleton R N x.val) (by
      intro a ha
      exact hn ⟨a, ha⟩)
  refine ⟨op (op n), ModuleCat.ofHom f, ?_⟩
  apply Subtype.ext
  change f (Ideal.Quotient.mk _ 1) = x.val
  exact one_smul R x.val

private noncomputable def evalCoconeIsColimit {R : Type u} [CommRing R] (J : Ideal R)
    (N : ModuleCat.{u} R) : IsColimit (evalCocone J N) := by
  have : IsFiltered ((ℕᵒᵖ)ᵒᵖ) := inferInstance
  letI : ReflectsFilteredColimitsOfSize.{0, 0} (forget (ModuleCat.{u} R)) :=
    reflectsSmallestFilteredColimits_of_reflectsFilteredColimits _
  apply isColimitOfReflects (forget (ModuleCat.{u} R))
  apply Types.FilteredColimit.isColimitOf'
  · intro x
    obtain ⟨n, f, hf⟩ := evalOne_surjective J N x
    exact ⟨n, f, hf.symm⟩
  · intro n f g h
    have hfg : f = g := evalOne_injective J N n h
    exact ⟨n, 𝟙 n, by rw [hfg]⟩

private def quotientHomCocone {R : Type u} [CommRing R] (J : Ideal R)
    (K : CochainComplex (ModuleCat.{u} R) ℕ) : Cocone
    ((localCohomology.ringModIdeals (localCohomology.idealPowersDiagram J)).op ⋙
      homComplexDiagram K) where
  pt := ((idealPowerTorsion J).mapHomologicalComplex (ComplexShape.up ℕ)).obj K
  ι :=
    { app := fun n ↦
        { f := fun k ↦ evalOne J (K.X k) n
          comm' := by
            intro i j hij
            ext f
            apply Subtype.ext
            rfl }
      naturality := by
        intro n m f
        ext k g
        apply Subtype.ext
        rfl }

/-- Taking the colimit of the complexes `Hom(R/J^n,K)` gives the ideal-power
 torsion subcomplex of `K`.
Source: Stacks Project, Tag 0954, proof of Lemma 47.8.2.
(blueprint: lem-sbc-quotient-hom-complex-colimit).

Proof: In each degree, evaluation of a linear map at the class of 1 identifies
`Hom(R/J^n,K^k)` with the submodule annihilated by `J^n`. The quotient transition
maps give inclusions of these submodules. Every torsion element is killed by
one power and therefore belongs to the image of one evaluation map. Two maps
with the same value at 1 agree, so these maps identify the filtered colimit
with the union of the annihilator submodules, namely `Ideal.primaryComponent`.
Postcomposition with the differential commutes with evaluation. Thus the
identifications in all degrees form an isomorphism of cochain complexes.
Exponent zero gives the zero module; for the zero and unit ideals the union
is respectively the entire module and zero. No finite-generation hypothesis
is needed for this identification. -/
theorem nonempty_colimit_quotientHomComplex_iso_torsion
    {R : Type u} [CommRing R] (J : Ideal R)
    (K : CochainComplex (ModuleCat.{u} R) ℕ) :
    Nonempty (colimit
      ((localCohomology.ringModIdeals (localCohomology.idealPowersDiagram J)).op ⋙
        homComplexDiagram K) ≅
      ((idealPowerTorsion J).mapHomologicalComplex (ComplexShape.up ℕ)).obj K) := by
  let c := quotientHomCocone J K
  have hc : IsColimit c := HomologicalComplex.isColimitOfEval _ c (fun k ↦ by
    change IsColimit (evalCocone J (K.X k))
    exact evalCoconeIsColimit J (K.X k))
  exact ⟨(colimit.isColimit _).coconePointUniqueUpToIso hc⟩

end ModuleCat
