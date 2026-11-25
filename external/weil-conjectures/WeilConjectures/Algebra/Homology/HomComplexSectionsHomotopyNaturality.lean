/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparison
import Mathlib.Algebra.Category.Grp.EpiMono

@[expose] public section

universe u v
open CategoryTheory Opposite
namespace CategoryTheory

private lemma homObjMap_section_component
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{max u v}) (U : C)
    {A A' B B' : SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)}
    (t : A' ⟶ A) (s : B ⟶ B')
    (φ : (SheafOfModules.homObj (R := R) A B).val.obj (op U))
    (W : (Over U)ᵒᵖ) :
    (((SheafOfModules.homObjMap t s).val.app (op U)) φ).app W =
      ((SheafOfModules.overFunctor _ U).map t).val.app W ≫ φ.app W ≫
        ((SheafOfModules.overFunctor _ U).map s).val.app W := by
  rfl

-- Projection comparisons involve several composed functors and chosen product objects.
/-- The shifted section Hom-complex comparison in the homotopy category is natural.
Source: Stacks Project, Tag 0A8Y, Equation (21.34.0.1).
(blueprint: lem-pur-hom-complex-sections-homotopy-naturality)

Proof: evaluate the product projections of the sheaf Hom complex at U. Sections
in degree n are families of maps L^p|U to I^(p+n)|U. The differential formula
identifies cycles with chain maps into the shifted target, whose differential
is (-1)^n times the original differential. Multiply a family in degree n-1
by (-1)^n to identify its differential with a null-homotopy into that target.
Quotienting gives a bijection between homology classes
and homotopy classes, since both quotient projections are surjective. Apply
this construction to (L,I') and (L',I), obtaining a and b. Componentwise
composition sends a family f to s f t; the homotopy sign correction depends
only on n and hence commutes with both maps. This proves the displayed equality
on cycles and then on all homology classes. No K-injectivity or localization
at quasi-isomorphisms is used. Degree zero recovers the unshifted comparison;
zero complexes give singleton Hom sets; unbounded complexes use products. -/
theorem homComplex_sections_homotopy_naturality
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{max u v}) (U : C)
    {I' I L' L : CochainComplex
      (SheafOfModules.{max u v}
        ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ℤ}
    (s : I' ⟶ I) (t : L' ⟶ L) (n : ℤ) :
    let R₀ := (sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R
    let E := (SheafOfModules.forget R₀ ⋙ PresheafOfModules.evaluation R₀.obj (op U) ⋙
      forget₂ (ModuleCat.{max u v} (R₀.obj.obj (op U))) AddCommGrpCat).mapHomologicalComplex
        (ComplexShape.up ℤ)
    letI := module_overFunctor_preservesZero R₀ U
    let res := (SheafOfModules.overFunctor.{max u v} R₀ U).mapHomologicalComplex
      (ComplexShape.up ℤ)
    let Q := HomotopyCategory.quotient (SheafOfModules.{max u v} (R₀.over U))
      (ComplexShape.up ℤ)
    let f := E.map (((homComplexFunctor (R := R)).map t.op).app I' ≫
      ((homComplexFunctor (R := R)).obj (op L')).map s)
    ∃ a : (E.obj (homComplex (R := R) L I')).homology n ≃
        (Q.obj (res.obj L) ⟶ Q.obj ((res.obj I')⟦n⟧)),
      ∃ b : (E.obj (homComplex (R := R) L' I)).homology n ≃
          (Q.obj (res.obj L') ⟶ Q.obj ((res.obj I)⟦n⟧)),
        ∀ x, b (HomologicalComplex.homologyMap f n x) =
          Q.map (res.map t) ≫ a x ≫ Q.map ((shiftFunctor _ n).map (res.map s)) := by
  classical
  let R₀ := (sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R
  let E := (SheafOfModules.forget R₀ ⋙ PresheafOfModules.evaluation R₀.obj (op U) ⋙
    forget₂ (ModuleCat.{max u v} (R₀.obj.obj (op U))) AddCommGrpCat).mapHomologicalComplex
      (ComplexShape.up ℤ)
  let := module_overFunctor_preservesZero R₀ U
  let res := (SheafOfModules.overFunctor.{max u v} R₀ U).mapHomologicalComplex
    (ComplexShape.up ℤ)
  let Q := HomotopyCategory.quotient (SheafOfModules.{max u v} (R₀.over U))
    (ComplexShape.up ℤ)
  let f := E.map (((homComplexFunctor (R := R)).map t.op).app I' ≫
    ((homComplexFunctor (R := R)).obj (op L')).map s)
  let S := E.obj (homComplex (R := R) L I')
  let T := E.obj (homComplex (R := R) L' I)
  let π := Classical.choose (Classical.choose_spec
    (homComplex_exists.{u, v, max u v, max u v} (J := J) (R := R)))
  have hmap := (Classical.choose_spec (Classical.choose_spec
    (homComplex_exists.{u, v, max u v, max u v} (J := J) (R := R)))).2.2
  obtain ⟨e, he, a, ha⟩ := homComplex_sections_canonical_comparison R U L I' n
  obtain ⟨e', he', b, hb⟩ := homComplex_sections_canonical_comparison R U L' I n
  change S.cycles n ≃ CochainComplex.HomComplex.Cocycle (res.obj L) (res.obj I') n at e
  change T.cycles n ≃ CochainComplex.HomComplex.Cocycle (res.obj L') (res.obj I) n at e'
  change S.homology n ≃ (Q.obj (res.obj L) ⟶ Q.obj ((res.obj I')⟦n⟧)) at a
  change T.homology n ≃ (Q.obj (res.obj L') ⟶ Q.obj ((res.obj I)⟦n⟧)) at b
  change ∀ (z : S.cycles n) (p q : ℤ) (hpq : p + n = q) (W : (Over U)ᵒᵖ),
    ((e z).val.v p q hpq).val.app W =
      (((π L I' n p q hpq).val.app (op U)) (S.iCycles n z)).app W at he
  change ∀ (z : T.cycles n) (p q : ℤ) (hpq : p + n = q) (W : (Over U)ᵒᵖ),
    ((e' z).val.v p q hpq).val.app W =
      (((π L' I n p q hpq).val.app (op U)) (T.iCycles n z)).app W at he'
  change ∀ z : S.cycles n, a (S.homologyπ n z) =
    Q.map (CochainComplex.HomComplex.Cocycle.equivHomShift.symm (e z)) at ha
  change ∀ z : T.cycles n, b (T.homologyπ n z) =
    Q.map (CochainComplex.HomComplex.Cocycle.equivHomShift.symm (e' z)) at hb
  change ∃ a : S.homology n ≃ (Q.obj (res.obj L) ⟶ Q.obj ((res.obj I')⟦n⟧)),
    ∃ b : T.homology n ≃ (Q.obj (res.obj L') ⟶ Q.obj ((res.obj I)⟦n⟧)),
      ∀ x, b (HomologicalComplex.homologyMap f n x) =
        Q.map (res.map t) ≫ a x ≫ Q.map ((shiftFunctor _ n).map (res.map s))
  refine ⟨a, b, ?_⟩
  intro x
  obtain ⟨z, rfl⟩ := (AddCommGrpCat.epi_iff_surjective (S.homologyπ n)).mp inferInstance x
  have hz : e' (HomologicalComplex.cyclesMap f n z) =
      ((e z).precomp (res.map t)).postcomp (res.map s) := by
    apply CochainComplex.HomComplex.Cocycle.ext
    apply CochainComplex.HomComplex.Cochain.ext
    intro p q hpq
    apply SheafOfModules.hom_ext
    ext W y
    rw [he']
    have hci := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i f n) z
    change T.iCycles n (HomologicalComplex.cyclesMap f n z) =
      f.f n (S.iCycles n z) at hci
    change ((((π L' I n p q hpq).val.app (op U))
      (T.iCycles n (HomologicalComplex.cyclesMap f n z))).app W).hom y = _
    refine (congrArg
      (fun x : T.X n ↦
        ((((π L' I n p q hpq).val.app (op U)) x).app W).hom y) hci).trans ?_
    have hm0 : (((homComplexFunctor (R := R)).map t.op).app I' ≫
        ((homComplexFunctor (R := R)).obj (op L')).map s).f n ≫ π L' I n p q hpq =
        π L I' n p q hpq ≫ SheafOfModules.homObjMap (R := R) (t.f p) (s.f q) :=
      hmap L L' I' I t s n p q hpq
    have hm := congrArg
      (fun k : (homComplex (R := R) L I').X n ⟶
          SheafOfModules.homObj (R := R) (L'.X p) (I.X q) ↦
        (k.val.app (op U)) (S.iCycles n z))
      hm0
    change ((π L' I n p q hpq).val.app (op U)) (f.f n (S.iCycles n z)) =
      (SheafOfModules.homObjMap (R := R) (t.f p) (s.f q)).val.app (op U)
        (((π L I' n p q hpq).val.app (op U)) (S.iCycles n z)) at hm
    refine (congrArg (fun k ↦ (k.app W).hom y) hm).trans ?_
    simp only [CochainComplex.HomComplex.Cocycle.postcomp_coe,
      CochainComplex.HomComplex.Cocycle.precomp_coe,
      CochainComplex.HomComplex.Cochain.comp_zero_cochain_v,
      CochainComplex.HomComplex.Cochain.zero_cochain_comp_v,
      CochainComplex.HomComplex.Cochain.ofHom_v]
    have hev := he z p q hpq W
    have hc := congrArg (fun k ↦ k.hom (((res.map t).f p).val.app W y)) hev
    have hc' := congrArg (((res.map s).f q).val.app W) hc
    rw [homObjMap_section_component]
    exact hc'.symm
  change b (HomologicalComplex.homologyMap f n (S.homologyπ n z)) =
    Q.map (res.map t) ≫ a (S.homologyπ n z) ≫
      Q.map ((shiftFunctor _ n).map (res.map s))
  have hn := ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality f n) z
  change HomologicalComplex.homologyMap f n (S.homologyπ n z) =
    T.homologyπ n (HomologicalComplex.cyclesMap f n z) at hn
  calc
    b (HomologicalComplex.homologyMap f n (S.homologyπ n z)) =
        b (T.homologyπ n (HomologicalComplex.cyclesMap f n z)) := congrArg b hn
    _ = Q.map (CochainComplex.HomComplex.Cocycle.equivHomShift.symm
        (e' (HomologicalComplex.cyclesMap f n z))) := hb _
    _ = Q.map (res.map t) ≫
        Q.map (CochainComplex.HomComplex.Cocycle.equivHomShift.symm (e z)) ≫
          Q.map ((shiftFunctor _ n).map (res.map s)) := by
      rw [hz, CochainComplex.HomComplex.Cocycle.equivHomShift_symm_postcomp,
        CochainComplex.HomComplex.Cocycle.equivHomShift_symm_precomp,
        Q.map_comp, Q.map_comp, Category.assoc]
    _ = _ := congrArg (fun k ↦ Q.map (res.map t) ≫ k ≫
      Q.map ((shiftFunctor _ n).map (res.map s))) (ha z).symm

end CategoryTheory
