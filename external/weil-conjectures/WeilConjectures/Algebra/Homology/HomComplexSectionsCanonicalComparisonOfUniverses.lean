/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses

/-!
# Canonical comparison for sections of a sheaf Hom complex

Source: Stacks Project, Tag 0A8Y, Equation (21.34.0.1).
(auxiliary; not a blueprint node)
-/

@[expose] public section

universe u v r
open CategoryTheory Opposite
namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false in
/-- The canonical shifted section comparison, specified on cocycle representatives.
Source: Stacks Project, Tag 0A8Y, Equation (21.34.0.1).
(auxiliary; not a blueprint node)

Proof: sections preserve the product cone specifying the sheaf Hom complex.
Its projections therefore identify degree-n sections with all degree-n cochains
between the restricted complexes. The differential projection formula identifies
the kernel with Mathlib's cocycles, giving e with the component formula below.
The same formula in degree n-1 identifies images of differentials with coboundaries.
Thus e descends to a bijection of the quotients. Compose that bijection with
Mathlib's equivalence from cohomology classes to shifted homotopy-category maps
to obtain a. On cocycles this composite is the quotient of equivHomShift.symm,
which proves the asserted representative formula. This construction works for
unbounded complexes since it uses products. Zero complexes give singleton
quotients; n=0 is the usual unshifted comparison. -/
theorem homComplex_sections_canonical_comparisonOfUniverses
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max u v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
    (R : Sheaf J CommRingCat.{max u v r}) (U : C)
    (L I : CochainComplex
      (SheafOfModules.{max u v r}
        ((sheafCompose J (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj R)) ℤ)
    (n : ℤ) :
    let R₀ := (sheafCompose J (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj R
    let E := (SheafOfModules.forget R₀ ⋙ PresheafOfModules.evaluation R₀.obj (op U) ⋙
      forget₂ (ModuleCat.{max u v r} (R₀.obj.obj (op U))) AddCommGrpCat).mapHomologicalComplex
        (ComplexShape.up ℤ)
    letI := module_overFunctor_preservesZero R₀ U
    let res := (SheafOfModules.overFunctor.{max u v r} R₀ U).mapHomologicalComplex
      (ComplexShape.up ℤ)
    let Q := HomotopyCategory.quotient (SheafOfModules.{max u v r} (R₀.over U))
      (ComplexShape.up ℤ)
    let S := E.obj (homComplex (R := R) L I)
    let π := Classical.choose
      (homComplex_projections_exists.{u, v, max u v r, max u v r} (J := J) (R := R))
    ∃ e : S.cycles n ≃ CochainComplex.HomComplex.Cocycle (res.obj L) (res.obj I) n,
      (∀ (z : S.cycles n) (p q : ℤ) (hpq : p + n = q) (W : (Over U)ᵒᵖ),
        ((e z).val.v p q hpq).val.app W =
          (((π L I n p q hpq).val.app (op U)) (S.iCycles n z)).app W) ∧
      ∃ a : S.homology n ≃ (Q.obj (res.obj L) ⟶ Q.obj ((res.obj I)⟦n⟧)),
        ∀ z : S.cycles n, a (S.homologyπ n z) =
          Q.map (CochainComplex.HomComplex.Cocycle.equivHomShift.symm (e z)) := by
  classical
  let R₀ := (sheafCompose J (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj R
  let := module_overFunctor_preservesZero.{u, v, max u v r, max u v r} R₀ U
  let res : CochainComplex (SheafOfModules.{max u v r} R₀) ℤ ⥤
      CochainComplex (SheafOfModules.{max u v r} (R₀.over U)) ℤ :=
    (SheafOfModules.overFunctor.{max u v r} R₀ U).mapHomologicalComplex
    (ComplexShape.up ℤ)
  let E := (SheafOfModules.forget R₀ ⋙ PresheafOfModules.evaluation R₀.obj (op U) ⋙
    forget₂ (ModuleCat.{max u v r} (R₀.obj.obj (op U))) AddCommGrpCat).mapHomologicalComplex
      (ComplexShape.up ℤ)
  let S : CochainComplex AddCommGrpCat.{max u v r} ℤ :=
    E.obj (homComplex (R := R) L I)
  let T : CochainComplex AddCommGrpCat.{max u v r} ℤ :=
    CochainComplex.HomComplex (res.obj L) (res.obj I)
  let π := Classical.choose
    (homComplex_projections_exists.{u, v, max u v r, max u v r} (J := J) (R := R))
  have hco := homComplex_sections_cochainsOfUniverses.{u, v, r} (C := C) (J := J) R U L I
  dsimp only at hco
  obtain ⟨e, he⟩ := hco
  have hcomm := homComplex_sections_cochains_commOfUniverses.{u, v, r}
    (C := C) (J := J) R U L I
  dsimp only at hcomm
  have hd := hcomm e he
  let f : S ⟶ T :=
    { f := fun i ↦ AddCommGrpCat.ofHom (e i).toAddMonoidHom
      comm' := by
        intro i j hij
        ext x
        exact (hd i j hij x).symm }
  have hf (i : ℤ) : IsIso (f.f i) := by
    exact (AddEquiv.toAddCommGrpIso (X := S.X i) (Y := T.X i) (e i)).isIso_hom
  have : IsIso f := HomologicalComplex.Hom.isIso_of_components f
  let F := asIso f
  let h := CochainComplex.HomComplex.leftHomologyData (res.obj L) (res.obj I) n
  let ec := (HomologicalComplex.cyclesMapIso F n) ≪≫ h.cyclesIso
  let ac := (HomologicalComplex.homologyMapIso F n) ≪≫ h.homologyIso
  let a := ac.addCommGroupIsoToAddEquiv.trans
    CochainComplex.HomComplex.CohomologyClass.homAddEquiv
  refine ⟨ec.addCommGroupIsoToAddEquiv.toEquiv, ?_, a.toEquiv, ?_⟩
  · intro z p q hpq W
    have hc : (ec.hom z).val = e n (S.iCycles n z) := by
      have hh := ConcreteCategory.congr_hom
        (h.cyclesIso_hom_comp_i) (HomologicalComplex.cyclesMap f n z)
      have hh' := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i f n) z
      exact hh.trans hh'
    exact (congrArg (fun c ↦ (c.v p q hpq).val.app W) hc).trans
      (he n (S.iCycles n z) p q hpq W)
  · intro z
    have ha : ac.hom (S.homologyπ n z) =
        CochainComplex.HomComplex.CohomologyClass.mk (ec.hom z) := by
      have hh := ConcreteCategory.congr_hom
        (h.homologyπ_comp_homologyIso_hom) (HomologicalComplex.cyclesMap f n z)
      have hh' := ConcreteCategory.congr_hom
        (HomologicalComplex.homologyπ_naturality f n) z
      exact (congrArg h.homologyIso.hom hh').trans hh
    change CochainComplex.HomComplex.CohomologyClass.homAddEquiv
      (ac.hom (S.homologyπ n z)) = _
    exact (congrArg CochainComplex.HomComplex.CohomologyClass.homAddEquiv ha).trans
      (CochainComplex.HomComplex.CohomologyClass.toHom_mk (ec.hom z))

end CategoryTheory
