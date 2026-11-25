/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel
import WeilConjectures.AlgebraicGeometry.ModuleFinitePresentationCokernel
import WeilConjectures.AlgebraicGeometry.AffineUniversallyExactOpcyclesFlat
import WeilConjectures.Algebra.Homology.RightExactTruncGEIso
import WeilConjectures.Algebra.Homology.FlatOpcyclesTorCriterion

/-! # Lower truncation of universally connective affine flat complexes -/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem flat_of_iso {S : Scheme.{u}} {M N : S.Modules}
    (e : M ≅ N) (hN : N.IsFlatOver (𝟙 S)) : M.IsFlatOver (𝟙 S) := by
  intro V U hUV
  let f := ((𝟙 S : S ⟶ S).appLE V.1 U.1 hUV).hom
  let : Module Γ(S, V.1) Γ(M, U.1) := Module.compHom _ f
  let : Module Γ(S, V.1) Γ(N, U.1) := Module.compHom _ f
  let E := (ModuleCat.restrictScalars f).mapIso
    ((SheafOfModules.evaluation (R := S.ringCatSheaf) (Opposite.op U.1)).mapIso e)
  exact (Module.Flat.equiv_iff E.toLinearEquiv).mpr (hN V U hUV)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem flat_of_isZero {S : Scheme.{u}} (M : S.Modules)
    (hM : IsZero M) : M.IsFlatOver (𝟙 S) := by
  intro V U hUV
  let F := SheafOfModules.forget.{u} S.ringCatSheaf ⋙
    PresheafOfModules.evaluation _ (Opposite.op U.1)
  have : Subsingleton (F.obj M) := ModuleCat.subsingleton_of_isZero (F.map_isZero hM)
  let : Module Γ(S, V.1) (F.obj M) :=
    Module.compHom _ ((𝟙 S : S ⟶ S).appLE V.1 U.1 hUV).hom
  change Module.Flat Γ(S, V.1) (F.obj M)
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem qc_of_isZero (S : Scheme.{u}) (N : S.Modules) (hN : IsZero N) :
    N.IsQuasicoherent := by
  let M := SheafOfModules.free (R := S.ringCatSheaf) PEmpty.{u + 1}
  have hz : IsZero M := (IsZero.iff_id_eq_zero M).mpr (by
    apply Sigma.hom_ext
    intro i
    exact i.elim)
  exact (SheafOfModules.isQuasicoherent S.ringCatSheaf).prop_of_iso (hz.iso hN)
    (SheafOfModules.isQuasicoherent_free PEmpty.{u + 1})

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem fp_of_isZero (S : Scheme.{u}) (N : S.Modules) (hN : IsZero N) :
    N.IsFinitePresentation := by
  let M := SheafOfModules.free (R := S.ringCatSheaf) PEmpty.{u + 1}
  have hz : IsZero M := (IsZero.iff_id_eq_zero M).mpr (by
    apply Sigma.hom_ext
    intro i
    exact i.elim)
  let q : M.LocalGeneratorsData :=
    (SheafOfModules.free.generatingSections
      (R := S.ringCatSheaf) PEmpty.{u + 1}).localGeneratorsData
  have hq : q.IsLocallyFreeData := inferInstance
  have hf : q.IsFiniteType := by
    constructor
    intro i
    constructor
    change Finite PEmpty.{u + 1}
    infer_instance
  have : M.IsFiniteLocallyFree := by
    constructor
    exact ⟨q, hq, hf⟩
  have : N.IsFiniteLocallyFree := SheafOfModules.IsFiniteLocallyFree.of_iso.{u, u, u} (hz.iso hN)
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private noncomputable def opcyclesCokernelIso {S : Scheme.{u}}
    (C : CochainComplex S.Modules ℤ) : C.opcycles 0 ≅ cokernel (C.d (-1) 0) :=
  (C.opcyclesIsCokernel (i := (-1)) (j := 0) (by simp)).coconePointUniqueUpToIso
    (colimit.isColimit _)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Canonical lower truncation retains finite presentation and flatness when
negative homology vanishes universally. It preserves nonnegative homology after
any base change. This statement has no proper morphism or coefficient sheaf.
Source: Stacks Project, Tags 0653 and 0654 (flat opcycles and lower truncation).
(blueprint: lem-pc-affine-flat-connective-truncation).

Proof: Write S = Spec A and pass to global sections using the affine
quasi-coherent equivalence. The terms of C become finitely presented flat, hence
finite projective, A-modules. Let P be their complex. For an arbitrary A-module N,
base change to the square-zero A-algebra A ⊕ N. The tensor complex is the direct
sum of P and P tensor N. Universal negative vanishing therefore makes P tensor N
exact in degree -1. The flat-opcycle criterion of Tag 0653 gives flatness of
coker(d : P^(-1) -> P^0). This cokernel is finitely presented as the cokernel of a
map between finitely presented modules. Sheafification identifies it with the
zeroth term of C.truncGE 0. Terms above zero are unchanged and terms below zero
are zero, proving all three termwise assertions. For any g, pullback is right
exact and identifies the degree-zero term with the cokernel of the pulled-back
differential. Thus g*(C.truncGE 0) is the canonical lower truncation of g*C up to
a canonical complex isomorphism. The truncation projection induces isomorphisms
on homology in degrees q >= 0 (in degree zero both are ker(d^0)/im(d^(-1))).
Taking the inverse yields the displayed isomorphisms. This is global even for
nonaffine S', since cokernels and these computations are sheaf-local. Empty S,
b = 0 and C = 0 require no nontriviality assumption. -/
theorem affine_flat_connective_truncation (S : Scheme.{u}) (hS : IsAffine S)
    (C : CochainComplex S.Modules ℤ) (a : ℤ) (b : ℕ)
    (hCge : C.IsStrictlyGE a) (hCle : C.IsStrictlyLE b)
    (hCflat : ∀ n : ℤ, (C.X n).IsFlatOver (𝟙 S))
    (hCqc : ∀ n : ℤ, (C.X n).IsQuasicoherent)
    (hCfp : ∀ n : ℤ, (C.X n).IsFinitePresentation)
    (hneg : ∀ {S' : Scheme.{u}} (g : S' ⟶ S) (i : ℤ), i < 0 →
      IsZero ((((Modules.pullback g).mapHomologicalComplex _).obj C).homology i)) :
    (∀ n : ℤ, ((C.truncGE 0).X n).IsFlatOver (𝟙 S)) ∧
    (∀ n : ℤ, ((C.truncGE 0).X n).IsQuasicoherent) ∧
    (∀ n : ℤ, ((C.truncGE 0).X n).IsFinitePresentation) ∧
    ∀ {S' : Scheme.{u}} (g : S' ⟶ S) (q : ℕ),
      Nonempty ((((Modules.pullback g).mapHomologicalComplex _).obj
          (C.truncGE 0)).homology q ≅
        (((Modules.pullback g).mapHomologicalComplex _).obj C).homology q) := by
  have _hBounds : C.IsStrictlyGE a ∧ C.IsStrictlyLE (b : ℤ) := ⟨hCge, hCle⟩
  have hopflat := affine_opcycles_flat_of_universally_exact S hS C hCflat hCqc
    (fun g ↦ hneg g (-1) (by decide))
  let e₀ := C.truncGEXIsoOpcycles 0 ≪≫ opcyclesCokernelIso C
  have hqc₀ : ((C.truncGE 0).X 0).IsQuasicoherent := by
    have := hCqc (-1)
    have := hCqc 0
    have hc := isQuasicoherent_cokernel (C.d (-1) 0)
    exact (SheafOfModules.isQuasicoherent S.ringCatSheaf).prop_of_iso e₀.symm hc
  have hfp₀ : ((C.truncGE 0).X 0).IsFinitePresentation := by
    have := hCfp (-1)
    have := hCfp 0
    have hc := RingedSpace.isFinitePresentation_cokernel_of_both_isFinitePresentation
      S.toRingedSpace (C.d (-1) 0)
    exact (SheafOfModules.isFinitePresentation S.ringCatSheaf).prop_of_iso e₀.symm hc
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n
    obtain hn | rfl | hn := lt_trichotomy n 0
    · exact flat_of_isZero _ ((C.truncGE 0).isZero_of_isStrictlyGE 0 n hn)
    · exact flat_of_iso (C.truncGEXIsoOpcycles 0) hopflat
    · exact flat_of_iso (C.truncGEXIso 0 n hn) (hCflat n)
  · intro n
    obtain hn | rfl | hn := lt_trichotomy n 0
    · exact qc_of_isZero S _ ((C.truncGE 0).isZero_of_isStrictlyGE 0 n hn)
    · exact hqc₀
    · exact (SheafOfModules.isQuasicoherent S.ringCatSheaf).prop_of_iso
        (C.truncGEXIso 0 n hn).symm (hCqc n)
  · intro n
    obtain hn | rfl | hn := lt_trichotomy n 0
    · exact fp_of_isZero S _ ((C.truncGE 0).isZero_of_isStrictlyGE 0 n hn)
    · exact hfp₀
    · exact (SheafOfModules.isFinitePresentation S.ringCatSheaf).prop_of_iso
        (C.truncGEXIso 0 n hn).symm (hCfp n)
  · intro S' g q
    let F := (Modules.pullback g).mapHomologicalComplex (.up ℤ)
    let P : CochainComplex S'.Modules ℤ := F.obj C
    obtain ⟨e⟩ := CochainComplex.nonempty_map_truncGE_iso (Modules.pullback g) C 0
    have : QuasiIsoAt (P.πTruncGE 0) (q : ℤ) :=
      CochainComplex.quasiIsoAt_πTruncGE _ 0 q (Int.natCast_nonneg q)
    exact ⟨(HomologicalComplex.homologyFunctor S'.Modules (.up ℤ) (q : ℤ)).mapIso e ≪≫
      (asIso (HomologicalComplex.homologyMap (P.πTruncGE 0) (q : ℤ))).symm⟩

end AlgebraicGeometry.Scheme.Modules
