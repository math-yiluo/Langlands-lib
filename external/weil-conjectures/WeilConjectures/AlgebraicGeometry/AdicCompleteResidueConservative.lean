/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicResidueLiftComparisons
import WeilConjectures.AlgebraicGeometry.AdicCompleteReductionCone
import WeilConjectures.AlgebraicGeometry.AdicResidueVanishingSuccessor
import all WeilConjectures.AlgebraicGeometry.AdicResidueQuotientUnitUniversal

/-! # Derived Nakayama on localized completed coefficient sites

Source: Stacks Project, Tags 09C6, 099M and 099F.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The universal scalar extension inherits exactness from the cochain model. -/
private theorem extension_exact
    {C : Type*} [SmallCategory C] {S : GrothendieckTopology C}
    {R B : Sheaf S CommRingCat} (q : R ⟶ B) :
    ∃ _s : (ConstantCompletion.extend q).CommShift ℤ,
      (ConstantCompletion.extend q).IsTriangulated := by
  let := HasDerivedCategory.standard (ConstantCompletion.Mod R)
  let := HasDerivedCategory.standard (ConstantCompletion.Mod B)
  obtain ⟨E, hobj, hmap, hpres, F, hpw, ε, hu, htri, hc⟩ :=
    (SheafOfModules.nonempty_derivedChangeOfRingsCochainModel q).some
  have hE : E = ConstantCompletion.change q := CategoryTheory.Functor.ext hobj (fun _ _ f ↦ hmap f)
  subst E
  let := hu
  let : (ConstantCompletion.extend q).IsLeftDerivedFunctor
      (ConstantCompletion.extendComparison q)
      (HomologicalComplex.quasiIso (ConstantCompletion.Mod R) (.up ℤ)) :=
    (ConstantCompletion.derivedExtension q).universal
  let e : F ≅ ConstantCompletion.extend q :=
    Functor.leftDerivedUnique (ConstantCompletion.extend q) F ε
      (ConstantCompletion.extendComparison q)
      (HomologicalComplex.quasiIso (ConstantCompletion.Mod R) (.up ℤ))
  obtain ⟨sF, hF⟩ := htri
  let := sF
  let := hF
  let s := Functor.CommShift.ofIso e ℤ
  have : NatTrans.CommShift e.hom ℤ := Functor.CommShift.ofIso_compatibility e ℤ
  exact ⟨s, Functor.isTriangulated_of_iso e⟩

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- Completeness, defined by vanishing of exact internal Hom tests, is closed under cones. -/
private theorem complete_cone
    {C : Type*} [SmallCategory C] {S : GrothendieckTopology C}
    {R B : Sheaf S CommRingCat} (q : R ⟶ B)
    (T : Triangle (ConstantCompletion.D R))
    (hT : T ∈ distTriang (ConstantCompletion.D R))
    (h₁ : ConstantCompletion.IsComplete q T.obj₁)
    (h₂ : ConstantCompletion.IsComplete q T.obj₂) :
    ConstantCompletion.IsComplete q T.obj₃ := by
  exact _root_.AlgebraicGeometry.Scheme.complete_cone q T hT h₁ h₂

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- Reconstruction from the quotient tower detects zero once all reductions vanish. -/
private theorem complete_zero_of_reductions
    (X : Scheme.{u}) {A : Type (max v (u + 1))} [CommRing A] [IsNoetherianRing A]
    (J : Ideal A) (U : coefficientProEtaleSiteModel.{u, v} X)
    (M : AdicResidueLocalDerived.{u, v} X J U)
    (hM : ConstantCompletion.IsComplete (adicResidueLocalProjection X J U 0) M)
    (hz : ∀ n, IsZero ((adicResidueLocalReduction X J U n).obj M)) : IsZero M := by
  obtain ⟨F, c, eM, e, adj, hc, hleg, hstep⟩ :=
    adicResidue_complete_reduction_cone X J U M hM
  have hF (n : ℕ) : IsZero (F.obj (op n)) := by
    let q := adicResidueLocalProjection X J U n
    have hres : (ConstantCompletion.dres q).Additive := by
      dsimp only [ConstantCompletion.dres, siteDerivedRestrictScalars]
      infer_instance
    exact ((ConstantCompletion.dres q).map_isZero (hz n)).of_iso (e n)
  have hc0 : IsZero c.pt := (IsZero.iff_id_eq_zero _).2
    (hc.hom_ext_zero (fun n g ↦ (hF n).eq_of_tgt g 0)
      (fun n g ↦ (hF n).eq_of_tgt g 0) (𝟙 c.pt))
  exact hc0.of_iso eM.symm

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- Residue reduction detects isomorphisms between locally complete objects on a slice.
Source: Stacks Project, proetale.tex, Tag 09C6, final step; Algebraization, Tags 099M and
099F, derived Nakayama.
(auxiliary; not a blueprint node).

Proof: complete f to a distinguished triangle with cone Q. The completion unit is a
map of exact functors, so the complete-object criterion and two-out-of-three make Q
complete. Its residue reduction is zero. The exact constant coefficient sequence
0 -> J^n/J^(n+1) -> A/J^(n+1) -> A/J^n -> 0 gives after derived tensor with Q a triangle.
The first term is the tensor of the zero residue reduction with J^n/J^(n+1), hence
vanishes. Induction makes every finite reduction of Q zero. The same calculation
holds on the slice, because restriction is exact and preserves the coefficient maps.
Completeness identifies Q with the derived limit of these zero reductions, hence Q
is zero. The distinguished triangle then makes f an isomorphism. Neither T nor M
is assumed bounded or constructible; no quotient is assumed perfect over A. -/
theorem adicResidue_isIso_of_residue
    (X : Scheme.{u}) {A : Type (max v (u + 1))} [CommRing A] [IsNoetherianRing A]
    (J : Ideal A) (U : coefficientProEtaleSiteModel.{u, v} X)
    (T M : AdicResidueLocalDerived.{u, v} X J U)
    (_hT : CategoryTheory.ConstantCompletion.IsComplete
      (adicResidueLocalProjection.{u, v} X J U 0) T)
    (_hM : CategoryTheory.ConstantCompletion.IsComplete
      (adicResidueLocalProjection.{u, v} X J U 0) M)
    (f : T ⟶ M) (_hf : IsIso ((adicResidueLocalReduction.{u, v} X J U 0).map f)) : IsIso f := by
  let R := adicResidueLocalReduction.{u, v} X J U 0
  obtain ⟨sR, hR⟩ := extension_exact (adicResidueLocalProjection.{u, v} X J U 0)
  let : R.CommShift ℤ := sR
  let : R.IsTriangulated := hR
  obtain ⟨Q, g, h, htriangle⟩ := Pretriangulated.distinguished_cocone_triangle f
  let Δ := Triangle.mk f g h
  have hQ : ConstantCompletion.IsComplete (adicResidueLocalProjection X J U 0) Q :=
    complete_cone _ Δ htriangle _hT _hM
  have hQ0 : IsZero (R.obj Q) :=
    Pretriangulated.Triangle.isZero₃_of_isIso₁ _ (R.map_distinguished Δ htriangle) _hf
  have hz : ∀ n, IsZero ((adicResidueLocalReduction X J U n).obj Q) := by
    intro n
    induction n with
    | zero => exact hQ0
    | succ n hn => exact adicResidue_vanishing_successor X J U Q n hQ0 hn
  exact (Δ.isZero₃_iff_isIso₁ htriangle).1
    (complete_zero_of_reductions X J U Q hQ hz)

end AlgebraicGeometry.Scheme
