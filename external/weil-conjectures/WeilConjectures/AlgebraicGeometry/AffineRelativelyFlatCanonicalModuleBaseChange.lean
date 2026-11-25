/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedModuleBaseChangeMap
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

import WeilConjectures.AlgebraicGeometry.FlatComplexDerivedPullback
import WeilConjectures.AlgebraicGeometry.AffineAlternatingCechModelFlat
import WeilConjectures.AlgebraicGeometry.AffineAlternatingCechBaseChangeFactorization

/-! # Affine computation of relatively flat canonical module base change

Source: blueprint `lemma-coherent-base-change-invertible-sheaves--2`, Steps 2--5;
Stacks Project, Tag 0A1D, specializing to a module in degree zero.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory Limits
namespace AlgebraicGeometry

private theorem affineAlternatingCechModel_bounded
    {A : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec A)
    {r : ℕ} (U : Fin r → X.Opens) (G : X.Modules) :
    ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero ((affineAlternatingCechModel f U G).X i) := by
  classical
  refine ⟨r, ?_⟩
  intro i hi
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, (n : ℤ) = i := ⟨i.toNat, by omega⟩
  let C := alternatingCechComplex U G.presheafModuleCat
  have hempty : IsEmpty (Fin (n + 1) ↪o Fin r) := ⟨fun t ↦ by
    have hcard := Fintype.card_le_of_injective t t.injective
    simp only [Fintype.card_fin] at hcard
    omega⟩
  have hzero : IsZero (C.X n) := by
    change IsZero (ModuleCat.of _ (∀ t : Fin (n + 1) ↪o Fin r,
      G.presheafModuleCat.obj (Opposite.op (alternatingCechIntersection U t))))
    exact ModuleCat.isZero_of_subsingleton _
  have hext : IsZero ((C.extend ComplexShape.embeddingUpNat).X (n : ℤ)) :=
    hzero.of_iso (C.extendXIso ComplexShape.embeddingUpNat (i := n) rfl)
  exact Functor.map_isZero
    (ModuleCat.restrictScalars (((Scheme.ΓSpecIso A).inv ≫ f.appTop).hom) ⋙
      tilde.functor A) hext

/-- Over affine bases the canonical module base-change composite is invertible.
Source: blueprint `lemma-coherent-base-change-invertible-sheaves--2`, Steps 2--5, and Stacks Tag
0A1D. (blueprint: lem-pc-affine-relatively-flat-canonical-module-base-change).

Proof: choose a finite ordered affine cover of X. Separatedness over Spec A makes
all finite intersections affine. Their modules of sections of G are flat over A
by relative flatness. The finite alternating Cech complex K thus consists of flat
A-modules and is bounded; its sheafification computes Rf_*G. Use the flat-complex
counit comparison to compute Lg^* on this complex by ordinary tensor with B.
For each intersection Spec C, the affine section-pullback isomorphism identifies
Gamma(G, Spec C) tensor_A B with the sections of the pulled-back module on
Spec (C tensor_A B). The pure-tensor formula respects restrictions, so these
isomorphisms commute with the alternating differentials. They identify the tensor
complex with the Cech complex of the pulled-back cover. The Cech characterization
of base change identifies its map with the displayed canonical mate followed by
Rf'_*c. This identifies the map, not merely its source and target. Consequently it
is a composite of isomorphisms. Derived tensor of G[0] has no positive cohomology,
and its degree-zero cohomology is ordinary pullback. A map from it to (p*G)[0]
factors through degree-zero cohomology. Two left-derived counits differ by a natural
automorphism of Lp*, by right Kan extension uniqueness; on degree-zero cohomology
this induces an automorphism of p*G. Thus changing the counit changes c by an
invertible ordinary-target map. Its derived direct image is invertible as well.
For an empty X the empty Cech complex is zero, and the same argument applies.
No flatness over O_X is used. -/
theorem canonicalModuleBaseChange_isIso_affine_of_isFlatOver
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {A B : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec A)
    [QuasiCompact f] [IsSeparated f] (g : Spec B ⟶ Spec A)
    [(Scheme.Modules.tensorPullback (pullback.fst f g)).Additive]
    (G : X.Modules) [SheafOfModules.IsQuasicoherent.{u} G]
    (hflat : Scheme.Modules.IsFlatOver G f)
    (c : (derivedPullback (pullback.fst f g)).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G) ⟶
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings (pullback f g).toRingedSpace)) 0).obj
            ((Scheme.Modules.tensorPullback (pullback.fst f g)).obj G))
    (hc : IsDerivedModulePullbackComparison (pullback.fst f g) G c) :
    IsIso (schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
        pullback.condition ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G) ≫
      (schemeDerivedDirectImage (pullback.snd f g)).map c) := by
  classical
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let cover := X.affineCover.finiteSubcover
  let r := Fintype.card cover.I₀
  let index : Fin r ≃ cover.I₀ := (Fintype.equivFin cover.I₀).symm
  let U : Fin r → X.Opens := fun i ↦ (cover.f (index i)).opensRange
  have hU : iSup U = ⊤ := by
    simpa [U] using (index.iSup_comp (g := fun i ↦ (cover.f i).opensRange)).trans
      cover.iSup_opensRange
  have haffine : ∀ i, IsAffineOpen (U i) := fun i ↦
    isAffineOpen_opensRange (cover.f (index i))
  let K := affineAlternatingCechModel f U G
  have hbounded := affineAlternatingCechModel_bounded f U G
  have hterms := affineAlternatingCechModel_flat f U haffine G hflat
  obtain ⟨F, hF, hFmap, hFadd, ε, hε, e, t, hfactor⟩ :=
    affineAlternatingCech_baseChange_factorization f g U hU haffine G c hc
  have hFeq : F = Scheme.Modules.tensorPullback g :=
    CategoryTheory.Functor.ext hF (fun M N a ↦ hFmap a)
  subst F
  obtain ⟨F₀, hF₀, hF₀map, hF₀add, ε₀, hε₀, e₀, he₀⟩ :=
    flatComplexDerivedPullback g K hbounded hterms
  have hF₀eq : F₀ = Scheme.Modules.tensorPullback g :=
    CategoryTheory.Functor.ext hF₀ (fun M N a ↦ hF₀map a)
  subst F₀
  let W := HomotopyCategory.quasiIso
    (SheafOfModules.{u} (moduleRings (Spec A).toRingedSpace)) (ComplexShape.up ℤ)
  let H := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K
  have := hε
  have := hε₀
  let α := (derivedPullback g).leftDerivedLift ε₀ W (derivedPullback g) ε
  have : IsIso α :=
    ((derivedPullback g).isLeftDerivedFunctor_iff_isIso_leftDerivedLift
      ε₀ W (derivedPullback g) ε).mp hε
  have : IsIso (ε₀.app H) := by
    rw [← he₀]
    infer_instance
  have hfac : α.app (DerivedCategory.Qh.obj H) ≫ ε₀.app H = ε.app H :=
    (derivedPullback g).leftDerived_fac_app ε₀ W (derivedPullback g) ε H
  have : IsIso (ε.app H) := by
    rw [← hfac]
    infer_instance
  rw [hfactor]
  infer_instance

end AlgebraicGeometry
