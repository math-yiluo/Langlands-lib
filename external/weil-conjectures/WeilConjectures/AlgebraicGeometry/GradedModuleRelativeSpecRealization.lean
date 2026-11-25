/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.RingTheory.FiniteType
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
import WeilConjectures.AlgebraicGeometry.GradedModuleQuasicoherentRealization
import WeilConjectures.AlgebraicGeometry.GradedModuleRealizationFiniteType
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.CoherentAffineSectionsFinite
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-! # Relative-spectrum realization of a finite-type graded module

Source: Stacks Project, Cohomology of Schemes, Tag 0897(1).
(blueprint: lem-weil-pbc-graded-module-relative-spec-realization).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace AlgebraicGeometry

private theorem finitePresentation_of_quasicoherent_finiteType
    (Y : Scheme.{u}) [IsLocallyNoetherian Y] (F : Y.Modules)
    (hq : F.IsQuasicoherent) (ht : F.IsFiniteType) : F.IsFinitePresentation := by
  have hc := (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType Y F).mpr
    ⟨hq, ht⟩
  have hfp (U : Y.affineOpens) : (F.over U.1).IsFinitePresentation := by
    have := IsLocallyNoetherian.component_noetherian U
    have := Scheme.Modules.coherent_affine_sections_finite Y F hc U.1 U.2
    have hp := Module.finitePresentation_of_finite Γ(Y, U.1) Γ(F, U.1)
    exact (((Scheme.Modules.quasicoherent_finite_type_affine.{u, u} Y).2 F hq).1 U.1 U.2).2.mpr hp
  exact @SheafOfModules.IsFinitePresentation.of_coversTop _ _ _ _ _ _ _ _ F
    Y.affineOpens (fun U ↦ U.1) (by
      rw [Opens.coversTop_iff]
      exact iSup_affineOpens_eq_top Y) hfp

/-- Realize a finite-type graded module on the base-changed scheme, before taking cohomology.

Source: Stacks Project, Cohomology of Schemes, Tag 0897(1), relative-spectrum proof,
lines 5267--5300; affine module correspondence (01SB) and finite type (01PB).
(blueprint: lem-weil-pbc-graded-module-relative-spec-realization).

Proof: Put Y = X ×_(Spec A) Spec B, pi = pr_X and fB = pr_B. On each affine open
U = Spec C of X, extend the homogeneous mu maps by finite sums to the module
sum_m G_m(U) over C tensor_A B. The internal grading makes this extension unique;
additivity, multiplicativity and the scalar condition give the module laws, including
one acting as identity. Quasi-coherence identifies restrictions with localization,
and localization commutes with direct sums and this action. The modules therefore
glue over the pulled-back algebra sheaf. Relative-spec base change identifies its
relative spectrum with Y. The affine module correspondence constructs the module F
on Y from these local modules and identifies pi_*F, as an O_X-module, with the sheaf
coproduct of the G_m. The coproduct inclusions are the asserted iota maps. On affine
opens multiplication by b in the degree-k piece is precisely mu m k b, so the
asserted square with multiplication by fB^sharp(b) commutes; equality of sheaf maps
is local, so it holds globally. The local homogeneous generators in hfinite generate
this module over the algebra sheaf: each homogeneous section is locally in their
span and each coproduct section is locally a finite sum of homogeneous sections.
The affine finite-type correspondence gives F finite type. It is quasi-coherent by
construction. B is Noetherian by finite type over A, and Y is locally Noetherian by
proper base change and finite type over Spec B. On every affine open of Y the finite
module of sections is finitely presented over the Noetherian coordinate ring.
These finite presentations give F.IsFinitePresentation. No cohomology or finiteness
of cohomology is asserted in this lemma; it also covers zero modules, an empty
scheme and an empty family of generators. -/
theorem gradedModule_relativeSpec_realization
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [Algebra.FiniteType A B]
    (graded : ℕ → Submodule A B)
    (hgrading : DirectSum.IsInternal graded)
    (hunit : (1 : B) ∈ graded 0)
    (hmul : ∀ (k l : ℕ) {x y : B}, x ∈ graded k → y ∈ graded l → x * y ∈ graded (k + l))
    (hscalar : ∀ (a : A), algebraMap A B a ∈ graded 0)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f]
    (G : ℕ → SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (hG : ∀ m : ℕ, (G m).IsQuasicoherent)
    (mu : ∀ (m k : ℕ), graded k → (G m ⟶ G (m + k)))
    (hmu_add : ∀ (m k : ℕ) (b b' : graded k),
      mu m k (b + b') = mu m k b + mu m k b')
    (hmu_mul : ∀ (m k l : ℕ) (b : graded k) (b' : graded l),
      HEq (mu m l b' ≫ mu (m + l) k b)
        (mu m (k + l) ⟨b.val * b'.val, hmul k l b.property b'.property⟩))
    (hmu_scalar : ∀ (m : ℕ) (a : A) (U : X.Opens)
      (t : (G m).val.obj (op U)),
      HEq ((mu m 0 ⟨algebraMap A B a, hscalar a⟩).val.app (op U) t)
        ((X.presheaf.map (homOfLE (le_top (a := U))).op).hom
          (((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom a) • t))
    (hfinite : ∀ x : X, ∃ (U : X.Opens), x ∈ U ∧
      ∃ (r : ℕ) (d : Fin r → ℕ) (s : ∀ i : Fin r, (G (d i)).val.obj (op U)),
        ∀ (m : ℕ) (V : X.Opens) (hVU : V ≤ U) (t : (G m).val.obj (op V))
          (y : X), y ∈ V → ∃ (W : X.Opens) (hWV : W ≤ V), y ∈ W ∧
            (G m).val.map (homOfLE hWV).op t ∈
              Submodule.span ((moduleRings X.toRingedSpace).obj.obj (op W))
                {z | ∃ (i : Fin r), d i ≤ m ∧
                  ∃ b : graded (m - d i),
                    HEq z ((mu (d i) (m - d i) b).val.app (op W)
                      ((G (d i)).val.map (homOfLE (hWV.trans hVU)).op (s i)))})
    :
    let g := Spec.map (CommRingCat.ofHom (algebraMap A B))
    let Y := pullback f g
    let pi : Y ⟶ X := pullback.fst f g
    let fB : Y ⟶ Spec (.of B) := pullback.snd f g
    ∃ (F : Y.Modules), F.IsQuasicoherent ∧ F.IsFinitePresentation ∧
      ∃ (iota : ∀ m : ℕ, G m ⟶ (Scheme.Modules.pushforward pi).obj F),
        Nonempty (IsColimit (Cofan.mk ((Scheme.Modules.pushforward pi).obj F) iota)) ∧
          ∀ (k m : ℕ) (b : graded k),
            mu m k b ≫ iota (m + k) = iota m ≫
              (Scheme.Modules.pushforward pi).map
                (F.smulHom (((Scheme.ΓSpecIso (.of B)).inv ≫ fB.appTop).hom b.val)) := by
  dsimp only
  obtain ⟨F, hF, iota, hcol, hcompat⟩ := gradedModule_quasicoherent_realization
    graded hgrading hunit hmul hscalar f G hG mu hmu_add hmu_mul hmu_scalar
  have ht := gradedModule_realization_isFiniteType graded f G mu hfinite
    F hF iota hcol hcompat
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  have : IsLocallyNoetherian (pullback f
      (Spec.map (CommRingCat.ofHom (algebraMap A B)))) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f _)
  exact ⟨F, hF, finitePresentation_of_quasicoherent_finiteType _ F hF ht,
    iota, hcol, hcompat⟩

end AlgebraicGeometry
