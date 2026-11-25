/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.FiniteFreeComplex


public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.AlgebraicGeometry.PQFCohomology
import WeilConjectures.AlgebraicGeometry.GradedModuleRelativeSpecRealization
import WeilConjectures.AlgebraicGeometry.AffineMorphismCohomologyEdge
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMapFunctorial
import WeilConjectures.AlgebraicGeometry.ModuleCohomologySourceComparison
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyScalarEndomorphism
import WeilConjectures.AlgebraicGeometry.QcqsCohomologyDirectSum
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex

/-!
# Finiteness for a compatible graded cohomology action

Source: Stacks Project, Cohomology of Schemes, Lemma 0897
(blueprint: lem-weil-pbc-graded-cohomology-module-finite).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace AlgebraicGeometry


/-- Transfer proper coherent finiteness from higher direct image sections to the
module-valued right-derived sections, preserving the given base-ring action. -/
private theorem finite_moduleCohomology
    {B : Type u} [CommRing B] [IsNoetherianRing B]
    {Y : Scheme.{u}} (fB : Y ⟶ Spec (CommRingCat.of B)) [IsProper fB]
    (F : Y.Modules) [F.IsQuasicoherent] [F.IsFinitePresentation] (p : ℕ) :
    Module.Finite B ((RingedSpace.moduleCohomology Y.toRingedSpace p ⋙
      ModuleCat.restrictScalars
        ((Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ fB.appTop).hom).obj F) := by
  classical
  have : IsNoetherianRing Γ(Spec (CommRingCat.of B), ⊤) :=
    isNoetherianRing_of_ringEquiv _
      (Scheme.ΓSpecIso (CommRingCat.of B)).commRingCatIsoToRingEquiv.symm
  let : EnoughInjectives Y.Modules :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives Y.toRingedSpace).2
  have := Scheme.Modules.finite_sections_higherDirectImage fB F p
  obtain ⟨b, hb⟩ :=
    Scheme.Modules.exists_bijective_semilinearMap_sections_higherDirectImage_H fB F p
  let R := Γ(Spec (CommRingCat.of B), ⊤)
  let H := (RingedSpace.moduleCohomology Y.toRingedSpace p).obj F
  let : Module R H := Module.compHom H fB.appTop.hom
  obtain ⟨a, ha⟩ := Scheme.Modules.exists_moduleCohomology_source_comparison Y p
  let : Module R (F.H p) := Module.compHom _ fB.appTop.hom
  let aR : H ≃ₗ[R] F.H p :=
    { a F with
      map_smul' := fun r x ↦ by
        have hn := ha F F (F.smulHom (fB.appTop r)) x
        have hm := moduleCohomology_scalar_endomorphism F
          (F.smulHom (fB.appTop r)) (fB.appTop r)
          (fun U t ↦ Scheme.Modules.smulHom_app_apply F (fB.appTop r) U t) p x
        rw [hm] at hn
        exact hn }
  let bR : Γ((Scheme.Modules.higherDirectImage fB p).obj F, ⊤) →ₗ[R] F.H p :=
    { b.toAddMonoidHom with map_smul' := fun r x ↦ b.map_smulₛₗ r x }
  have : Module.Finite R (F.H p) := Module.Finite.of_surjective bR hb.2
  have : Module.Finite R H := Module.Finite.equiv aR.symm
  let C := (RingedSpace.moduleCohomology Y.toRingedSpace p ⋙
    ModuleCat.restrictScalars
      ((Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ fB.appTop).hom).obj F
  let c : C →ₛₗ[(Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom] H :=
    { toFun := fun x ↦ x
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  let : RingHomSurjective (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom :=
    ⟨(Scheme.ΓSpecIso (CommRingCat.of B)).commRingCatIsoToRingEquiv.symm.surjective⟩
  exact (c.finite_iff_of_bijective Function.bijective_id).mpr inferInstance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- Naturality and scalar transport need additional elaboration heartbeats.
/-- The compatible graded cohomology direct sum has a finitely generated top submodule.

Source: Stacks Project, Cohomology of Schemes, Lemma 0897(1), relative-spectrum
proof of finiteness, with the compatible action given as an input.
(blueprint: lem-weil-pbc-graded-cohomology-module-finite-generators).

Proof:
1. Let X' = X times_(Spec A) Spec B, with projection pi to X and f' to Spec B.
Properness is preserved by base change. Since B is finite type over Noetherian A,
B is Noetherian, and the finite-type scheme X' over Spec B is Noetherian. Also X
is quasi-compact and quasi-separated, since it is proper over the affine base.
2. Form the sheaf direct sum F = directSum_m G_m. The homogeneous maps extend by
finite sums to a B-action on F; hmu_add and hmu_mul give additivity and the product
law, and hmu_scalar gives the unit and compatibility with A. On an affine open
Spec C, this is the action of C tensor_A B on directSum_m G_m(Spec C).
Quasi-coherence of each G_m and localization of direct sums show that these
modules glue to a quasi-coherent module over the algebra sheaf f^* B~.
The sections s_i in hfinite generate F over this algebra sheaf locally: their
homogeneous multiples generate each degree by the given span condition, and a
section of a sheaf direct sum is locally a finite sum of homogeneous sections.
The coefficients from O_X are absorbed into f^* B~. Thus F is of finite type.
3. Relative-spec base change identifies X' with Spec_X(f^* B~). The affine module
correspondence realizes F as pi_* F' for a quasi-coherent module F' on X'.
The affine finite-type correspondence makes F' finite type, hence coherent on
the locally Noetherian scheme X'. Proper coherent cohomology finiteness for f'
gives a finite B-module H^p(X', F').
4. The affine cohomology edge isomorphism identifies H^p(X, F) with H^p(X', F').
It intertwines B: for each b, multiplication on F' pushes forward to the
multiplication map on F, and naturality of the edge map gives the commuting
square with these endomorphisms. Since X is qcqs, the canonical direct-sum
cohomology isomorphism identifies directSum_m H^p(X, G_m) with H^p(X, F).
For homogeneous b, its square with the inclusion of G_m has other side mu m k b,
so applying cohomology shows that this isomorphism intertwines exactly the
homogeneous action stated in the hypothesis on mod. Every scalar in B and every
vector are finite sums of homogeneous terms; distributivity therefore makes
the composite isomorphism B-linear for the given mod, not an arbitrary action.
The inverse images of a finite set of B-generators of H^p(X', F') generate the
direct sum, proving Module.Finite for mod.
-/
theorem gradedCohomologyModuleFinite_generators
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
    (p : ℕ)
    :
    ∀ (mod : Module B (DirectSum ℕ (fun m =>
      ((RingedSpace.moduleCohomology X.toRingedSpace p).obj (G m) : Type u)))),
      (∀ (k m : ℕ) (b : graded k)
        (x : (RingedSpace.moduleCohomology X.toRingedSpace p).obj (G m)),
        @SMul.smul B _ mod.toDistribMulAction.toMulAction.toSemigroupAction.toSMul b.val
          (DirectSum.of (fun n => ((RingedSpace.moduleCohomology
            X.toRingedSpace p).obj (G n) : Type u)) m x) =
        DirectSum.of (fun n =>
          ((RingedSpace.moduleCohomology X.toRingedSpace p).obj (G n) : Type u)) (m + k)
          ((RingedSpace.moduleCohomology X.toRingedSpace p).map (mu m k b) x)) →
      (⊤ : Submodule B (DirectSum ℕ (fun m =>
        ((RingedSpace.moduleCohomology X.toRingedSpace p).obj (G m) : Type u)))).FG := by
  classical
  intro mod hcompat
  let : Module B (DirectSum ℕ (fun m ↦
    ((RingedSpace.moduleCohomology X.toRingedSpace p).obj (G m) : Type u))) := mod
  let : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  let g := Spec.map (CommRingCat.ofHom (algebraMap A B))
  let Y := pullback f (Spec.map (CommRingCat.ofHom (algebraMap A B)))
  let pi : Y ⟶ X := pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A B)))
  let fB : Y ⟶ Spec (.of B) :=
    pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A B)))
  have : IsProper fB := inferInstanceAs (IsProper (pullback.snd f g))
  have : IsAffineHom g := isAffineHom_of_isAffine _
  have : IsAffineHom pi := MorphismProperty.pullback_fst f g inferInstance
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  obtain ⟨F, hFqc, hFfp, iota, ⟨hiota⟩, hact⟩ :=
    gradedModule_relativeSpec_realization graded hgrading hunit hmul hscalar f
      G hG mu hmu_add hmu_mul hmu_scalar hfinite
  have : F.IsQuasicoherent := hFqc
  have : F.IsFinitePresentation := hFfp
  let M := fun m ↦ ((RingedSpace.moduleCohomology X.toRingedSpace p).obj (G m) : Type u)
  let S := (Scheme.Modules.pushforward pi).obj F
  let C := (RingedSpace.moduleCohomology Y.toRingedSpace p ⋙
    ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of B)).inv ≫ fB.appTop).hom).obj F
  have : Module.Finite B C := finite_moduleCohomology fB F p
  let D := DirectSum.toModule ((moduleRings X.toRingedSpace).obj.obj (op ⊤)) ℕ
    ((RingedSpace.moduleCohomology X.toRingedSpace p).obj S)
    (fun m ↦ ((RingedSpace.moduleCohomology X.toRingedSpace p).map (iota m)).hom)
  have hD : Function.Bijective D := by
    have h := Scheme.moduleCohomology_directSum_bijective X ℕ G S iota hiota p
    have hd : (fun a b : ℕ ↦ Classical.propDecidable (a = b)) =
        instDecidableEqNat := Subsingleton.elim _ _
    rw [hd] at h
    exact h
  let edge := Scheme.Modules.moduleCohomologyEdgeMap pi F p
  have : IsIso edge := (Scheme.Modules.affine_morphism_cohomology_edge pi F).2 p |>.1
  let phi : DirectSum ℕ M →+ C := edge.hom.comp D.toAddMonoidHom
  have hphi : Function.Bijective phi :=
    (ConcreteCategory.bijective_of_isIso edge).comp hD
  have hphi_of (m : ℕ) (x : M m) :
      phi (DirectSum.of M m x) =
        edge (((RingedSpace.moduleCohomology X.toRingedSpace p).map (iota m)).hom x) := by
    change edge (D (DirectSum.of M m x)) = _
    congr 1
    exact DirectSum.toModule_lof
      (φ := fun m ↦ ((RingedSpace.moduleCohomology X.toRingedSpace p).map (iota m)).hom)
      ((moduleRings X.toRingedSpace).obj.obj (op ⊤)) m x
  have hhomogeneous (k : ℕ) (b : graded k) (x : DirectSum ℕ M) :
      phi (b.val • x) = b.val • phi x := by
    induction x using DirectSum.induction_on with
    | zero => simp
    | of m x =>
      have hc : b.val • DirectSum.of M m x =
          DirectSum.of M (m + k)
            ((RingedSpace.moduleCohomology X.toRingedSpace p).map (mu m k b) x) := by
        convert hcompat k m b x using 1
      rw [hc, hphi_of, hphi_of]
      let r : Γ(Y, ⊤) := ((Scheme.ΓSpecIso (.of B)).inv ≫ fB.appTop).hom b.val
      let tau := F.smulHom r
      have hn (z : (RingedSpace.moduleCohomology X.toRingedSpace p).obj S) :
          edge (((RingedSpace.moduleCohomology X.toRingedSpace p).map
            ((Scheme.Modules.pushforward pi).map tau)).hom z) =
            ((RingedSpace.moduleCohomology Y.toRingedSpace p).map tau).hom (edge z) := by
        have hs := Scheme.Modules.moduleCohomologyFMap_source_naturality pi
          ((Scheme.Modules.pushforward pi).map tau) (𝟙 S) p
        have ht := Scheme.Modules.moduleCohomologyFMap_target_naturality pi tau (𝟙 S) p
        have hst := hs.trans ht.symm
        have hz := ConcreteCategory.congr_hom hst z
        change edge (((RingedSpace.moduleCohomology X.toRingedSpace p).map
          ((Scheme.Modules.pushforward pi).map tau)).hom z) =
            ((RingedSpace.moduleCohomology Y.toRingedSpace p).map tau).hom
              (edge z) at hz
        exact hz
      have hx : ((RingedSpace.moduleCohomology X.toRingedSpace p).map (iota (m + k))).hom
          (((RingedSpace.moduleCohomology X.toRingedSpace p).map (mu m k b)).hom x) =
          ((RingedSpace.moduleCohomology X.toRingedSpace p).map
            ((Scheme.Modules.pushforward pi).map tau)).hom
            (((RingedSpace.moduleCohomology X.toRingedSpace p).map (iota m)).hom x) := by
        change ((RingedSpace.moduleCohomology X.toRingedSpace p).map (mu m k b) ≫
          (RingedSpace.moduleCohomology X.toRingedSpace p).map (iota (m + k))).hom x =
          ((RingedSpace.moduleCohomology X.toRingedSpace p).map (iota m) ≫
            (RingedSpace.moduleCohomology X.toRingedSpace p).map
              ((Scheme.Modules.pushforward pi).map tau)).hom x
        rw [← (RingedSpace.moduleCohomology X.toRingedSpace p).map_comp,
          ← (RingedSpace.moduleCohomology X.toRingedSpace p).map_comp, hact k m b]
      rw [hx, hn]
      exact moduleCohomology_scalar_endomorphism F tau r
        (fun U t ↦ Scheme.Modules.smulHom_app_apply F r U t) p _
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  have hlinear (b : B) (x : DirectSum ℕ M) : phi (b • x) = b • phi x := by
    obtain ⟨v, hv⟩ := hgrading.2 b
    subst b
    induction v using DirectSum.induction_on with
    | zero => simp
    | of k b =>
      simpa only [DirectSum.coeAddMonoidHom_of] using hhomogeneous k b x
    | add v w hv hw => simp only [map_add, add_smul, hv, hw]
  let L : DirectSum ℕ M →ₗ[B] C := { phi with map_smul' := hlinear }
  have : Module.Finite B (DirectSum ℕ M) :=
    Module.Finite.equiv (LinearEquiv.ofBijective L hphi).symm
  exact Module.Finite.fg_top

/-- (blueprint: lem-weil-pbc-graded-cohomology-module-finite) -/
theorem gradedCohomologyModuleFinite
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
    (p : ℕ)
    :
    ∀ (mod : Module B (DirectSum ℕ (fun m => ((RingedSpace.moduleCohomology
      X.toRingedSpace p).obj (G m) : Type u)))),
      (∀ (k m : ℕ) (b : graded k)
        (x : (RingedSpace.moduleCohomology X.toRingedSpace p).obj (G m)),
        @SMul.smul B _ mod.toDistribMulAction.toMulAction.toSemigroupAction.toSMul b.val
          (DirectSum.of (fun n => ((RingedSpace.moduleCohomology
            X.toRingedSpace p).obj (G n) : Type u)) m x) =
        DirectSum.of (fun n => ((RingedSpace.moduleCohomology
          X.toRingedSpace p).obj (G n) : Type u)) (m + k)
          ((RingedSpace.moduleCohomology X.toRingedSpace p).map (mu m k b) x)) →
      @Module.Finite B _ _ _ mod     := by
  intro mod hcompat
  let htop : Module.Finite B (⊤ : Submodule B
      (DirectSum ℕ (fun m => ((RingedSpace.moduleCohomology X.toRingedSpace p).obj
        (G m) : Type u)))) :=
    Module.Finite.iff_fg.mpr (gradedCohomologyModuleFinite_generators
      graded hgrading hunit hmul hscalar f G hG mu hmu_add hmu_mul hmu_scalar hfinite p mod hcompat)
  have hsurj : Function.Surjective (Submodule.subtype (⊤ : Submodule B (DirectSum ℕ (fun m =>
      ((RingedSpace.moduleCohomology X.toRingedSpace p).obj (G m) : Type u)))) ) := by
    intro x
    exact ⟨⟨x, trivial⟩, rfl⟩
  exact Module.Finite.of_surjective (Submodule.subtype (⊤ : Submodule B (DirectSum ℕ (fun m =>
      ((RingedSpace.moduleCohomology X.toRingedSpace p).obj (G m) : Type u)))) ) hsurj
end AlgebraicGeometry
