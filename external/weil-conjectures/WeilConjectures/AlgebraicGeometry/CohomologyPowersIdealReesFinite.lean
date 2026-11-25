/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.ReesAlgebra
public import Mathlib.Algebra.DirectSum.Basic
public import WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.AlgebraicGeometry.Coherent
import WeilConjectures.AlgebraicGeometry.IdealPowersReesGradedData
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyScalarEndomorphism
import WeilConjectures.AlgebraicGeometry.GradedFinitenessCohomology

/-! # Finiteness of cohomology of ideal powers over the Rees algebra

Source: Stacks Project, Cohomology of Schemes, Lemma 02O8, and its preceding paragraph
(blueprint: lem-weil-pbc-cohomology-powers-ideal-rees-finite).

The sheaves `I^n F` are the shared `Scheme.idealModuleProduct (Scheme.idealSheafPower
J.toModulesι n).2 F` (at `n = 0` the power is `O_X` with identity inclusion, so the product
is canonically `F`), and `H^q(X, -)` is an `A`-module by restriction of scalars along
`A ≅ Γ(Spec A, O) → Γ(X, O_X)`, as in the existing statements.
-/

@[expose] public section

universe v

open CategoryTheory Opposite DirectSum

namespace AlgebraicGeometry

open Classical in
/-- For a proper scheme over a Noetherian affine base and a coherent module, the
cohomology of its ideal powers is finite over the Rees algebra. `J` is the extended ideal
`I O_X`. The multiplication maps are specified on every open after the inclusions into `F`.
The double finite sum is the convolution formula: its degree `n` consists exactly of terms
with `k + m = n`.

Source: Stacks Project, Lemma 02O8 and the preceding paragraph
(blueprint: lem-weil-pbc-cohomology-powers-ideal-rees-finite).

Proof:
1. The base is Noetherian and proper implies finite type, so X is Noetherian. Coherence
implies quasi-coherence (pqf-lem-coherent-ft-locnoeth). Extend I by comap; on affine opens
its powers times F have sections f^sharp(I^n) F(U), by
lem-weil-pbc-module-pullback-ideal-quotient and
lem-weil-pbc-ideal-times-quasi-coherent-affine-sections. Multiplication by a in I^k
therefore carries the mth image into the (m+k)th image. This holds on arbitrary opens by
checking on an affine cover. The resulting lambda maps are additive in a, compose by
multiplication of coefficients, and in degree zero are scalar multiplication.
2. The Rees algebra has degree k piece I^k t^k and degree zero A
(definition-admissible-blow-up--1, lemma-nagata-rees-degree-zero). Noetherianity makes I finitely
generated, hence its Rees algebra finite type over A (definition-admissible-blow-up--1).
3. Regard the family I^m F with these maps as a graded module sheaf. Local generators of
F in degree zero generate all degrees: on affine opens write a section as a sum a_j u_j
and locally express each u_j in the chosen generators. Thus the graded sheaf is finite
type, and the maps satisfy all the conditions of lem-weil-pbc-graded-finiteness-cohomology.
4. Apply that lemma (Stacks 0897 (1)): the direct sum of cohomology is a finite Rees
module with the asserted convolution action. For degree zero the induced cohomology map
is the A-scalar action, by the convention defining the A-module structure.
-/
theorem cohomology_powers_ideal_rees_finite {A : Type v} [CommRing A]
    [IsNoetherianRing A] {X : Scheme.{v}} (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (I : Ideal A) (J : X.IdealSheafData)
    (hJ : J = (Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f)
    (F : X.Modules) (hF : RingedSpace.IsCoherent X.toRingedSpace F) (q : ℕ) :
    ∃ lam : ∀ (k m : ℕ) (a : A) (_ha : a ∈ I ^ k),
        Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι m).2 F ⟶
          Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι (m + k)).2 F,
      (∀ (k m : ℕ) (a : A) (ha : a ∈ I ^ k) (U : X.Opens)
        (s : (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι m).2 F).val.obj
          (op U)),
        ((Scheme.idealModuleProductι (Scheme.idealSheafPower J.toModulesι (m + k)).2 F).app
            U).hom ((lam k m a ha).app U s) =
          (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appLE ⊤ U le_top).hom a) •
            ((Scheme.idealModuleProductι (Scheme.idealSheafPower J.toModulesι m).2 F).app
              U).hom s) ∧
      (∀ (m : ℕ) (a : A) (ha : a ∈ I ^ 0)
        (x : (ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).obj
            ((RingedSpace.moduleCohomology X.toRingedSpace q).obj
              (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι m).2 F))),
        ((RingedSpace.moduleCohomology X.toRingedSpace q).map (lam 0 m a ha)).hom x =
          a • x) ∧
      ∃ mod : Module (reesAlgebra I) (⨁ n : ℕ, (ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).obj
            ((RingedSpace.moduleCohomology X.toRingedSpace q).obj
              (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι n).2 F))),
        @Module.Finite (reesAlgebra I) (⨁ n : ℕ, (ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).obj
            ((RingedSpace.moduleCohomology X.toRingedSpace q).obj
              (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι n).2 F))) _ _
          mod ∧
        ∀ (b : reesAlgebra I) (x : ⨁ n : ℕ, (ModuleCat.restrictScalars
            ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).obj
              ((RingedSpace.moduleCohomology X.toRingedSpace q).obj
                (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι n).2 F))),
          @SMul.smul _ _ mod.toSMul b x =
            ∑ k ∈ b.val.support, ∑ m ∈ x.support,
              DirectSum.of (fun n : ℕ ↦ (ModuleCat.restrictScalars
                  ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).obj
                    ((RingedSpace.moduleCohomology X.toRingedSpace q).obj
                      (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι n).2 F)))
                (m + k)
                (((RingedSpace.moduleCohomology X.toRingedSpace q).map
                  (lam k m (b.val.coeff k) (b.property k))).hom (x m)) := by
  classical
  let G := fun m ↦ Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι m).2 F
  obtain ⟨mu, hsection, hG, hadd, hmul, hscalar, hgen⟩ :=
    idealPowersReesGradedData f I J hJ F hF
  let lam := fun (k m : ℕ) (a : A) (ha : a ∈ I ^ k) ↦
    mu m k ⟨reesMonomial I a ha, reesMonomial_mem I a ha⟩
  refine ⟨lam, ?_, ?_, ?_⟩
  · intro k m a ha U s
    simpa [lam, reesMonomial] using
      hsection m k ⟨reesMonomial I a ha, reesMonomial_mem I a ha⟩ U s
  · intro m a ha x
    have hb : (⟨reesMonomial I a ha, reesMonomial_mem I a ha⟩ : reesGrading I 0) =
        ⟨algebraMap A (reesAlgebra I) a, algebraMap_mem_reesGrading_zero I a⟩ := by
      apply Subtype.ext
      apply Subtype.ext
      simp [reesMonomial]
    have hs : ∀ (U : X.Opens) (t : (G m).val.obj (op U)),
        (lam 0 m a ha).val.app (op U) t =
          (X.presheaf.map (homOfLE (le_top (a := U))).op).hom
            (((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom a) • t := by
      intro U t
      dsimp [lam]
      rw [hb]
      exact eq_of_heq (hscalar m a U t)
    exact moduleCohomology_scalar_endomorphism (G m) (lam 0 m a ha) _ hs q x
  · obtain ⟨mod, hfin, hact⟩ := gradedFinitenessCohomology (reesGrading I)
      (reesGrading_isInternal I) (SetLike.one_mem_graded (reesGrading I))
      (fun _ _ _ _ hx hy ↦ SetLike.mul_mem_graded hx hy)
      (algebraMap_mem_reesGrading_zero I) f G hG mu hadd hmul hscalar hgen q
    refine ⟨mod, hfin, ?_⟩
    intro b x
    let M := fun n ↦ ((RingedSpace.moduleCohomology X.toRingedSpace q).obj (G n) : Type v)
    let : Module (reesAlgebra I) (⨁ n : ℕ, M n) := mod
    have hb : b = ∑ k ∈ b.val.support,
        reesMonomial I (b.val.coeff k) (b.property k) := by
      apply Subtype.ext
      simp only [AddSubmonoidClass.coe_finsetSum, coe_reesMonomial]
      exact b.val.as_sum_support
    let x' : ⨁ n : ℕ, M n := x
    change b • x' = _
    conv_lhs => rw [hb, ← DirectSum.sum_support_of x']
    rw [Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    exact hact k m
      ⟨reesMonomial I (b.val.coeff k) (b.property k), reesMonomial_mem I _ _⟩ (x m)

end AlgebraicGeometry
