/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Finiteness.Defs
public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.PQFCohomology
import WeilConjectures.AlgebraicGeometry.GradedCohomologyModuleStructure
import WeilConjectures.AlgebraicGeometry.GradedCohomologyModuleFinite

/-!
# Cohomology of a finite type graded module

Source: Stacks Project, Cohomology of Schemes, Lemma 0897
(blueprint: lem-weil-pbc-graded-finiteness-cohomology).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace AlgebraicGeometry

/-- Cohomology of a finite type graded module over `f ^* B~` is finite over `B`.

Source: Stacks Project, Cohomology of Schemes, Lemma 0897(1), with the graded
module action written through the homogeneous maps
(blueprint: lem-weil-pbc-graded-finiteness-cohomology).

Proof:
1. Put X'=X\times_{\operatorname{Spec}A}\operatorname{Spec}B, with projections \pi:X'\to X and
f':X'\to\operatorname{Spec}B. Since f is proper, f' is proper by base change [lem-weil-pbc-proper-
fp-permanence](b). Since B is finite type over the Noetherian ring A, it is Noetherian [lem-weil-
pbc-finite-type-algebra-noetherian]. Thus \operatorname{Spec}B is Noetherian, and the proper map
f' is of finite type [def-weil-proper-morphism], so X' is Noetherian [lem-weil-pbc-finite-type-
over-noetherian]. In particular X and X' are quasi-compact and quasi-separated. Dependencies: lem-
weil-pbc-proper-fp-permanence, lem-weil-pbc-finite-type-algebra-noetherian, def-weil-proper-
morphism, lem-weil-pbc-finite-type-over-noetherian.

2. Write \mathcal B=f^*\widetilde B and \mathcal G=\bigoplus_{m\ge0}\mathcal G_m, with
multiplication by a homogeneous b\in B_k given by \mu_b^{(m)}. Conditions (i) and (ii) make this
an action of the graded algebra B; (iii) identifies its degree-zero A-action with the \mathcal
O_X-module action through f^\sharp. On an affine open U=\operatorname{Spec}C\subseteq X, quasi-
coherence gives \mathcal G_m|_U=\widetilde{G_m} for G_m=\mathcal G_m(U) [pqf-def-coherent].
Localization commutes with direct sums, so \mathcal G|_U=\widetilde{\bigoplus_mG_m}; the same
calculation identifies \mathcal B|_U with the tilde of B\otimes_AC. The action maps localize,
hence \mathcal G is quasi-coherent as a \mathcal B-module. The local homogeneous generators s_i in
(iv) give a surjection \mathcal B|_U^{\oplus r}\to\mathcal G|_U: every section in a homogeneous
summand is locally a sum of the stipulated b_{ij}s_i, and every section of \mathcal G is locally a
finite sum of homogeneous sections. Thus \mathcal G has finite type over \mathcal B. Dependencies:
pqf-def-coherent, def-weil-pbc-finite-type-algebra, situation-conventions.

3. The base-change description of relative spectrum [lem-weil-pbc-relative-spec-base-change](2),
applied to \widetilde B on \operatorname{Spec}A, identifies X' over X with
\underline{\operatorname{Spec}}_X(\mathcal B). Therefore \pi is affine and \pi_*\mathcal
O_{X'}\cong\mathcal B [lem-weil-pbc-affine-morphism-relative-spec](2). By the affine module
correspondence [lem-weil-pbc-affine-module-correspondence](2), the quasi-coherent \mathcal
B-module \mathcal G uniquely corresponds to a quasi-coherent \mathcal O_{X'}-module \mathcal G'
with \pi_*\mathcal G'\cong\mathcal G as \mathcal B-modules. Its finite-type property follows from
[lem-weil-pbc-affine-module-finite-type], applied to the generators of step 2. Since X' is locally
Noetherian by step 1, finite type and quasi-coherent imply \mathcal G' coherent [pqf-lem-coherent-
ft-locnoeth]. Dependencies: lem-weil-pbc-relative-spec-base-change, lem-weil-pbc-affine-morphism-
relative-spec, lem-weil-pbc-affine-module-correspondence, lem-weil-pbc-affine-module-finite-type,
pqf-lem-coherent-ft-locnoeth.

4. Because f' is proper over the affine Noetherian base \operatorname{Spec}B and \mathcal G' is
coherent, [lem-pc-coherent-hi] (its 02O6 clause) makes H^p(X',\mathcal G') a finite B-module.
Since \pi is affine and \mathcal G' quasi-coherent, [lem-weil-pbc-affine-morphism-cohomology-edge]
gives the canonical isomorphism H^p(X,\pi_*\mathcal G')\cong H^p(X',\mathcal G'). This is
B-linear: multiplication by b\in B on \mathcal G' pushes forward to multiplication by the
corresponding section of \mathcal B on \mathcal G, and the edge map is induced by the identity
\pi-map, so its naturality with respect to this endomorphism identifies the two actions [def-weil-
pbc-module-cohomology-fmap]. Thus H^p(X,\mathcal G) is finite over B. Dependencies: lem-pc-
coherent-hi, lem-weil-pbc-affine-morphism-cohomology-edge, def-weil-pbc-module-cohomology-fmap.

5. The proper scheme X is quasi-compact and quasi-separated, so [lem-weil-pbc-qcqs-cohomology-
direct-sum] applied to the family (\mathcal G_m)_{m\ge0} identifies H^p(X,\mathcal G) with
\bigoplus_mH^p(X,\mathcal G_m)=M. Under this isomorphism the endomorphism of \mathcal G induced by
homogeneous b\in B_k has degree-m component \mu_b^{(m)}, so functoriality of cohomology [pqf-def-
cohomology] makes its action on M_m exactly H^p(X,\mu_b^{(m)}). Finite sums of homogeneous
elements and of homogeneous cohomology classes give the displayed convolution formula; conditions
(i)-(iii) ensure the unit, additivity, and associativity. Thus the isomorphism is B-linear, and
finite generation of H^p(X,\mathcal G) from step 4 transfers to M. Dependencies: lem-weil-pbc-
qcqs-cohomology-direct-sum, pqf-def-cohomology, def-weil-finitely-generated-module.
-/
theorem gradedFinitenessCohomology
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
    (p : ℕ) :
    ∃ mod : Module B (DirectSum ℕ (fun m => ((RingedSpace.moduleCohomology
      X.toRingedSpace p).obj (G m) : Type u))),
      @Module.Finite B _ _ _ mod ∧
      ∀ (k m : ℕ) (b : graded k)
        (x : (RingedSpace.moduleCohomology X.toRingedSpace p).obj (G m)),
        @SMul.smul B _ mod.toDistribMulAction.toMulAction.toSemigroupAction.toSMul b.val
          (DirectSum.of (fun n => ((RingedSpace.moduleCohomology
            X.toRingedSpace p).obj (G n) : Type u)) m x) =
        DirectSum.of (fun n => ((RingedSpace.moduleCohomology
          X.toRingedSpace p).obj (G n) : Type u)) (m + k)
          ((RingedSpace.moduleCohomology X.toRingedSpace p).map (mu m k b) x) := by
  obtain ⟨mod, hact⟩ := gradedCohomologyModuleStructure
    graded hgrading hunit hmul hscalar f G mu hmu_add hmu_mul hmu_scalar p
  exact ⟨mod, gradedCohomologyModuleFinite
    graded hgrading hunit hmul hscalar f G hG mu hmu_add hmu_mul hmu_scalar hfinite p
    mod hact, hact⟩

end AlgebraicGeometry
