/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Noetherian.Defs
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.PQFCohomology
import Mathlib.Algebra.Category.Grp.Zero
import WeilConjectures.AlgebraicGeometry.GradedModuleAffineBaseChange
import WeilConjectures.AlgebraicGeometry.AffineMorphismCohomologyEdge
import WeilConjectures.AlgebraicGeometry.AmplePullback
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.CoherentSerreVanishing
import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula

/-! # Serre vanishing for finite graded modules

Source: Stacks Project, Cohomology of Schemes, Lemma 0897 (2)
(blueprint: lem-weil-pbc-formal-systems-graded-vanishing).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace AlgebraicGeometry

/-- A finite type graded quasi-coherent module over a pulled-back finite type graded
algebra has uniformly vanishing higher cohomology after sufficiently large ample twists.
The graded module `G = ⊕ G m` over `f ^* B~` is written, as in
`gradedFinitenessCohomology` (Lemma 0897 (1)), through its homogeneous pieces and the
homogeneous action maps `mu`; finite type allows generators in arbitrary degrees `d i`.
No equality between the degree-zero algebra and the base ring, and no degree-one
algebra generators, are assumed.
Source: Stacks Project, Cohomology of Schemes, Lemma 0897 (2)
(blueprint: lem-weil-pbc-formal-systems-graded-vanishing).

Proof:
1. Forget the grading. Set X' = Spec(B) ×_Spec(A) X. Its projection pi to X is affine
   by lem-weil-pbc-morphism-affine-schemes-affine and
   lem-weil-pbc-affine-morphism-permanence; its map to Spec(B) is proper by
   lem-weil-pbc-proper-fp-permanence. B and X' are Noetherian by
   lem-weil-pbc-finite-type-algebra-noetherian and lem-weil-pbc-finite-type-over-noetherian.
2. The associated algebra and tensor pullback identify X' with the relative spectrum
   (lem-weil-pbc-affine-morphism-relative-spec). The affine module correspondence
   (lem-weil-pbc-affine-module-correspondence) realizes G as pi_* G'. Local finite
   generation is preserved (lem-weil-pbc-affine-module-finite-type), so G' is coherent
   by pqf-lem-coherent-ft-locnoeth.
3. The pullback L' = pi^* L is ample by lem-weil-pbc-pullback-ample-invertible.
   Apply lem-weil-pbc-coherent-serre-vanishing on X' to obtain one bound d0 for all p > 0.
4. Trivialize L locally. Both pi_*(G' tensor pi^* L^d) and G tensor L^d identify with
   pi_* G'. Changing the local generator by a unit a changes both identifications by
   a^d, so they glue. The same computation identifies (pi^* L)^d with pi^*(L^d).
5. The twisted module upstairs is quasi-coherent since locally it is G'. The affine
   cohomology comparison lem-weil-pbc-affine-morphism-cohomology-edge identifies its
   cohomology with the cohomology downstairs. Step 3 gives the required vanishing. -/
theorem graded_serre_vanishing
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [Algebra.FiniteType A B]
    (graded : ℕ → Submodule A B)
    (hgrading : DirectSum.IsInternal graded)
    (hunit : (1 : B) ∈ graded 0)
    (hmul : ∀ (k l : ℕ) {x y : B}, x ∈ graded k → y ∈ graded l → x * y ∈ graded (k + l))
    (hscalar : ∀ (a : A), algebraMap A B a ∈ graded 0)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f]
    (G : ℕ → X.Modules)
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
    (L : X.Modules) [L.IsInvertible] (hL : Scheme.Modules.IsAmple X L) :
    ∃ d₀ : ℕ, ∀ (p d : ℕ), 0 < p → d₀ ≤ d →
      IsZero ((RingedSpace.moduleCohomology X.toRingedSpace p).obj
        (Scheme.Modules.tensorObj (∐ G) (L.tensorPow d))) := by
  classical
  let b : Spec (.of B) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom (algebraMap A B))
  let Y := pullback f b
  let pi : Y ⟶ X := pullback.fst f b
  let f' : Y ⟶ Spec (.of B) := pullback.snd f b
  have : IsAffineHom b :=
    inferInstanceAs (IsAffineHom (Spec.map (CommRingCat.ofHom (algebraMap A B))))
  have : IsAffineHom pi := by
    change IsAffineHom (pullback.fst f b)
    exact MorphismProperty.pullback_fst _ _ ‹IsAffineHom b›
  have : IsProper f' := inferInstanceAs (IsProper (pullback.snd f b))
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f'
  obtain ⟨F, hFq, hFt, ⟨e⟩⟩ := exists_finiteType_graded_module_affine_baseChange
    graded hgrading hunit hmul hscalar f G hG mu hmu_add hmu_mul hmu_scalar hfinite
  have hF : RingedSpace.IsCoherent Y.toRingedSpace F :=
    (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType Y F).2 ⟨hFq, hFt⟩
  have : F.IsQuasicoherent := hFq
  let L' := (Scheme.Modules.tensorPullback pi).obj L
  have : L'.IsInvertible := (Scheme.Modules.invertible_pullback_tensor pi).1 L |>.2
  have hL' : Scheme.Modules.IsAmple Y L' :=
    Scheme.Modules.isAmple_tensorPullback_of_isAffineHom pi L hL
  obtain ⟨d₀, hd₀⟩ := Scheme.Modules.exists_isZero_moduleCohomology_tensorPow_of_ample
    B f' F hF L' hL'
  refine ⟨d₀, ?_⟩
  intro p d hp hd
  let c := (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction pi)).leftAdjointUniq
    (Scheme.Modules.pullbackPushforwardAdjunction pi)
  have cp (n : ℕ) : Nonempty (L'.tensorPow n ≅
      ((Scheme.Modules.pullback pi).obj L).tensorPow n) := by
    induction n with
    | zero => exact ⟨Iso.refl _⟩
    | succ n ih => exact ⟨MonoidalCategory.tensorIso (c.app L) ih.some⟩
  obtain ⟨q⟩ := Scheme.Modules.nonempty_pullback_tensorPow_iso pi L d
  let t := cp d |>.some
  let twistIso := t ≪≫ q.symm
  obtain ⟨r⟩ := Scheme.Modules.nonempty_pushforward_tensorObj_pullback_iso pi F (L.tensorPow d)
  let s := (Scheme.Modules.pushforward pi).mapIso
      (MonoidalCategory.tensorIso (Iso.refl F) twistIso) ≪≫
    r ≪≫ (MonoidalCategory.tensorIso e (Iso.refl (L.tensorPow d)))
  have hFqd : (Scheme.Modules.tensorObj F (L'.tensorPow d)).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_tensorObj F (L'.tensorPow d)
  have hc := (Scheme.Modules.affine_morphism_cohomology_edge pi
    (Scheme.Modules.tensorObj F (L'.tensorPow d))).2 p |>.1
  have hz := hd₀ p d hp hd
  have hz' := (forget₂ _ AddCommGrpCat.{u}).map_isZero hz
  have hdown := hz'.of_iso
    (asIso (Scheme.Modules.moduleCohomologyEdgeMap pi
      (Scheme.Modules.tensorObj F (L'.tensorPow d)) p))
  have : Subsingleton ((RingedSpace.moduleCohomology X.toRingedSpace p).obj
      ((Scheme.Modules.pushforward pi).obj
        (Scheme.Modules.tensorObj F (L'.tensorPow d)))) :=
    (AddCommGrpCat.isZero_iff_subsingleton).mp hdown
  have hzero := ModuleCat.isZero_of_subsingleton
    ((RingedSpace.moduleCohomology X.toRingedSpace p).obj
      ((Scheme.Modules.pushforward pi).obj
        (Scheme.Modules.tensorObj F (L'.tensorPow d))))
  exact hzero.of_iso ((RingedSpace.moduleCohomology X.toRingedSpace p).mapIso s).symm

end AlgebraicGeometry
