/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Affine.Linear.AffineLinearTraceAction
import WeilConjectures.AlgebraicGeometry.Affine.Linear.AffineLinearActionFamily
import WeilConjectures.AlgebraicGeometry.Affine.Linear.AffineLinearActionRigidity

/-! # Linear changes of coordinates preserve the affine-space counit trace

Source: blueprint sec-smooth-purity/sk-prop-an/lem-amb-linear-trace-invariance.md,
proof paragraphs 1 and 2 (blueprint: proposition-purity-vector-bundles).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

/-- Every invertible linear coordinate change preserves the actual coordinate-tower
counit trace. The existential square is the Cartesian-square certificate for the concrete
polynomial map v ↦ gv; it is not an extra hypothesis on g or a choice of action.
Source: blueprint linear-trace lemma, statement and both proof paragraphs
(blueprint: proposition-purity-vector-bundles).

Proof, following the node's seven steps:
1. Construct G = D(det) in affine matrix space. Its coordinate ring on Spec R is
   R[x_ij,z]/(z det(x)-1), finite type over R, hence G is Noetherian. The universal
   invertible matrix gives a; the inverse is z adj(x). The given g and the identity
   define sections s_g and e. The coordinate formulas give the Cartesian square below.
2. Compactify the affine-space projections by the standard open in projective space;
   these maps are separated and finite type, with quasi-compact open and proper factors.
   Apply proposition-composition-base-change-rf-shriek to the universal automorphism square and base
   changes. Use lem-asd-etale-finite-twist-pullback for theta_a. Exchange pasting gives
   C_u u* rho_a = rho_(a_T) C_u; at the identity both factors are identities.
3. Conjugate rho_a by the specified trace isomorphism of lemma-integral-linear-character--1.
   Degree-zero full faithfulness identifies the resulting endomorphism of A_G with an
   ordinary module-sheaf map. Its value b on 1 determines it by linearity. The constant
   sheaf section lemmas identify b with a Zariski-locally-constant function beta on G.
   The trace base-change equation identifies its pullback with the corresponding scalar.
4. Each residue-field fibre of G is nonempty and connected: its ring is a polynomial
   domain localized at the nonzero determinant, whose value at the identity is 1.
   Its zero prime lies in every nonempty basic open. This includes dimension zero.
5. On each such fibre beta equals 1 at the identity by Step 2. A locally constant map
   on a connected space is constant (lem-weil-pbc-connected-locally-constant-map).
6. Every point of G lifts to its residue-field fibre. Thus beta is everywhere 1, hence
   b = 1 by the constant-sheaf section identification. Degree-zero faithfulness gives
   t_G rho_a = t_G as an actual derived equality. The empty base causes no exception.
7. Pull back along s_g and use exchange pasting and trace base change. Cancel C_(s_g)
   to obtain t_S rho_g = t_S. In dimension zero this is the identity-adjunction equation.
-/
theorem affineSpaceLinearTraceInvariance (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin d) Γ(S, ⊤)) :
    ∃ sq : IsPullback (affineTraceLinearMap S d g) (affineTraceProjection S d)
        (affineTraceProjection S d) (𝟙 S),
      affineLinearTraceAction N hN A hA t S hS d (affineTraceLinearMap S d g) sq ≫
        affineTraceCounit A N hA t D S hS d = affineTraceCounit A N hA t D S hS d  := by
  let sq := affineTraceLinearMap_isPullback S d g
  refine ⟨sq, ?_⟩
  have hcomp := affineLinearAction_family N hN A hA t S hS d
  let r := linearActionMatrix N hN A hA t (generalLinearOpen d S).toScheme
    (linearUniversalInvertible N S hS d) d (linearUniversalMatrix S d)
  have hid : (ordinaryFinitePullback A (glOne (c := d) (S := S))).map r = 𝟙 _ := by
    obtain ⟨C, hC⟩ := hcomp 1
    change (ordinaryFinitePullback A (glOne (c := d) (S := S))).map r ≫ C.hom = _ at hC
    rw [affineLinearAction_one, Category.comp_id] at hC
    apply (cancel_mono C.hom).mp
    simpa only [Category.id_comp] using hC
  have hr : r = 𝟙 _ :=
    linearAction_eq_id_of_identitySection N hN A hA S hS d r hid
  obtain ⟨C, hC⟩ := hcomp g
  change (ordinaryFinitePullback A _).map r ≫ C.hom = _ at hC
  rw [hr, CategoryTheory.Functor.map_id, Category.id_comp] at hC
  have hg : linearActionMatrix N hN A hA t S hS d g = 𝟙 _ := by
    apply (cancel_epi C.hom).mp
    simpa only [Category.comp_id] using hC.symm
  change linearActionMatrix N hN A hA t S hS d g ≫ _ = _
  rw [hg, Category.id_comp]

end AlgebraicGeometry.Etale
