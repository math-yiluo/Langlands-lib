/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FiniteAffineCechModel
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.AlgebraicGeometry.AdditiveAlternatingCechCoordinates
import WeilConjectures.AlgebraicGeometry.FiniteAffineCechCoefficientBaseChange

/-! # Local section formulas for the pulled-back finite affine Čech model

Source: Stacks Project, Tag 02KE, the affine termwise base-change calculation.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules

/-- The pulled-back specified model has the ordered section formulas, naturally on all
opens and linearly over their local rings. This is a termwise statement, before homology.
Source: Stacks Project, Tag 02KE, affine Čech terms and arbitrary base change.
(blueprint: lem-pc-finite-affine-cech-base-change-coordinates).

Proof: Separatedness makes every nonempty finite intersection of the V_i affine over U.
For each such intersection Z, the cartesian square identifies its new inverse image
with Z times_U T'. Its morphism to T' is affine by affine base change. On any affine
open B of T', its inverse image is affine. The affine pullback section formula identifies
its coefficient sections with Gamma(B,O) tensor over Gamma(U,O) Gamma(Z,F).
Restricting scalars by GammaSpecIso and pulling back along the affine chart in the
specified model gives precisely this same module and its pure-tensor formula.
Tensor commutes with the finite product over increasing tuples, including empty products.
The coordinate map sends a pure tensor b tensor s to b times the pullback of s,
restricted to the new intersection over B. This gives a bijective coordinate map on B.
Its pure-tensor formula commutes with every
face restriction and restriction of B, and respects all scalars in Gamma(B,O).
The affine-open maps therefore glue, together with their inverses, to isomorphisms of
module sheaves, giving additive equivalences on every open B, not just affine opens.
Naturality and local linearity hold after gluing. Commutation with the signed face sums
is checked on the affine basis using naturality of the affine pullback formula.
Extension from natural degrees and its extendXIso identify the nonnegative terms and
differentials of the specified integer complex. Empty intersections and r = 0 give
zero coefficient modules and empty products, so the same formulas apply. No flatness,
covering, usual Čech complex, or tensor-homology interchange enters this statement. -/
theorem finiteAffineCech_baseChange_coordinates {X T : Scheme.{u}} (f : X ⟶ T)
    [IsSeparated f] (F : X.Modules) [F.IsQuasicoherent]
    (U : T.Opens) (hU : IsAffineOpen U) {r : ℕ}
    (V : Fin r → (f ⁻¹ᵁ U).toScheme.Opens) (hV : ∀ i, IsAffineOpen (V i))
    {T' X' : Scheme.{u}} (g : T' ⟶ U.toScheme) (g' : X' ⟶ X) (f' : X' ⟶ T')
    (sq : IsPullback g' f' f (g ≫ U.ι))
    (W₀ : ULift.{u} (Fin r) → X'.Opens)
    (hW : ∀ i, W₀ i = g' ⁻¹ᵁ ((f ⁻¹ᵁ U).ι ''ᵁ V i.down)) :
    let K := ((Modules.pullback g).mapHomologicalComplex _).obj
      (finiteAffineCechModel (f ∣_ U) (F.restrict (f ⁻¹ᵁ U).ι) V)
    let M := (Modules.pullback g').obj F
    ∃ a : ∀ (p : ℕ) (B : T'.Opens),
      Γ(K.X (p : ℤ), B) ≃+
        (∀ t : Fin (p + 1) ↪o Fin r,
          Γ(M, alternatingCechIntersection (fun i ↦ W₀ ⟨i⟩) t ⊓ f' ⁻¹ᵁ B)),
      (∀ (p : ℕ) {B C : T'.Opens} (i : B ⟶ C)
        (s : Γ(K.X (p : ℤ), C)) (t : Fin (p + 1) ↪o Fin r),
      a p B ((K.X (p : ℤ)).presheaf.map i.op s) t =
        M.presheaf.map (homOfLE (inf_le_inf le_rfl
          ((TopologicalSpace.Opens.map f'.base).map i).le)).op (a p C s t)) ∧
      (∀ (p : ℕ) (B : T'.Opens) (b : Γ(T', B))
        (s : Γ(K.X (p : ℤ), B)) (t : Fin (p + 1) ↪o Fin r),
      a p B (b • s) t =
        X'.presheaf.map (homOfLE (show
          alternatingCechIntersection (fun i ↦ W₀ ⟨i⟩) t ⊓ f' ⁻¹ᵁ B ≤ f' ⁻¹ᵁ B
            from inf_le_right)).op (f'.app B b) • a p B s t) ∧
      (∀ (p : ℕ) (B : T'.Opens) (s : Γ(K.X (p : ℤ), B))
        (t : Fin (p + 2) ↪o Fin r),
      a (p + 1) B ((K.d (p : ℤ) ((p + 1 : ℕ) : ℤ)).app B s) t =
        ∑ j : Fin (p + 2), (-1 : ℤ) ^ j.val •
          M.presheaf.map (homOfLE (inf_le_inf
            (alternatingCechIntersection_face_le (fun i ↦ W₀ ⟨i⟩) p t j) le_rfl)).op
              (a p B s ((Fin.succAboveOrderEmb j).trans t))) := by
  classical
  let G := (F.restrict (f ⁻¹ᵁ U).ι).presheafModuleCat
  let H := ModuleCat.restrictScalars
    (((Scheme.ΓSpecIso Γ(U.toScheme, ⊤)).inv ≫
      ((f ∣_ U) ≫ U.toScheme.toSpecΓ).appTop).hom) ⋙
    tilde.functor Γ(U.toScheme, ⊤) ⋙
    Modules.pullback U.toScheme.toSpecΓ ⋙ Modules.pullback g
  let L := (H.mapHomologicalComplex _).obj
    ((alternatingCechComplex V G).extend ComplexShape.embeddingUpNat)
  obtain ⟨e, en, el, ed⟩ := additive_alternatingCech_coordinates V G H
  obtain ⟨c, cn, cl, cf⟩ :=
    finiteAffineCech_coefficient_baseChange f F U hU V hV g g' f' sq W₀ hW
  refine ⟨fun p B ↦ (e p B).trans (AddEquiv.piCongrRight fun t ↦ c p t B), ?_, ?_, ?_⟩
  · intro p B C i s t
    change c p t B (e p B ((L.X (p : ℤ)).presheaf.map i.op s) t) = _
    exact (congrArg (c p t B) (en p i s t)).trans (cn p t i _)
  · intro p B b s t
    change c p t B (e p B (b • s) t) = _
    exact (congrArg (c p t B) (el p B b s t)).trans (cl p t B b _)
  · intro p B s t
    change c (p + 1) t B (e (p + 1) B ((L.d (p : ℤ) ((p + 1 : ℕ) : ℤ)).app B s) t) = _
    refine (congrArg (c (p + 1) t B) (ed p B s t)).trans ?_
    refine (map_sum (c (p + 1) t B) _ _).trans ?_
    apply Finset.sum_congr rfl
    intro j _
    exact (map_zsmul (c (p + 1) t B) _ _).trans
      (congrArg (fun x ↦ (-1 : ℤ) ^ j.val • x) (cf p t j B _))


end AlgebraicGeometry.Scheme.Modules
