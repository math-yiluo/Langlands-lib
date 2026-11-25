/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module

import WeilConjectures.AlgebraicGeometry.ChowFiniteCohomologyWitness
import WeilConjectures.AlgebraicGeometry.IntegralIdealComparisonFiltrations
import WeilConjectures.AlgebraicGeometry.Cohomology.LongExact

/-! # Proper cohomology for integral-ideal filtration factors

Source: Stacks Project, Tags 02O5 and 01YH.
(blueprint: lem-pc-e2-integral-ideal-proper-cohomology)
 -/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

private theorem finite_of_exact {R A B C : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module R A] [Module R B] [Module R C]
    (a : A →ₗ[R] B) (b : B →ₗ[R] C)
    (hab : LinearMap.ker b = LinearMap.range a)
    [Module.Finite R A] [Module.Finite R C] : Module.Finite R B := by
  refine ⟨(⊤ : Submodule R B).fg_of_fg_map_of_fg_inf_ker b ?_ ?_⟩
  · exact IsNoetherian.noetherian _
  · rw [top_inf_eq, hab]
    exact Submodule.fg_range a

private theorem finite_cohomology_two_out_of_three {X : Scheme.{u}}
    (R : Type u) [CommRing R] [IsNoetherianRing R] (σ : R →+* Γ(X, ⊤))
    (S : ShortComplex X.Modules) (hS : S.ShortExact) :
    let P (M : X.Modules) : Prop := ∀ q : ℕ,
      letI : Module R (M.H q) := Module.compHom _ σ
      Module.Finite R (M.H q)
    ((P S.X₁ ∧ P S.X₂) → P S.X₃) ∧
    ((P S.X₁ ∧ P S.X₃) → P S.X₂) ∧
    ((P S.X₂ ∧ P S.X₃) → P S.X₁) := by
  let (M : X.Modules) (q : ℕ) : Module R (M.H q) := Module.compHom _ σ
  let a (q : ℕ) : S.X₁.H q →ₗ[R] S.X₂.H q :=
    { H.map S.f q with map_smul' := fun r x ↦ H.map_smul S.f q (σ r) x }
  let b (q : ℕ) : S.X₂.H q →ₗ[R] S.X₃.H q :=
    { H.map S.g q with map_smul' := fun r x ↦ H.map_smul S.g q (σ r) x }
  let d (q : ℕ) : S.X₃.H q →ₗ[R] S.X₁.H (q + 1) :=
    { H.δ hS q with map_smul' := fun r x ↦ H.δ_smul hS q (σ r) x }
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨h₁, h₂⟩ q
    have := h₁ (q + 1)
    have := h₂ q
    apply finite_of_exact (b q) (d q)
    ext x
    exact SetLike.ext_iff.mp (H.ker_δ_eq_range_map_g hS q) x
  · rintro ⟨h₁, h₃⟩ q
    have := h₁ q
    have := h₃ q
    apply finite_of_exact (a q) (b q)
    ext x
    exact SetLike.ext_iff.mp (H.ker_map_g_eq_range_map_f hS q) x
  · rintro ⟨h₂, h₃⟩ q
    cases q with
    | zero =>
      have := h₂ 0
      exact Module.Finite.of_injective (a 0) (H.injective_map_zero_of_shortExact hS)
    | succ q =>
      have := h₂ (q + 1)
      have := h₃ q
      apply finite_of_exact (d q) (a (q + 1))
      ext x
      exact SetLike.ext_iff.mp (H.ker_map_f_eq_range_δ hS q) x

private theorem finite_cohomology_of_isZero {X T : Scheme.{u}} (f : X ⟶ T)
    (M : X.Modules) (hM : IsZero M) (n : ℕ) :
    letI : Module Γ(T, ⊤) (M.H n) := Module.compHom _ f.appTop.hom
    Module.Finite Γ(T, ⊤) (M.H n) := by
  let : Module Γ(T, ⊤) (M.H n) := Module.compHom _ f.appTop.hom
  have hz (x : M.H n) : x = 0 := by
    have h := congrArg (fun φ ↦ H.map φ n x) (hM.eq_of_src (𝟙 M) 0)
    simpa only [H.map_id_apply, H.map_zero_apply] using h
  have : Subsingleton (M.H n) := ⟨fun x y ↦ (hz x).trans (hz y).symm⟩
  infer_instance

private theorem finite_cohomology_of_iso {X T : Scheme.{u}} (f : X ⟶ T)
    {M N : X.Modules} (e : M ≅ N)
    (hM : ∀ n : ℕ,
      letI : Module Γ(T, ⊤) (M.H n) := Module.compHom _ f.appTop.hom
      Module.Finite Γ(T, ⊤) (M.H n)) (n : ℕ) :
    letI : Module Γ(T, ⊤) (N.H n) := Module.compHom _ f.appTop.hom
    Module.Finite Γ(T, ⊤) (N.H n) := by
  let : Module Γ(T, ⊤) (M.H n) := Module.compHom _ f.appTop.hom
  let : Module Γ(T, ⊤) (N.H n) := Module.compHom _ f.appTop.hom
  let eR : M.H n ≃ₗ[Γ(T, ⊤)] N.H n :=
    { H.mapLinearEquiv e n with
      map_smul' := fun a x ↦ (H.mapLinearEquiv e n).map_smul (f.appTop a) x }
  have := hM n
  exact Module.Finite.equiv eR

private theorem finite_cohomology_of_filtration {X T : Scheme.{u}} (f : X ⟶ T)
    [IsNoetherianRing Γ(T, ⊤)] (F : X.Modules)
    (m : ℕ) (c : Fin (m + 1) → Subobject F) (hc : Monotone c)
    (hbot : c 0 = ⊥) (htop : c (Fin.last m) = ⊤)
    (hpieces : ∀ j : Fin m, ∀ n : ℕ,
      letI : Module Γ(T, ⊤)
        ((cokernel (Subobject.ofLE (c j.castSucc) (c j.succ)
          (hc j.castSucc_le_succ))).H n) := Module.compHom _ f.appTop.hom
      Module.Finite Γ(T, ⊤)
        ((cokernel (Subobject.ofLE (c j.castSucc) (c j.succ)
          (hc j.castSucc_le_succ))).H n)) (n : ℕ) :
    letI : Module Γ(T, ⊤) (F.H n) := Module.compHom _ f.appTop.hom
    Module.Finite Γ(T, ⊤) (F.H n) := by
  let P (M : X.Modules) : Prop := ∀ q : ℕ,
    letI : Module Γ(T, ⊤) (M.H q) := Module.compHom _ f.appTop.hom
    Module.Finite Γ(T, ⊤) (M.H q)
  have hp : ∀ j : Fin (m + 1), P (c j : X.Modules) := by
    intro j
    induction j using Fin.induction with
    | zero =>
      exact finite_cohomology_of_isZero f _
        ((Subobject.isoOfEq _ _ hbot ≪≫ Subobject.botCoeIsoZero).isZero_iff.mpr
          (isZero_zero X.Modules))
    | succ j ih =>
      let a := Subobject.ofLE (c j.castSucc) (c j.succ) (hc j.castSucc_le_succ)
      let S := ShortComplex.mk a (cokernel.π a) (cokernel.condition a)
      have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel a }
      exact (finite_cohomology_two_out_of_three Γ(T, ⊤) f.appTop.hom S hS).2.1
        ⟨ih, hpieces j⟩
  exact finite_cohomology_of_iso f
    (Subobject.isoOfEq _ _ htop ≪≫ asIso (⊤ : Subobject F).arrow) (hp _) n

/-- Proper cohomology is finite for a filtration factor supported on an integral
closed subscheme of the source.

Source: Stacks Project, Cohomology of Schemes, proof of Proposition 30.19.1, Tag 02O5,
and Lemmas 30.12.5 and 30.12.6, Tags 01YH and 01YI.
(blueprint: lem-pc-e2-integral-ideal-proper-cohomology)

Proof: First X is Noetherian: the affine Noetherian base is Noetherian, and f is
proper, hence of finite type and quasi-compact. Closed subschemes of X are Noetherian,
so the quasi-coherent ideal specified by IdealSheafData is coherent. Induct on closed
integral supports, simultaneously in every cohomological degree. Smaller-support
coherent modules reduce by the support-preserving filtration of 01YF to integral
ideals on strictly smaller closed subschemes. Finiteness in all degrees has the
two-out-of-three property by the long exact sequence over the Noetherian base ring:
for the left term use the segment starting in degree q - 1 (zero when q = 0), and
for the right term use the segment ending in degree q + 1. For Z closed in X, Chow's
lemma gives a
projective modification pi : Z' -> Z, an isomorphism on a dense open, together with a
closed immersion into projective space over the affine base. Choose a large common twist
L^n that kills positive higher direct images both for pi and for Z' -> T. Projective
cohomology finiteness, proved independently from the projective-space case, makes
G = pi_* L^n coherent with finite cohomology over T. Derived composition and the vanishing
identify its cohomology with that of L^n. Push G into X along the closed immersion; affine
pushforward is exact, so its cohomology remains finite. Its support is all of Z and its
generic stalk is one-dimensional over the residue field. The irreducible-support
argument of 01YH compares any nonzero ideal I on Z with this generic-rank-one module:
clear denominators to embed a nonzero ideal into G, then intersect with I. The cokernels
of these inclusions miss the generic point and have smaller support, so induction and
the long exact sequence give finiteness for i_* I. The zero ideal has zero cohomology.
All scalar actions are induced by f.appTop; all comparisons are linear for this action.
Empty integral schemes are excluded by IsIntegral, and the zero ideal is allowed. -/
theorem finite_H_pushforward_integral_ideal {X T : Scheme.{u}}
    (f : X ⟶ T) [IsProper f] [IsAffine T] [IsNoetherianRing Γ(T, ⊤)]
    (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
    (I : Z.IdealSheafData) (q : ℕ) :
    letI : Module Γ(T, ⊤) (((pushforward i).obj I.toModules).H q) :=
      Module.compHom _ f.appTop.hom
    Module.Finite Γ(T, ⊤) (((pushforward i).obj I.toModules).H q) := by
  classical
  have : IsLocallyNoetherian T := isLocallyNoetherian_of_isOpenImmersion T.isoSpec.hom
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := {}
  let P (M : X.Modules) : Prop := ∀ n : ℕ,
    letI : Module Γ(T, ⊤) (M.H n) := Module.compHom _ f.appTop.hom
    Module.Finite Γ(T, ⊤) (M.H n)
  have hall : ∀ C : TopologicalSpace.Closeds X,
      ∀ (W : Scheme.{u}) (j : W ⟶ X) [IsClosedImmersion j] [IsIntegral W],
        Set.range j.base = (C : Set X) → ∀ J : W.IdealSheafData,
          P ((pushforward j).obj J.toModules) := by
    intro C
    induction C using WellFoundedLT.induction with
    | ind C ih =>
      intro W j _ _ hj J
      obtain ⟨G, hGcoh, hGsupp, hGann, hGrank, hGfinite⟩ :=
        exists_chow_finite_cohomology_witness f W j
      rcases exists_integral_ideal_comparison_filtrations X W j G
          hGcoh hGsupp hGann hGrank J with hzero | hcomp
      · exact finite_cohomology_of_isZero f _ hzero
      · obtain ⟨K, Q₁, Q₂, a, b, hab, hS₁, d, e, hde, hS₂, hfil⟩ := hcomp
        have hQ : ∀ Q : X.Modules, Q = Q₁ ∨ Q = Q₂ → P Q := by
          intro Q hQ
          obtain ⟨m, c, hc, hbot, htop, hpieces⟩ := hfil Q hQ
          apply finite_cohomology_of_filtration f Q m c hc hbot htop
          intro k
          obtain ⟨W', j', hj', hW', J', hlt, ⟨iso⟩⟩ := hpieces k
          have := hj'
          have := hW'
          let C' : TopologicalSpace.Closeds X :=
            ⟨Set.range j'.base, j'.isClosedEmbedding.isClosed_range⟩
          have hlt' : C' < C := by
            change Set.range j'.base ⊂ (C : Set X)
            rwa [← hj]
          exact finite_cohomology_of_iso f iso.symm (ih C' hlt' W' j' rfl J')
        have hK : P K :=
          (finite_cohomology_two_out_of_three Γ(T, ⊤) f.appTop.hom
            (ShortComplex.mk a b hab) hS₁).2.2 ⟨hGfinite, hQ Q₁ (Or.inl rfl)⟩
        exact (finite_cohomology_two_out_of_three Γ(T, ⊤) f.appTop.hom
          (ShortComplex.mk d e hde) hS₂).2.1 ⟨hK, hQ Q₂ (Or.inr rfl)⟩
  exact hall ⟨Set.range i.base, i.isClosedEmbedding.isClosed_range⟩ Z i rfl I q

end AlgebraicGeometry.Scheme.Modules
