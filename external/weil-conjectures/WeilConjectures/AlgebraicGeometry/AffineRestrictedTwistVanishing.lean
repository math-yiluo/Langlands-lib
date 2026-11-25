/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.Topology.RingedSpaceModuleCohomology

import WeilConjectures.AlgebraicGeometry.AmpleImmersionAffineBase
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.CoherentAffineSectionsFinite
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.AlgebraicGeometry.ClosedImmersionFixedDegreeVanishing
import WeilConjectures.AlgebraicGeometry.CoherentModuleLocalOnOpenCover
import WeilConjectures.AlgebraicGeometry.TensorPowerSectionOpenRestrictionN

/-! # Fixed-degree affine Serre vanishing

Source: Stacks Project, Tag 0B5T (4).
(blueprint: lem-pc-e4-affine-restricted-twist-fixed-degree)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

private theorem exists_isZero_affine_tensorPow_degree
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (F : X.Modules) (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (L : X.Modules) [L.IsInvertible] (hL : IsAmple X L) (q : ℕ) (hq : 0 < q) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      IsZero ((RingedSpace.moduleCohomology X.toRingedSpace q).obj
        (tensorObj F (L.tensorPow n))) := by
  classical
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : F.IsQuasicoherent :=
    ((isCoherent_iff_isQuasicoherent_and_isFiniteType X F).mp hF).1
  have hfp (U : X.affineOpens) : (F.over U.1).IsFinitePresentation := by
    let : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
    let : Module.Finite Γ(X, U.1) Γ(F, U.1) :=
      coherent_affine_sections_finite X F hF U.1 U.2
    exact (((quasicoherent_finite_type_affine.{u, u} X).2 F inferInstance).1 U.1 U.2).2.mpr
      (Module.finitePresentation_of_finite _ _)
  let : F.IsFinitePresentation := SheafOfModules.IsFinitePresentation.of_coversTop F
    (fun U : X.affineOpens ↦ U.1) ((Opens.coversTop_iff X _).mpr
      (TopologicalSpace.IsOpenCover.mk (iSup_affineOpens_eq_top X)))
  obtain ⟨d, hd, N, i, hi, hif, ⟨epos⟩⟩ := hL.exists_immersion_affine_base A X f L
  let : IsImmersion i := hi
  have hcomp : IsProper (i ≫ ℙ(ULift.{u} (Fin (N + 1)); Spec (.of A)) ↘ Spec (.of A)) := by
    rw [hif]
    infer_instance
  let : IsProper i := IsProper.of_comp i
    (ℙ(ULift.{u} (Fin (N + 1)); Spec (.of A)) ↘ Spec (.of A))
  let : IsClosedImmersion i := IsClosedImmersion.of_isPreimmersion i
    (i.isClosedMap.isClosed_range)
  have epos' : ∀ (n : ℕ) (hn : 0 < n),
      Nonempty (SheafOfModules.positiveTensorPower X.sheaf L n hn ≅ L.tensorPow n) := by
    let := SheafOfModules.monoidalCategory X.sheaf
    let := SheafOfModules.symmetricCategory X.sheaf
    intro n
    induction n using Nat.twoStepInduction with
    | zero => intro hn; omega
    | one => intro hn; exact ⟨(MonoidalCategoryStruct.rightUnitor L).symm⟩
    | more n _ ih =>
      intro hn
      obtain ⟨e⟩ := ih (by omega)
      exact ⟨(MonoidalCategory.tensorIso e (Iso.refl L)) ≪≫ BraidedCategory.braiding _ _⟩
  obtain ⟨adj⟩ := nonempty_tensorPullbackAdjunction i
  let epb := (adj.leftAdjointUniq (pullbackPushforwardAdjunction i)).app
    (ProjectiveSpace.twist (ULift.{u} (Fin (N + 1))) (Spec (.of A)) 1)
  let e : L.tensorPow d ≅ ProjectiveSpace.twistRestrict i 1 :=
    (epos' d hd).some.symm ≪≫ epos ≪≫ epb
  have key (r : Fin d) : ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
      IsZero ((RingedSpace.moduleCohomology X.toRingedSpace q).obj
        (tensorObj (tensorObj F (L.tensorPow r)) (ProjectiveSpace.twistRestrict i t))) := by
    have := isQuasicoherent_tensorObj F (L.tensorPow r)
    have := isFinitePresentation_tensorObj F (L.tensorPow r)
    exact exists_isZero_closedImmersion_twist_degree A i
      (tensorObj F (L.tensorPow r)) q hq
  choose t₀ ht₀ using key
  refine ⟨d * ∑ r, t₀ r, ?_⟩
  intro n hn
  let r : Fin d := ⟨n % d, Nat.mod_lt n hd⟩
  let t := n / d
  have hn' : n = r + d * t := (Nat.mod_add_div n d).symm
  have ht : t₀ r ≤ t := by
    refine le_trans (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ r)) ?_
    exact (Nat.le_div_iff_mul_le hd).2 (by rw [mul_comm]; exact hn)
  have hpow : ∀ s : ℕ, Nonempty ((L.tensorPow d).tensorPow s ≅
      (ProjectiveSpace.twistRestrict i 1).tensorPow s) := by
    intro s
    induction s with
    | zero => exact ⟨Iso.refl _⟩
    | succ s ih => exact ⟨MonoidalCategory.tensorIso e ih.some⟩
  obtain ⟨e₁⟩ := nonempty_pullback_tensorPow_iso i
    (ProjectiveSpace.twist (ULift.{u} (Fin (N + 1))) (Spec (.of A)) 1) t
  obtain ⟨e₂⟩ := ProjectiveSpace.nonempty_tensorPow_twist_one_iso
    (ULift.{u} (Fin (N + 1))) (Spec (.of A)) t
  let e₃ : L.tensorPow n ≅ tensorObj (L.tensorPow r) (ProjectiveSpace.twistRestrict i t) :=
    eqToIso (congrArg L.tensorPow hn') ≪≫ L.tensorPowAddIso r (d * t) ≪≫
      (MonoidalCategory.tensorIso (Iso.refl _) (L.tensorPowMulIso d t ≪≫ (hpow t).some ≪≫ e₁.symm ≪≫
        (pullback i).mapIso e₂))
  let e₄ : tensorObj F (L.tensorPow n) ≅
      tensorObj (tensorObj F (L.tensorPow r)) (ProjectiveSpace.twistRestrict i t) :=
    (MonoidalCategory.tensorIso (Iso.refl F) e₃) ≪≫ (MonoidalCategoryStruct.associator _ _ _).symm
  exact (ht₀ r t ht).of_iso
    ((RingedSpace.moduleCohomology X.toRingedSpace q).mapIso e₄)

/-- Fixed-degree Serre vanishing on the inverse image of one affine open.

Source: Stacks Project, Tag 0B5T (4), used in the affine-local proof of Tag 02O1.
(blueprint: lem-pc-e4-affine-restricted-twist-fixed-degree)

Proof: Base change f to V. Properness gives a Noetherian source over the
Noetherian affine base. Restriction preserves coherence, and the hypothesis
provides an ample invertible module on this source. Apply Tag 0B5T (4) in the
specified positive degree as follows. A positive power L^d comes from O(1)
along an immersion into projective space; properness makes that immersion
closed. For each residue r<d, the projection formula and affine closed-immersion
cohomology comparison identify the dt+r twist with projective cohomology of
i_*(F tensor L^r) tensor O(t). This pushforward is coherent. Projective Serre
vanishing supplies a threshold t_r. The finite maximum T of these thresholds
gives the bound d*T, since n=dt+r and n>=d*T imply t>=T. Open restriction commutes
with tensor products and powers, identifying the coefficient module with
F restricted tensor the nth power of L restricted. Transport cohomology
vanishing through this isomorphism. For empty V or empty inverse image the
module category is zero, so threshold zero works. No threshold uniform in
cohomological degree is asserted here. -/
theorem exists_isZero_restricted_twist_moduleCohomology_degree
    {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S) [IsProper f]
    (F : X.Modules) [F.IsQuasicoherent] (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (L : X.Modules) [L.IsInvertible] (V : S.Opens) (hV : IsAffineOpen V)
    (hL : ∃ h : (L.restrict (f ⁻¹ᵁ V).ι).IsInvertible,
      @IsAmple (f ⁻¹ᵁ V).toScheme (L.restrict (f ⁻¹ᵁ V).ι) h)
    (q : ℕ) (hq : 0 < q) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      IsZero ((RingedSpace.moduleCohomology (f ⁻¹ᵁ V).toScheme.toRingedSpace q).obj
        ((F ⊗ L.tensorPow n).restrict (f ⁻¹ᵁ V).ι)) := by
  classical
  obtain ⟨hInv, hAmp⟩ := hL
  let := hInv
  let A := Γ(S, V)
  let : IsNoetherianRing A := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  let g : (f ⁻¹ᵁ V).toScheme ⟶ Spec (.of A) := (f ∣_ V) ≫ hV.isoSpec.hom
  let : IsProper g := inferInstance
  have hFr : RingedSpace.IsCoherent (f ⁻¹ᵁ V).toScheme.toRingedSpace
      (F.restrict (f ⁻¹ᵁ V).ι) :=
    (coherent_module_local_on_open_cover X F PUnit (fun _ ↦ ⊤) (by simp)).1 hF _
  obtain ⟨n₀, hn₀⟩ := exists_isZero_affine_tensorPow_degree A g
    (F.restrict (f ⁻¹ᵁ V).ι) hFr (L.restrict (f ⁻¹ᵁ V).ι) hAmp q hq
  refine ⟨n₀, fun n hn ↦ ?_⟩
  exact (hn₀ n hn).of_iso
    ((RingedSpace.moduleCohomology (f ⁻¹ᵁ V).toScheme.toRingedSpace q).mapIso
      (openRestrictionNumeratorIso (f ⁻¹ᵁ V).ι F L n))

end AlgebraicGeometry.Scheme.Modules
