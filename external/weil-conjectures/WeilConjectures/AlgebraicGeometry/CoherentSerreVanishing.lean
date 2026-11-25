/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.Noetherian.Defs
public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.PQFCohomology
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.AlgebraicGeometry.AmpleImmersionAffineBase
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.CoherentAffineSectionsFinite
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.AlgebraicGeometry.ClosedImmersionSerreVanishing

/-!
# Serre vanishing over a Noetherian affine base

Source: Stacks Project, Cohomology of Schemes, Tags 02O1 and 0B5T (4);
Morphisms, Tag 01VK (blueprint: lem-weil-pbc-coherent-serre-vanishing).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- A coherent module on a proper scheme over a Noetherian ring has zero positive-degree
cohomology after sufficiently large tensor powers of an ample invertible module, with
one nonnegative bound for every positive cohomological degree. Tensor powers include
`L.tensorPow 0 = 𝒪_X`. Cohomology is the right derived functor of module global sections.
Source: Stacks Project, Cohomology of Schemes, Tags 02O1 and 0B5T (4), and Morphisms,
Tag 01VK (blueprint: lem-weil-pbc-coherent-serre-vanishing).

Proof:
1. The affine base is Noetherian: def-weil-pbc-noetherian-ring, pqf-def-locnoeth,
   lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact. Properness gives finite type
   (def-weil-proper-morphism), so lem-weil-pbc-finite-type-over-noetherian makes X
   Noetherian. The standard affine charts of projective space (def-pc-proj) are
   Noetherian by lem-weil-pbc-finite-type-algebra-noetherian.
2. By lem-weil-pbc-ample-very-ample-immersion-affine-base there are d > 0 and an
   immersion i into projective space P over A, over the base, with L^{⊗ d} ≅ i^*O_P(1)
   (def-pc-projective-space-twist). Write M = i^*O_P(1).
3. P is separated over A (lem-weil-pbc-projective-space-proj-separated), so i is proper
   by lem-weil-pbc-proper-over-separated. By lem-weil-pbc-proper-immersion-closed it is
   a closed immersion (def-weil-closed-immersion).
4. For 0 ≤ r < d and t ≥ 0 put G_{r,t} = F ⊗ L^{⊗ r} ⊗ M^{⊗ t} and G_r = F ⊗ L^{⊗ r}.
   Local trivializations of the invertible factors (def-sc-invertible-module) identify
   these modules locally with F. Thus pqf-lem-coherent-ft-locnoeth and pqf-def-coherent
   give coherence. By lem-weil-pbc-closed-immersion-coherent-equivalence their
   pushforwards along i are coherent.
5. The projection formula (lem-pc-closed-immersion-coherent-cohomology) gives
   i_*G_{r,t} ≅ i_*G_r ⊗ O_P(t), inductively using theorem-riemann-roch-coherent-serre-duality and
   the trivialization O_P(0) ≅ O_P from def-pc-projective-space-twist. All tensor products
   and exponent laws are those of def-pur-sheaf-tensor-product.
6. For n = td + r the tensor exponent laws give F ⊗ L^{⊗ n} ≅ G_{r,t}.
   Functoriality of pqf-def-cohomology and the affine closed immersion comparison
   lem-weil-pbc-affine-morphism-cohomology-edge identify its degree-p cohomology
   with H^p(P, i_*G_r ⊗ O_P(t)).
7. Apply lemma-coherent-base-change-invertible-sheaves--1 to each coherent i_*G_r, obtaining
   bounds t_r for all p > 0. Let T be their finite maximum and n₀ = dT. For n ≥ n₀,
   division by d gives n = td + r, 0 ≤ r < d, and t ≥ T ≥ t_r. The comparison of
   step 6 therefore gives vanishing simultaneously in every positive degree. -/
theorem exists_isZero_moduleCohomology_tensorPow_of_ample
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (F : X.Modules) (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (L : X.Modules) [L.IsInvertible] (hL : IsAmple X L) :
    ∃ n₀ : ℕ, ∀ (p n : ℕ), 0 < p → n₀ ≤ n →
      IsZero ((RingedSpace.moduleCohomology X.toRingedSpace p).obj
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
  have key (r : Fin d) : ∃ t₀ : ℕ, ∀ (p t : ℕ), 0 < p → t₀ ≤ t →
      IsZero ((RingedSpace.moduleCohomology X.toRingedSpace p).obj
        (tensorObj (tensorObj F (L.tensorPow r)) (ProjectiveSpace.twistRestrict i t))) := by
    have := isQuasicoherent_tensorObj F (L.tensorPow r)
    have := isFinitePresentation_tensorObj F (L.tensorPow r)
    exact exists_isZero_moduleCohomology_tensor_twist_of_closedImmersion A i
      (tensorObj F (L.tensorPow r))
  choose t₀ ht₀ using key
  refine ⟨d * ∑ r, t₀ r, ?_⟩
  intro p n hp hn
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
  exact (ht₀ r p t hp ht).of_iso
    ((RingedSpace.moduleCohomology X.toRingedSpace p).mapIso e₄)

end AlgebraicGeometry.Scheme.Modules
