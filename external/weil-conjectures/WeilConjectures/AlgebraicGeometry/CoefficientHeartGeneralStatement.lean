/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartFiltration
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartSmall
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartClosure
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartCommonStratification
public import WeilConjectures.AlgebraicGeometry.CoefficientHeartStatement

/-!
# Constructible coefficient sheaves over a general field

Source: blueprint latest,
`part-six-operations/sec-reduction-finite-coefficients/`
`sec-constructible-sheaves-with-field-coefficients/sk-lem-coefficient-heart/_section.md`,
and `sk-lem-coefficient-heart.proof.md`, clauses (1)--(3), with the standing
field hypothesis `char(k) ≠ ℓ` (blueprint: lemma-constructible-sheaves).

This file states the current coefficient-heart lemma. The coefficient ring is either a
finite extension inside the algebraic closure of `ℚ_ℓ` or the finite-subextension-valued
condensed algebraic closure. The proof is postponed; its route is the three clauses of the
blueprint: closure and exactness, essential smallness, and finite locally closed lisse
filtrations.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Finite free local charts give finite constant presentations, including rank zero. -/
private lemma generalHeart_free_model
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {Y : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (hM : IsLisseCoefficientModule Λ M) : HasFiniteConstantLocalModel Λ Y M := by
  open MonoidalCategory MonObj Functor.LaxMonoidal Functor.OplaxMonoidal in
  obtain ⟨U, hU⟩ := hM
  refine ⟨U, fun i ↦ ?_⟩
  obtain ⟨n, ⟨e⟩⟩ := hU i
  have : PreservesFiniteColimits (upperStarFromPoint (U.X i)) := by
    let : pointUpperStar.{u}.IsLeftAdjoint := pointUpperStarLowerStarAdjunction.isLeftAdjoint
    unfold upperStarFromPoint
    infer_instance
  let F := (upperStarFromPoint (U.X i)).mapMod Λ
  have : PreservesFiniteColimits F := inferInstance
  have : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  have : F.Additive := Functor.additive_of_preservesBinaryBiproducts F
  have : PreservesFiniteBiproducts F := inferInstance
  let en : F.obj (Mod.finiteFree Λ n) ≅ Mod.finiteFree (condensedRingObj Λ (U.X i)) n :=
    F.mapBiproduct (fun _ : Fin n ↦ Mod.regular Λ) ≪≫
      biproduct.mapIso (fun _ ↦ Mod.isoMk (Iso.refl _) (by simp [Mod.act]))
  exact ⟨Mod.finiteFree Λ n, ⟨n, n, 0, ⟨cokernelZeroIsoTarget.symm⟩⟩, ⟨e ≪≫ en.symm⟩⟩

/-- Keep the counit image abstract while assembling its finite filtration. -/
private def generalHeart_filtrationImage
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {Y : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (V : Y.Opens) : Subobject M :=
  imageSubobject (coefficientHeartOpenCounit Λ M V)

private theorem generalHeart_filtrationImage_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {Y : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (V : Y.Opens) :
    generalHeart_filtrationImage Λ M V = coefficientHeartFiltrationStep Λ M V := rfl

/-- Constructible coefficient sheaves over any field of characteristic different from `ℓ`
form an exact essentially small abelian heart and admit finite filtrations by canonical
locally closed extensions of lisse sheaves.

Source: blueprint latest,
`part-six-operations/sec-reduction-finite-coefficients/`
`sec-constructible-sheaves-with-field-coefficients/sk-lem-coefficient-heart/_section.md`,
clauses (1)--(3), and
`sk-lem-coefficient-heart.proof.md`, steps (1)--(3)
(blueprint: lemma-constructible-sheaves).

Proof, following the node's five steps:
1. Finite type over k makes X Noetherian (locally Noetherian and quasi-compact).
2. Clause (1): `coefficientHeart_closure` gives closure under kernels, cokernels and
   extensions, the abelian full subcategory and its exact inclusion, and the criterion
   "constructible iff lisse on the strata of a finite stratification".
3. Clause (2): `coefficientHeart_essentiallySmall`.
4. Clause (3): for constructible F take its lisse stratification; a finite free chart is
   a finite constant local model (`generalHeart_free_model`, rank zero included). Refine
   it by `coefficientHeart_commonStratification` to ordered strata with open prefixes,
   on which F stays lisse.
5. `coefficientHeart_filtration` gives the open-prefix counit images as a filtration from
   zero to F whose quotients are the locally closed extensions of the lisse restrictions.
   Repeated terms, rank zero and empty schemes are allowed.
-/
theorem coefficientHeartGeneralStatement (ℓ : ℕ) [Fact ℓ.Prime]
    (L : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj L)]
    (hL : (∃ E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ),
      FiniteDimensional ℚ_[ℓ] E ∧ L = Profinite.padicSubfieldCondensedRing ℓ E) ∨
      L = Profinite.padicAlgClCondensedRing ℓ)
    (k : Type u) [Field k] (hchar : ringChar k ≠ ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] :
    ObjectProperty.IsClosedUnderKernels
        (IsConstantModelConstructible (coefficientHeartRingObj L) X) ∧
      ObjectProperty.IsClosedUnderCokernels
        (IsConstantModelConstructible (coefficientHeartRingObj L) X) ∧
      ObjectProperty.IsClosedUnderExtensions
        (IsConstantModelConstructible (coefficientHeartRingObj L) X) ∧
      Nonempty (Abelian (ConstantModelConstructible (coefficientHeartRingObj L) X)) ∧
      PreservesFiniteLimits
        (ObjectProperty.ι (IsConstantModelConstructible
          (coefficientHeartRingObj L) X)) ∧
      PreservesFiniteColimits
        (ObjectProperty.ι (IsConstantModelConstructible
          (coefficientHeartRingObj L) X)) ∧
      EssentiallySmall.{u + 1} (ConstantModelConstructible (coefficientHeartRingObj L) X) ∧
      @CoefficientHeartFiltrationAssertions (coefficientHeartRingObj L) _ _ X
        { toIsLocallyNoetherian :=
            LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
          toCompactSpace :=
            QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k)) } := by
  classical
  have _characteristic_separation := hchar
  have : IsNoetherian X :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k)) }
  have hclosure := (coefficientHeart_closure ℓ L hL).2 X
  refine ⟨hclosure.1, hclosure.2.1, hclosure.2.2.1, hclosure.2.2.2.1,
    hclosure.2.2.2.2.1, hclosure.2.2.2.2.2.1,
    coefficientHeart_essentiallySmall ℓ L hL X, ?_⟩
  intro F
  obtain ⟨S, hS⟩ := (hclosure.2.2.2.2.2.2 F.obj).mp F.property
  have hcommon := coefficientHeart_commonStratification ℓ L X hL
  obtain ⟨R, hR, _, hopen⟩ := hcommon.1 1 (fun _ ↦ S)
  have hRfree := hcommon.2.1.2 S R F.obj
    (fun a ↦ generalHeart_free_model (coefficientHeartRingObj L) _ (hS a)) (hR 0)
  let V (a : Fin (R.n + 1)) : X.Opens := ⟨_, hopen a⟩
  have hfil := coefficientHeart_filtration ℓ L hL X F.obj F.property R
    (fun a ↦ generalHeart_free_model (coefficientHeartRingObj L) _ (hRfree a))
    V (fun _ ↦ rfl)
  simp only [← generalHeart_filtrationImage_eq] at hfil
  obtain ⟨h, hquot⟩ := hfil.2.2.2
  refine ⟨R.n, fun a ↦ generalHeart_filtrationImage (coefficientHeartRingObj L) F.obj (V a),
    hfil.2.1, hfil.2.2.1, h, fun a ↦ ?_⟩
  exact ⟨R.domain a, R.immersion a, R.isImmersion a,
    (CondensedRing.upperStar (coefficientHeartRingObj L) (R.immersion a)).obj F.obj,
    (hquot a).2, (hquot a).1⟩

end AlgebraicGeometry.ProEtale
