import Langlands.Shimura.PEL.HarrisTaylorCMDvrAction
import Langlands.AbelianScheme.PolarizedFiniteLevel.CanonicalCubicBundleAmpleProof
import Langlands.AlgebraicGeometry.Picard.NoetherianAffineAbelianGenericAmpleProof

/-! # The ample diagonal bundle of an extended dual-valued homomorphism -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open Langlands.AbelianScheme Langlands.AbelianScheme.PolarizedFiniteLevel
open Langlands.AlgebraicGeometry.Picard

private theorem isAmple_diagonal_of_field_polarization (P : Prerequisites.{0})
    (K : Type) [Field K] (B : AbelianScheme (Spec (.of K)))
    (W : DualWitness B) (lam : B ⟶ W.dual P) (h : W.IsPolarization P lam) :
    (poincareDiagonalBundle B W.hasDual (W.parameterMap P lam)).IsAmple := by
  let Ω := AlgebraicClosure K
  let t : Spec (.of Ω) ⟶ Spec (.of K) := Spec.algebraMap K Ω
  let L := poincareDiagonalBundle B W.hasDual (W.parameterMap P lam)
  have hgeom := poincareDiagonal_isAmple_of_fieldPresentation P Ω
    ((baseChange t).obj B) (W.pullback P t)
    (dualBaseChangeMap B W.hasDual P.universality t (W.parameterMap P lam)) (h.2 Ω t)
  have hL : ((LineBundle.pullback (pullback.fst B.X.hom t)).obj L).IsAmple :=
    hgeom.of_iso ((LineBundle.forget _).mapIso
      (poincareDiagonalBaseChangeIso P.universality t B W.hasDual (W.parameterMap P lam)))
  exact fieldBaseChangeAmpleReflection K Ω t B.X.left B.X.hom L hL

variable {V : Type} [CommRing V]
  (K : Type) [Field K] [Algebra V K] [IsFractionRing V K]

local notation "j" => Spec.algebraMap V K

private theorem isAmple_of_fractionField [IsNoetherianRing V]
    (B : AbelianScheme (Spec (.of V))) (L : LineBundle B.X.left)
    (hL : ((LineBundle.pullback (pullback.fst B.X.hom j)).obj L).IsAmple) : L.IsAmple := by
  let S := Spec (CommRingCat.of V)
  let b : Spec (.of K) ⟶ S := j
  let η := b (IsLocalRing.closedPoint K)
  have hη : (η : PrimeSpectrum V).asIdeal = ⊥ := by
    change Ideal.comap (algebraMap V K) (IsLocalRing.closedPoint K).asIdeal = ⊥
    rw [Ideal.eq_bot_of_prime (IsLocalRing.closedPoint K).asIdeal,
      Ideal.comap_bot_of_injective _ (IsFractionRing.injective V K)]
  have hdense : closure ({η} : Set S) = Set.univ := by
    change closure ({η} : Set (PrimeSpectrum V)) = Set.univ
    rw [PrimeSpectrum.closure_singleton, hη, PrimeSpectrum.zeroLocus_bot]
  have hηL := L.isAmple_fibre_of_fieldPoint B.X.hom K b hL
  have hclosed := abelianFibreAmpleLocusClosed S B L
  have hsub : closure ({η} : Set S) ⊆
      {s : S | ((LineBundle.pullback (B.X.hom.fiberι s)).obj L).IsAmple} :=
    closure_minimal (Set.singleton_subset_iff.mpr hηL) hclosed
  rw [hdense] at hsub
  exact properAffineFibrewiseAmple _ S B.X.hom L (fun s => hsub (Set.mem_univ s))

variable [IsDomain V] [IsDiscreteValuationRing V]

set_option maxHeartbeats 800000 in
/-- Extend a homomorphism into the specified dual of a good model using its
canonical generic-fibre comparison. -/
def extendDvrDualHom (P : Prerequisites.{0}) (B : AbelianScheme (Spec (.of V)))
    (W : DualWitness B) (WK : DualWitness ((baseChange j).obj B))
    (lam : (baseChange j).obj B ⟶ WK.dual P) : B ⟶ W.dual P :=
  Function.surjInv (dvrGenericHom_bijective (V := V) K B (W.dual P)).2
    (lam ≫ (W.baseChangeIso P j WK).inv)

set_option maxHeartbeats 800000 in
/-- The integral extension gives the specified map after base change and the
canonical comparison of duals. -/
@[simp]
theorem pullbackMap_extendDvrDualHom (P : Prerequisites.{0}) (B : AbelianScheme (Spec (.of V)))
    (W : DualWitness B) (WK : DualWitness ((baseChange j).obj B))
    (lam : (baseChange j).obj B ⟶ WK.dual P) :
    W.pullbackMap P j WK (extendDvrDualHom (V := V) K P B W WK lam) = lam := by
  have he := Function.surjInv_eq (dvrGenericHom_bijective (V := V) K B (W.dual P)).2
    (lam ≫ (W.baseChangeIso P j WK).inv)
  unfold DualWitness.pullbackMap extendDvrDualHom
  rw [he, Category.assoc, Iso.inv_hom_id, Category.comp_id]

set_option maxHeartbeats 800000 in
/-- The diagonal Poincaré bundle of an integral dual-valued map over the DVR
is ample if its canonically transported generic map is a polarization. -/
theorem dvrIsAmpleDiagonal_of_genericPolarization (P : Prerequisites.{0})
    (B : AbelianScheme (Spec (.of V))) (W : DualWitness B) (lam : B ⟶ W.dual P)
    (h : (W.pullback P j).IsPolarization P (W.pullbackMap P j (W.pullback P j) lam)) :
    (poincareDiagonalBundle B W.hasDual (W.parameterMap P lam)).IsAmple := by
  let b : Spec (.of K) ⟶ Spec (.of V) := j
  have hK := isAmple_diagonal_of_field_polarization P K ((baseChange b).obj B)
    (W.pullback P b) (W.pullbackMap P b (W.pullback P b) lam) h
  rw [DualWitness.parameterMap_pullbackMap] at hK
  apply isAmple_of_fractionField (V := V) K B
  exact hK.of_iso ((LineBundle.forget _).mapIso
    (poincareDiagonalBaseChangeIso P.universality b B W.hasDual (W.parameterMap P lam)))

set_option maxHeartbeats 800000 in
/-- The actual ample diagonal Poincaré bundle formed from the extended
homomorphism of a generic polarization on a good model. -/
def extendDvrAmpleDiagonalBundle (P : Prerequisites.{0}) (B : AbelianScheme (Spec (.of V)))
    (W : DualWitness B) (lam : (baseChange j).obj B ⟶ (W.pullback P j).dual P)
    (h : (W.pullback P j).IsPolarization P lam) : {L : LineBundle B.X.left // L.IsAmple} := by
  let lam₀ := extendDvrDualHom (V := V) K P B W (W.pullback P j) lam
  have he := pullbackMap_extendDvrDualHom (V := V) K P B W (W.pullback P j) lam
  refine ⟨poincareDiagonalBundle B W.hasDual (W.parameterMap P lam₀),
    dvrIsAmpleDiagonal_of_genericPolarization (V := V) K P B W lam₀ ?_⟩
  exact he.symm ▸ h

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
