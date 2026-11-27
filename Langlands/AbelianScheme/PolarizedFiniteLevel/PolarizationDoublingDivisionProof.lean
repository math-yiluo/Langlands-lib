import Langlands.AbelianScheme.PolarizedFiniteLevel.PolarizationDoublingDivisionStatement
import Langlands.AbelianScheme.PolarizedFiniteLevel.AmpleMumfordDiagonalProof
import Langlands.AbelianScheme.MultiplicationIsogenyProof
import Langlands.AbelianScheme.Tate.IntegralReflectionAlgebra
import Langlands.AbelianScheme.RationalBaseChange
import Langlands.AlgebraicGeometry.AlgebraicSpace.FlatMorphismCharts
import Langlands.AlgebraicGeometry.Picard.PolarizationDiagonalMumfordProof
import Langlands.AlgebraicGeometry.Picard.MumfordSchemeMapHomomorphismProof
import Langlands.AlgebraicGeometry.Picard.PositiveTensorPowerAmpleReflection

/-! # Polarizations obtained by doubling divisors of a polarization -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.Picard.LineBundle (isoClass)

section Multiplication

variable {S : Scheme.{u}} {A B : AbelianScheme S}

private theorem isIsogeny_nsmul_id (A : AbelianScheme S) {k : ℕ} (hk : 0 < k) :
    IsIsogeny (k • 𝟙 A) := by
  change GroupScheme.IsIsogeny (groupHom (k • 𝟙 A))
  rw [Tate.groupHom_nsmul_id]
  exact GroupScheme.multiplicationIsogeny S A.toGrp A.smooth A.proper
    A.geometricallyConnected (k : ℤ) (Nat.cast_ne_zero.mpr hk.ne')

/-- Positive integral multiplication is injective on abelian-scheme homomorphisms. -/
theorem nsmul_hom_injective {k : ℕ} (hk : 0 < k) :
    Function.Injective (fun f : A ⟶ B => k • f) := by
  intro f g h
  have hf : (k • 𝟙 A) ≫ f = (k • 𝟙 A) ≫ g := by
    simpa only [Preadditive.nsmul_comp, Category.id_comp] using h
  have hfg := congrArg (fun a : A ⟶ B => groupHom a) hf
  exact congrArg Additive.ofMul (GroupScheme.IsogenyFactorization.hom_ext
    (isIsogeny_nsmul_id A hk) (groupHom f) (groupHom g) hfg)

private theorem isIsogeny_of_nsmul (f : A ⟶ B) {k : ℕ} (hk : 0 < k)
    (hf : IsIsogeny (k • f)) : IsIsogeny f := by
  let p : A ⟶ A := k • 𝟙 A
  let q : B ⟶ B := k • 𝟙 B
  have hp : IsIsogeny p := isIsogeny_nsmul_id A hk
  have hq : IsIsogeny q := isIsogeny_nsmul_id B hk
  have hleft : p ≫ f = k • f := by rw [Preadditive.nsmul_comp, Category.id_comp]
  have hright : f ≫ q = k • f := by rw [Preadditive.comp_nsmul, Category.comp_id]
  have hleft' : hom p ≫ hom f = hom (k • f) :=
    (hom_comp p f).symm.trans (congrArg hom hleft)
  have hright' : hom f ≫ hom q = hom (k • f) :=
    (hom_comp f q).symm.trans (congrArg hom hright)
  let : IsFinite (hom q) := hq.1
  let : IsFinite (hom f ≫ hom q) := hright' ▸ hf.1
  let : Flat (hom p) := hp.2.1
  let : Surjective (hom p) := hp.2.2
  let : Flat (hom p ≫ hom f) := hleft' ▸ hf.2.1
  refine ⟨IsFinite.of_comp (hom f) (hom q),
    Langlands.AlgebraicGeometry.AlgebraicSpace.flat_of_surjective_flat_comp
      (hom p) (hom f), ⟨?_⟩⟩
  intro y
  obtain ⟨x, hx⟩ := hf.2.2.surj y
  exact ⟨hom p x, by simpa only [← Scheme.Hom.comp_apply, hleft'] using hx⟩

private theorem isIsogeny_nsmul (f : A ⟶ B) {k : ℕ} (hk : 0 < k)
    (hf : IsIsogeny f) : IsIsogeny (k • f) := by
  simpa only [Preadditive.nsmul_comp, Category.id_comp] using
    (isIsogeny_nsmul_id A hk).comp hf

end Multiplication

variable (P : Prerequisites.{u}) {S : Scheme.{u}} {A : AbelianScheme S} (W : DualWitness A)

private theorem parameterMap_nsmul (f : A ⟶ W.dual P) (k : ℕ) :
    (groupHom (k • f)).hom.hom = ((groupHom f).hom.hom) ^ k := by
  change (Additive.toMul (k • f)).hom.hom = ((groupHom f).hom.hom) ^ k
  rw [toMul_nsmul, Grp.Hom.hom_pow, Mon.Hom.hom_pow]

private theorem isoClass_diagonal_nsmul (f : A ⟶ W.dual P) (k : ℕ) :
    isoClass P.preservation (poincareDiagonalBundle A W.hasDual (groupHom (k • f)).hom.hom) =
      (isoClass P.preservation (poincareDiagonalBundle A W.hasDual (groupHom f).hom.hom)) ^ k := by
  have diagClass (v : A.X ⟶ (W.dual P).X) :
      isoClass P.preservation (poincareDiagonalBundle A W.hasDual v) =
        familyPointClass P.preservation A (poincareFamily A W.hasDual) v (𝟙 A.X) := by
    simpa only [Over.id_left, ← LineBundle.pullbackHom_isoClass, LineBundle.pullbackHom_id,
      MonoidHom.id_apply, Category.id_comp] using
      isoClass_pullback_poincareDiagonalBundle P.preservation A W.hasDual v (𝟙 A.X)
  rw [diagClass, diagClass, parameterMap_nsmul]
  exact familyPointClass_poincareFamily_pow_left P A W (W.parameterMap P f) (𝟙 A.X) k

private theorem ampleMumford_two_of_nsmul {K : Type u} [Field K]
    {A : AbelianScheme (Spec (CommRingCat.of K))} (W : DualWitness A)
    (mu : A ⟶ W.dual P) (k : ℕ) (hk : 0 < k)
    (hpol : W.IsPolarization P (k • mu))
    (hpre : HasAmpleMumfordPresentation P.preservation P.square A W.hasDual
      (W.parameterMap P (k • mu))) :
    HasAmpleMumfordPresentation P.preservation P.square A W.hasDual
      (W.parameterMap P (2 • mu)) := by
  let L := poincareDiagonalBundle A W.hasDual (W.parameterMap P mu)
  let Lk := poincareDiagonalBundle A W.hasDual (W.parameterMap P (k • mu))
  have hc := isoClass_diagonal_nsmul P W mu k
  obtain ⟨e⟩ := LineBundle.isoClass_eq_iff.mp
    (hc.trans (isoClass_tensorPow P.preservation L k).symm)
  have hLk : Lk.IsAmple := ampleMumfordDiagonal P _ A W _ hpre
  have hL := hLk.of_positive_tensorPower_iso hk ((LineBundle.forget _).mapIso e)
  obtain ⟨B, ⟨evB⟩⟩ := LineBundle.exists_tensorObj_iso_structureSheaf
    ((LineBundle.pullback (unitSection A)).obj L)
  let N := LineBundle.normalize P.preservation A.X.hom (unitSection A) (unitSection_comp A)
    L B evB
  obtain ⟨M, ⟨ev⟩⟩ :=
    LineBundle.exists_tensorObj_iso_structureSheaf ((RigidifiedLineBundle.forget _).obj N)
  let hf := relativeMumfordSchemeMapHomomorphism P.preservation P.stability P.square _
    A N M ev W.hasDual
  let f := mumfordHomOfLineBundle P.preservation A L B evB M ev P.square W.hasDual
    P.composition P.unitCoherence P.associativity P.comparison P.symmetry P.stability hf
    W.inverseBundle W.evaluation W.geometry
  obtain ⟨B', evB', M', ev', hm⟩ := polarizationDiagonalMumford P.preservation P.square
    P.universality P.composition P.unitCoherence P.associativity P.comparison P.symmetry
    P.stability _ A W.hasDual W.geometry W.inverseBundle W.evaluation (k • mu) hpol
  have hpow := mumfordSchemeMapOfLineBundle_eq_pow_of_isoClass P A W L B evB M ev
    Lk B' evB' M' ev' k hc
  have hmultiple : k • (2 • mu) = k • f := by
    apply Additive.toMul.injective
    apply Grp.hom_ext
    change (groupHom (k • (2 • mu))).hom.hom = (groupHom (k • f)).hom.hom
    rw [parameterMap_nsmul P W f,
      show k • (2 • mu) = 2 • (k • mu) by rw [smul_smul, smul_smul, Nat.mul_comm]]
    exact hm.symm.trans hpow
  have heq := nsmul_hom_injective hk hmultiple
  exact ⟨L, B, evB, M, ev, hL, congrArg (W.parameterMap P) heq⟩

private theorem pullbackMap_nsmul {T : Scheme.{u}} (b : T ⟶ S)
    (V : DualWitness ((baseChange b).obj A)) (f : A ⟶ W.dual P) (k : ℕ) :
    W.pullbackMap P b V (k • f) = k • W.pullbackMap P b V f := by
  unfold DualWitness.pullbackMap
  rw [Functor.map_nsmul, Preadditive.nsmul_comp]

private theorem polarization_pullback {T : Scheme.{u}} (b : T ⟶ S)
    (V : DualWitness ((baseChange b).obj A)) (f : A ⟶ W.dual P)
    (hf : W.IsPolarization P f) :
    V.IsPolarization P (W.pullbackMap P b V f) :=
  P.polarizationBaseChange P.preservation P.square P.universality P.stability P.composition
    P.unitCoherence P.associativity P.comparison P.symmetry P.compatibility S T b A
    W.hasDual W.geometry W.inverseBundle W.evaluation
    V.hasDual V.geometry V.inverseBundle V.evaluation f hf

/-- A positive multiple that is a polarization makes the double of the
original homomorphism a polarization. -/
theorem polarizationDoublingDivision : PolarizationDoublingDivisionStatement.{u} := by
  intro P S A W mu k hk hpol
  refine ⟨isIsogeny_nsmul mu (by decide : 0 < (2 : ℕ)) (isIsogeny_of_nsmul mu hk hpol.1), ?_⟩
  intro K _ _ s
  obtain ⟨K', instK', iota, hpre⟩ := hpol.2 K s
  let : Field K' := instK'
  let b := Spec.map (CommRingCat.ofHom iota)
  let W₁ := W.pullback P s
  let W₂ := W₁.pullback P b
  let mu₁ := W.pullbackMap P s W₁ mu
  let mu₂ := W₁.pullbackMap P b W₂ mu₁
  have hp₁ := polarization_pullback P W s W₁ (k • mu) hpol
  rw [pullbackMap_nsmul] at hp₁
  have hp₂ := polarization_pullback P W₁ b W₂ (k • mu₁) hp₁
  rw [pullbackMap_nsmul] at hp₂
  have change_eq (j : ℕ) :
      W₂.parameterMap P (j • mu₂) =
        dualBaseChangeMap _ W₁.hasDual P.universality b
          (dualBaseChangeMap A W.hasDual P.universality s (W.parameterMap P (j • mu))) := by
    rw [← pullbackMap_nsmul P W₁ b W₂ mu₁, ← pullbackMap_nsmul P W s W₁ mu,
      DualWitness.parameterMap_pullbackMap, DualWitness.parameterMap_pullbackMap]
  have hpre' : HasAmpleMumfordPresentation P.preservation P.square _ W₂.hasDual
      (W₂.parameterMap P (k • mu₂)) := by
    rw [change_eq]
    exact hpre
  have hdouble := ampleMumford_two_of_nsmul P W₂ mu₂ k hk hp₂ hpre'
  rw [change_eq] at hdouble
  exact ⟨K', instK', iota, hdouble⟩

end Langlands.AbelianScheme.PolarizedFiniteLevel
