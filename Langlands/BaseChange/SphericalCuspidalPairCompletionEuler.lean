import Langlands.BaseChange.CommonNormTwistAuxiliaryFactors
import Langlands.BaseChange.SphericalPairNormTwistEuler
import Langlands.Automorphic.AssociatedGammaAutomorphicFamily

/-! # Spherical pair Euler products at finite completions -/

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false

universe u uQ uI

namespace Langlands.BaseChange

open Automorphic Correspondence Global Global.AdelicFunctoriality Global.CompletionPadic
open Global.CuspidalPairFunctionalEquation LocalClassField RankinSelberg Unramified
open scoped BigOperators NumberField FiniteExtension

private structure SphericalPairTwistAt {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)
    {r t : ℕ} (a : Eigenvalues (r + 1)) (b : Eigenvalues (t + 1))
    (χ : QuasiCharacter F) (P : Polynomial ℂ) where
  first : AutomorphicObject.{u,u} F r.succPNat
  twisted : AutomorphicObject.{u,u} F r.succPNat
  second : AutomorphicObject.{u,u} F t.succPNat
  hfirst : HasSphericalSpectrum F first a
  hsecond : HasSphericalSpectrum F second b
  htwist : IsCharacterTwist F χ (automorphicClassOf F first) (automorphicClassOf F twisted)
  additive : NontrivialAdditiveCharacter F
  measure : LocalAdditiveHaarMeasure F
  hmeasure : IsSelfDualMeasure F additive measure
  hpoly : IsAutomorphicPairLPolynomial F additive measure
    (automorphicClassOf F twisted) (automorphicClassOf F second) P

private def SphericalPairTwistAt.atPrime {L : Type u} [Field L] [NumberField L]
    (w : FinitePlace L) {p : ℕ} [Fact p.Prime] (hw : residuePrime w = p)
    {r t : ℕ} {a : Eigenvalues (r + 1)} {b : Eigenvalues (t + 1)}
    (χ : (w.adicCompletion L)ˣ →ₜ* ℂˣ) {P : Polynomial ℂ}
    (d : SphericalPairTwistAt (padicField w) a b (quasicharacterBase w χ) P) :
    SphericalPairTwistAt (padicFieldAt w hw) a b (quasicharacterAt w hw χ) P := by
  subst p
  exact d

section Fields

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : FinitePlace K) (w : FinitePlacesAbove L v)

local notation "F" => padicField v
local notation "E" => CompletionPadic.towerPadicField v (Subtype.val w)
local notation "f" => Ideal.inertiaDeg (IsDedekindDomain.HeightOneSpectrum.asIdeal (Subtype.val w)) (𝓞 K)

set_option maxHeartbeats 800000 in
private theorem sphericalPairEuler_atCompletion {r t : ℕ}
    (a : Eigenvalues (r + 1)) (b : Eigenvalues (t + 1))
    (A : AutomorphicObject.{u,u} F r.succPNat) (B : AutomorphicObject.{u,u} F t.succPNat)
    (ha : HasSphericalSpectrum F A a) (hb : HasSphericalSpectrum F B b)
    (ψ : NontrivialAdditiveCharacter F) (ν : LocalAdditiveHaarMeasure F) (hν : IsSelfDualMeasure F ψ ν)
    (X : Finset ((F).Carrierˣ →* ℂˣ)) (hX : ∀ κ, κ ∈ X ↔ IsNormTrivial (E).Carrier κ)
    (μ : HeckeCharacter K) (ω : X → QuasiCharacter F)
    (hω : letI := (F).canonicalTopologicalData.topology; ∀ κ : X, (ω κ).toMonoidHom = κ.val)
    (C : X → AutomorphicObject.{u,u} F r.succPNat)
    (hC : letI := (F).canonicalTopologicalData.topology; ∀ κ,
      IsCharacterTwist F (ω κ * quasicharacterBase v (μ.finiteComponent v))
        (automorphicClassOf F A) (automorphicClassOf F (C κ)))
    (PF : X → Polynomial ℂ) (PE : Polynomial ℂ)
    (hPF : ∀ κ, IsAutomorphicPairLPolynomial F ψ ν (automorphicClassOf F (C κ))
      (automorphicClassOf F B) (PF κ))
    (d : SphericalPairTwistAt (padicField w.1) (a.power f) (b.power f)
      (quasicharacterBase w.1 ((μ.normComp (L := L)).finiteComponent w.1)) PE) :
    ∀ z : ℂ, (∏ κ : X, ((PF κ).eval (spectralPoint (residueCardinality v) z))⁻¹) =
      (PE.eval (spectralPoint (residueCardinality w.1) z))⁻¹ := by
  let := towerPadicField_isScalarTower v w.1
  let := (F).canonicalTopologicalData.topology
  let := (E).canonicalTopologicalData.topology
  let := (F).canonicalTopologicalData.valuativeRel
  let := (E).canonicalTopologicalData.valuativeRel
  let d' := d.atPrime w.1 (residuePrime_eq v w.1) ((μ.normComp (L := L)).finiteComponent w.1)
  have hnorm := d'.htwist
  rw (occs := .pos [1]) [quasicharacterAt_normComp v w μ] at hnorm
  have hpoly := sphericalPairNormTwistEuler (residuePrime v) F E f r t (completion_isResidueDegree v w.1)
    ψ d'.additive ν d'.measure hν d'.hmeasure X hX (quasicharacterBase v (μ.finiteComponent v))
    ω hω A B d'.first d'.twisted d'.second C a b ha hb d'.hfirst d'.hsecond hC hnorm PF PE hPF d'.hpoly
  intro z
  have hq : residueCardinality w.1 = residueCardinality v ^ f := by
    unfold residueCardinality
    rw [canonicalResidueCardinality_eq_absNorm, canonicalResidueCardinality_eq_absNorm]
    exact (Ideal.absNorm_pow_inertiaDeg v.asIdeal w.1.asIdeal).symm
  have hs : spectralPoint (residueCardinality w.1) z = spectralPoint (residueCardinality v) z ^ f := by
    rw [hq]
    simp only [spectralPoint, Nat.cast_pow, ← Complex.cpow_nat_mul, Complex.natCast_cpow_natCast_mul]
  rw [Finset.prod_inv_distrib, ← Polynomial.eval_prod, hpoly, Polynomial.eval_comp,
    Polynomial.eval_pow, Polynomial.eval_X, hs]

end Fields

section Presentations

variable {k : Type u} [Field k] [NumberField k]

private local instance rationalAddCommGroup (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions k n) := Submodule.addCommGroup _
private local instance continuousAddCommGroup (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions k n) := Submodule.addCommGroup _
private local instance smoothAddCommGroup (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions k n) := Submodule.addCommGroup _
private local instance formAddCommGroup (n : ℕ) :
    AddCommGroup (AutomorphicForms k n) := Submodule.addCommGroup _
private local instance localComponentAddCommGroup {n : ℕ} {v : FinitePlace k}
    (A : LocalRealization k n v) : AddCommGroup A.Space := Submodule.addCommGroup _

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [CompactSpace (AdeleQuotient K)] [CompactSpace (AdeleQuotient L)]
  {r t : ℕ} {T : CuspidalOperatorRealization K r} {T' : CuspidalOperatorRealization K t}
  {U : CuspidalOperatorRealization L r} {U' : CuspidalOperatorRealization L t}
  (P : CuspidalSpectralPresentation.{u,uQ} T) (P' : CuspidalSpectralPresentation.{u,uQ} T')
  (Q : CuspidalSpectralPresentation.{u,uQ} U) (Q' : CuspidalSpectralPresentation.{u,uQ} U')
  (hP : HasIrreducibleAdmissibleComponents P) (hP' : HasIrreducibleAdmissibleComponents P')
  (hQ : HasIrreducibleAdmissibleComponents Q) (hQ' : HasIrreducibleAdmissibleComponents Q')
  (v : FinitePlace K) (I : Type uI) [Fintype I] (χ : I → HeckeCharacter K) (μ : HeckeCharacter K)

local notation "F" => padicField v

/-- If the two pairs have matching spherical spectra by residue-degree powers,
compare the product of the certified lower norm-twisted Euler values with the
product of the upper Euler values after the common auxiliary twist. -/
def SphericalCuspidalPairCompletionEulerStatement : Prop :=
  ∀ (a : Eigenvalues (r + 1)) (b : Eigenvalues (t + 1)),
    HasSphericalSpectrum F ((P.localComponent v).padicObject (hP v).1 (hP v).2) a →
    HasSphericalSpectrum F ((P'.localComponent v).padicObject (hP' v).1 (hP' v).2) b →
    (∀ w : FinitePlacesAbove L v,
      HasSphericalSpectrum (padicField w.1) ((Q.localComponent w.1).padicObject (hQ w.1).1 (hQ w.1).2)
        (a.power (w.1.asIdeal.inertiaDeg (𝓞 K))) ∧
      HasSphericalSpectrum (padicField w.1) ((Q'.localComponent w.1).padicObject (hQ' w.1).1 (hQ' w.1).2)
        (b.power (w.1.asIdeal.inertiaDeg (𝓞 K)))) →
    (∀ (w : FinitePlacesAbove L v) (κ : (F).Carrierˣ →* ℂˣ),
      (IsNormTrivial (w.1.adicCompletion L) κ ↔ ∃ i, ((χ i).finiteComponent v).toMonoidHom = κ) ∧
      (IsNormTrivial (w.1.adicCompletion L) κ →
        Nat.card {i // ((χ i).finiteComponent v).toMonoidHom = κ} = Nat.card (FinitePlacesAbove L v))) →
  ∀ (ψ : NontrivialAdditiveCharacter F) (ν : LocalAdditiveHaarMeasure F), IsSelfDualMeasure F ψ ν →
  ∀ (ψ' : ∀ w : FinitePlacesAbove L v, NontrivialAdditiveCharacter (padicField w.1))
    (ν' : ∀ w : FinitePlacesAbove L v, LocalAdditiveHaarMeasure (padicField w.1)),
    (∀ w, IsSelfDualMeasure (padicField w.1) (ψ' w) (ν' w)) →
  ∀ (PF : I → Polynomial ℂ) (PE : FinitePlacesAbove L v → Polynomial ℂ),
    (∀ i, IsAutomorphicPairLPolynomial F ψ ν
      (localClass (P.heckeDeterminantTwist (χ i * μ))
        (P.heckeDeterminantTwist_hasIrreducibleAdmissibleComponents (χ i * μ) hP) v)
      (localClass P' hP' v) (PF i)) →
    (∀ w, IsAutomorphicPairLPolynomial (padicField w.1) (ψ' w) (ν' w)
      (localClass (Q.heckeDeterminantTwist (μ.normComp (L := L)))
        (Q.heckeDeterminantTwist_hasIrreducibleAdmissibleComponents (μ.normComp (L := L)) hQ) w.1)
      (localClass Q' hQ' w.1) (PE w)) →
    ∀ z : ℂ, (∏ i, ((PF i).eval (spectralPoint (residueCardinality v) z))⁻¹) =
      ∏ w, ((PE w).eval (spectralPoint (residueCardinality w.1) z))⁻¹

set_option maxHeartbeats 9500000 in
/-- Restrict the global characters once at the lower place. Each local
character occurs once per upper place in the resulting Euler product. -/
theorem sphericalCuspidalPairCompletionEuler :
    SphericalCuspidalPairCompletionEulerStatement P P' Q Q' hP hP' hQ hQ' v I χ μ := by
  classical
  intro a b ha hb hspec hres ψ ν hν ψ' ν' hν' PF PE hPF hPE z
  let raw (i : I) := ((χ i).finiteComponent v).toMonoidHom
  let := (F).canonicalTopologicalData.topology
  let X := Finset.univ.image raw
  let res (i : I) : X := ⟨raw i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
  have hsurj : Function.Surjective res := by
    intro κ
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp κ.property
    exact ⟨i, Subtype.ext hi⟩
  choose pick hpick using hsurj
  have hmem (w : FinitePlacesAbove L v) (κ : (F).Carrierˣ →* ℂˣ) :
      κ ∈ X ↔ IsNormTrivial (w.1.adicCompletion L) κ := by
    rw [(hres w κ).1]
    simp [X, raw]
  let ω (κ : X) := quasicharacterBase v ((χ (pick κ)).finiteComponent v)
  have hω (κ : X) : (ω κ).toMonoidHom = κ.1 := congrArg Subtype.val (hpick κ)
  let Pχ (i : I) := P.heckeDeterminantTwist (χ i * μ)
  let hPχ (i : I) := P.heckeDeterminantTwist_hasIrreducibleAdmissibleComponents (χ i * μ) hP
  let A := (P.localComponent v).padicObject (hP v).1 (hP v).2
  let B := (P'.localComponent v).padicObject (hP' v).1 (hP' v).2
  let C (i : I) := ((Pχ i).localComponent v).padicObject (hPχ i v).1 (hPχ i v).2
  have htw (i : I) : IsCharacterTwist F (quasicharacterBase v ((χ i).finiteComponent v) *
      quasicharacterBase v (μ.finiteComponent v)) (automorphicClassOf F A) (automorphicClassOf F (C i)) := by
    exact P.isCharacterTwist_heckeDeterminantTwist_padicClass (χ i * μ) v
      (hP v).1 (hP v).2 (hPχ i v).1 (hPχ i v).2
  have hrep (i : I) : PF i = PF (pick (res i)) := by
    have hωi : ω (res i) = quasicharacterBase v ((χ i).finiteComponent v) :=
      ContinuousMonoidHom.toMonoidHom_injective (hω (res i))
    have hclass := (htw i).unique ((congrArg (fun x : QuasiCharacter F =>
      x * quasicharacterBase v (μ.finiteComponent v)) hωi) ▸ htw (pick (res i)))
    have hi : IsAutomorphicPairLPolynomial F ψ ν (automorphicClassOf F (C i))
        (automorphicClassOf F B) (PF i) := hPF i
    rw [hclass] at hi
    exact hi.unique (hPF (pick (res i)))
  let w₀ := placeAbove L v
  have hcount (κ : X) : Fintype.card {i // res i = κ} = Fintype.card (FinitePlacesAbove L v) := by
    have he (i : I) : res i = κ ↔ raw i = κ.1 := ⟨congrArg Subtype.val, fun hx => Subtype.ext hx⟩
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, Nat.card_congr (Equiv.subtypeEquivRight he)]
    exact (hres w₀ κ.1).2 ((hmem w₀ κ.1).mp κ.property)
  let N : HeckeCharacter L := μ.normComp (L := L)
  let Qχ : CuspidalSpectralPresentation.{u,uQ} (U.heckeDeterminantTwist N) := Q.heckeDeterminantTwist N
  let hQχ : HasIrreducibleAdmissibleComponents Qχ :=
    Q.heckeDeterminantTwist_hasIrreducibleAdmissibleComponents N hQ
  let C' (w : FinitePlacesAbove L v) : AutomorphicObject.{u,u} (padicField w.1) r.succPNat :=
    (Qχ.localComponent w.1).padicObject (hQχ w.1).1 (hQχ w.1).2
  have hu (w : FinitePlacesAbove L v) :
      (∏ κ : X, ((PF (pick κ)).eval (spectralPoint (residueCardinality v) z))⁻¹) =
        ((PE w).eval (spectralPoint (residueCardinality w.1) z))⁻¹ := by
    let d : SphericalPairTwistAt (padicField w.1) (a.power (w.1.asIdeal.inertiaDeg (𝓞 K)))
        (b.power (w.1.asIdeal.inertiaDeg (𝓞 K))) (quasicharacterBase w.1 (N.finiteComponent w.1)) (PE w) :=
      { first := (Q.localComponent w.1).padicObject (hQ w.1).1 (hQ w.1).2
        twisted := C' w
        second := (Q'.localComponent w.1).padicObject (hQ' w.1).1 (hQ' w.1).2
        hfirst := (hspec w).1
        hsecond := (hspec w).2
        htwist := Q.isCharacterTwist_heckeDeterminantTwist_padicClass N w.1
          (hQ w.1).1 (hQ w.1).2 (hQχ w.1).1 (hQχ w.1).2
        additive := ψ' w
        measure := ν' w
        hmeasure := hν' w
        hpoly := hPE w }
    exact sphericalPairEuler_atCompletion v w a b A B ha hb ψ ν hν X (hmem w) μ ω hω
      (C ∘ pick) (fun κ => htw (pick κ)) (PF ∘ pick) (PE w) (fun κ => hPF (pick κ)) d z
  let g (κ : X) := ((PF (pick κ)).eval (spectralPoint (residueCardinality v) z))⁻¹
  calc
    (∏ i, ((PF i).eval (spectralPoint (residueCardinality v) z))⁻¹) = ∏ i, g (res i) :=
      Finset.prod_congr rfl fun i _ => congrArg (fun p : Polynomial ℂ =>
        (p.eval (spectralPoint (residueCardinality v) z))⁻¹) (hrep i)
    _ = (∏ κ : X, g κ) ^ Fintype.card (FinitePlacesAbove L v) := by
      rw [← Fintype.prod_fiberwise' res g, ← Finset.prod_pow]
      exact Finset.prod_congr rfl fun κ _ => by simp [hcount κ]
    _ = _ := by simp_rw [← hu, Finset.prod_const, Finset.card_univ, g]

end Presentations

end Langlands.BaseChange
