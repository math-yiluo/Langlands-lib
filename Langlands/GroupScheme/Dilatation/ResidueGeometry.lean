import Langlands.GroupScheme.Dilatation.BlowupLocalization
import Langlands.GroupScheme.Dilatation.ChartGenerators
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk
import StacksFrontier.RingTheory.Localization.AtPrimeQuotient
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-! # Smoothness and connectedness of the reduced dilatation algebra over the centre -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 100000

namespace Langlands.GroupScheme.Dilatation

universe u

/-- A smooth affine scheme over a field has a regular coordinate ring. -/
theorem isRegularRing_of_smoothSpec {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    (h : Smooth (Spec.algebraMap k A)) : IsRegularRing A := by
  let : Smooth (Spec.algebraMap k A) := h
  let : Algebra.Smooth k A := (RingHom.smooth_algebraMap).mp
    ((HasRingHomProperty.Spec_iff (P := @Smooth)).mp h)
  let : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  apply (isRegularRing_iff).2
  intro p hp
  let x : PrimeSpectrum A := ⟨p, hp⟩
  let : IsRegularLocalRing ((Spec (CommRingCat.of A)).presheaf.stalk x) :=
    Smooth.isRegularLocalRing_stalkFLT (f := Spec.algebraMap k A) x
  exact IsRegularLocalRing.of_ringEquiv (Spec.stalkIso (CommRingCat.of A) x).commRingCatIsoToRingEquiv

private theorem isRegularLocalRing_quotient_localization {A : Type u} [CommRing A]
    (p : Ideal A) [p.IsPrime] (I : Ideal A) (hp : I ≤ p) [IsRegularRing (A ⧸ I)] :
    IsRegularLocalRing (Localization.AtPrime p ⧸ I.map (algebraMap A (Localization.AtPrime p))) := by
  let q := p.map (Ideal.Quotient.mk I)
  let : q.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by
    rw [Ideal.mk_ker]
    exact hp)
  have hq : q.comap (Ideal.Quotient.mk I) = p := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker, sup_eq_left.mpr hp]
  let : IsLocalization.AtPrime (Localization.AtPrime p ⧸ I.map
      (algebraMap A (Localization.AtPrime p))) q :=
    isLocalization_atPrime_quotient p (Localization.AtPrime p) I q hq
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q) _).toRingEquiv

private theorem flat_localized_of_polynomial {Q Qp C : Type u}
    [CommRing Q] [CommRing Qp] [CommRing C] [Algebra Q Qp] [Algebra Q C]
    (S : Submonoid Q) [IsLocalization S Qp] {n : ℕ}
    (e : Qp ⊗[Q] C ≃ₐ[Qp] MvPolynomial (Fin n) Qp) : Module.Flat Q (LocalizedModule S C) := by
  let : Module.Flat Qp (Qp ⊗[Q] C) := Module.Flat.of_linearEquiv e.toLinearEquiv
  let : Module.Flat Q Qp := IsLocalization.flat Qp S
  let : Module.Flat Q (Qp ⊗[Q] C) := Module.Flat.trans Q Qp (Qp ⊗[Q] C)
  let f := TensorProduct.mk Q Qp C 1
  let : IsLocalizedModule S f := inferInstance
  exact Module.Flat.of_linearEquiv (IsLocalizedModule.iso S f)

private theorem formallySmooth_of_polynomial_fibre {Q C : Type u}
    [CommRing Q] [CommRing C] [Algebra Q C] (p : Ideal Q) [p.IsPrime]
    (h : ∃ n : ℕ, Nonempty (p.ResidueField ⊗[Q] C ≃ₐ[p.ResidueField] MvPolynomial (Fin n) p.ResidueField)) :
    Algebra.FormallySmooth p.ResidueField (p.Fiber C) := by
  obtain ⟨_, ⟨e⟩⟩ := h
  exact Algebra.FormallySmooth.of_equiv e.symm

private theorem geometricallyConnected_of_polynomial_fibres {Q C : Type u}
    [CommRing Q] [CommRing C] [Algebra Q C]
    (h : ∀ (F : Type u) [Field F] [Algebra Q F],
      ∃ n : ℕ, Nonempty (F ⊗[Q] C ≃ₐ[F] MvPolynomial (Fin n) F)) :
    GeometricallyConnected (Spec.algebraMap Q C) := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr ?_⟩
  intro F _ y
  obtain ⟨f, hf⟩ := Spec.map_surjective y
  let : Algebra Q F := f.hom.toAlgebra
  obtain ⟨n, ⟨e⟩⟩ := h F
  have hy : Spec.algebraMap Q F = y := hf
  rw [← hy]
  let e' := (Algebra.TensorProduct.comm Q C F).toRingEquiv.trans e.toRingEquiv
  let eq := pullbackSpecIso Q C F ≪≫ Scheme.Spec.mapIso e'.symm.toCommRingCatIso.op
  let : IsDomain (MvPolynomial (Fin n) F) := inferInstance
  let : IrreducibleSpace (PrimeSpectrum (MvPolynomial (Fin n) F)) := PrimeSpectrum.irreducibleSpace
  exact eq.hom.homeomorph.connectedSpace_iff.mpr
    (IrreducibleSpace.connectedSpace (PrimeSpectrum (MvPolynomial (Fin n) F)))

section Geometry

variable {R A : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing A] [Algebra R A] [Module.Flat R A] {r : R}
  (hr : Irreducible r) (I : Ideal A) (hi : algebraMap R A r ∈ I)
  [IsRegularRing (A ⧸ Ideal.span {algebraMap R A r})] [IsRegularRing (A ⧸ I)]

private abbrev centrePrime (q : Ideal (A ⧸ I)) := q.comap (Ideal.Quotient.mk I)

private instance centrePrime_isPrime (q : Ideal (A ⧸ I)) [q.IsPrime] :
    (centrePrime I q).IsPrime := Ideal.comap_isPrime _ _

private abbrev centreLocalRing (q : Ideal (A ⧸ I)) [q.IsPrime] :=
  let Ap := Localization.AtPrime (centrePrime I q)
  Ap ⧸ I.map (algebraMap A Ap)

private instance centreLocalRing_isLocalization (q : Ideal (A ⧸ I)) [q.IsPrime] :
    IsLocalization.AtPrime (centreLocalRing I q) q :=
  isLocalization_atPrime_quotient (centrePrime I q) (Localization.AtPrime (centrePrime I q)) I q rfl

include hr hi in
private theorem exists_blowupResidue_localEquiv (q : Ideal (A ⧸ I)) [q.IsPrime] :
    ∃ n : ℕ, Nonempty (centreLocalRing I q ⊗[A ⧸ I] blowupResidue r I ≃ₐ[centreLocalRing I q]
      MvPolynomial (Fin n) (centreLocalRing I q)) := by
  let p := q.comap (Ideal.Quotient.mk I)
  let : p.IsPrime := Ideal.comap_isPrime _ _
  have hp : I ≤ p := by
    have h : RingHom.ker (Ideal.Quotient.mk I) ≤ p := Ideal.ker_le_comap _
    simpa only [Ideal.mk_ker] using h
  let Ap := Localization.AtPrime p
  let Ip := I.map (algebraMap A Ap)
  let J : Ideal A := Ideal.span {algebraMap R A r}
  have hJ : J ≤ p := (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hi)).trans hp
  have hπ : J.map (algebraMap A Ap) = Ideal.span {algebraMap R Ap r} := by
    rw [Ideal.map_span, Set.image_singleton, ← IsScalarTower.algebraMap_apply R A Ap]
  let : Module.Flat A Ap := IsLocalization.flat Ap p.primeCompl
  let : Module.Flat R Ap := Module.Flat.trans R A Ap
  let : IsRegularLocalRing (Ap ⧸ J.map (algebraMap A Ap)) :=
    isRegularLocalRing_quotient_localization p J hJ
  let : IsRegularLocalRing (Ap ⧸ Ideal.span {algebraMap R Ap r}) :=
    IsRegularLocalRing.of_ringEquiv (Ideal.quotEquivOfEq hπ)
  let : IsRegularLocalRing (Ap ⧸ Ip) := isRegularLocalRing_quotient_localization p I hp
  have hi' : algebraMap R Ap r ∈ Ip := by
    rw [IsScalarTower.algebraMap_apply R A Ap]
    exact Ideal.mem_map_of_mem _ hi
  obtain ⟨xs, hgen, hxs⟩ := exists_lifted_regular_generators (algebraMap R Ap r) Ip hi'
  exact ⟨xs.length, ⟨
    (blowupResidueLocalizationEquiv hr.ne_zero I p.primeCompl).trans
      (blowupResidueEquivPolynomial hr Ip xs hgen hxs)⟩⟩

include hr hi in
/-- Every field-valued fibre of the special fibre over the centre has a polynomial
coordinate ring over the test field. -/
theorem exists_blowupResidue_fieldEquiv (F : Type u) [Field F] [Algebra (A ⧸ I) F] :
    ∃ n : ℕ, Nonempty (F ⊗[A ⧸ I] blowupResidue r I ≃ₐ[F] MvPolynomial (Fin n) F) := by
  let Q := A ⧸ I
  let q := RingHom.ker (algebraMap Q F)
  let : q.IsPrime := RingHom.ker_isPrime _
  let Qp := centreLocalRing I q
  let : IsLocalization.AtPrime Qp q := centreLocalRing_isLocalization I q
  obtain ⟨n, ⟨e⟩⟩ := exists_blowupResidue_localEquiv hr I hi q
  let f : Qp →ₐ[Q] F := IsLocalization.liftAlgHom (M := q.primeCompl)
    (f := Algebra.ofId Q F) (fun a => isUnit_iff_ne_zero.mpr a.property)
  let : Algebra Qp F := f.toRingHom.toAlgebra
  let : IsScalarTower Q Qp F := IsScalarTower.of_algHom f
  exact ⟨n, ⟨(Algebra.TensorProduct.cancelBaseChange Q Qp F F (blowupResidue r I)).symm.trans
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : F ≃ₐ[F] F) e).trans
      (MvPolynomial.algebraTensorAlgEquiv Qp F))⟩⟩

include hr hi in
private theorem blowupResidue_flat : Module.Flat (A ⧸ I) (blowupResidue r I) := by
  let Q := A ⧸ I
  let C := blowupResidue r I
  change Module.Flat Q C
  apply Module.flat_of_localized_maximal
  intro q hq
  let Qp := centreLocalRing I q
  let : IsLocalization.AtPrime Qp q := centreLocalRing_isLocalization I q
  obtain ⟨n, ⟨e⟩⟩ := exists_blowupResidue_localEquiv hr I hi q
  exact flat_localized_of_polynomial (Q := Q) (Qp := Qp) (C := C) q.primeCompl e

include hr hi in
/-- With regular special-fibre and centre coordinate rings, the special fibre
of the dilatation is smooth over the centre. -/
theorem blowupResidue_smooth [Algebra.FiniteType R A] :
    Algebra.Smooth (A ⧸ I) (blowupResidue r I) := by
  let Q := A ⧸ I
  let C := blowupResidue r I
  let : IsScalarTower R Q C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Algebra.FiniteType Q C := Algebra.FiniteType.of_restrictScalars_finiteType R Q C
  let : Algebra.FinitePresentation Q C :=
    (Algebra.FinitePresentation.of_finiteType (R := Q) (A := C)).mp inferInstance
  let : Module.Flat Q C := blowupResidue_flat hr I hi
  exact Algebra.Smooth.of_formallySmooth_fiber (R := Q) (S := C) (by
    intro p hp
    exact formallySmooth_of_polynomial_fibre p
      (exists_blowupResidue_fieldEquiv hr I hi p.ResidueField))

include hr hi in
/-- The special fibre of the dilatation is geometrically connected over the centre
when its original special-fibre and centre coordinate rings are regular. -/
theorem blowupResidue_geometricallyConnected :
    GeometricallyConnected (Spec.algebraMap (A ⧸ I) (blowupResidue r I)) :=
  geometricallyConnected_of_polynomial_fibres (Q := A ⧸ I) (C := blowupResidue r I)
    (fun F _ _ => exists_blowupResidue_fieldEquiv hr I hi F)

end Geometry

end Langlands.GroupScheme.Dilatation
