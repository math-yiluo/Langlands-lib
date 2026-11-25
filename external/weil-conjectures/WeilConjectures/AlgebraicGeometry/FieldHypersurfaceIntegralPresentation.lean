/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.Localization.FractionRing

import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.FieldTheory.SeparablyGenerated
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.Mathlib.RingTheory.LocalProperties.Reduced
import WeilConjectures.RingTheory.GenericIrreducibility

/-! # Integral hypersurface presentation of a separable function field

Source: Stacks Project, Tag 0559, separating generators in the first proof.
-/

@[expose] public section
universe u
open CategoryTheory Topology
namespace AlgebraicGeometry

open scoped TensorProduct in
private lemma finite_separating_basis_of_reduced_tensor
    (K F : Type u) [Field K] [Field F] [Algebra K F] [Algebra.EssFiniteType K F]
    (hredF : ∀ (E : Type u) [Field E] [Algebra K E], _root_.IsReduced (E ⊗[K] F)) :
    ∃ s : Finset F, IsTranscendenceBasis K ((↑) : s → F) ∧
      Algebra.IsSeparable (IntermediateField.adjoin K (s : Set F)) F := by
  classical
  obtain _ | ⟨p, hp, hpk⟩ := CharP.exists' K
  · exact exists_isTranscendenceBasis_and_isSeparable_of_perfectField K F
  have : ExpChar K p := .prime hp.out
  have hpow : ∀ s : Finset F,
      LinearIndepOn K _root_.id (s : Set F) →
        LinearIndepOn K (· ^ p) (s : Set F) := by
    let L := AlgebraicClosure K
    let : _root_.IsReduced (L ⊗[K] F) := hredF L
    let : Nontrivial (L ⊗[K] F) :=
      Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left
        K L F (algebraMap K F).injective
    let : CharP (L ⊗[K] F) p :=
      charP_of_injective_algebraMap (algebraMap K (L ⊗[K] F)).injective p
    intro s hs
    rw [linearIndepOn_finset_iff]
    intro c hc i hi
    have hroot (x : F) : ∃ r : L, r ^ p = algebraMap K L (c x) := by
      obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq
        (algebraMap K (AlgebraicClosure K) (c x)) (hp.out : p.Prime).pos
      exact ⟨r, hr⟩
    choose r hr using hroot
    have hz : (∑ x ∈ s, r x ⊗ₜ[K] x : L ⊗[K] F) ^ p = 0 := by
      rw [sum_pow_char]
      have heq : (∑ x ∈ s, (r x ⊗ₜ[K] x : L ⊗[K] F) ^ p) =
          ∑ x ∈ s, (r x ^ p) ⊗ₜ[K] (x ^ p) := by
        apply Finset.sum_congr rfl
        intro x hx
        exact Algebra.TensorProduct.tmul_pow (R := K) (r x) x p
      rw [heq]
      simp_rw [hr]
      have hterm (x : F) :
          (algebraMap K L (c x)) ⊗ₜ[K] (x ^ p) = (1 : L) ⊗ₜ[K] (c x • x ^ p) := by
        rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
      simp_rw [hterm]
      rw [← TensorProduct.tmul_sum, hc, TensorProduct.tmul_zero]
    have hz' : (∑ x ∈ s, r x ⊗ₜ[K] x : L ⊗[K] F) = 0 :=
      _root_.IsReduced.eq_zero _ ⟨p, hz⟩
    have hli : LinearIndependent L (fun x : s ↦ (1 : L) ⊗ₜ[K] (x : F)) :=
      Module.Flat.linearIndependent_one_tmul hs
    rw [← s.sum_attach (fun x ↦ r x ⊗ₜ[K] x)] at hz'
    have hsum : (∑ x : s, r x • ((1 : L) ⊗ₜ[K] (x : F))) = 0 := by
      simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one, Finset.attach_eq_univ] using hz'
    have hri : r i = 0 := (Fintype.linearIndependent_iff.mp hli) (fun x : s ↦ r x) hsum ⟨i, hi⟩
    apply (algebraMap K L).injective
    simpa [hri, zero_pow (hp.out : p.Prime).ne_zero] using (hr i).symm
  exact exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_essFiniteType
    p hp.out hpow


open scoped TensorProduct in
open CategoryTheory.Limits in
/-- The fraction field of an integral affine finite type geometrically reduced scheme
is finitely generated and has a finite separating transcendence basis over its base field.

Source: Stacks Project, Tag 0559, first proof; Tags 030W and 030Q.
Proof: Use the canonical identification of the sections of Spec K with K and the
pullback on sections to make B = Gamma(Y) a K-algebra. Since Y is affine and p is
locally of finite type, B is a finitely generated K-algebra. Integrality makes B a
domain. Localizing B at its nonzero elements gives L, a finitely generated field
extension of K (essentially finite type as an algebra). For each field extension E/K,
geometric reducedness says E tensor B is reduced, by the affine pullback formula.
The ring E tensor L is the localization of E tensor B at the images of the nonzero
elements of B, so is reduced. The geometric reducedness criterion for fields (030W)
therefore makes L/K separable. The separating transcendence basis theorem (030Q)
provides a separating transcendence basis; finite generation makes it finite, so
represent it as a finite subset of L. This includes the empty basis for an algebraic
extension and for L = K.
-/
private theorem finite_separating_basis_fractionRing_of_geometricallyReduced
    {K : Type u} [Field K] {Y : Scheme.{u}} [IsAffine Y] [IsIntegral Y]
    (p : Y ⟶ Spec (.of K)) [LocallyOfFiniteType p]
    (hred : GeometricallyReduced p) :
    letI : Algebra K Γ(Y, ⊤) :=
      (p.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra
    letI : Algebra K (FractionRing Γ(Y, ⊤)) := inferInstance
    Algebra.EssFiniteType K (FractionRing Γ(Y, ⊤)) ∧
      ∃ s : Finset (FractionRing Γ(Y, ⊤)),
        IsTranscendenceBasis K ((↑) : s → FractionRing Γ(Y, ⊤)) ∧
          Algebra.IsSeparable (IntermediateField.adjoin K (s : Set (FractionRing Γ(Y, ⊤))))
            (FractionRing Γ(Y, ⊤)) := by
  classical
  let B := Γ(Y, ⊤)
  let φ : K →+* B := p.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom
  let : Algebra K B := φ.toAlgebra
  let F := FractionRing B
  let : Algebra K F := inferInstance
  have : IsScalarTower K B F := by infer_instance
  have hft : φ.FiniteType :=
    (HasRingHomProperty.appTop (P := @LocallyOfFiniteType) p inferInstance).comp
      (RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv.surjective)
  have : Algebra.FiniteType K B := hft
  have hfg : Algebra.EssFiniteType K F := Algebra.EssFiniteType.comp K B F
  let := hfg
  have hgeom : GeometricallyReduced (Spec.map (CommRingCat.ofHom φ)) := by
    have hcomp : Y.isoSpec.inv ≫ p = Spec.map (CommRingCat.ofHom φ) := by
      rw [← Scheme.isoSpec_inv_naturality, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
      rfl
    rw [← hcomp, GeometricallyReduced.eq_geometrically]
    exact MorphismProperty.RespectsIso.precomp (geometrically IsReduced) Y.isoSpec.inv p
      hred.geometrically_isReduced
  have hredB (E : Type u) [Field E] [Algebra K E] : _root_.IsReduced (E ⊗[K] B) := by
    have : IsReduced (pullback (Spec.map (CommRingCat.ofHom φ))
        (Spec.map (CommRingCat.ofHom (algebraMap K E)))) :=
      hgeom.geometrically_isReduced _ _ _ (.of_hasPullback _ _)
    have : IsReduced (Spec (.of (B ⊗[K] E))) :=
      isReduced_of_isOpenImmersion (pullbackSpecIso K B E).inv
    have : _root_.IsReduced (B ⊗[K] E) := (affine_isReduced_iff _).mp ‹_›
    exact isReduced_of_injective (Algebra.TensorProduct.comm K E B)
      (Algebra.TensorProduct.comm K E B).injective
  have hredF (E : Type u) [Field E] [Algebra K E] : _root_.IsReduced (E ⊗[K] F) := by
    let := hredB E
    exact isReduced_tensorProduct_of_isLocalization (nonZeroDivisors B)
  refine ⟨hfg, ?_⟩
  exact finite_separating_basis_of_reduced_tensor K F hredF


open MvPolynomial in
private lemma hypersurface_of_separating_basis (L F : Type*) [Field L] [Field F]
    [Algebra L F] [Algebra.EssFiniteType L F] (s' : Finset F)
    (hs' : IsTranscendenceBasis L ((↑) : s' → F))
    (hsep : Algebra.IsSeparable (IntermediateField.adjoin L (s' : Set F)) F) :
    ∃ (r : ℕ) (v : Fin (r + 1) → F) (P : MvPolynomial (Fin (r + 1)) L),
      AlgebraicIndependent L (v ∘ Fin.succ) ∧ Irreducible P ∧ aeval v P = 0 ∧
      ∀ z : F, ∃ Q h : MvPolynomial (Fin (r + 1)) L, aeval v h ≠ 0 ∧ z * aeval v h = aeval v Q := by
  classical
  set r := s'.card
  let t : Fin r → F := Subtype.val ∘ s'.equivFin.symm
  have hrange : Set.range t = Set.range ((↑) : s' → F) := by
    rw [Set.range_comp, Equiv.range_eq_univ, Set.image_univ]
  have ht : AlgebraicIndependent L t := hs'.1.comp _ s'.equivFin.symm.injective
  set E := IntermediateField.adjoin L (Set.range ((↑) : s' → F))
  have halg : Algebra.IsAlgebraic E F := hs'.isAlgebraic_field
  have hsep' : Algebra.IsSeparable E F := by
    convert hsep <;> simp
  obtain ⟨G, hG⟩ := IntermediateField.fg_top L F
  have hfin : FiniteDimensional E F := by
    have h1 : IntermediateField.adjoin E (G : Set F) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have hx : x ∈ IntermediateField.adjoin L (G : Set F) := hG ▸ IntermediateField.mem_top
      exact (IntermediateField.adjoin_le_iff
        (T := (IntermediateField.adjoin E (G : Set F)).restrictScalars L)).mpr
        (IntermediateField.subset_adjoin E _) hx
    have := IntermediateField.finiteDimensional_adjoin (K := E) (S := (G : Set F))
      fun x _ ↦ (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
    rw [h1] at this
    exact IntermediateField.topEquiv.toLinearEquiv.finiteDimensional
  obtain ⟨y, hy⟩ := Field.exists_primitive_element E F
  let v : Fin (r + 1) → F := Fin.cons y t
  have hvt : v ∘ Fin.succ = t := by
    funext i
    simp [v]
  have hdep : ¬ AlgebraicIndependent L v := by
    intro h
    have := h.transcendental_adjoin (i := 0) (s := Set.range Fin.succ) (by simp)
    rw [← Set.range_comp, hvt, hrange] at this
    exact this ((IntermediateField.isAlgebraic_adjoin_iff).mp (Algebra.IsAlgebraic.isAlgebraic y))
  have hne : {P : MvPolynomial (Fin (r + 1)) L | P ≠ 0 ∧ aeval v P = 0}.Nonempty := by
    obtain ⟨P, hP⟩ : ∃ P, ¬P = 0 ∧ aeval v P = 0 := by
      simpa [algebraicIndependent_iff, and_comm] using hdep
    exact ⟨P, hP⟩
  set P := Function.argminOn totalDegree _ hne
  have hP : P ≠ 0 ∧ aeval v P = 0 := Function.argminOn_mem _ _ hne
  have hmin (P' : MvPolynomial (Fin (r + 1)) L) (h0 : P' ≠ 0) (h1 : aeval v P' = 0) :
      totalDegree P ≤ totalDegree P' :=
    Function.argminOn_le totalDegree {P : MvPolynomial (Fin (r + 1)) L | P ≠ 0 ∧ aeval v P = 0}
      (a := P') ⟨h0, h1⟩
  have htop : IntermediateField.adjoin L (Set.range v) = ⊤ := by
    have := IntermediateField.adjoin_adjoin_left L (Set.range ((↑) : s' → F)) {y}
    rw [hy, IntermediateField.restrictScalars_top] at this
    rw [this, Fin.range_cons, hrange, Set.union_singleton]
  refine ⟨r, v, P, hvt ▸ ht, MvPolynomial.irreducible_of_forall_totalDegree_le hmin hP.1 hP.2,
    hP.2, fun z ↦ ?_⟩
  have hz : z ∈ IntermediateField.adjoin L (Set.range v) := htop ▸ IntermediateField.mem_top
  obtain ⟨a, ha, b, hb, rfl⟩ := IntermediateField.mem_adjoin_iff_div.mp hz
  rw [Algebra.adjoin_range_eq_range_aeval] at ha hb
  obtain ⟨Q, rfl⟩ := ha
  obtain ⟨h, rfl⟩ := hb
  by_cases h0 : aeval v h = 0
  · exact ⟨0, 1, by simp, by simp [h0]⟩
  · exact ⟨Q, h, h0, div_mul_cancel₀ _ h0⟩

open MvPolynomial in
private lemma fraction_equiv_of_hypersurface
    {K F : Type u} [Field K] [Field F] [Algebra K F] {r : ℕ}
    (v : Fin (r + 1) → F) (hv : AlgebraicIndependent K (v ∘ Fin.succ))
    (Q : MvPolynomial (Fin (r + 1)) K) (hQ : Irreducible Q)
    (hQv : aeval v Q = 0)
    (hrep : ∀ z : F, ∃ a b : MvPolynomial (Fin (r + 1)) K,
      aeval v b ≠ 0 ∧ z * aeval v b = aeval v a) :
    IsDomain (MvPolynomial (Fin (r + 1)) K ⧸ Ideal.span {Q}) ∧
      Nonempty (FractionRing (MvPolynomial (Fin (r + 1)) K ⧸ Ideal.span {Q}) ≃ₐ[K] F) := by
  let I : Ideal (MvPolynomial (Fin (r + 1)) K) := Ideal.span {Q}
  have hI : I.IsPrime := (Ideal.span_singleton_prime hQ.ne_zero).mpr hQ.prime
  let := hI
  let A := MvPolynomial (Fin (r + 1)) K ⧸ I
  have hzero : ∀ a ∈ I, aeval v a = 0 := by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.mp ha
    simp [hQv]
  let f : A →ₐ[K] F := Ideal.Quotient.liftₐ I (aeval v) hzero
  have hf : Function.Injective f := by
    apply RingHom.lift_injective_of_ker_le_ideal I hzero
    intro a ha
    exact Ideal.mem_span_singleton.mpr
      (GenericIrreducibility.dvd_of_aeval_eq_zero v hv hQ hQv ha)
  let g : FractionRing A →ₐ[K] F := IsFractionRing.liftAlgHom hf
  have hg (a : MvPolynomial (Fin (r + 1)) K) :
      g (algebraMap A (FractionRing A) (Ideal.Quotient.mk I a)) = aeval v a := by
    change IsFractionRing.lift hf (algebraMap A (FractionRing A)
      (Ideal.Quotient.mk I a)) = aeval v a
    rw [IsFractionRing.lift_algebraMap]
    rfl
  have hsurj : Function.Surjective g := by
    intro z
    obtain ⟨a, b, hb, hz⟩ := hrep z
    refine ⟨algebraMap A (FractionRing A) (Ideal.Quotient.mk I a) /
      algebraMap A (FractionRing A) (Ideal.Quotient.mk I b), ?_⟩
    rw [map_div₀, hg, hg, ← hz, mul_div_cancel_right₀ _ hb]
  exact ⟨inferInstance, ⟨AlgEquiv.ofBijective g ⟨g.injective, hsurj⟩⟩⟩

/-- A geometrically reduced integral affine scheme of finite type over a field admits
an integral hypersurface presentation of its fraction field, over the base field.

Source: Stacks Project, Tag 0559, first proof, paragraphs on separating generators;
Tags 030W and 030Q (separability and separating generators).
Proof: Let B be the affine section algebra and L its fraction field. Integrality
makes B a domain. Finite type makes L finitely generated over K. Geometric
reducedness implies that L/K is separably generated: field base change commutes
with localization, and reducedness of the base-changed B passes to its localization.
Choose a separating transcendence basis t_1,...,t_r and a primitive element z for
L/K(t_1,...,t_r). Take the numerator of the monic minimal polynomial of z and
remove its content over the UFD K[t_1,...,t_r]. Gauss's lemma says its kernel of
evaluation in L is the principal ideal generated by this primitive polynomial Q.
Thus C = K[t_1,...,t_r,T]/(Q) injects in L, and its fraction field is L: it contains
the separating generators and is contained in L. Spec C is integral. The two
identifications of fraction fields with L fix K, so their composite fixes base
sections via the canonical section identification Gamma(Spec K)=K. If the finite
extension is trivial take Q=T and evaluate T at zero, including L=K. Nonemptiness
is supplied by integrality; no geometric irreducibility is used here.
(blueprint: lem-sbc-field-hypersurface-integral-presentation) -/
theorem exists_integral_field_hypersurface_presentation
    {K : Type u} [Field K] {Y : Scheme.{u}} [IsAffine Y] [IsIntegral Y]
    (p : Y ⟶ Spec (.of K)) [LocallyOfFiniteType p]
    (hred : GeometricallyReduced p) :
    ∃ (n : ℕ) (Q : MvPolynomial (Fin n) K),
      let Z := Spec (.of (MvPolynomial (Fin n) K ⧸ Ideal.span {Q}))
      let q : Z ⟶ Spec (.of K) := Spec.map (CommRingCat.ofHom
        ((Ideal.Quotient.mk (Ideal.span {Q})).comp MvPolynomial.C))
      IsIntegral Z ∧
        ∃ e : FractionRing Γ(Y, ⊤) ≃+* FractionRing Γ(Z, ⊤),
          ∀ a : Γ(Spec (.of K), ⊤),
            e (algebraMap Γ(Y, ⊤) (FractionRing Γ(Y, ⊤)) (p.appTop.hom a)) =
              algebraMap Γ(Z, ⊤) (FractionRing Γ(Z, ⊤)) (q.appTop.hom a) := by
  classical
  let B := Γ(Y, ⊤)
  let : Algebra K B :=
    (p.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra
  let F := FractionRing B
  let : Algebra K F := inferInstance
  obtain ⟨hfg, s, hs, hsep⟩ :=
    finite_separating_basis_fractionRing_of_geometricallyReduced p hred
  let := hfg
  obtain ⟨r, v, Q, hv, hQ, hQv, hrep⟩ := hypersurface_of_separating_basis K F s hs hsep
  obtain ⟨hA, ⟨e⟩⟩ := fraction_equiv_of_hypersurface v hv Q hQ hQv hrep
  let A := MvPolynomial (Fin (r + 1)) K ⧸ Ideal.span {Q}
  let := hA
  let : DistribMulAction A A := (Semiring.toModule : Module A A).toDistribMulAction
  let Z := Spec (.of A)
  let q : Z ⟶ Spec (.of K) := Spec.map (CommRingCat.ofHom
    ((Ideal.Quotient.mk (Ideal.span {Q})).comp MvPolynomial.C))
  let i : A ≃+* Γ(Z, ⊤) := (Scheme.ΓSpecIso (.of A)).symm.commRingCatIsoToRingEquiv
  let j : FractionRing A ≃+* FractionRing Γ(Z, ⊤) :=
    IsFractionRing.ringEquivOfRingEquiv i
  refine ⟨r + 1, Q, inferInstance, e.symm.toRingEquiv.trans j, ?_⟩
  intro a
  obtain ⟨c, rfl⟩ := (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv.surjective a
  change j (e.symm (algebraMap K F c)) = _
  rw [e.symm.commutes]
  change j (algebraMap A (FractionRing A) (algebraMap K A c)) = _
  rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  congr 1
  change (Scheme.ΓSpecIso (.of A)).inv.hom
      (((Ideal.Quotient.mk (Ideal.span {Q})).comp MvPolynomial.C) c) =
    q.appTop.hom ((Scheme.ΓSpecIso (.of K)).inv.hom c)
  exact congrArg (fun f : CommRingCat.of K ⟶ Γ(Z, ⊤) ↦ f.hom c)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom
      ((Ideal.Quotient.mk (Ideal.span {Q})).comp MvPolynomial.C)))

end AlgebraicGeometry
