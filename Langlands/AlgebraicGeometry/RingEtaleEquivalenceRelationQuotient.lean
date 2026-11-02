import Langlands.AlgebraicGeometry.GroupoidCoactionUniversal
import Mathlib.RingTheory.TensorProduct.Quotient

/-! # Restricting a ring étale equivalence relation to an invariant ideal -/

universe u

namespace Langlands.AlgebraicGeometry

namespace RingEtaleEquivalenceRelation

variable {B C : Type u} [CommRing B] [CommRing C] [Algebra B C]
variable {t : B →+* C}

/-- The target map on the actual quotient rings. The source algebra is Mathlib's
canonical `Ideal.Quotient.algebraQuotientMapQuotient`. -/
def quotientTarget (I : Ideal B)
    (hI : I.map (algebraMap B C) = I.map t) :
    B ⧸ I →+* C ⧸ I.map (algebraMap B C) :=
  Ideal.quotientMap (I.map (algebraMap B C)) t
    (Ideal.map_le_iff_le_comap.mp hI.ge)

@[simp]
lemma quotientTarget_mk (I : Ideal B)
    (hI : I.map (algebraMap B C) = I.map t) (b : B) :
    quotientTarget I hI (Ideal.Quotient.mk I b) =
      Ideal.Quotient.mk (I.map (algebraMap B C)) (t b) := rfl

lemma quotientTarget_comp_mk (I : Ideal B)
    (hI : I.map (algebraMap B C) = I.map t) :
    (quotientTarget I hI).comp (Ideal.Quotient.mk I) =
      (Ideal.Quotient.mk (I.map (algebraMap B C))).comp t := rfl

lemma quotientSource_comp_mk (I : Ideal B) :
    (algebraMap (B ⧸ I) (C ⧸ I.map (algebraMap B C))).comp (Ideal.Quotient.mk I) =
      (Ideal.Quotient.mk (I.map (algebraMap B C))).comp (algebraMap B C) := rfl

omit [Algebra B C] in
/-- Étaleness passes to the quotient map by the extended ideal. This is the
usual quotient base change, through the actual tensor quotient equivalence. -/
lemma etale_quotientMap (f : B →+* C) (hf : f.Etale) (I : Ideal B) :
    (Ideal.quotientMap (I.map f) f Ideal.le_comap_map).Etale := by
  let : Algebra B C := f.toAlgebra
  let : Algebra.Etale B C := hf.toAlgebra
  change (algebraMap (B ⧸ I) (C ⧸ I.map (algebraMap B C))).Etale
  apply RingHom.etale_algebraMap.mpr
  exact Algebra.Etale.of_equiv
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor C I).symm

omit [Algebra B C] in
lemma etale_quotientMap_of_eq (f : B →+* C) (hf : f.Etale)
    (I : Ideal B) (J : Ideal C) (hJ : I.map f = J) :
    (Ideal.quotientMap J f (Ideal.map_le_iff_le_comap.mp hJ.le)).Etale := by
  subst J
  exact etale_quotientMap f hf I

lemma etale_quotientSource (hE : RingEtaleEquivalenceRelation t) (I : Ideal B) :
    (algebraMap (B ⧸ I) (C ⧸ I.map (algebraMap B C))).Etale :=
  etale_quotientMap (algebraMap B C) hE.etale_algebraMap I

lemma etale_quotientTarget (hE : RingEtaleEquivalenceRelation t) (I : Ideal B)
    (hI : I.map (algebraMap B C) = I.map t) :
    (quotientTarget I hI).Etale :=
  etale_quotientMap_of_eq t hE.etale_t I (I.map (algebraMap B C)) hI.symm

/-- A ring-valued point whose source factors through `B/I` factors through
the actual relation quotient `C/s(I)`. -/
def quotientPoint (I : Ideal B) {T : Type u} [CommRing T]
    (φ : C →+* T) (a : B ⧸ I →+* T)
    (hs : φ.comp (algebraMap B C) = a.comp (Ideal.Quotient.mk I)) :
    C ⧸ I.map (algebraMap B C) →+* T :=
  Ideal.Quotient.lift (I.map (algebraMap B C)) φ (by
    have hker : I.map (algebraMap B C) ≤ RingHom.ker φ := by
      apply Ideal.map_le_iff_le_comap.mpr
      intro b hb
      change φ (algebraMap B C b) = 0
      have h := congrArg (fun f : B →+* T => f b) hs
      change φ (algebraMap B C b) = a (Ideal.Quotient.mk I b) at h
      rw [h, Ideal.Quotient.eq_zero_iff_mem.mpr hb, map_zero]
    exact fun c hc => hker hc)

@[simp]
lemma quotientPoint_mk (I : Ideal B) {T : Type u} [CommRing T]
    (φ : C →+* T) (a : B ⧸ I →+* T)
    (hs : φ.comp (algebraMap B C) = a.comp (Ideal.Quotient.mk I)) (c : C) :
    quotientPoint I φ a hs (Ideal.Quotient.mk (I.map (algebraMap B C)) c) = φ c := rfl

lemma quotientPoint_comp_source (I : Ideal B) {T : Type u} [CommRing T]
    (φ : C →+* T) (a : B ⧸ I →+* T)
    (hs : φ.comp (algebraMap B C) = a.comp (Ideal.Quotient.mk I)) :
    (quotientPoint I φ a hs).comp
      (algebraMap (B ⧸ I) (C ⧸ I.map (algebraMap B C))) = a := by
  apply Ideal.Quotient.ringHom_ext
  ext b
  exact congrArg (fun f : B →+* T => f b) hs

lemma quotientPoint_comp_target (I : Ideal B)
    (hI : I.map (algebraMap B C) = I.map t) {T : Type u} [CommRing T]
    (φ : C →+* T) (a a' : B ⧸ I →+* T)
    (hs : φ.comp (algebraMap B C) = a.comp (Ideal.Quotient.mk I))
    (ht : φ.comp t = a'.comp (Ideal.Quotient.mk I)) :
    (quotientPoint I φ a hs).comp (quotientTarget I hI) = a' := by
  apply Ideal.Quotient.ringHom_ext
  ext b
  exact congrArg (fun f : B →+* T => f b) ht

lemma quotient_adjoin_range_eq_top (hE : RingEtaleEquivalenceRelation t)
    (I : Ideal B) (hI : I.map (algebraMap B C) = I.map t) :
    Algebra.adjoin (B ⧸ I) (Set.range (quotientTarget I hI)) = ⊤ := by
  apply top_unique
  intro c htop
  clear htop
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
  have hc : c ∈ Algebra.adjoin B (Set.range t) := by
    rw [hE.adjoin_range_eq_top]
    trivial
  induction hc using Algebra.adjoin_induction with
  | mem c hc =>
    obtain ⟨b, rfl⟩ := hc
    exact Algebra.subset_adjoin
      ⟨Ideal.Quotient.mk I b, quotientTarget_mk I hI b⟩
  | algebraMap b =>
    exact (Algebra.adjoin (B ⧸ I) (Set.range (quotientTarget I hI))).algebraMap_mem
      (Ideal.Quotient.mk I b)
  | add x y hx hy hx' hy' =>
    simpa only [map_add] using add_mem hx' hy'
  | mul x y hx hy hx' hy' =>
    simpa only [map_mul] using mul_mem hx' hy'

/-- Restriction of the actual ring relation to an ideal whose source and
target extensions agree. Both rings and both maps are the ordinary quotients. -/
theorem quotient (hE : RingEtaleEquivalenceRelation t)
    (I : Ideal B) (hI : I.map (algebraMap B C) = I.map t) :
    RingEtaleEquivalenceRelation (quotientTarget I hI) where
  adjoin_range_eq_top := quotient_adjoin_range_eq_top hE I hI
  refl T _ a := by
    obtain ⟨φ, ht, hs⟩ := hE.refl T (a.comp (Ideal.Quotient.mk I))
    exact ⟨quotientPoint I φ a hs,
      quotientPoint_comp_target I hI φ a a hs ht,
      quotientPoint_comp_source I φ a hs⟩
  symm T _ φ := by
    let qC := Ideal.Quotient.mk (I.map (algebraMap B C))
    let s' := algebraMap (B ⧸ I) (C ⧸ I.map (algebraMap B C))
    obtain ⟨ψ, ht, hs⟩ := hE.symm T (φ.comp qC)
    have hs' : ψ.comp (algebraMap B C) =
        (φ.comp (quotientTarget I hI)).comp (Ideal.Quotient.mk I) := by
      exact hs
    have ht' : ψ.comp t = (φ.comp s').comp (Ideal.Quotient.mk I) := by
      exact ht
    exact ⟨quotientPoint I ψ (φ.comp (quotientTarget I hI)) hs',
      quotientPoint_comp_target I hI ψ _ _ hs' ht',
      quotientPoint_comp_source I ψ _ hs'⟩
  trans T _ φ ψ h := by
    let qC := Ideal.Quotient.mk (I.map (algebraMap B C))
    let s' := algebraMap (B ⧸ I) (C ⧸ I.map (algebraMap B C))
    have h' : (φ.comp qC).comp (algebraMap B C) = (ψ.comp qC).comp t := by
      have hh := congrArg (fun f => f.comp (Ideal.Quotient.mk I)) h
      simpa only [RingHom.comp_assoc, quotientSource_comp_mk,
        quotientTarget_comp_mk, qC] using hh
    obtain ⟨χ, ht, hs⟩ := hE.trans T (φ.comp qC) (ψ.comp qC) h'
    have hs' : χ.comp (algebraMap B C) =
        (ψ.comp s').comp (Ideal.Quotient.mk I) := by
      exact hs
    have ht' : χ.comp t =
        (φ.comp (quotientTarget I hI)).comp (Ideal.Quotient.mk I) := by
      exact ht
    exact ⟨quotientPoint I χ (ψ.comp s') hs',
      quotientPoint_comp_target I hI χ _ _ hs' ht',
      quotientPoint_comp_source I χ _ hs'⟩
  etale_algebraMap := etale_quotientSource hE I
  etale_t := etale_quotientTarget hE I hI

end RingEtaleEquivalenceRelation

end Langlands.AlgebraicGeometry
