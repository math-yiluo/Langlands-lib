import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.TensorProduct.Maps

universe u

open Set TopologicalSpace CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

/-- Tensor products compute irreducibility of actual affine field pullbacks. -/
theorem irreducibleSpace_pullbackSpec_iff_nilradical_isPrime
    (R B K : Type u) [CommRing R] [CommRing B] [CommRing K]
    [Algebra R B] [Algebra R K] :
    IrreducibleSpace ↥(pullback (Spec.map (CommRingCat.ofHom (algebraMap R B)))
      (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ↔
        (nilradical (K ⊗[R] B)).IsPrime := by
  let e := pullbackSymmetry (Spec.map (CommRingCat.ofHom (algebraMap R B)))
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≪≫ pullbackSpecIso R K B
  exact e.hom.homeomorph.irreducibleSpace_iff.trans
    PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical

/-- An affine morphism is geometrically irreducible exactly when all its field
scalar extensions have prime nilradical. -/
theorem geometricallyIrreducible_specMap_iff
    (R B : Type u) [CommRing R] [CommRing B] [Algebra R B] :
    GeometricallyIrreducible (Spec.map (CommRingCat.ofHom (algebraMap R B))) ↔
      ∀ (K : Type u) [Field K] [Algebra R K],
        (nilradical (K ⊗[R] B)).IsPrime := by
  rw [GeometricallyIrreducible.eq_geometrically,
    geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  exact forall_congr' fun K => forall_congr' fun _ => forall_congr' fun _ =>
    irreducibleSpace_pullbackSpec_iff_nilradical_isPrime R B K

/-- The actual scheme generic-fibre hypothesis supplies the algebraic hypothesis
used by affine spreading, with the ideal residue field and its algebraic closure. -/
theorem nilradical_isPrime_algebraicClosure_tensor_of_generic_fiber
    (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
    [(nilradical R).IsPrime]
    (hgeneric : GeometricallyIrreducible
      ((Spec.map (CommRingCat.ofHom (algebraMap R B))).fiberToSpecResidueField
        ⟨nilradical R, inferInstance⟩)) :
    (nilradical (AlgebraicClosure (nilradical R).ResidueField ⊗[R] B)).IsPrime := by
  let p : PrimeSpectrum R := ⟨nilradical R, inferInstance⟩
  have hgeom : GeometricallyIrreducible
      (Spec.map (CommRingCat.ofHom (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber B)))) :=
    ⟨(MorphismProperty.arrow_mk_iso_iff (geometrically (IrreducibleSpace ·))
      (Spec.fiberToSpecResidueFieldIso R B p)).mp hgeneric.geometrically_irreducibleSpace⟩
  have hdouble := (geometricallyIrreducible_specMap_iff p.asIdeal.ResidueField
    (p.asIdeal.Fiber B)).mp hgeom (AlgebraicClosure p.asIdeal.ResidueField)
  have hirr : IrreducibleSpace
      (Spec (.of (AlgebraicClosure p.asIdeal.ResidueField ⊗[p.asIdeal.ResidueField]
        (p.asIdeal.Fiber B)))) :=
    PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.mpr hdouble
  let e := ((Algebra.TensorProduct.cancelBaseChange R p.asIdeal.ResidueField
      (AlgebraicClosure p.asIdeal.ResidueField) (AlgebraicClosure p.asIdeal.ResidueField) B).toRingEquiv).toCommRingCatIso
  apply PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.mp
  exact (Scheme.Spec.mapIso e.op).hom.homeomorph.irreducibleSpace_iff.mpr hirr

/-- The generic point of a whole affine scheme is its prime nilradical. -/
theorem asIdeal_eq_nilradical_of_isGenericPoint
    {R : Type u} [CommRing R] {η : PrimeSpectrum R}
    (hη : IsGenericPoint η univ) : η.asIdeal = nilradical R := by
  change closure {η} = univ at hη
  calc
    η.asIdeal = PrimeSpectrum.vanishingIdeal (closure {η}) := by
      rw [PrimeSpectrum.vanishingIdeal_closure, PrimeSpectrum.vanishingIdeal_singleton]
    _ = nilradical R := by rw [hη, PrimeSpectrum.vanishingIdeal_univ]

/-- A nonnilpotent scalar defines an open neighbourhood of the generic point. -/
theorem genericPoint_mem_basicOpen_iff
    {R : Type u} [CommRing R] {η : PrimeSpectrum R}
    (hη : IsGenericPoint η univ) (c : R) :
    η ∈ PrimeSpectrum.basicOpen c ↔ ¬ IsNilpotent c := by
  change c ∉ η.asIdeal ↔ _
  rw [asIdeal_eq_nilradical_of_isGenericPoint hη, mem_nilradical]

/-- The affine generic-fibre comparison also applies to an arbitrary point
generic for the whole spectrum. -/
theorem nilradical_isPrime_algebraicClosure_tensor_of_isGenericPoint
    (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
    (η : PrimeSpectrum R) (hη : IsGenericPoint η univ)
    (hgeneric : GeometricallyIrreducible
      ((Spec.map (CommRingCat.ofHom (algebraMap R B))).fiberToSpecResidueField η)) :
    letI : (nilradical R).IsPrime :=
      asIdeal_eq_nilradical_of_isGenericPoint hη ▸ η.isPrime
    (nilradical (AlgebraicClosure (nilradical R).ResidueField ⊗[R] B)).IsPrime := by
  let : (nilradical R).IsPrime :=
    asIdeal_eq_nilradical_of_isGenericPoint hη ▸ η.isPrime
  have heq : η = ⟨nilradical R, inferInstance⟩ :=
    PrimeSpectrum.ext (asIdeal_eq_nilradical_of_isGenericPoint hη)
  apply nilradical_isPrime_algebraicClosure_tensor_of_generic_fiber R B
  exact heq ▸ hgeneric

/-- An affine morphism missing the generic point vanishes over a principal
neighbourhood. No finiteness assumption is needed for this step. -/
theorem exists_basicOpen_preimage_eq_bot_of_not_mem_range
    {R B : Type u} [CommRing R] [CommRing B] (φ : R →+* B)
    (η : PrimeSpectrum R) (hη : IsGenericPoint η univ)
    (hmiss : η ∉ Set.range (PrimeSpectrum.comap φ)) :
    ∃ c : R, η ∈ PrimeSpectrum.basicOpen c ∧
      (Spec.map (CommRingCat.ofHom φ)) ⁻¹ᵁ PrimeSpectrum.basicOpen c = ⊥ := by
  have hker : ¬ RingHom.ker φ ≤ η.asIdeal := by
    intro hle
    have hminimal : η.asIdeal ∈ (Ideal.comap φ ⊥).minimalPrimes := by
      refine ⟨⟨η.isPrime, hle⟩, fun q hq _ => ?_⟩
      rw [asIdeal_eq_nilradical_of_isGenericPoint hη]
      let := hq.1
      exact nilradical_le_prime q
    obtain ⟨q, hq, -, heq⟩ :=
      Ideal.exists_comap_eq_of_mem_minimalPrimes φ η.asIdeal hminimal
    exact hmiss ⟨⟨q, hq⟩, PrimeSpectrum.ext heq⟩
  obtain ⟨c, hc, hcη⟩ := Set.not_subset.mp hker
  refine ⟨c, hcη, ?_⟩
  change PrimeSpectrum.basicOpen (φ c) = ⊥
  rw [RingHom.mem_ker.mp hc, PrimeSpectrum.basicOpen_zero]

/-- Universal field-tensor irreducibility away from a scalar is geometric
irreducibility of the actual principal-open restriction. -/
theorem geometricallyIrreducible_restrict_basicOpen_of_tensor
    (R B : Type u) [CommRing R] [CommRing B] [Algebra R B] (c : R)
    (h : ∀ (K : Type u) [Field K] (φ : R →+* K), φ c ≠ 0 →
      let : Algebra R K := φ.toAlgebra
      (nilradical (K ⊗[R] B)).IsPrime) :
    GeometricallyIrreducible
      (Spec.map (CommRingCat.ofHom (algebraMap R B)) ∣_ PrimeSpectrum.basicOpen c) := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap R B))
  let V : (Spec (.of R)).Opens := PrimeSpectrum.basicOpen c
  refine ⟨fun K _ y Z fst snd hpb => ?_⟩
  let φ : R →+* K := (Spec.preimage (y ≫ V.ι)).hom
  have hφ : Spec.map (CommRingCat.ofHom φ) = y ≫ V.ι := Spec.map_preimage _
  have hc : φ c ≠ 0 := by
    have hmem : (Spec.map (CommRingCat.ofHom φ)) (IsLocalRing.closedPoint K) ∈ V := by
      rw [hφ]
      exact (y (IsLocalRing.closedPoint K)).property
    change φ c ∉ (IsLocalRing.closedPoint K).asIdeal at hmem
    intro hc
    exact hmem (hc ▸ (IsLocalRing.closedPoint K).asIdeal.zero_mem)
  let : Algebra R K := φ.toAlgebra
  have hirr := (irreducibleSpace_pullbackSpec_iff_nilradical_isPrime R B K).mpr
    (h K φ hc)
  have hsquare : IsPullback (fst ≫ (f ⁻¹ᵁ V).ι) snd f (y ≫ V.ι) :=
    hpb.paste_horiz (isPullback_morphismRestrict f V).flip
  rw [← hφ] at hsquare
  exact hsquare.isoPullback.hom.homeomorph.irreducibleSpace_iff.mpr hirr

end Langlands.AlgebraicGeometry.SchemeFiberGeometry
