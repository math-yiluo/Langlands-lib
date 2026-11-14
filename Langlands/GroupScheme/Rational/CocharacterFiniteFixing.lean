import Langlands.GroupScheme.Absolute.CocharacterDescent
import Langlands.GroupScheme.Lie.GroupAlgebraCoordinates
import Langlands.GroupScheme.Rational.CorootRationalGaloisTransport

/-! # Cocharacters over an algebraic extension are fixed by a finite-index subgroup -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GaloisCocharacterDescent

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  (G : GroupScheme (Spec (CommRingCat.of k)))

/-- `universalValue_of_projection` for a cocharacter given with the type of a transported one.
Stating it for a variable keeps the kernel check of `universalValue_transport` cheap. -/
private theorem universalValue_of_projection'
    (σ : K ≃ₐ[k] K) (ν : (Gm (Spec (CommRingCat.of K))).toGrp ⟶
      (GroupScheme.baseChange (algebraBaseMap k K)).obj G)
    (ν' : (Gm (Spec (CommRingCat.of K))).toGrp ⟶
      (Over.pullback (algebraBaseMap k K)).mapGrp.obj G)
    (h : baseChangePointsEquiv (algebraBaseMap k K) G (Gm.relativeLaurent (CommRingCat.of K))
      (Gm.laurentPoint K ≫ ν'.hom.hom) =
      (descentTestIso (algebraBaseMap k K) (galoisBaseMap k K σ)
        (galoisBaseMap_over k K σ) (Gm.relativeLaurent (CommRingCat.of K))).hom ≫
      (Over.map (algebraBaseMap k K)).map (conjugateTest k K σ) ≫
      baseChangePointsEquiv (algebraBaseMap k K) G (Gm.relativeLaurent (CommRingCat.of K))
        (Gm.laurentPoint K ≫ ν.hom.hom)) :
    universalValue k K G ν' = Lie.affineMap G (conjugateAlg k K σ) (universalValue k K G ν) :=
  universalValue_of_projection k K G ν ν' σ h

/-- The universal value of a transported cocharacter is the conjugated universal value. -/
theorem universalValue_transport (σ : K ≃ₐ[k] K)
    (ν : (Gm (Spec (CommRingCat.of K))).toGrp ⟶
      (GroupScheme.baseChange (algebraBaseMap k K)).obj G) :
    universalValue k K G (transportCocharacter (algebraBaseMap k K) (galoisBaseMap k K σ)
        (galoisBaseMap_over k K σ) G ν) =
      Lie.affineMap G (conjugateAlg k K σ) (universalValue k K G ν) :=
  universalValue_of_projection' k K G σ ν _ (universalProjection_transport k K G ν σ)

variable [IsAffineHom G.X.hom]

/-- The Laurent coordinates of a transported cocharacter are the conjugated coordinates. -/
theorem coordinates_transport (σ : K ≃ₐ[k] K)
    (ν : (Gm (Spec (CommRingCat.of K))).toGrp ⟶
      (GroupScheme.baseChange (algebraBaseMap k K)).obj G) :
    coordinates k K G (transportCocharacter (algebraBaseMap k K) (galoisBaseMap k K σ)
        (galoisBaseMap_over k K σ) G ν) =
      (conjugateAlg k K σ).comp (coordinates k K G ν) :=
  (congrArg (Lie.pointCoordinates G) (universalValue_transport k K G σ ν)).trans
    (Lie.pointCoordinates_naturality G _ _)

/-- A cocharacter is determined by its Laurent coordinates. -/
theorem coordinates_injective : Function.Injective (coordinates k K G) := by
  intro ν ν' h
  have h1 : universalValue k K G ν = universalValue k K G ν' :=
    (Lie.pointCoordinates G).injective h
  rw [universalValue_eq, universalValue_eq] at h1
  have h2 := (cancel_epi _).1 h1
  have h3 := (baseChangePointsEquiv (algebraBaseMap k K) G _).injective h2
  have h4 : ν.hom.hom = ν'.hom.hom := by
    unfold Gm.laurentPoint at h3
    exact (cancel_epi _).1 h3
  apply Grp.hom_ext
  exact h4

/-- A cocharacter whose coordinates are fixed by `σ` is fixed by the transport along `σ`. -/
theorem transport_eq_of_coordinates (σ : K ≃ₐ[k] K)
    (ν : (Gm (Spec (CommRingCat.of K))).toGrp ⟶
      (GroupScheme.baseChange (algebraBaseMap k K)).obj G)
    (h : (conjugateAlg k K σ).comp (coordinates k K G ν) = coordinates k K G ν) :
    @Eq ((Gm (Spec (CommRingCat.of K))).toGrp ⟶
      (GroupScheme.baseChange (algebraBaseMap k K)).obj G)
      (transportCocharacter (algebraBaseMap k K) (galoisBaseMap k K σ)
        (galoisBaseMap_over k K σ) G ν) ν :=
  coordinates_injective k K G ((coordinates_transport k K G σ ν).trans h)

/-- Finitely many cocharacters have Laurent coordinates fixed by the fixing subgroup of one
finite intermediate field. -/
theorem exists_finite_fixing_coordinates [LocallyOfFiniteType G.X.hom]
    [Algebra.IsAlgebraic k K] {J : Type u} [Finite J]
    (ν : J → ((Gm (Spec (CommRingCat.of K))).toGrp ⟶
      (GroupScheme.baseChange (algebraBaseMap k K)).obj G)) :
    ∃ E : IntermediateField k K, FiniteDimensional k E ∧
      ∀ σ ∈ E.fixingSubgroup, ∀ j,
        (conjugateAlg k K σ).comp (coordinates k K G (ν j)) = coordinates k K G (ν j) := by
  classical
  let := Fintype.ofFinite J
  obtain ⟨s, hs⟩ := (Lie.coordinateAlgebraFiniteType G).out
  let t : Finset K := Finset.univ.biUnion fun j => s.biUnion fun a =>
    (coordinates k K G (ν j) a).coeff.support.image (coordinates k K G (ν j) a).coeff
  let E : IntermediateField k K := IntermediateField.adjoin k (t : Set K)
  refine ⟨E, IntermediateField.finiteDimensional_adjoin
    (fun x _ => Algebra.IsIntegral.isIntegral (R := k) x), ?_⟩
  intro σ hσ j
  apply AlgHom.ext_of_adjoin_eq_top hs
  intro a ha
  apply LaurentPolynomial.ext
  intro m
  change (LaurentGaloisDescent.conjugate k K σ (coordinates k K G (ν j) a)).coeff m = _
  rw [LaurentGaloisDescent.coeff_conjugate]
  by_cases hm : m ∈ (coordinates k K G (ν j) a).coeff.support
  · apply (IntermediateField.mem_fixingSubgroup_iff E σ).mp hσ
    apply IntermediateField.subset_adjoin
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, Finset.mem_biUnion.mpr
      ⟨a, ha, Finset.mem_image.mpr ⟨m, hm, rfl⟩⟩⟩
  · rw [Finsupp.notMem_support_iff.mp hm, map_zero]

/-- **Cocharacters are defined over a finite subextension, pointwise.** For finitely many
cocharacters `ν_j` of `G_K`, with `K/k` algebraic, there is a finite intermediate field `E` such
that every `σ ∈ Aut(K/E)` satisfies `σ(ν_j(t)) = ν_j(σ t)` on rational points. -/
theorem exists_finite_fixing_cocharacterValues [LocallyOfFiniteType G.X.hom]
    [Algebra.IsAlgebraic k K] {J : Type u} [Finite J]
    (ν : J → ((Gm (Spec (CommRingCat.of K))).toGrp ⟶
      (GroupScheme.baseChange (algebraBaseMap k K)).obj G)) :
    ∃ E : IntermediateField k K, FiniteDimensional k E ∧
      ∀ σ ∈ E.fixingSubgroup, ∀ j (t : Kˣ),
        GaloisPointComparison.rationalConjugate k K G σ
            (rationalCocharacterValue k K G (ν j) t) =
          rationalCocharacterValue k K G (ν j) (Units.map σ.toMonoidHom t) := by
  obtain ⟨E, hE, hfix⟩ := exists_finite_fixing_coordinates k K G ν
  refine ⟨E, hE, fun σ hσ j t => ?_⟩
  exact (rationalCocharacterValue_rationalConjugate k K G σ (ν j) t).trans
    (congrArg (fun x => rationalCocharacterValue k K G x (Units.map σ.toMonoidHom t))
      (transport_eq_of_coordinates k K G σ (ν j) (hfix σ hσ j)))

end Langlands.GroupScheme.GaloisCocharacterDescent
