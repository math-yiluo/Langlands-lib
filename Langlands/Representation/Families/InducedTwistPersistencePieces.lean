import Langlands.Representation.Families.InducedTwistPersistenceAlgebra
import Langlands.Representation.Exponents.LeviJacquetInductionSupercuspidalFiltrationProof
import Langlands.Representation.Exponents.LeviNormalizerQuotientProof
import Langlands.Representation.Exponents.RepresentedCuspidalProjection
import Langlands.Representation.Filtration.SimpleSubquotientFactorProof
import Langlands.Representation.Classification.SupercuspidalSupport
import Langlands.Representation.Aubert.General.RationalRootAssociationCuspidalityTransport
import Langlands.GroupScheme.InnerAutomorphismHom
import Langlands.GroupScheme.Rational.ParabolicPointConjugation
import Langlands.Representation.Exponents.ArbitraryParabolicTemperedAmbientTransport

/-! # Irreducible subquotients of `r_{R'} i_R` of a supercuspidal representation

For actual parabolics `R` and `R'` of `G` with the same Levi `L`, and a supercuspidal
irreducible `τ` of `L(k)`, the published Renard VI.5.3 (iii) filtration of
`X = r_{R'}(i_R τ)` has irreducible factors, conjugates of `τ` by elements normalizing `L`.
Hence `X` has finite length, `X` is supercuspidal, and every irreducible subquotient of `X` is
equivalent to such a conjugate. Modulo `L(k)`, the conjugating elements range over the
finite set of representatives of `N_G(L)(k)/L(k)` given by Renard V.4.3.3.
-/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.InducedTwistPersistence

open Langlands.Aubert.General Langlands.Aubert.General.RepresentedParabolic GroupScheme

section Conjugation

variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ]

/-- Pulling back along `e` and along `x ↦ e(m x m⁻¹)` gives equivalent representations. -/
def pullbackConjEquiv (τ : SmoothRep.{0, u, v} ℂ Γ) (e e' : Γ ≃ₜ* Γ) (m : Γ)
    (he' : ∀ x, e' x = e (m * x * m⁻¹)) :
    (SmoothRep.pullback e' τ).representation.Equiv (SmoothRep.pullback e τ).representation where
  toLinearMap := τ.representation (e m⁻¹)
  isIntertwining' x := by
    have h : τ.representation (e m⁻¹) * τ.representation (e (m * x * m⁻¹)) =
        τ.representation (e x) * τ.representation (e m⁻¹) := by
      rw [← map_mul, ← map_mul, ← map_mul, ← map_mul]
      congr 2
      group
    change τ.representation (e m⁻¹) * τ.representation (e' x) =
      τ.representation (e x) * τ.representation (e m⁻¹)
    rw [he']
    exact h
  invFun := τ.representation (e m)
  left_inv v := by
    have h : τ.representation (e m) * τ.representation (e m⁻¹) = 1 := by
      rw [← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one]
    exact LinearMap.congr_fun h v
  right_inv v := by
    have h : τ.representation (e m⁻¹) * τ.representation (e m) = 1 := by
      rw [← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one]
    exact LinearMap.congr_fun h v

end Conjugation

section Filtration

variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ]

/-- A smooth representation with a finite filtration whose graded pieces are equivalent to
given irreducible representations has finite length, and each of its irreducible
subquotients is equivalent to one of them. -/
theorem hasFiniteLength_and_classify_of_filtration {X : SmoothRep.{0, u, w} ℂ Γ} {m : ℕ}
    (s : ObjectRepFiltration (SmoothRep.toRep.obj X) m) (P : Fin m → SmoothRep.{0, u, v} ℂ Γ)
    (hP : ∀ i, (P i).IsIrreducible)
    (hs : ∀ i, Nonempty ((s.gradedRepresentation i).ρ.Equiv (P i).representation)) :
    X.HasFiniteLength ∧
      ∀ C : SmoothRep.{0, u, w} ℂ Γ, C.IsIrreducible → SmoothRep.IsSubquotient C X →
        ∃ i, Nonempty (C.representation.Equiv (P i).representation) := by
  have hsimple : s.HasSimpleFactors := by
    intro i
    obtain ⟨E⟩ := hs i
    exact (isIrreducible_iff_of_equiv E).mpr (hP i)
  refine ⟨hasFiniteLength_of_hasSimpleFactors s hsimple, ?_⟩
  intro C hC hCX
  obtain ⟨S, U, ⟨iso⟩⟩ := hCX
  obtain ⟨i, ⟨E⟩⟩ := simpleSubquotientFactor ℂ Γ X m s hsimple C S U hC
    ⟨SmoothRep.equivOfIso iso⟩
  obtain ⟨E'⟩ := hs i
  exact ⟨i, ⟨E.trans E'⟩⟩

end Filtration

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance persistencePiecesAmbientTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {L R R' NR NR' : GroupScheme (Spec (CommRingCat.of k))}
  (r : R ⟶ G) (lR : L ⟶ R) (nR : NR ⟶ R) (hr : IsParabolicSubgroup r)
  (hlR : IsRationalLeviSubgroup lR) (hnR : LeviSubgroup.IsGeometricUnipotentRadical nR)
  (hmulR : IsIso (subgroupMultiplication lR nR))
  (r' : R' ⟶ G) (lR' : L ⟶ R') (nR' : NR' ⟶ R') (hr' : IsParabolicSubgroup r')
  (hlR' : IsRationalLeviSubgroup lR') (hnR' : LeviSubgroup.IsGeometricUnipotentRadical nR')
  (hmulR' : IsIso (subgroupMultiplication lR' nR'))

set_option maxHeartbeats 1000000 in
/-- **Pieces.** For a supercuspidal irreducible `τ` of `L(k)`, the representation
`X = r_{R'}(i_R τ)` has finite length and is supercuspidal, and every irreducible
subquotient of `X` is equivalent to the pullback of `τ` along the point map of an
automorphism of `L` given by conjugation by an element of `G(k)`. -/
theorem pieces_of_supercuspidal (hG : IsConnectedReductive G) (hLevi : lR' ≫ r' = lR ≫ r)
    (τ : letI := leviPointTopology lR hlR; SmoothRep.{0, u, v} ℂ (rationalPoints L))
    (hτ : letI := leviPointTopology lR hlR; τ.IsIrreducible)
    (hsc : haveI := hlR.isConnectedReductive.isAffineHom
      letI := leviPointTopology lR hlR
      haveI := leviPoints_locallyCompactSpace r lR hr hlR
      haveI := leviPoints_nonarchimedeanGroup r lR hr hlR
      ∀ (P' L' U' : GroupScheme (Spec (CommRingCat.of k)))
        (p' : P' ⟶ L) (l' : L' ⟶ P') (u' : U' ⟶ P')
        (hp' : IsParabolicSubgroup p') (hl' : IsRationalLeviSubgroup l')
        (hu' : LeviSubgroup.IsGeometricUnipotentRadical u')
        (hmul' : IsIso (subgroupMultiplication l' u')),
        ¬ IsIso p' → Subsingleton ((jacquetFunctor p' l' u' hp' hu' hl' hmul').obj τ)) :
    haveI := hlR.isConnectedReductive.isAffineHom
    letI := leviPointTopology lR hlR
    haveI := leviPoints_locallyCompactSpace r lR hr hlR
    haveI := leviPoints_nonarchimedeanGroup r lR hr hlR
    let X := (leviJacquetFunctor.{u, max u v} r' lR' nR' hr' hnR' hlR' hmulR').obj
      ((leviInductionFunctor r lR nR hr hnR hlR hmulR).obj τ)
    X.HasFiniteLength ∧ IsSupercuspidal X ∧
      ∀ C : SmoothRep.{0, u, max u v} ℂ (rationalPoints L), C.IsIrreducible →
        SmoothRep.IsSubquotient C X →
          ∃ (z : rationalPoints G) (φ : L ≅ L) (e : rationalPoints L ≃ₜ* rationalPoints L),
            φ.hom ≫ lR ≫ r = lR ≫ r ≫ (G.innerIso z).hom ∧
            (∀ x, e x = rationalPoints.map φ.hom x) ∧
            Nonempty (C.representation.Equiv (SmoothRep.pullback e τ).representation) := by

  have := hlR.isConnectedReductive.isAffineHom
  let := leviPointTopology lR hlR
  have := leviPoints_locallyCompactSpace r lR hr hlR
  have := leviPoints_nonarchimedeanGroup r lR hr hlR
  have hconj : ∃ (g : rationalPoints G) (φ : L ≅ L),
      φ.hom ≫ lR' ≫ r' = lR ≫ r ≫ (G.innerIso g).hom :=
    ⟨1, Iso.refl L, by rw [innerIso_one_hom, Category.comp_id, Iso.refl_hom, Category.id_comp,
      hLevi]⟩
  obtain ⟨⟨m, c, z, φ, e, -, hφ, he, s, hs⟩, hX⟩ :=
    leviJacquetInductionSupercuspidalFiltration k G hG R L NR R' L NR'
      r lR nR hr hlR hnR hmulR r' lR' nR' hr' hlR' hnR' hmulR' hconj τ hsc
  obtain ⟨hfl, hcl⟩ := hasFiniteLength_and_classify_of_filtration s
    (fun i => SmoothRep.pullback (e i) τ)
    (fun i => (SmoothRep.isIrreducible_pullbackFunctor_obj_iff (e i) τ).mpr hτ) hs
  refine ⟨hfl, hX, ?_⟩
  intro C hC hCX
  obtain ⟨i, hi⟩ := hcl C hC hCX
  refine ⟨z i, φ i, e i, ?_, he i, hi⟩
  rw [hφ i, ← Category.assoc, hLevi, Category.assoc]

set_option maxHeartbeats 1000000 in
/-- **Pieces, normalizer form.** Given representatives `g j` of `N_G(L)(k)/L(k)` with
automorphisms `φ j` of `L` (Renard V.4.3.3), every irreducible subquotient of
`X = r_{R'}(i_R τ)` is equivalent to the pullback of `τ` along one of the finitely many
point maps of the `φ j`, which do not depend on `τ`. -/
theorem pieces_of_supercuspidal_normalizer (hG : IsConnectedReductive G)
    (hLevi : lR' ≫ r' = lR ≫ r) {n : ℕ} (g : Fin n → rationalPoints G) (φ : Fin n → (L ≅ L))
    (hφ : ∀ j, (φ j).hom ≫ lR ≫ r = lR ≫ r ≫ (G.innerIso (g j)).hom)
    (hg : ∀ (w : rationalPoints G) (φ' : L ≅ L),
      φ'.hom ≫ lR ≫ r = lR ≫ r ≫ (G.innerIso w).hom →
        ∃ (j : Fin n) (m : rationalPoints L), w = g j * rationalPoints.map (lR ≫ r) m)
    (τ : letI := leviPointTopology lR hlR; SmoothRep.{0, u, v} ℂ (rationalPoints L))
    (hτ : letI := leviPointTopology lR hlR; τ.IsIrreducible)
    (hsc : haveI := hlR.isConnectedReductive.isAffineHom
      letI := leviPointTopology lR hlR
      haveI := leviPoints_locallyCompactSpace r lR hr hlR
      haveI := leviPoints_nonarchimedeanGroup r lR hr hlR
      ∀ (P' L' U' : GroupScheme (Spec (CommRingCat.of k)))
        (p' : P' ⟶ L) (l' : L' ⟶ P') (u' : U' ⟶ P')
        (hp' : IsParabolicSubgroup p') (hl' : IsRationalLeviSubgroup l')
        (hu' : LeviSubgroup.IsGeometricUnipotentRadical u')
        (hmul' : IsIso (subgroupMultiplication l' u')),
        ¬ IsIso p' → Subsingleton ((jacquetFunctor p' l' u' hp' hu' hl' hmul').obj τ)) :
    haveI := hlR.isConnectedReductive.isAffineHom
    letI := leviPointTopology lR hlR
    haveI := leviPoints_locallyCompactSpace r lR hr hlR
    haveI := leviPoints_nonarchimedeanGroup r lR hr hlR
    let X := (leviJacquetFunctor.{u, max u v} r' lR' nR' hr' hnR' hlR' hmulR').obj
      ((leviInductionFunctor r lR nR hr hnR hlR hmulR).obj τ)
    X.HasFiniteLength ∧ IsSupercuspidal X ∧
      ∀ C : SmoothRep.{0, u, max u v} ℂ (rationalPoints L), C.IsIrreducible →
        SmoothRep.IsSubquotient C X →
          ∃ j, Nonempty (C.representation.Equiv
            (SmoothRep.pullback (ambientIsoPointsEquiv (φ j)) τ).representation) := by
  have := hlR.isConnectedReductive.isAffineHom
  let := leviPointTopology lR hlR
  have := leviPoints_locallyCompactSpace r lR hr hlR
  have := leviPoints_nonarchimedeanGroup r lR hr hlR
  obtain ⟨hfl, hX, hcl⟩ := pieces_of_supercuspidal r lR nR hr hlR hnR hmulR r' lR' nR' hr' hlR'
    hnR' hmulR' hG hLevi τ hτ hsc
  refine ⟨hfl, hX, ?_⟩
  intro C hC hCX
  obtain ⟨z, φ', e', hφ', he', ⟨E⟩⟩ := hcl C hC hCX
  obtain ⟨j, m, rfl⟩ := hg _ φ' hφ'
  have hinj : Function.Injective (rationalPoints.map (lR ≫ r)) := by
    intro x y hxy
    apply (leviPointsEquiv r lR hr hlR).injective
    exact Subtype.ext hxy
  refine ⟨j, ⟨E.trans (pullbackConjEquiv τ (ambientIsoPointsEquiv (φ j)) e' m ?_)⟩⟩
  intro x
  apply hinj
  rw [he', ambientIsoPointsEquiv_apply, ← pointMap_comp_apply, ← pointMap_comp_apply, hφ', hφ j]
  simp only [pointMap_comp_apply, rationalPoints_map_innerIso, MulEquiv.toMonoidHom_eq_coe,
    MonoidHom.coe_coe, MulAut.conj_apply, map_mul, map_inv, MulAut.mul_apply]

end Langlands.InducedTwistPersistence
