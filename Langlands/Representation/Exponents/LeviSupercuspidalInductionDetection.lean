import Langlands.Representation.Exponents.LeviConjugateEmbedding
import Langlands.Representation.Exponents.LeviCuspidalEmbeddingProof
import Langlands.Representation.Exponents.LeviJacquetInductionNoSupercuspidalStatement
import Langlands.Representation.Exponents.LeviParabolicFunctorsExactProof
import Langlands.Representation.Exponents.ArbitraryParabolicConjugation
import Langlands.Representation.Filtration.ExactSmoothSubquotients
import Langlands.Representation.Filtration.SubquotientAlgebraProof
import Langlands.Automorphic.GroupSchemeParabolicRadicals

/-! # Detecting the irreducible subquotients of a supercuspidal induction

The first paragraph of the proof of Renard VI.5.4: every irreducible subquotient of
`i_P^G ρ`, with `ρ` supercuspidal, has a nonzero normalized Jacquet module along an actual
parabolic whose Levi is `G(k)`-conjugate to `M`, through VI.2.1 (proved) and VI.5.3 (ii).
Also the transport of nontriviality of Jacquet modules between conjugate parabolics.
-/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

section Ranges

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}

/-- The range of a subgroup map followed by an ambient isomorphism is the
preimage of the original range under the inverse isomorphism. -/
theorem range_comp_iso_hom_eq_comap {H : GroupScheme (Spec (CommRingCat.of k))}
    (j : H ⟶ G) (e : G ≅ G) :
    SubgroupFunctor.range (j ≫ e.hom) = (SubgroupFunctor.range j).comap e.inv := by
  ext T x
  rw [SubgroupFunctor.mem_comap, SubgroupFunctor.mem_range, SubgroupFunctor.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨y, ?_⟩
    rw [Grp.comp_hom_hom, Category.assoc, Category.assoc, ← Grp.comp_hom_hom e.hom e.inv,
      Iso.hom_inv_id, Grp.id_hom_hom, Category.comp_id]
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    rw [Grp.comp_hom_hom, ← Category.assoc, hy, Category.assoc, ← Grp.comp_hom_hom e.inv e.hom,
      Iso.inv_hom_id, Grp.id_hom_hom, Category.comp_id]

/-- Two subgroup maps whose ranges are conjugates of one subgroup functor `Y` by
rational points are conjugate to each other. -/
theorem range_eq_range_comp_innerIso_of_comap
    {H H' : GroupScheme (Spec (CommRingCat.of k))} (j : H ⟶ G) (j' : H' ⟶ G)
    (Y : SubgroupFunctor G) (g g' : rationalPoints G)
    (h : SubgroupFunctor.range j = Y.comap (G.innerIso g).hom)
    (h' : SubgroupFunctor.range j' = Y.comap (G.innerIso g').hom) :
    SubgroupFunctor.range j' = SubgroupFunctor.range (j ≫ (G.innerIso (g'⁻¹ * g)).hom) := by
  rw [range_comp_iso_hom_eq_comap, h, ← SubgroupFunctor.comap_comp, h',
    ← innerIso_inv_hom, ← innerIso_mul_hom]
  congr 2
  group

end Ranges

section Transport

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance detectionAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]

/-- Nontriviality of the actual normalized Jacquet carrier depends only on the
`G(k)`-conjugacy class of the parabolic subgroup functor: a second represented
parabolic whose range is the conjugate by `g` of the first has a nonzero Jacquet
module whenever the first does. The Levi and radical presentations may differ. -/
theorem nontrivial_leviJacquet_of_range_eq_comp_innerIso
    {Q L U Q' L' U' : GroupScheme (Spec (CommRingCat.of k))}
    (q : Q ⟶ G) (lQ : L ⟶ Q) (rQ : U ⟶ Q)
    (hq : IsParabolicSubgroup q) (hlQ : IsRationalLeviSubgroup lQ)
    (hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ)
    (hmulQ : IsIso (subgroupMultiplication lQ rQ))
    (q' : Q' ⟶ G) (lQ' : L' ⟶ Q') (rQ' : U' ⟶ Q')
    (hq' : IsParabolicSubgroup q') (hlQ' : IsRationalLeviSubgroup lQ')
    (hrQ' : LeviSubgroup.IsGeometricUnipotentRadical rQ')
    (hmulQ' : IsIso (subgroupMultiplication lQ' rQ'))
    (g : rationalPoints G)
    (hrange : SubgroupFunctor.range q' = SubgroupFunctor.range (q ≫ (G.innerIso g).hom))
    (A : SmoothRep.{0, u, w} ℂ (rationalPoints G)) :
    letI := leviPointTopology lQ hlQ
    letI := leviPointTopology lQ' hlQ'
    Nontrivial ((leviJacquetFunctor q lQ rQ hq hrQ hlQ hmulQ).obj A) →
      Nontrivial ((leviJacquetFunctor q' lQ' rQ' hq' hrQ' hlQ' hmulQ').obj A) := by
  let := leviPointTopology lQ hlQ
  let := leviPointTopology lQ' hlQ'
  intro hA
  have hrad : SubgroupFunctor.range (rQ ≫ (q ≫ (G.innerIso g).hom)) =
      SubgroupFunctor.range (rQ' ≫ q') :=
    Automorphic.GroupSchemeFunctions.parabolicRadical_range_eq
      (hq.comp_iso (G.innerIso g)).isClosedSubgroup hq'.isClosedSubgroup hrange.symm
      hrQ.1 hrQ'.1
  have hN : ∀ x : rationalPoints G,
      x ∈ pointImage (rQ' ≫ q') ↔ g⁻¹ * x * g ∈ pointImage (rQ ≫ q) := by
    intro x
    rw [pointImage_eq_range_carrier (rQ' ≫ q'), ← hrad, ← pointImage_eq_range_carrier]
    simpa only [Category.assoc] using mem_pointImage_comp_innerIso (rQ ≫ q) g x
  have : Nontrivial (Jacquet.Localization.Coinvariants A.representation
      (pointImage (rQ ≫ q)) 1) := hA
  exact (coinvariantsTranslateEquiv g hN A.representation).symm.toEquiv.nontrivial

end Transport

section Detection

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance detectionPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]

/-- Renard VI.5.4, proof, first paragraph, for actual represented parabolics: let `ρ` be a
supercuspidal representation of `M(k)` and `A` an irreducible subquotient of `i_P^G ρ`.
Then some actual parabolic `Q' = L'U'` has `L'` conjugate to `M` under `G(k)`, a nonzero
normalized Jacquet module `r_{Q'} A`, and an irreducible supercuspidal quotient `σ` of
`r_{Q'} A` that is a subquotient of `r_{Q'} i_P^G ρ`. Inputs: the proved
`leviCuspidalEmbedding` (VI.2.1) and VI.5.3 (ii). -/
theorem exists_conjugateLevi_supercuspidal_jacquetQuotient
    (hns : LeviJacquetInductionNoSupercuspidalStatement.{u, v}) (hG : IsConnectedReductive G)
    {P M N : GroupScheme (Spec (CommRingCat.of k))}
    (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P)
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication l r)) :
    haveI := hl.isConnectedReductive.isAffineHom
    letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
    haveI : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
    haveI : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
    ∀ ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M),
      (∀ (P₁ M₁ U₁ : GroupScheme (Spec (CommRingCat.of k)))
        (p₁ : P₁ ⟶ M) (l₁ : M₁ ⟶ P₁) (r₁ : U₁ ⟶ P₁)
        (hp₁ : IsParabolicSubgroup p₁) (hl₁ : IsRationalLeviSubgroup l₁)
        (hr₁ : LeviSubgroup.IsGeometricUnipotentRadical r₁)
        (hmul₁ : IsIso (subgroupMultiplication l₁ r₁)),
        ¬ IsIso p₁ → Subsingleton ((jacquetFunctor p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁).obj ρ)) →
      ∀ A : SmoothRep.{0, u, max u v} ℂ (rationalPoints G), A.IsIrreducible →
        SmoothRep.IsSubquotient A ((leviInductionFunctor p l r hp hr hl hmul).obj ρ) →
        ∃ (Q' L' U' : GroupScheme (Spec (CommRingCat.of k)))
          (q' : Q' ⟶ G) (l' : L' ⟶ Q') (r' : U' ⟶ Q')
          (hq' : IsParabolicSubgroup q') (hl' : IsRationalLeviSubgroup l')
          (hr' : LeviSubgroup.IsGeometricUnipotentRadical r')
          (hmul' : IsIso (subgroupMultiplication l' r')),
          (∃ (g : rationalPoints G) (φ : M ≅ L'),
            φ.hom ≫ l' ≫ q' = l ≫ p ≫ (G.innerIso g).hom) ∧
          haveI := hl'.isConnectedReductive.isAffineHom
          letI : TopologicalSpace (rationalPoints L') := leviPointTopology l' hl'
          haveI : LocallyCompactSpace (rationalPoints L') :=
            leviPoints_locallyCompactSpace q' l' hq' hl'
          haveI : NonarchimedeanGroup (rationalPoints L') :=
            leviPoints_nonarchimedeanGroup q' l' hq' hl'
          Nontrivial ((leviJacquetFunctor q' l' r' hq' hr' hl' hmul').obj A) ∧
          ∃ σ : SmoothRep.{0, u, max u v} ℂ (rationalPoints L'),
            σ.IsIrreducible ∧
            (∀ (P₁ M₁ U₁ : GroupScheme (Spec (CommRingCat.of k)))
              (p₁ : P₁ ⟶ L') (l₁ : M₁ ⟶ P₁) (r₁ : U₁ ⟶ P₁)
              (hp₁ : IsParabolicSubgroup p₁) (hl₁ : IsRationalLeviSubgroup l₁)
              (hr₁ : LeviSubgroup.IsGeometricUnipotentRadical r₁)
              (hmul₁ : IsIso (subgroupMultiplication l₁ r₁)),
              ¬ IsIso p₁ → Subsingleton ((jacquetFunctor p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁).obj σ)) ∧
            SmoothRep.IsQuotient σ ((leviJacquetFunctor q' l' r' hq' hr' hl' hmul').obj A) ∧
            SmoothRep.IsSubquotient σ ((leviJacquetFunctor q' l' r' hq' hr' hl' hmul').obj
              ((leviInductionFunctor p l r hp hr hl hmul).obj ρ)) := by
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  have := leviPoints_locallyCompactSpace p l hp hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  intro ρ hρsc A hA hsub
  obtain ⟨Q', L', U', q', l', r', hq', hl', hr', hmul', hJ, -,
      σ, hσ, hσsc, ⟨t, ht⟩, -⟩ := leviCuspidalEmbedding.{u, max u v} k G hG A hA
  have := hl'.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints L') := leviPointTopology l' hl'
  have := leviPoints_locallyCompactSpace q' l' hq' hl'
  have := leviPoints_nonarchimedeanGroup q' l' hq' hl'
  let J := leviJacquetFunctor.{u, max u v} q' l' r' hq' hr' hl' hmul'
  have hJex : Derivative.Mirabolic.MapsShortExactIntertwiners J := by
    intro X Y Z a b ha hb hab
    have hx := (leviParabolicFunctorsExact.{u, max u v}
      k G hG Q' L' U' q' l' r' hq' hl' hr' hmul').2 a b ⟨ha, hb, hab⟩
    exact ⟨hx.1, hx.2.2, hx.2.1⟩
  have hσq : SmoothRep.IsQuotient σ (J.obj A) := ⟨SmoothRep.ofHom t, ht⟩
  have hσP : SmoothRep.IsSubquotient σ
      (J.obj ((leviInductionFunctor p l r hp hr hl hmul).obj ρ)) :=
    smoothSubquotientTransitivity ℂ (rationalPoints L') _ _ _
      (SmoothRep.IsQuotient.isSubquotient hσq)
      (ExactSmoothTransport.map_isSubquotient J hJex hsub)
  have hconj : ∃ (g : rationalPoints G) (φ : M ≅ L'),
      φ.hom ≫ l' ≫ q' = l ≫ p ≫ (G.innerIso g).hom := by
    by_contra hno
    exact hns k G hG P M N Q' L' U' p l r hp hl hr hmul q' l' r' hq' hl' hr' hmul'
      hno ρ hρsc σ hσ hσP hσsc
  exact ⟨Q', L', U', q', l', r', hq', hl', hr', hmul', hconj, hJ, σ, hσ, hσsc, hσq, hσP⟩

/-- The same detection along a parabolic whose Levi embedding is exactly `l ≫ p`: the
parabolic of `exists_conjugateLevi_supercuspidal_jacquetQuotient`, conjugated back by
`g⁻¹`, with its Levi source changed to `M` by `φ`. -/
theorem exists_leviEmbedding_nontrivial_jacquet
    (hns : LeviJacquetInductionNoSupercuspidalStatement.{u, v}) (hG : IsConnectedReductive G)
    {P M N : GroupScheme (Spec (CommRingCat.of k))}
    (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P)
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication l r)) :
    haveI := hl.isConnectedReductive.isAffineHom
    letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
    haveI : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
    haveI : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
    ∀ ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M),
      (∀ (P₁ M₁ U₁ : GroupScheme (Spec (CommRingCat.of k)))
        (p₁ : P₁ ⟶ M) (l₁ : M₁ ⟶ P₁) (r₁ : U₁ ⟶ P₁)
        (hp₁ : IsParabolicSubgroup p₁) (hl₁ : IsRationalLeviSubgroup l₁)
        (hr₁ : LeviSubgroup.IsGeometricUnipotentRadical r₁)
        (hmul₁ : IsIso (subgroupMultiplication l₁ r₁)),
        ¬ IsIso p₁ → Subsingleton ((jacquetFunctor p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁).obj ρ)) →
      ∀ A : SmoothRep.{0, u, max u v} ℂ (rationalPoints G), A.IsIrreducible →
        SmoothRep.IsSubquotient A ((leviInductionFunctor p l r hp hr hl hmul).obj ρ) →
        ∃ (Q U : GroupScheme (Spec (CommRingCat.of k)))
          (q : Q ⟶ G) (lQ : M ⟶ Q) (rQ : U ⟶ Q)
          (hq : IsParabolicSubgroup q) (hlQ : IsRationalLeviSubgroup lQ)
          (hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ)
          (hmulQ : IsIso (subgroupMultiplication lQ rQ)),
          lQ ≫ q = l ≫ p ∧
          haveI := hlQ.isConnectedReductive.isAffineHom
          letI : TopologicalSpace (rationalPoints M) := leviPointTopology lQ hlQ
          Nontrivial ((leviJacquetFunctor q lQ rQ hq hrQ hlQ hmulQ).obj A) := by
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  have := leviPoints_locallyCompactSpace p l hp hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  intro ρ hρsc A hA hsub
  obtain ⟨Q', L', U', q', l', r', hq', hl', hr', hmul', ⟨g, φ, hφ⟩, hJ, -⟩ :=
    exists_conjugateLevi_supercuspidal_jacquetQuotient hns hG p l r hp hl hr hmul ρ hρsc A hA
      hsub
  have hlevi : (φ.hom ≫ l') ≫ q' ≫ (G.innerIso g⁻¹).hom = l ≫ p := by
    rw [Category.assoc, ← Category.assoc l', ← Category.assoc φ.hom, hφ]
    simp only [Category.assoc]
    rw [← innerIso_mul_hom, inv_mul_cancel, innerIso_one_hom, Category.comp_id]
  refine ⟨Q', U', q' ≫ (G.innerIso g⁻¹).hom, φ.hom ≫ l', r', hq'.comp_iso _, hl'.iso_comp φ, hr',
    isIso_subgroupMultiplication_iso_comp φ (l := l') (r := r') hmul', hlevi, ?_⟩
  exact nontrivial_leviJacquet_of_range_eq_comp_innerIso q' l' r' hq' hl' hr' hmul'
    (q' ≫ (G.innerIso g⁻¹).hom) (φ.hom ≫ l') r' (hq'.comp_iso _) (hl'.iso_comp φ) hr'
    (isIso_subgroupMultiplication_iso_comp φ (l := l') (r := r') hmul') g⁻¹ rfl A hJ

end Detection

end Langlands.Aubert.General.RepresentedParabolic
