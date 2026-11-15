import Langlands.Representation.Classification.LeftCuspidalDerivative.Core
import Langlands.Representation.Classification.MultiplicityOneConstituentProof
import Langlands.Representation.Classification.UpperJacquetSubrepresentationDetectionProof
import Langlands.Representation.Classification.CuspidalJacquetFunctorExactnessProof
import Langlands.Representation.Parabolic.FiniteLengthFunctorProof

/-!
# Irreducible subrepresentations of `𝔄 × E`

For a supercuspidal `A` of `GL_d`, an irreducible `A`-pure `𝔄` of `GL_a` and an irreducible
left `A`-reduced `E` of `GL_m` (`a, m > 0`), the normalized product `𝔄 × E` has an irreducible
socle (`hasIrreducibleSocle_twoBlock`), so any two irreducible subrepresentations of `𝔄 × E`
are isomorphic (`nonempty_iso_of_isSubrepresentation_binaryProduct`).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.Classification.LeftCuspidalDerivative

open GeneralLinear Geometric CuspidalSupport PadicField.TopologicalData
open CuspidalJacquetMultiplicity

universe uF uV uG uW

section Socle

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- Two irreducible subrepresentations of a representation with an irreducible socle are
isomorphic. -/
theorem nonempty_iso_of_hasIrreducibleSocle {P π π' : SmoothRep.{0, uG, uW} ℂ G}
    (h : HasIrreducibleSocle P.representation) (hπ : π.IsIrreducible)
    (hπ' : π'.IsIrreducible) (hs : SmoothRep.IsSubrepresentation π P)
    (hs' : SmoothRep.IsSubrepresentation π' P) :
    Nonempty (π ≅ π') := by
  have hS := SmoothRep.isIrreducibleSocle_socleSubrepresentation_iff.mpr h
  have key : ∀ {ρ : SmoothRep.{0, uG, uW} ℂ G}, ρ.IsIrreducible →
      SmoothRep.IsSubrepresentation ρ P → Nonempty (ρ ≅ P.socleSubrepresentation) := by
    intro ρ hρ hsρ
    obtain ⟨j, hj⟩ := hsρ
    have hρS : IsIrreducibleSocle P.representation ρ.representation := by
      refine ⟨hρ, SmoothRep.hom j, hj, ?_⟩
      intro W _ _ σ hσ k hk
      exact (hS.socle_eq σ hσ k hk).symm.trans (hS.socle_eq ρ.representation hρ _ hj)
    exact SmoothRep.nonempty_iso_socleSubrepresentation hρS
  obtain ⟨e⟩ := key hπ hs
  obtain ⟨e'⟩ := key hπ' hs'
  exact ⟨e ≪≫ e'.symm⟩

end Socle

section Generic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- **Irreducible socle, generic form.** Let `Y` be a family of representations of the blocks
of `C` whose external tensor product `X` is irreducible and occurs with multiplicity one in
the Jacquet module of its own normalized product induction. If that induction has some
irreducible subrepresentation, its socle is irreducible. -/
theorem hasIrreducibleSocle_productInduction {n : ℕ} (C : BlockShape n)
    (Y : letI := T.topology
      ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (C.size i) F.Carrier))
    (hX : letI := T.topology; (FiniteTensor.externalSmoothObject Y).IsIrreducible)
    (hM1 : letI := T.topology; ∀ M : ℕ, HasJordanHolderMultiplicity
      ((jacquetInductionFunctor.{uF, max uF uV} T C C).obj
        (FiniteTensor.externalSmoothObject Y))
      (FiniteTensor.externalSmoothObject Y).obj M → M = 1)
    (hex : letI := T.topology;
      ∃ P : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier), P.IsIrreducible ∧
        SmoothRep.IsSubrepresentation P ((T.normalizedProductInductionFunctor C).obj Y)) :
    letI := T.topology
    HasIrreducibleSocle ((T.normalizedProductInductionFunctor C).obj Y).representation := by
  let := T.topology
  have hXfl := SmoothRep.hasFiniteLength_of_isIrreducible hX
  have hIfl := (Parabolic.normalizedParabolicFiniteLength.{uF, max uF uV} F T).1 n C _ hXfl
  have hJfl := (Parabolic.normalizedParabolicFiniteLength.{uF, max uF uV} F T).2 n C _ hIfl
  have hM := SmoothRep.IrreducibleGrothendieckProof.compositionMultiplicity_witness ⟨_, hJfl⟩
    (FiniteTensor.externalSmoothObject Y)
  have h1 := hM1 _ hM
  rw [h1] at hM
  have hJ1 : HasJordanHolderMultiplicity
      ((upperFunctor.{uF, max uF uV} T C).obj ((T.normalizedProductInductionFunctor C).obj Y))
      (FiniteTensor.externalSmoothObject Y).obj 1 := hM
  have hJ1' : HasJordanHolderMultiplicity
      (upperJacquet T C (induced T C (FiniteTensor.externalSmoothObject Y).obj))
      (FiniteTensor.externalSmoothObject Y).obj 1 := hM
  refine (multiplicityOneConstituentCriterion.{uF, uF, max uF uV, max uF uV, max uF uV}).2
    (GeneralLinear n F.Carrier) (C.Levi F.Carrier)
    (upperFunctor.{uF, max uF uV} T C) _ (FiniteTensor.externalSmoothObject Y).obj hJ1 ?_ ?_
  · obtain ⟨P, hP, j, hj⟩ := hex
    exact ⟨P, hP, j, hj⟩
  · intro P hP j hj
    have hPnt : Nontrivial P := nontrivial_of_isIrreducible hP
    have hj0 : SmoothRep.hom j ≠ 0 := by
      intro h0
      obtain ⟨x, y, hxy⟩ := exists_pair_ne P
      apply hxy
      apply hj
      rw [h0]
      rfl
    obtain ⟨k, hk, hkpos, -⟩ :=
      upperJacquetSubrepresentationDetection.{uF, max uF uV, max uF uV} p F T n C
        (FiniteTensor.externalSmoothObject Y).obj hX P.obj (SmoothRep.hom j) hj hj0 1 hJ1'
    exact ⟨k, hk, hkpos⟩

end Generic

section Main

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- **Irreducible socle.** If `𝔄 ⊠ E` induces to a representation with some irreducible
subrepresentation, its socle is irreducible. -/
theorem hasIrreducibleSocle_twoBlock {d a m : ℕ} (hd : 0 < d) (ha : 0 < a) (hm : 0 < m)
    (A : letI := T.topology; SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := d))
    {𝔄 : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier)}
    (h𝔄 : letI := T.topology; 𝔄.IsIrreducible) (hp : IsPure T hd A 𝔄)
    {E : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)}
    (hE : letI := T.topology; E.IsIrreducible) (hr : LeftReduced F T A E)
    (hex : letI := T.topology;
      ∃ P : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (a + m) F.Carrier), P.IsIrreducible ∧
        SmoothRep.IsSubrepresentation P
          ((T.normalizedProductInductionFunctor (BlockShape.ofPair a m ha hm rfl)).obj
            (twoBlockFactors ha hm 𝔄 E))) :
    letI := T.topology
    HasIrreducibleSocle
      ((T.normalizedProductInductionFunctor (BlockShape.ofPair a m ha hm rfl)).obj
        (twoBlockFactors ha hm 𝔄 E)).representation := by
  let := T.topology
  exact hasIrreducibleSocle_productInduction.{uF, uV} F T (BlockShape.ofPair a m ha hm rfl)
    (twoBlockFactors ha hm 𝔄 E) (isIrreducible_twoBlock F T ha hm h𝔄 hE)
    (fun M hM => multiplicity_eq_one_jacquetInduction F T hd ha hm A h𝔄 hp hE hr M hM) hex

/-- **Uniqueness for `𝔄 × E`.** Any two irreducible subrepresentations of the normalized
product `𝔄 × E` are isomorphic. -/
theorem nonempty_iso_of_isSubrepresentation_binaryProduct {d a m : ℕ} (hd : 0 < d)
    (ha : 0 < a) (hm : 0 < m)
    (A : letI := T.topology; SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := d))
    {𝔄 : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier)}
    (h𝔄 : letI := T.topology; 𝔄.IsIrreducible) (hp : IsPure T hd A 𝔄)
    {E : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)}
    (hE : letI := T.topology; E.IsIrreducible) (hr : LeftReduced F T A E)
    {π π' : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (a + m) F.Carrier)}
    (hπ : letI := T.topology; π.IsIrreducible) (hπ' : letI := T.topology; π'.IsIrreducible)
    (hs : letI := T.topology;
      SmoothRep.IsSubrepresentation π ((T.binaryNormalizedProductFunctor a m).obj (𝔄, E)))
    (hs' : letI := T.topology;
      SmoothRep.IsSubrepresentation π' ((T.binaryNormalizedProductFunctor a m).obj (𝔄, E))) :
    letI := T.topology
    Nonempty (π ≅ π') := by
  let := T.topology
  obtain ⟨e⟩ := SegmentSocleDerivativesProof.nonempty_ofPairProductIso T ha hm 𝔄 E
  have hs₁ := isSubrepresentation_of_iso T hs e
  have hs₁' := isSubrepresentation_of_iso T hs' e
  have hsoc := hasIrreducibleSocle_twoBlock F T hd ha hm A h𝔄 hp hE hr ⟨π, hπ, hs₁⟩
  exact nonempty_iso_of_hasIrreducibleSocle hsoc hπ hπ' hs₁ hs₁'

end Main

end Langlands.Classification.LeftCuspidalDerivative
