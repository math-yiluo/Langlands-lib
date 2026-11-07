import Langlands.GroupScheme.Reductive.FibrewiseRootDatum
import Langlands.GroupScheme.Reductive.RootDatumFiniteGeneratorComparison
import Langlands.GroupScheme.Torus.NormalizerRepresentationWeights
import Langlands.GroupScheme.Torus.RingRepresentationWeightsBaseChange
import Langlands.GroupScheme.Torus.LocalRootSupportComparison

/-! # Full root-data comparison from actual integral representation weights -/

noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

namespace CoordinateRootDatum

variable {I : Type u} [Fintype I] {J : Type v}
  (k : Type u) [Field k] (P : RootDatum J (I → ℤ) (I → ℤ))

/-- Realization intertwines each reflection on the entire coordinate lattice. -/
theorem fieldRealization_reflection_exponentCharacter (α : J) (m : I → ℤ) :
    (fieldRealization k P).reflection α
        (splitTorus.exponentCharacter (Spec (CommRingCat.of k)) I m) =
      splitTorus.exponentCharacter (Spec (CommRingCat.of k)) I (P.reflection α m) := by
  have hi : (fieldRealizationEquiv k P).toHom.indexEquiv = Equiv.refl J := rfl
  simpa only [RootPairing.Equiv.weightEquiv_apply, fieldRealizationEquiv_weightMap,
    hi, Equiv.refl_apply]
    using ((fieldRealizationEquiv k P).weightEquiv_reflection α m).symm

variable {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : splitTorus (Spec (CommRingCat.of k)) I ⟶ G)

/-- A realized actual datum forces the coordinate pairing to be the dot product. -/
theorem pairing_of_isRootDatumOf
    (hP : IsRootDatumOf i (fieldRealization k P)) (m n : I → ℤ) :
    P.toLinearMap m n = ∑ j, m j * n j := by
  rw [← fieldRealization_pairing k P m n, hP.1]
  exact splitTorus.latticePairing_exponentCharacter_exponentCocharacter I k m n

/-- Actual roots are precisely the coordinate roots of a realized actual datum. -/
theorem mem_rootRange_iff
    (hP : IsRootDatumOf i (fieldRealization k P)) (m : I → ℤ) :
    m ∈ Set.range P.root ↔
      splitTorus.exponentCharacter (Spec (CommRingCat.of k)) I m ∈ roots i := by
  rw [← hP.2.1]
  constructor
  · rintro ⟨α, rfl⟩
    exact ⟨α, fieldRealization_root k P α⟩
  · rintro ⟨α, hα⟩
    refine ⟨α, ?_⟩
    rw [fieldRealization_root,
      splitTorus.exponentCharacter_eq_characterLatticeEquiv_symm,
      splitTorus.exponentCharacter_eq_characterLatticeEquiv_symm] at hα
    exact (splitTorus.characterLatticeEquiv k I).symm.injective hα

variable {k P i} [DecidableEq I]

/-- The actual reflection normalizers preserve every occurring representation weight,
expressed on the whole integral coordinate lattice. -/
theorem weight_ne_zero_reflection {N : ℕ} (ρ : MatrixRepresentation G (Fin N))
    (hP : IsRootDatumOf i (fieldRealization k P)) (α : J) {m : I → ℤ}
    (hm : SplitTorusRepresentationWeights.weight ρ I i m ≠ 0) :
    SplitTorusRepresentationWeights.weight ρ I i (P.reflection α m) ≠ 0 := by
  obtain ⟨n, σ, hn, hσ⟩ := hP.2.2 α
  have hexp : RepresentationWeightWeylFinite.exponentAut I σ m = P.reflection α m := by
    apply (splitTorus.characterLatticeEquiv k I).symm.injective
    rw [RepresentationWeightWeylFinite.characterLatticeEquiv_symm_exponentAut, hσ]
    rw [← splitTorus.exponentCharacter_eq_characterLatticeEquiv_symm,
      fieldRealization_reflection_exponentCharacter,
      splitTorus.exponentCharacter_eq_characterLatticeEquiv_symm]
  rw [SplitTorusRepresentationWeights.weight_eq_field_weight] at hm ⊢
  rw [← hexp]
  exact NormalizerRepresentationWeights.weight_ne_zero_exponentAut I ρ i hn hm

end CoordinateRootDatum

namespace CoordinateRootDatum

section LocalBase

variable {R : Type u} [CommRing R] [IsLocalRing R]
  (I : Type u) [Fintype I] [DecidableEq I]
  (G : GroupScheme (Spec (CommRingCat.of R)))
  [Smooth G.X.hom] [IsAffineHom G.X.hom]
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
  {N : ℕ} (ρ : MatrixRepresentation G (Fin N))
  (k : Type u) [Field k] [Algebra R k]
  {J : Type v} (P : RootDatum J (I → ℤ) (I → ℤ))

local instance representationFibreAffine :
    IsAffineHom ((baseChange (algebraBaseMap R k)).obj G).X.hom :=
  inferInstanceAs (IsAffineHom (pullback.snd G.X.hom (algebraBaseMap R k)))

omit [Smooth G.X.hom] in
/-- Reflections realized on one field fibre preserve the actual integral
representation support over the local base. -/
theorem mapsTo_weights_of_field
    (hP : IsRootDatumOf (splitTorus.baseChangeHom (K := k) G I i)
      (fieldRealization k P)) (α : J) :
    Set.MapsTo (P.reflection α)
      {m : I → ℤ | SplitTorusRepresentationWeights.weight ρ I i m ≠ 0}
      {m : I → ℤ | SplitTorusRepresentationWeights.weight ρ I i m ≠ 0} := by
  intro m hm
  have hbase (n : I → ℤ) :
      SplitTorusRepresentationWeights.weight (ρ.baseChange (algebraBaseMap R k)) I
        (splitTorus.baseChangeHom (K := k) G I i) n ≠ 0 ↔
      SplitTorusRepresentationWeights.weight ρ I i n ≠ 0 :=
    SplitTorusRepresentationWeights.weight_baseChange_ne_zero_iff
      (algebraMap R k) ρ I i n
  exact (hbase _).1
    (weight_ne_zero_reflection (ρ.baseChange (algebraBaseMap R k)) hP α ((hbase m).2 hm))

variable (l : Type u) [Field l] [Algebra R l]
  {J' : Type w} (Q : RootDatum J' (I → ℤ) (I → ℤ))

omit [Smooth G.X.hom] [IsLocalRing R] [DecidableEq I] in
/-- The pairings of two actual coordinate fibre data coincide on both
entire lattices. -/
theorem pairing_eq_of_fields
    (hP : IsRootDatumOf (splitTorus.baseChangeHom (K := k) G I i)
      (fieldRealization k P))
    (hQ : IsRootDatumOf (splitTorus.baseChangeHom (K := l) G I i)
      (fieldRealization l Q)) :
    P.toLinearMap = Q.toLinearMap := by
  apply LinearMap.ext
  intro m
  apply LinearMap.ext
  intro n
  exact (pairing_of_isRootDatumOf k P _ hP m n).trans
    (pairing_of_isRootDatumOf l Q _ hQ m n).symm

/-- Local constancy of the actual adjoint roots identifies the coordinate
root ranges of two actual fibre data. -/
theorem rootRange_eq_of_fields
    (hP : IsRootDatumOf (splitTorus.baseChangeHom (K := k) G I i)
      (fieldRealization k P))
    (hQ : IsRootDatumOf (splitTorus.baseChangeHom (K := l) G I i)
      (fieldRealization l Q)) :
    Set.range P.root = Set.range Q.root := by
  ext m
  rw [mem_rootRange_iff k P _ hP, mem_rootRange_iff l Q _ hQ]
  exact splitTorus.mem_roots_fieldBaseChange_iff_of_isLocalRing
    (k := k) (l := l) I G i m

/-- A supplied representation whose torus composite is a scheme monomorphism
determines a full identity-lattice equivalence between actual coordinate
root data on any two field fibres of a smooth affine group over a local ring. -/
def equivOfRepresentation
    (hmono : Mono (i.hom.hom ≫ ρ.hom.hom).left)
    (hP : IsRootDatumOf (splitTorus.baseChangeHom (K := k) G I i)
      (fieldRealization k P))
    (hQ : IsRootDatumOf (splitTorus.baseChangeHom (K := l) G I i)
      (fieldRealization l Q)) : RootPairing.Equiv P Q := by
  letI : Nontrivial R := (algebraMap R k).domain_nontrivial
  exact Langlands.LinearAlgebra.rootDatumEquivOfCommonGenerators P Q
    (pairing_eq_of_fields I G i k P l Q hP hQ)
    (rootRange_eq_of_fields I G i k P l Q hP hQ)
    {m : I → ℤ | SplitTorusRepresentationWeights.weight ρ I i m ≠ 0}
    (SplitTorusRepresentationWeights.finite_weights ρ I i)
    (SplitTorusRepresentationWeights.closure_weights_eq_top ρ I i hmono)
    (mapsTo_weights_of_field I G i ρ k P hP)
    (mapsTo_weights_of_field I G i ρ l Q hQ)

variable (hmono : Mono (i.hom.hom ≫ ρ.hom.hom).left)
  (hP : IsRootDatumOf (splitTorus.baseChangeHom (K := k) G I i)
    (fieldRealization k P))
  (hQ : IsRootDatumOf (splitTorus.baseChangeHom (K := l) G I i)
    (fieldRealization l Q))

@[simp]
theorem equivOfRepresentation_weightMap :
    (equivOfRepresentation I G i ρ k P l Q hmono hP hQ).toHom.weightMap =
      LinearMap.id := rfl

@[simp]
theorem equivOfRepresentation_coweightMap :
    (equivOfRepresentation I G i ρ k P l Q hmono hP hQ).toHom.coweightMap =
      LinearMap.id := rfl

@[simp]
theorem equivOfRepresentation_root (α : J) :
    Q.root ((equivOfRepresentation I G i ρ k P l Q hmono hP hQ).toHom.indexEquiv α) =
      P.root α :=
  (congrFun (equivOfRepresentation I G i ρ k P l Q hmono hP hQ).toHom.root_weightMap α).symm

@[simp]
theorem equivOfRepresentation_coroot (α : J) :
    Q.coroot ((equivOfRepresentation I G i ρ k P l Q hmono hP hQ).toHom.indexEquiv α) =
      P.coroot α := by
  have h := congrFun
    (equivOfRepresentation I G i ρ k P l Q hmono hP hQ).toHom.coroot_coweightMap
    ((equivOfRepresentation I G i ρ k P l Q hmono hP hQ).toHom.indexEquiv α)
  simpa only [Function.comp_apply, equivOfRepresentation_coweightMap,
    LinearMap.id_apply, Equiv.symm_apply_apply] using h

/-- Compare the two actual realized full data by retaining their common
integral coordinate vectors. -/
def fieldEquivOfRepresentation :
    RootPairing.Equiv (fieldRealization k P) (fieldRealization l Q) :=
  (fieldRealizationEquiv l Q).comp
    ((equivOfRepresentation I G i ρ k P l Q hmono hP hQ).comp
      (fieldRealizationEquiv k P).symm)

end LocalBase

end CoordinateRootDatum

end Langlands.GroupScheme
