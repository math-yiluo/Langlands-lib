import Langlands.GroupScheme.Rational.ParabolicConjugacyTransport

/-! # Conditional assembly of standard-parabolic classification -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SubgroupFunctor

variable {S : Scheme.{u}} {G : GroupScheme S}

/-- Injectivity and conjugacy rigidity of the representatives upgrade existence
of a conjugacy index to uniqueness. -/
theorem existsUnique_conjugacy_index_of_rigidity {Index : Sort v}
    (representative : Index → SubgroupFunctor G)
    (hinj : Function.Injective representative)
    (hrigid : ∀ j k, (representative j).IsRationallyConjugate (representative k) →
      representative j = representative k)
    {P : SubgroupFunctor G} (hexists : ∃ j, P.IsRationallyConjugate (representative j)) :
    ∃! j, P.IsRationallyConjugate (representative j) := by
  obtain ⟨j, hj⟩ := hexists
  exact ⟨j, hj, fun k hk => hinj (hrigid k j (hk.symm.trans hj))⟩

end SubgroupFunctor

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- Standardness of overgroups of the fixed generic parabolic, movement into
such an overgroup, injectivity, and rigidity give the exact local two-clause
classification. Every structural input remains explicit. -/
theorem standardParabolicClassification_of_local_inputs
    (hstandard : ∀ zeta : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G,
      Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) ≤ Dynamic.parabolic zeta →
        ∃ J : Set (characterLattice T), J ⊆ simpleRelativeRoots i ν ∧
          Dynamic.parabolic zeta = standardParabolic i ν J)
    (hmove : ∀ zeta : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G,
      ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
        Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) ≤
          Dynamic.parabolic (zeta ≫ (G.innerIso g).hom))
    (hinj : Function.Injective
      (fun J : {J : Set (characterLattice T) // J ⊆ simpleRelativeRoots i ν} =>
        standardParabolic i ν J.1))
    (hrigid : ∀ J K : {J : Set (characterLattice T) // J ⊆ simpleRelativeRoots i ν},
      (standardParabolic i ν J.1).IsRationallyConjugate (standardParabolic i ν K.1) →
        standardParabolic i ν J.1 = standardParabolic i ν K.1) :
    (∀ zeta : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G,
      Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) ≤ Dynamic.parabolic zeta →
        ∃ J : Set (characterLattice T), J ⊆ simpleRelativeRoots i ν ∧
          Dynamic.parabolic zeta = standardParabolic i ν J) ∧
    ∀ zeta : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G,
      ∃! J : {J : Set (characterLattice T) // J ⊆ simpleRelativeRoots i ν},
        ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
          Dynamic.parabolic zeta =
            (standardParabolic i ν J.1).comap (G.innerIso g).hom := by
  refine ⟨hstandard, fun zeta => ?_⟩
  obtain ⟨g, hg⟩ := hmove zeta
  obtain ⟨J, hJ, hstd⟩ := hstandard (zeta ≫ (G.innerIso g).hom) hg
  have hexists :
      ∃ J : {J : Set (characterLattice T) // J ⊆ simpleRelativeRoots i ν},
        (Dynamic.parabolic zeta).IsRationallyConjugate (standardParabolic i ν J.1) := by
    refine ⟨⟨J, hJ⟩, g, ?_⟩
    rw [← hstd]
    exact Dynamic.parabolic_eq_comap_of_iso zeta (G.innerIso g)
  exact SubgroupFunctor.existsUnique_conjugacy_index_of_rigidity
    (fun J : {J : Set (characterLattice T) // J ⊆ simpleRelativeRoots i ν} =>
      standardParabolic i ν J.1) hinj hrigid hexists

/-- Choose the unique actual standard index of a subgroup functor, conditional
on a conjugacy representative, index injectivity, and standard rigidity. -/
def standardParabolicConjugacyIndex
    (hinj : Function.Injective
      (fun J : {J : Set (characterLattice T) // J ⊆ simpleRelativeRoots i ν} =>
        standardParabolic i ν J.1))
    (hrigid : ∀ J K : {J : Set (characterLattice T) // J ⊆ simpleRelativeRoots i ν},
      (standardParabolic i ν J.1).IsRationallyConjugate (standardParabolic i ν K.1) →
        standardParabolic i ν J.1 = standardParabolic i ν K.1)
    (P : SubgroupFunctor G)
    (hexists : ∃ J : {J : Set (characterLattice T) // J ⊆ simpleRelativeRoots i ν},
      P.IsRationallyConjugate (standardParabolic i ν J.1)) :
    {J : {J : Set (characterLattice T) // J ⊆ simpleRelativeRoots i ν} //
      P.IsRationallyConjugate (standardParabolic i ν J.1) ∧
        ∀ K : {J : Set (characterLattice T) // J ⊆ simpleRelativeRoots i ν},
          P.IsRationallyConjugate (standardParabolic i ν K.1) → K = J} :=
  Classical.indefiniteDescription _
    (SubgroupFunctor.existsUnique_conjugacy_index_of_rigidity
      (fun J : {J : Set (characterLattice T) // J ⊆ simpleRelativeRoots i ν} =>
        standardParabolic i ν J.1) hinj hrigid hexists)

end Langlands.GroupScheme
