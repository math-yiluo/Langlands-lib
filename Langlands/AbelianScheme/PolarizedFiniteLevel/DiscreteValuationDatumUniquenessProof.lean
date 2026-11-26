import Langlands.AbelianScheme.PolarizedFiniteLevel.DiscreteValuationDatumUniquenessStatement
import Langlands.AbelianScheme.PolarizedFiniteLevel.PullbackCoherence
import Langlands.AbelianScheme.PolarizedFiniteLevel.LevelCoherence
import Langlands.AbelianScheme.RelativeHomNeronExtension

/-! # Uniqueness of ordinary polarized full-level data over a discrete valuation ring -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open GroupScheme.Tate

section GenericFibre

variable {R : Type u} [CommRing R] [IsDomain R] (K : Type u) [Field K] [Algebra R K]
  [IsFractionRing R K]

/-- Morphisms over `Spec R` from a flat scheme to a separated scheme are equal if they agree
after composing with the first projection of the generic fibre. -/
theorem overHom_eq_of_genericFibre {Y Z : Over (Spec (CommRingCat.of R))} [Flat Y.hom]
    [IsSeparated Z.hom] {u w : Y ⟶ Z}
    (h : pullback.fst Y.hom (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫ u.left =
      pullback.fst Y.hom (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫ w.left) :
    u = w := by
  apply Langlands.AbelianScheme.genericFibre_map_injective K
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simpa [pullback.lift_fst] using h
  · simp

/-- Homomorphisms of abelian schemes over `Spec R` are determined by their generic fibres. -/
theorem abelianHom_eq_of_baseChange {A B : AbelianScheme (Spec (CommRingCat.of R))}
    {f f' : A ⟶ B}
    (h : (baseChange (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map f =
      (baseChange (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map f') : f = f' := by
  have h1 : (groupHom f).hom.hom = (groupHom f').hom.hom := by
    apply overHom_eq_of_genericFibre K
    have := congrArg (fun x => hom x ≫
      pullback.fst B.X.hom (Spec.map (CommRingCat.ofHom (algebraMap R K)))) h
    change ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map
        (groupHom f).hom.hom).left ≫ pullback.fst B.X.hom _ =
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map
        (groupHom f').hom.hom).left ≫ pullback.fst B.X.hom _ at this
    simpa [pullback.lift_fst] using this
  have h2 : groupHom f = groupHom f' := Grp.hom_ext _ _ h1
  exact congrArg Additive.ofMul h2

omit [IsDomain R] in
/-- An abelian scheme over `Spec R` satisfies FLT's abelian scheme property bundle. -/
theorem abelianSchemePropertyBundle_self (B : AbelianScheme (Spec (CommRingCat.of R))) :
    GoodReductionJacobian.AbelianSchemePropertyBundle R B.X.hom where
  smooth := inferInstance
  proper := inferInstance
  connectedFibres := fun s => B.X.hom.isConnected_preimage_singleton s
  hasGroupLaw := ⟨@GoodReductionJacobian.relativeGroupLawOfGrpObj R _ _ B.X.hom
    (inferInstanceAs (GrpObj B.X))⟩

variable [IsDiscreteValuationRing R]

/-- Over a discrete valuation ring, every homomorphism of generic fibres of abelian schemes
extends. -/
theorem exists_abelianHom_extension {A B : AbelianScheme (Spec (CommRingCat.of R))}
    (χ : (baseChange (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj A ⟶
      (baseChange (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj B) :
    ∃ φ : A ⟶ B, (baseChange (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map φ = χ := by
  obtain ⟨φ₀, hφ₀⟩ := Langlands.AbelianScheme.baseChange_map_surjective K A.toGrp B.toGrp
    (abelianSchemePropertyBundle_self B) (groupHom χ)
  exact ⟨Additive.ofMul φ₀, congrArg Additive.ofMul hφ₀⟩

/-- Over a discrete valuation ring, every isomorphism of generic fibres of abelian schemes
extends to an isomorphism. -/
theorem exists_abelianIso_extension {A B : AbelianScheme (Spec (CommRingCat.of R))}
    (e : (baseChange (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj A ≅
      (baseChange (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj B) :
    ∃ e' : A ≅ B,
      (baseChange (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map e'.hom = e.hom := by
  obtain ⟨φ, hφ⟩ := exists_abelianHom_extension K e.hom
  obtain ⟨ψ, hψ⟩ := exists_abelianHom_extension K e.inv
  refine ⟨⟨φ, ψ, ?_, ?_⟩, hφ⟩
  · apply abelianHom_eq_of_baseChange K
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id, hφ, hψ, e.hom_inv_id]
  · apply abelianHom_eq_of_baseChange K
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id, hφ, hψ, e.inv_hom_id]

end GenericFibre

/-- Two ordinary polarized full-level data over the spectrum of a discrete valuation ring are
isomorphic if their pullbacks to the fraction field are isomorphic. -/
theorem discreteValuationDatumUniqueness : DiscreteValuationDatumUniquenessStatement.{u} := by
  intro P g d n R _ _ _ K _ _ _ _ a b ⟨e⟩
  obtain ⟨φ, hφ⟩ := exists_abelianIso_extension K e.abelianIso
  refine ⟨⟨φ, ?_, ?_⟩⟩
  · apply abelianHom_eq_of_baseChange K
    apply (cancel_mono (a.dualWitness.baseChangeIso P
      (Spec.map (CommRingCat.ofHom (algebraMap R K)))
      (a.dualWitness.pullback P (Spec.map (CommRingCat.ofHom (algebraMap R K))))).hom).1
    change (a.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).polarization = _
    rw [e.polarization_eq]
    rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
      DualWitness.baseChangeIso_naturality, hφ]
    rfl
  · intro i
    have h2 : pullbackTuple (Spec.map (CommRingCat.ofHom (algebraMap R K)))
        (mapTuple φ.hom a.level.sections) i =
        pullbackTuple (Spec.map (CommRingCat.ofHom (algebraMap R K))) b.level.sections i := by
      rw [← pullbackTuple_map, hφ]
      exact e.level_eq i
    have h3 : Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫
          (Additive.toMul (mapTuple φ.hom a.level.sections i)).val.left =
        Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫
          (Additive.toMul (b.level.sections i)).val.left :=
      (pullbackTuple_fst _ _ i).symm.trans
        ((congrArg (fun x => (Additive.toMul x).val.left ≫
          pullback.fst b.abelian.X.hom (Spec.map (CommRingCat.ofHom (algebraMap R K)))) h2).trans
          (pullbackTuple_fst _ _ i))
    apply toSection_injective b.abelian.toGrp (Over.mk (𝟙 _)) n
    have : Flat (Over.mk (𝟙 (Spec (CommRingCat.of R)))).hom :=
      inferInstanceAs (Flat (𝟙 (Spec (CommRingCat.of R))))
    apply overHom_eq_of_genericFibre K
    have hc : pullback.fst (𝟙 (Spec (CommRingCat.of R)))
        (Spec.map (CommRingCat.ofHom (algebraMap R K))) =
        pullback.snd (𝟙 (Spec (CommRingCat.of R)))
          (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
      simpa using pullback.condition (f := 𝟙 (Spec (CommRingCat.of R)))
        (g := Spec.map (CommRingCat.ofHom (algebraMap R K)))
    change pullback.fst (𝟙 (Spec (CommRingCat.of R)))
        (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫
          (Additive.toMul (mapTuple φ.hom a.level.sections i)).val.left =
      pullback.fst (𝟙 (Spec (CommRingCat.of R)))
        (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫
          (Additive.toMul (b.level.sections i)).val.left
    rw [hc, Category.assoc, Category.assoc, h3]

end Langlands.AbelianScheme.PolarizedFiniteLevel
