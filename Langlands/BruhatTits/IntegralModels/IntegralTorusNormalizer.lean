import Langlands.BruhatTits.IntegralModels.FacetRootDatum
import Langlands.GroupScheme.Rational.SplitTorusHomBaseChange
import Langlands.GroupScheme.Rational.SubgroupConjugacyDescent
import Langlands.GroupScheme.Torus.CharacterIsomorphism
import Langlands.GroupScheme.IntegralModel.GenericRigidity
import Langlands.GroupScheme.HomogeneousQuotientFiber

/-! # Specializing integral torus normalizers -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.BruhatTits.IntegralModels

open GroupScheme

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  {D : RelativeComponentModelData R K G}
  {S : CommGroupScheme (Spec (CommRingCat.of K))} {i : S.toGrp ⟶ G}

namespace IntegralTorusData

variable (T : IntegralTorusData D S i)

private theorem baseChange_hom_injective (hT : IsSplitTorus T.torus.toGrp) :
    Function.Injective (fun f : T.torus ⟶ T.torus =>
      (CommGroupScheme.baseChange (Spec.algebraMap R K)).map f) := by
  intro f g h
  dsimp only at h
  apply hT.hom_ext_of_characters
  intro χ
  apply (hT.characterLattice_baseChange_bijective (Spec.algebraMap R K) T.torus).1
  rw [characterLattice.baseChange_precomp, characterLattice.baseChange_precomp, h]

private theorem exists_baseChange_automorphism
    (hT : IsSplitTorus T.torus.toGrp)
    (σ : (CommGroupScheme.baseChange (Spec.algebraMap R K)).obj T.torus ≅
      (CommGroupScheme.baseChange (Spec.algebraMap R K)).obj T.torus) :
    ∃ τ : T.torus ≅ T.torus,
      (CommGroupScheme.baseChange (Spec.algebraMap R K)).map τ.hom = σ.hom := by
  have hchar : Function.Surjective
      (fun χ : T.torus.toGrp ⟶ (Gm (Spec (CommRingCat.of R))).toGrp =>
        (GroupScheme.baseChange (Spec.algebraMap R K)).map χ ≫
          (Gm.baseChangeIso (Spec.algebraMap R K)).hom) := by
    intro χ
    obtain ⟨ψ, hψ⟩ :=
      (hT.characterLattice_baseChange_bijective (Spec.algebraMap R K) T.torus).2
        (Additive.ofMul χ)
    exact ⟨CommGroupScheme.groupHom ψ, congrArg CommGroupScheme.groupHom hψ⟩
  have hsurj := hT.hom_baseChange_surjective_of_characterSurjective
    (Spec.algebraMap R K) hchar
  obtain ⟨f, hf⟩ := hsurj (CommGroupScheme.groupHom σ.hom)
  obtain ⟨g, hg⟩ := hsurj (CommGroupScheme.groupHom σ.inv)
  have hf' : (CommGroupScheme.baseChange (Spec.algebraMap R K)).map
      (Additive.ofMul f) = σ.hom := congrArg Additive.ofMul hf
  have hg' : (CommGroupScheme.baseChange (Spec.algebraMap R K)).map
      (Additive.ofMul g) = σ.inv := congrArg Additive.ofMul hg
  refine ⟨⟨Additive.ofMul f, Additive.ofMul g, ?_, ?_⟩, hf'⟩
  · apply T.baseChange_hom_injective hT
    dsimp only
    rw [Functor.map_comp, CategoryTheory.Functor.map_id, hf', hg', σ.hom_inv_id]
  · apply T.baseChange_hom_injective hT
    dsimp only
    rw [Functor.map_comp, CategoryTheory.Functor.map_id, hg', hf', σ.inv_hom_id]

/-- Every automorphism of the specified generic split torus extends to an
automorphism of the same integral split torus, with its compatibility square. -/
theorem exists_integralAutomorphism (hT : IsSplitTorus T.torus.toGrp) (σ : S ≅ S) :
    ∃ τ : T.torus ≅ T.torus,
      (GroupScheme.baseChange (Spec.algebraMap R K)).map
          (CommGroupScheme.groupHom τ.hom) ≫ T.genericIso.hom =
        T.genericIso.hom ≫ CommGroupScheme.groupHom σ.hom := by
  let e : (CommGroupScheme.baseChange (Spec.algebraMap R K)).obj T.torus ≅ S :=
    CommGroupScheme.isoOfGroupIso T.genericIso
  obtain ⟨τ, hτ⟩ := T.exists_baseChange_automorphism hT (e ≪≫ σ ≪≫ e.symm)
  refine ⟨τ, ?_⟩
  have h := congrArg CommGroupScheme.groupHom
    (congrArg (fun f => f ≫ e.hom) hτ)
  change CommGroupScheme.groupHom
      ((CommGroupScheme.baseChange (Spec.algebraMap R K)).map τ.hom ≫ e.hom) =
    CommGroupScheme.groupHom (e.hom ≫ σ.hom)
  simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
    Category.comp_id] using h

/-- The chosen integral extension of a generic torus automorphism. -/
def integralAutomorphism (hT : IsSplitTorus T.torus.toGrp) (σ : S ≅ S) :
    T.torus ≅ T.torus :=
  Classical.choose (T.exists_integralAutomorphism hT σ)

theorem integralAutomorphism_generic_comm
    (hT : IsSplitTorus T.torus.toGrp) (σ : S ≅ S) :
    (GroupScheme.baseChange (Spec.algebraMap R K)).map
        (CommGroupScheme.groupHom (T.integralAutomorphism hT σ).hom) ≫ T.genericIso.hom =
      T.genericIso.hom ≫ CommGroupScheme.groupHom σ.hom :=
  Classical.choose_spec (T.exists_integralAutomorphism hT σ)

variable [IsLocalRing R]

/-- Residue specialization of the chosen integral automorphism. -/
def specializedAutomorphism (hT : IsSplitTorus T.torus.toGrp) (σ : S ≅ S) :
    T.specialFibre ≅ T.specialFibre :=
  (CommGroupScheme.baseChange (IntegralModel.residueBaseMap R)).mapIso
    (T.integralAutomorphism hT σ)

omit [IsLocalRing R] in
private theorem genericCharacter_characterAut
    (hT : IsSplitTorus T.torus.toGrp) (σ : S ≅ S)
    (χ : characterLattice T.torus) :
    T.genericCharacter (characterAut (T.integralAutomorphism hT σ) χ) =
      characterAut σ (T.genericCharacter χ) := by
  let e : (CommGroupScheme.baseChange (Spec.algebraMap R K)).obj T.torus ≅ S :=
    CommGroupScheme.isoOfGroupIso T.genericIso
  let τ := T.integralAutomorphism hT σ
  have hc : (CommGroupScheme.baseChange (Spec.algebraMap R K)).map τ.hom ≫ e.hom =
      e.hom ≫ σ.hom :=
    congrArg Additive.ofMul (T.integralAutomorphism_generic_comm hT σ)
  have hi : (CommGroupScheme.baseChange (Spec.algebraMap R K)).map τ.inv ≫ e.hom =
      e.hom ≫ σ.inv := by
    change ((CommGroupScheme.baseChange (Spec.algebraMap R K)).mapIso τ).inv ≫ e.hom = _
    rw [Iso.inv_comp_eq]
    change e.hom = (CommGroupScheme.baseChange (Spec.algebraMap R K)).map τ.hom ≫
      e.hom ≫ σ.inv
    rw [← Category.assoc, hc, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  have hi' : e.inv ≫ (CommGroupScheme.baseChange (Spec.algebraMap R K)).map τ.inv =
      σ.inv ≫ e.inv := by
    apply (cancel_mono e.hom).1
    simp only [Category.assoc, hi, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
      Category.comp_id]
  change e.inv ≫ characterLattice.baseChange (Spec.algebraMap R K) T.torus
      (τ.inv ≫ χ) =
    σ.inv ≫ e.inv ≫ characterLattice.baseChange (Spec.algebraMap R K) T.torus χ
  rw [characterLattice.baseChange_precomp, ← Category.assoc, hi', Category.assoc]

/-- The generic and specialized automorphisms have the same action on
characters under the canonical specialization through the integral torus. -/
theorem characterSpecialization_characterAut
    (hT : IsSplitTorus T.torus.toGrp) (σ : S ≅ S) (χ : characterLattice S) :
    T.characterSpecialization hT (characterAut σ χ) =
      characterAut (T.specializedAutomorphism hT σ) (T.characterSpecialization hT χ) := by
  obtain ⟨ψ, rfl⟩ := (T.genericCharacterEquiv hT).surjective χ
  change T.characterSpecialization hT (characterAut σ (T.genericCharacter ψ)) =
    characterAut (T.specializedAutomorphism hT σ)
      (T.characterSpecialization hT (T.genericCharacter ψ))
  rw [← T.genericCharacter_characterAut hT σ ψ,
    T.characterSpecialization_genericCharacter, T.characterSpecialization_genericCharacter]
  exact characterLattice.baseChange_precomp (IntegralModel.residueBaseMap R)
    (T.integralAutomorphism hT σ).inv ψ

/-- The same integral torus transports a generic reflection formula with its
specified coroot to the actual special-fibre lattices. -/
theorem characterAut_specialized_reflection
    (hT : IsSplitTorus T.torus.toGrp) (σ : S ≅ S)
    (a : characterLattice S) (ν : cocharacterLattice S)
    (hσ : ∀ χ, characterAut σ χ = χ - latticePairing S χ ν • a)
    (χ : characterLattice T.specialFibre) :
    characterAut (T.specializedAutomorphism hT σ) χ =
      χ - latticePairing T.specialFibre χ (T.cocharacterSpecialization hT ν) •
        T.characterSpecialization hT a := by
  obtain ⟨ψ, rfl⟩ := (T.characterSpecialization hT).surjective χ
  rw [← T.characterSpecialization_characterAut, hσ, map_sub, map_zsmul,
    T.latticePairing_specialization]

omit [IsLocalRing R] in
/-- A generic normalizer coming from an actual integral section normalizes
the supplied integral torus through its constructed integral automorphism. -/
theorem isNormalizingPoint_integral
    (hT : T.IsClosedSplit) (x : D.neutral.integralSections) (σ : S ≅ S)
    (hx : IsNormalizingPoint i (D.neutral.integralPointMap x) σ) :
    IsNormalizingPoint T.inclusion x (T.integralAutomorphism hT.1 σ) := by
  let : Smooth T.torus.toGrp.X.hom := hT.1.smooth
  have hgeneric :
      (GroupScheme.baseChange (Spec.algebraMap R K)).map
          (T.inclusion ≫ (D.neutral.group.innerIso x).hom) =
        (GroupScheme.baseChange (Spec.algebraMap R K)).map
          (CommGroupScheme.groupHom (T.integralAutomorphism hT.1 σ).hom ≫ T.inclusion) := by
    apply (cancel_mono D.neutral.genericIso.hom).1
    calc
      _ = (GroupScheme.baseChange (Spec.algebraMap R K)).map T.inclusion ≫
          D.neutral.genericIso.hom ≫ (G.innerIso (D.neutral.integralPointMap x)).hom := by
        rw [Functor.map_comp, Category.assoc, baseChange_innerIso_hom, innerIso_hom_comp]
        rfl
      _ = T.genericIso.hom ≫ i ≫
          (G.innerIso (D.neutral.integralPointMap x)).hom := by
        rw [← Category.assoc, T.generic_comm, Category.assoc]
      _ = T.genericIso.hom ≫ CommGroupScheme.groupHom σ.hom ≫ i := by rw [hx]
      _ = (GroupScheme.baseChange (Spec.algebraMap R K)).map
          (CommGroupScheme.groupHom (T.integralAutomorphism hT.1 σ).hom) ≫
          T.genericIso.hom ≫ i := by
        simpa only [Category.assoc] using congrArg (fun f => f ≫ i)
          (T.integralAutomorphism_generic_comm hT.1 σ).symm
      _ = _ := by rw [Functor.map_comp, Category.assoc, T.generic_comm]
  apply Grp.hom_ext
  exact Langlands.AbelianScheme.genericFibre_map_injective K
    (congrArg (fun f => f.hom.hom) hgeneric)

/-- Reduction of the actual integral section normalizes the actual special
torus through the residue automorphism of that same integral torus. -/
theorem isNormalizingPoint_reduction
    (hT : T.IsClosedSplit) (x : D.neutral.integralSections) (σ : S ≅ S)
    (hx : IsNormalizingPoint i (D.neutral.integralPointMap x) σ) :
    IsNormalizingPoint T.specialFibreInclusion (D.neutral.reduction x)
      (T.specializedAutomorphism hT.1 σ) := by
  have h := congrArg ((GroupScheme.baseChange (IntegralModel.residueBaseMap R)).map)
    (T.isNormalizingPoint_integral hT x σ hx)
  change (GroupScheme.baseChange (IntegralModel.residueBaseMap R)).map T.inclusion ≫
      (D.neutral.specialFibre.innerIso
        (baseChangeBasePoint (IntegralModel.residueBaseMap R) D.neutral.group x)).hom =
    (GroupScheme.baseChange (IntegralModel.residueBaseMap R)).map
        (CommGroupScheme.groupHom (T.integralAutomorphism hT.1 σ).hom) ≫
      (GroupScheme.baseChange (IntegralModel.residueBaseMap R)).map T.inclusion
  simpa only [Functor.map_comp, baseChange_innerIso_hom] using h

/-- Passing the reduced section through the supplied quotient preserves the
normalizer square. No surjectivity on rational points is assumed. -/
theorem isNormalizingPoint_quotient
    (Q : SpecialFibreQuotientData D)
    (hT : T.IsClosedSplit) (x : D.neutral.integralSections) (σ : S ≅ S)
    (hx : IsNormalizingPoint i (D.neutral.integralPointMap x) σ) :
    IsNormalizingPoint (T.specialFibreInclusion ≫ Q.projection)
      (rationalPoints.map Q.projection (D.neutral.reduction x))
      (T.specializedAutomorphism hT.1 σ) := by
  have h := T.isNormalizingPoint_reduction hT x σ hx
  change (T.specialFibreInclusion ≫ Q.projection) ≫
      (Q.quotient.innerIso (D.neutral.reduction x ≫ Q.projection.hom.hom)).hom =
    CommGroupScheme.groupHom (T.specializedAutomorphism hT.1 σ).hom ≫
      T.specialFibreInclusion ≫ Q.projection
  rw [Category.assoc, ← innerIso_hom_comp, ← Category.assoc, h, Category.assoc]

end IntegralTorusData
end Langlands.BruhatTits.IntegralModels
