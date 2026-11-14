import Langlands.GroupScheme.Reductive.SplitIsogenyStatement
import Langlands.GroupScheme.Reductive.SplitCentralIsogenyExistenceProof
import Langlands.GroupScheme.Reductive.RootDatumHomLattices
import Langlands.GroupScheme.Rational.SplitTorusIsogenyOfLatticeMapsProof
import Langlands.GroupScheme.Torus.CharacterMapHom

/-! # The actual torus map attached to an isogeny of root data -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.RootDatumIsogenyRealization

variable {k : Type u} [Field k]
    {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
    {J J' : Type u} [Finite J] [Finite J']
    [Module.Finite ℤ (characterLattice T)] [Module.Finite ℤ (cocharacterLattice T)]
    [Module.Finite ℤ (characterLattice T')] [Module.Finite ℤ (cocharacterLattice T')]
    {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
    {P' : RootDatum J' (characterLattice T') (cocharacterLattice T')}
    [P.IsReduced] [P'.IsReduced] {p : ℕ}

/-- The transpose of actual character pullback is actual cocharacter pushforward,
including for noncentral root-datum isogenies. -/
theorem coweightMap_apply_of_weightMap
    (hP : P.toLinearMap = latticePairing T) (hP' : P'.toLinearMap = latticePairing T')
    (f : Langlands.LinearAlgebra.RootDatumIsogeny p P' P) (t : T ⟶ T')
    (hw : ∀ χ : characterLattice T', f.weightMap χ = t ≫ χ)
    (ν : cocharacterLattice T) : f.coweightMap ν = ν ≫ t := by
  apply P'.flip.toPerfPair.injective
  ext χ
  change P'.toLinearMap χ (f.coweightMap ν) = P'.toLinearMap χ (ν ≫ t)
  rw [← f.pairing_apply, hP, hP', hw]
  exact congrArg (gmEndEquiv k) (Category.assoc ν t χ).symm

/-- The actual torus morphism whose character pullback is the given weight map. -/
def torusMap (hT' : IsSplitTorus T'.toGrp)
    (f : Langlands.LinearAlgebra.RootDatumIsogeny p P' P) : T ⟶ T' :=
  hT'.homOfCharacterMap f.weightMap.toAddMonoidHom

@[simp]
theorem torusMap_comp (hT' : IsSplitTorus T'.toGrp)
    (f : Langlands.LinearAlgebra.RootDatumIsogeny p P' P) (χ : characterLattice T') :
    torusMap hT' f ≫ χ = f.weightMap χ :=
  hT'.homOfCharacterMap_comp f.weightMap.toAddMonoidHom χ

/-- The torus morphism also induces the prescribed map on cocharacters. -/
theorem comp_torusMap (hT' : IsSplitTorus T'.toGrp)
    (hP : P.toLinearMap = latticePairing T) (hP' : P'.toLinearMap = latticePairing T')
    (f : Langlands.LinearAlgebra.RootDatumIsogeny p P' P) (ν : cocharacterLattice T) :
    ν ≫ torusMap hT' f = f.coweightMap ν :=
  (coweightMap_apply_of_weightMap hP hP' f _
    (fun χ => (torusMap_comp hT' f χ).symm) ν).symm

/-- Characters determine the realizing torus map uniquely. -/
theorem eq_torusMap (hT' : IsSplitTorus T'.toGrp)
    (f : Langlands.LinearAlgebra.RootDatumIsogeny p P' P) {t : T ⟶ T'}
    (hw : ∀ χ : characterLattice T', f.weightMap χ = t ≫ χ) : t = torusMap hT' f :=
  hT'.hom_ext_of_characters fun χ => (hw χ).symm.trans (torusMap_comp hT' f χ).symm

/-- Both injective lattice maps make the actual torus map finite, flat and surjective. -/
theorem torusMap_isIsogeny (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    (hP : P.toLinearMap = latticePairing T) (hP' : P'.toLinearMap = latticePairing T')
    (f : Langlands.LinearAlgebra.RootDatumIsogeny p P' P) :
    IsIsogeny (CommGroupScheme.groupHom (torusMap hT' f)) := by
  apply splitTorusIsogenyOfLatticeMaps k T T' _ hT hT'
  · intro χ ψ h
    apply f.weightMap_injective
    simpa only [torusMap_comp] using h
  · intro ν μ h
    apply f.coweightMap_injective
    simpa only [comp_torusMap hT' hP hP'] using h

section Central

variable {G G' : GroupScheme (Spec (CommRingCat.of k))}

/-- A central root-datum isogeny is realized over the unique prescribed torus map.
Both actual lattice equations and the torus isogeny conclusion are retained. -/
theorem exists_central_realization (hG : IsConnectedReductive G) (hG' : IsConnectedReductive G')
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    (i : T.toGrp ⟶ G) (i' : T'.toGrp ⟶ G') (hi : IsMaximalTorus i) (hi' : IsMaximalTorus i')
    (hP : haveI := hG.isAffineHom; IsRootDatumOf i P)
    (hP' : haveI := hG'.isAffineHom; IsRootDatumOf i' P')
    (f : Langlands.LinearAlgebra.RootDatumIsogeny p P' P) (hf : f.IsCentral) :
    ∃ φ : G ⟶ G', IsCentralIsogeny φ ∧
      IsIsogeny (CommGroupScheme.groupHom (torusMap hT' f)) ∧
      i ≫ φ = CommGroupScheme.groupHom (torusMap hT' f) ≫ i' ∧
      (∀ χ : characterLattice T', f.weightMap χ = torusMap hT' f ≫ χ) ∧
      (∀ ν : cocharacterLattice T, f.coweightMap ν = ν ≫ torusMap hT' f) := by
  obtain ⟨φ, t, hsq, hw, hφ⟩ :=
    splitCentralIsogenyExistence k G G' hG hG' T T' hT hT' i i' hi hi'
      J J' P P' hP hP' (f.toHom hf) f.weightMap_injective f.coweightMap_injective
  have hw' : ∀ χ : characterLattice T', f.weightMap χ = t ≫ χ := hw
  have ht := eq_torusMap hT' f hw'
  refine ⟨φ, hφ, torusMap_isIsogeny hT hT' hP.1 hP'.1 f, ?_, ?_, ?_⟩
  · simpa only [ht] using hsq
  · exact fun χ => (torusMap_comp hT' f χ).symm
  · exact fun ν => (comp_torusMap hT' hP.1 hP'.1 f ν).symm

/-- Characteristic-exponent-one isogenies are central, so their realization is
already a consequence of the published central theorem. -/
theorem exists_realization_expChar_one (hG : IsConnectedReductive G)
    (hG' : IsConnectedReductive G') (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    (i : T.toGrp ⟶ G) (i' : T'.toGrp ⟶ G') (hi : IsMaximalTorus i) (hi' : IsMaximalTorus i')
    (hP : haveI := hG.isAffineHom; IsRootDatumOf i P)
    (hP' : haveI := hG'.isAffineHom; IsRootDatumOf i' P')
    (f : Langlands.LinearAlgebra.RootDatumIsogeny 1 P' P) :
    ∃ φ : G ⟶ G', IsCentralIsogeny φ ∧
      IsIsogeny (CommGroupScheme.groupHom (torusMap hT' f)) ∧
      i ≫ φ = CommGroupScheme.groupHom (torusMap hT' f) ≫ i' ∧
      (∀ χ : characterLattice T', f.weightMap χ = torusMap hT' f ≫ χ) ∧
      (∀ ν : cocharacterLattice T, f.coweightMap ν = ν ≫ torusMap hT' f) :=
  exists_central_realization hG hG' hT hT' i i' hi hi' hP hP' f f.isCentral_one

end Central

end Langlands.GroupScheme.RootDatumIsogenyRealization
