import Langlands.GroupScheme.Rational.ParabolicRootPresentation
import Langlands.GroupScheme.Rational.CrossTorusLieTransport
import Langlands.GroupScheme.Rational.ParabolicAmbientTransport
import Langlands.GroupScheme.Rational.SplitUnipotentTransport

/-! # Ambient transport of compatible parabolic root presentations -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G G' : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom G'.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- An ambient isomorphism preserves the actual simple roots on the same torus. -/
theorem simpleRelativeRoots_comp_ambientIso (i : T.toGrp ⟶ G)
    (ν : cocharacterLattice T) (e : G ≅ G') :
    simpleRelativeRoots (i ≫ e.hom) ν = simpleRelativeRoots i ν := by
  ext α
  simpa only [characterLattice.congr_apply, cocharacterLattice.congr_apply,
    Iso.refl_inv, Iso.refl_hom, Category.id_comp, Category.comp_id] using
    simpleRelativeRoots_mem_of_transport_iff (Iso.refl T) e (by
      change i ≫ e.hom = (𝟙 T.toGrp) ≫ (i ≫ e.hom)
      rw [Category.id_comp]) ν α

/-- The same generic cocharacter remains generic after an ambient isomorphism. -/
theorem isGenericCocharacter_comp_ambientIso_iff (i : T.toGrp ⟶ G)
    (ν : cocharacterLattice T) (e : G ≅ G') :
    IsGenericCocharacter (i ≫ e.hom) ν ↔ IsGenericCocharacter i ν := by
  simpa only [cocharacterLattice.congr_apply, Iso.refl_hom, Category.comp_id] using
    isGenericCocharacter_of_transport_iff (Iso.refl T) e (by
      change i ≫ e.hom = (𝟙 T.toGrp) ≫ (i ≫ e.hom)
      rw [Category.id_comp]) ν

/-- Standardness uses the same actual characters, face and cocharacter. -/
theorem isStandardCocharacter_comp_ambientIso_iff (i : T.toGrp ⟶ G)
    (ν : cocharacterLattice T) (J : Set (characterLattice T))
    (ζ : cocharacterLattice T) (e : G ≅ G') :
    IsStandardCocharacter (i ≫ e.hom) ν J ζ ↔ IsStandardCocharacter i ν J ζ := by
  simp only [IsStandardCocharacter, simpleRelativeRoots_comp_ambientIso]

omit [IsAffineHom G.X.hom] [IsAffineHom G'.X.hom] in
private theorem dynamicParabolic_comp_ambientIso
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) (e : G ≅ G') :
    Dynamic.parabolic (χ ≫ e.hom) = (Dynamic.parabolic χ).comap e.inv := by
  simpa only [Iso.symm_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id] using
    Dynamic.parabolic_eq_comap_of_iso (χ ≫ e.hom) e.symm

omit [IsAffineHom G.X.hom] [IsAffineHom G'.X.hom] in
private theorem dynamicCentralizer_comp_ambientIso
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) (e : G ≅ G') :
    Dynamic.centralizer (χ ≫ e.hom) = (Dynamic.centralizer χ).comap e.inv := by
  simpa only [Iso.symm_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id] using
    Dynamic.centralizer_eq_comap_of_iso (χ ≫ e.hom) e.symm

/-- Choice-free standard parabolics transport on every test scheme. -/
theorem standardParabolic_comp_ambientIso (i : T.toGrp ⟶ G)
    (ν : cocharacterLattice T) (J : Set (characterLattice T)) (e : G ≅ G') :
    standardParabolic (i ≫ e.hom) ν J = (standardParabolic i ν J).comap e.inv := by
  apply SubgroupFunctor.ext
  intro U
  apply Subgroup.ext
  intro x
  simp only [SubgroupFunctor.mem_comap, mem_standardParabolic,
    isStandardCocharacter_comp_ambientIso_iff, ← Category.assoc,
    dynamicParabolic_comp_ambientIso, SubgroupFunctor.mem_comap]

/-- Choice-free standard Levis transport on every test scheme. -/
theorem standardLevi_comp_ambientIso (i : T.toGrp ⟶ G)
    (ν : cocharacterLattice T) (J : Set (characterLattice T)) (e : G ≅ G') :
    standardLevi (i ≫ e.hom) ν J = (standardLevi i ν J).comap e.inv := by
  apply SubgroupFunctor.ext
  intro U
  apply Subgroup.ext
  intro x
  simp only [SubgroupFunctor.mem_comap, mem_standardLevi,
    isStandardCocharacter_comp_ambientIso_iff, ← Category.assoc,
    dynamicCentralizer_comp_ambientIso, SubgroupFunctor.mem_comap]

omit [IsAffineHom G.X.hom] [IsAffineHom G'.X.hom] in
/-- Ambient isomorphisms transport minimality of all-test parabolic functors. -/
theorem IsMinimalParabolicFunctor.comap_ambientIso
    {F : SubgroupFunctor G} (hF : IsMinimalParabolicFunctor F) (e : G ≅ G') :
    IsMinimalParabolicFunctor (F.comap e.inv) := by
  obtain ⟨P, p, hp, rfl⟩ := isMinimalParabolicFunctor_iff_exists.mp hF
  apply isMinimalParabolicFunctor_iff_exists.mpr
  exact ⟨P, p ≫ e.hom, hp.comp_iso e, SubgroupFunctor.range_comp_iso p e⟩

namespace ParabolicRootPresentation

variable {P M : GroupScheme (Spec (CommRingCat.of k))}
  {A : CommGroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}

/-- Transport the same presentation data through an actual ambient group
isomorphism. The source parabolic, Levi and split-component maps are retained. -/
def compAmbientIso (r : ParabolicRootPresentation p l a) (e : G ≅ G') :
    ParabolicRootPresentation (p ≫ e.hom) l a where
  data := { r.data with i := r.data.i ≫ e.hom }
  isCompatible := by
    refine {
      parabolic := r.isCompatible.parabolic.comp_iso e
      levi := r.isCompatible.levi
      splitComponent := r.isCompatible.splitComponent
      maximalSplit := r.isCompatible.maximalSplit.comp_iso e
      generic := (isGenericCocharacter_comp_ambientIso_iff _ _ e).mpr r.isCompatible.generic
      subset_simpleRoots := ?_
      parabolic_eq := ?_
      levi_eq := ?_
      factor_comp := ?_
      minimal := ?_
      minimal_le := ?_
      realization := ?_ }
    · simpa only [simpleRelativeRoots_comp_ambientIso] using r.isCompatible.subset_simpleRoots
    · rw [SubgroupFunctor.range_comp_iso, standardParabolic_comp_ambientIso,
        r.isCompatible.parabolic_eq]
    · rw [← Category.assoc, SubgroupFunctor.range_comp_iso,
        standardLevi_comp_ambientIso, r.isCompatible.levi_eq]
    · simpa only [Category.assoc] using
        congrArg (fun q => q ≫ e.hom) r.isCompatible.factor_comp
    · rw [← Category.assoc, dynamicParabolic_comp_ambientIso]
      exact r.isCompatible.minimal.comap_ambientIso e
    · rw [← Category.assoc, dynamicParabolic_comp_ambientIso,
        SubgroupFunctor.range_comp_iso]
      exact SubgroupFunctor.comap_mono r.isCompatible.minimal_le
    · obtain ⟨ζ, hζ, hP, hM⟩ := r.isCompatible.realization
      refine ⟨ζ, (isStandardCocharacter_comp_ambientIso_iff _ _ _ _ e).mpr hζ, ?_, ?_⟩
      · rw [SubgroupFunctor.range_comp_iso, ← Category.assoc,
          dynamicParabolic_comp_ambientIso, hP]
      · rw [← Category.assoc, SubgroupFunctor.range_comp_iso]
        change (SubgroupFunctor.range (l ≫ p)).comap e.inv =
          Dynamic.centralizer ((CommGroupScheme.groupHom ζ ≫ r.data.i) ≫ e.hom)
        rw [dynamicCentralizer_comp_ambientIso, hM]

@[simp] theorem compAmbientIso_torus (r : ParabolicRootPresentation p l a) (e : G ≅ G') :
    (r.compAmbientIso e).data.T = r.data.T := rfl

/-- The actual simple-root restrictions agree in the full real character space. -/
theorem restrictedRoots_compAmbientIso (r : ParabolicRootPresentation p l a) (e : G ≅ G') :
    (r.compAmbientIso e).restrictedRoots = r.restrictedRoots := by
  change restrictedSimpleRoots (r.data.i ≫ e.hom) r.data.ν r.data.J r.data.f = _
  simp only [restrictedSimpleRoots, simpleRelativeRoots_comp_ambientIso]

section FiniteType

variable [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType G'.X.hom]

/-- Ambient transport preserves the entire positive root-combination cone. -/
theorem positiveCone_compAmbientIso (r : ParabolicRootPresentation p l a) (e : G ≅ G') :
    (r.compAmbientIso e).positiveCone = r.positiveCone := by
  ext x
  rw [mem_positiveCone, mem_positiveCone, restrictedRoots_compAmbientIso]

/-- Ambient transport preserves the entire nonnegative root-combination cone. -/
theorem nonnegCone_compAmbientIso (r : ParabolicRootPresentation p l a) (e : G ≅ G') :
    (r.compAmbientIso e).nonnegCone = r.nonnegCone := by
  ext x
  rw [mem_nonnegCone, mem_nonnegCone, restrictedRoots_compAmbientIso]

end FiniteType

end ParabolicRootPresentation

end Langlands.GroupScheme
