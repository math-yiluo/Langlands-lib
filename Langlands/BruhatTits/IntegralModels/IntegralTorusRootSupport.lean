import Langlands.BruhatTits.IntegralModels.FacetLieWeights
import Langlands.BruhatTits.IntegralModels.ReductiveQuotientRoots
import Langlands.GroupScheme.Torus.LocalRootSupportComparison
import Langlands.GroupScheme.Rational.CrossTorusLieTransport

/-! # Actual root support through an integral split torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

section LocalSupport

variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {k l : Type u} [Field k] [Field l] [Algebra R k] [Algebra R l]
  (H : GroupScheme (Spec (CommRingCat.of R)))
  [Smooth H.X.hom] [IsAffineHom H.X.hom]

local instance integralRootSupport_fibreAffine {A : Type u} [CommRing A] [Algebra R A] :
    IsAffineHom ((baseChange (algebraBaseMap R A)).obj H).X.hom :=
  inferInstanceAs (IsAffineHom (CategoryTheory.Limits.pullback.snd H.X.hom
    (algebraBaseMap R A)))

private theorem coordinate_root_baseChange_iff
    (I : Type u) [Fintype I] [DecidableEq I]
    (j : splitTorus (Spec (CommRingCat.of R)) I ⟶ H)
    (χ : characterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I)) :
    characterLattice.baseChange (algebraBaseMap R k) _ χ ∈
        roots ((baseChange (algebraBaseMap R k)).map j) ↔
      characterLattice.baseChange (algebraBaseMap R l) _ χ ∈
        roots ((baseChange (algebraBaseMap R l)).map j) := by
  let m := splitTorus.characterLatticeEquiv R I χ
  have hχ : χ = splitTorus.exponentCharacter (Spec (CommRingCat.of R)) I m := by
    change χ = ∑ a, m a • splitTorus.proj _ I a
    have hc := ((splitTorus.characterLatticeEquiv R I).symm_apply_apply χ).symm
    change χ = ∑ᶠ a, m a • splitTorus.proj _ I a at hc
    simpa only [finsum_eq_sum_of_fintype] using hc
  rw [hχ]
  have hk := roots_mem_of_transport_iff
    (splitTorus.commBaseChangeIso (algebraBaseMap R k) I)
    (Iso.refl ((baseChange (algebraBaseMap R k)).obj H))
    (i := (baseChange (algebraBaseMap R k)).map j)
    (j := splitTorus.baseChangeHom (K := k) H I j)
    (by simp [splitTorus.baseChangeHom, splitTorus.commBaseChangeIso,
      CommGroupScheme.isoOfGroupIso])
    (characterLattice.baseChange (algebraBaseMap R k) _
      (splitTorus.exponentCharacter _ I m))
  have hl := roots_mem_of_transport_iff
    (splitTorus.commBaseChangeIso (algebraBaseMap R l) I)
    (Iso.refl ((baseChange (algebraBaseMap R l)).obj H))
    (i := (baseChange (algebraBaseMap R l)).map j)
    (j := splitTorus.baseChangeHom (K := l) H I j)
    (by simp [splitTorus.baseChangeHom, splitTorus.commBaseChangeIso,
      CommGroupScheme.isoOfGroupIso])
    (characterLattice.baseChange (algebraBaseMap R l) _
      (splitTorus.exponentCharacter _ I m))
  have hex (A : Type u) [Field A] [Algebra R A] :
      characterLattice.congr (splitTorus.commBaseChangeIso (algebraBaseMap R A) I)
        (characterLattice.baseChange (algebraBaseMap R A) _
          (splitTorus.exponentCharacter _ I m)) =
        splitTorus.exponentCharacter (Spec (CommRingCat.of A)) I m := by
    rw [characterLattice.congr_apply,
      ← splitTorus.exponentCharacter_baseChange (Spec (CommRingCat.of R)) I
        (algebraBaseMap R A) m, Iso.inv_hom_id_assoc]
  rw [hex k] at hk
  rw [hex l] at hl
  exact hk.symm.trans
    ((splitTorus.mem_roots_fieldBaseChange_iff_of_isLocalRing
      (k := k) (l := l) I H j m).trans hl)

/-- A fixed integral character has the same actual root membership on any two
field-valued fibres over a local domain. -/
theorem mem_roots_baseChange_iff_of_split
    (T : CommGroupScheme (Spec (CommRingCat.of R)))
    (j : T.toGrp ⟶ H) (hT : IsSplitTorus T.toGrp) (χ : characterLattice T) :
    characterLattice.baseChange (algebraBaseMap R k) T χ ∈
        roots ((baseChange (algebraBaseMap R k)).map j) ↔
      characterLattice.baseChange (algebraBaseMap R l) T χ ∈
        roots ((baseChange (algebraBaseMap R l)).map j) := by
  classical
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let : Fintype I := Fintype.ofFinite I
  let e' : T ≅ splitTorus.commGroupScheme _ I := CommGroupScheme.isoOfGroupIso e
  have fibre (A : Type u) [Field A] [Algebra R A] :
      characterLattice.baseChange (algebraBaseMap R A) T χ ∈
          roots ((baseChange (algebraBaseMap R A)).map j) ↔
        characterLattice.baseChange (algebraBaseMap R A) _
          (characterLattice.congr e' χ) ∈
            roots ((baseChange (algebraBaseMap R A)).map (e.inv ≫ j)) := by
    have he := roots_mem_of_transport_iff
      ((CommGroupScheme.baseChange (algebraBaseMap R A)).mapIso e')
      (Iso.refl ((baseChange (algebraBaseMap R A)).obj H))
      (i := (baseChange (algebraBaseMap R A)).map j)
      (j := (baseChange (algebraBaseMap R A)).map (e.inv ≫ j))
      (by
        change (baseChange (algebraBaseMap R A)).map j =
          (baseChange (algebraBaseMap R A)).map e.hom ≫
            (baseChange (algebraBaseMap R A)).map (e.inv ≫ j)
        rw [← Functor.map_comp, ← Category.assoc, Iso.hom_inv_id, Category.id_comp])
      (characterLattice.baseChange (algebraBaseMap R A) T χ)
    simpa only [characterLattice.congr_apply,
      characterLattice.baseChange_precomp, Functor.mapIso_inv] using he.symm
  exact (fibre k).trans
    ((coordinate_root_baseChange_iff (k := k) (l := l) H I (e.inv ≫ j)
      (characterLattice.congr e' χ)).trans (fibre l).symm)

end LocalSupport

end Langlands.GroupScheme

namespace Langlands.BruhatTits.IntegralModels

open GroupScheme

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] [IsLocalRing R]
  {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom G.X.hom]

namespace IntegralTorusData

variable {D : RelativeComponentModelData R K G}
  {S : CommGroupScheme (Spec (CommRingCat.of K))} {i : S.toGrp ⟶ G}
  (T : IntegralTorusData D S i) (hT : IsSplitTorus T.torus.toGrp)

local instance integralRootSupport_neutralSmooth : Smooth D.neutral.group.X.hom :=
  D.neutral_smooth

local instance integralRootSupport_neutralFibreAffine {A : Type u}
    [CommRing A] [Algebra R A] :
    IsAffineHom ((baseChange (algebraBaseMap R A)).obj D.neutral.group).X.hom :=
  inferInstanceAs (IsAffineHom (CategoryTheory.Limits.pullback.snd D.neutral.group.X.hom
    (algebraBaseMap R A)))

local instance integralRootSupport_neutralSpecialAffine :
    IsAffineHom D.neutral.specialFibre.X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd D.neutral.group.X.hom
    (IntegralModel.residueBaseMap R))
  infer_instance

omit [IsLocalRing R] in
/-- The specified generic-fibre square transports each actual integral
character's generic root membership. -/
theorem mem_relativeRoots_genericCharacter_iff (χ : characterLattice T.torus) :
    T.genericCharacter χ ∈ relativeRoots i ↔
      characterLattice.baseChange (Spec.algebraMap R K) T.torus χ ∈
        roots ((baseChange (Spec.algebraMap R K)).map T.inclusion) := by
  let e : (CommGroupScheme.baseChange (Spec.algebraMap R K)).obj T.torus ≅ S :=
    CommGroupScheme.isoOfGroupIso T.genericIso
  have he := roots_mem_of_transport_iff
    (S := (CommGroupScheme.baseChange (Spec.algebraMap R K)).obj T.torus) (S' := S)
    (G := D.neutral.genericFibre) (H := G)
    (i := (baseChange (Spec.algebraMap R K)).map T.inclusion) (j := i)
    e D.neutral.genericIso T.generic_comm
    (characterLattice.baseChange (Spec.algebraMap R K) T.torus χ)
  exact he

include hT

/-- Actual root membership of the generic and neutral special fibres agrees
for the same integral character. -/
theorem mem_relativeRoots_specialCharacter_iff (χ : characterLattice T.torus) :
    T.specialCharacter χ ∈ relativeRoots T.specialFibreInclusion ↔
      T.genericCharacter χ ∈ relativeRoots i := by
  rw [T.mem_relativeRoots_genericCharacter_iff]
  exact (mem_roots_baseChange_iff_of_split
    (k := K) (l := IsLocalRing.ResidueField R)
    D.neutral.group T.torus T.inclusion hT χ).symm

/-- The canonical specialization through the supplied integral split torus
preserves and reflects actual relative roots. -/
theorem mem_relativeRoots_characterSpecialization_iff (χ : characterLattice S) :
    T.characterSpecialization hT χ ∈ relativeRoots T.specialFibreInclusion ↔
      χ ∈ relativeRoots i := by
  obtain ⟨χ₀, rfl⟩ := (T.genericCharacterEquiv hT).surjective χ
  change T.characterSpecialization hT (T.genericCharacter χ₀) ∈
    relativeRoots T.specialFibreInclusion ↔ T.genericCharacter χ₀ ∈ relativeRoots i
  rw [T.characterSpecialization_genericCharacter]
  exact T.mem_relativeRoots_specialCharacter_iff hT χ₀

/-- Equality of the actual neutral special-fibre root set with the canonical
specializations of the generic roots. -/
theorem relativeRoots_specialFibre_eq_image :
    relativeRoots T.specialFibreInclusion =
      T.characterSpecialization hT '' relativeRoots i := by
  ext χ
  obtain ⟨χ₀, rfl⟩ := (T.characterSpecialization hT).surjective χ
  rw [T.mem_relativeRoots_characterSpecialization_iff]
  constructor
  · intro hχ
    exact ⟨χ₀, hχ, rfl⟩
  · rintro ⟨χ₁, hχ₁, he⟩
    exact (T.characterSpecialization hT).injective he ▸ hχ₁

/-- The actual root-set bijection induced by the supplied integral torus.
No quotient-root survival or facet assumption enters its construction. -/
def rootsSpecializationEquiv :
    relativeRoots i ≃ relativeRoots T.specialFibreInclusion :=
  (T.characterSpecialization hT).toEquiv.subtypeEquiv
    (fun χ => (T.mem_relativeRoots_characterSpecialization_iff hT χ).symm)

@[simp]
theorem rootsSpecializationEquiv_character (α : relativeRoots i) :
    (T.rootsSpecializationEquiv hT α).val =
      T.characterSpecialization hT α.val := rfl

/-- Every actual reductive-quotient root specializes an actual generic root.
This is containment in the generic support, without a facet criterion. -/
theorem relativeRoots_quotient_subset_image
    (Q : SpecialFibreQuotientData D) (hQ : Q.IsReductiveQuotient) :
    relativeRoots (T.specialFibreInclusion ≫ Q.projection) ⊆
      T.characterSpecialization hT '' relativeRoots i := by
  rw [← T.relativeRoots_specialFibre_eq_image hT]
  exact Q.relativeRoots_subset_specialFibre hQ T hT

end IntegralTorusData
end Langlands.BruhatTits.IntegralModels
