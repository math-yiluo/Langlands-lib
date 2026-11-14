import Langlands.BruhatTits.IntegralModels.UnramifiedZeroFixerResidueRoots
import Langlands.GroupScheme.Torus.LocalRootSupportComparison
import Langlands.GroupScheme.Rational.CrossTorusLieTransport

/-! # Actual full-special-fibre root support of zero-fixer models -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.LocalGalois.Separable

namespace Langlands.BruhatTits.IntegralModels

section LocalComparison

variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
    {k l : Type u} [Field k] [Field l] [Algebra R k] [Algebra R l]
    (H : GroupScheme (Spec (CommRingCat.of R)))
    [IsAffineHom H.X.hom] [Smooth H.X.hom]

private instance localFibre_affine {A : Type u} [CommRing A] [Algebra R A] :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap R A)).obj H).X.hom :=
  MorphismProperty.pullback_snd _ _ (inferInstanceAs (IsAffineHom H.X.hom))

private theorem coordinate_mem_roots_baseChange_iff
    (I : Type u) [Fintype I] [DecidableEq I]
    (j : splitTorus (Spec (CommRingCat.of R)) I ⟶ H)
    (χ : characterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I)) :
    characterLattice.baseChange (algebraBaseMap R k) _ χ ∈
        roots ((GroupScheme.baseChange (algebraBaseMap R k)).map j) ↔
      characterLattice.baseChange (algebraBaseMap R l) _ χ ∈
        roots ((GroupScheme.baseChange (algebraBaseMap R l)).map j) := by
  obtain ⟨m, rfl⟩ := (splitTorus.characterLatticeEquiv R I).symm.surjective χ
  have hexp : (splitTorus.characterLatticeEquiv R I).symm m =
      splitTorus.exponentCharacter (Spec (CommRingCat.of R)) I m :=
    splitTorus.characterLatticeEquiv_symm_eq R I m
  rw [hexp]
  have hf {q : Type u} [Field q] [Algebra R q] :
      characterLattice.baseChange (algebraBaseMap R q) _
          (splitTorus.exponentCharacter (Spec (CommRingCat.of R)) I m) ∈
          roots ((GroupScheme.baseChange (algebraBaseMap R q)).map j) ↔
        splitTorus.exponentCharacter (Spec (CommRingCat.of q)) I m ∈
          roots (splitTorus.baseChangeHom (K := q) H I j) := by
    have ht := roots_mem_of_transport_iff
      (splitTorus.commBaseChangeIso (algebraBaseMap R q) I).symm
      (Iso.refl ((GroupScheme.baseChange (algebraBaseMap R q)).obj H))
      (i := splitTorus.baseChangeHom (K := q) H I j)
      (j := (GroupScheme.baseChange (algebraBaseMap R q)).map j)
      (by rfl) (splitTorus.exponentCharacter (Spec (CommRingCat.of q)) I m)
    simpa only [characterLattice.congr_apply, Iso.symm_inv,
      splitTorus.exponentCharacter_baseChange] using ht
  rw [hf, hf]
  exact splitTorus.mem_roots_fieldBaseChange_iff_of_isLocalRing I H j m

/-- Actual character-root membership agrees on two field fibres of a smooth
model over a local domain, using one actual integral split torus. -/
theorem integralSplit_mem_roots_baseChange_iff
    (T : CommGroupScheme (Spec (CommRingCat.of R))) (hT : IsSplitTorus T.toGrp)
    (j : T.toGrp ⟶ H) (χ : characterLattice T) :
    characterLattice.baseChange (algebraBaseMap R k) T χ ∈
        roots ((GroupScheme.baseChange (algebraBaseMap R k)).map j) ↔
      characterLattice.baseChange (algebraBaseMap R l) T χ ∈
        roots ((GroupScheme.baseChange (algebraBaseMap R l)).map j) := by
  classical
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let : Fintype I := Fintype.ofFinite I
  let c : T ≅ splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I :=
    CommGroupScheme.isoOfGroupIso e
  let j₀ : splitTorus (Spec (CommRingCat.of R)) I ⟶ H := e.inv ≫ j
  have hf {q : Type u} [Field q] [Algebra R q] :
      characterLattice.baseChange (algebraBaseMap R q) T χ ∈
          roots ((GroupScheme.baseChange (algebraBaseMap R q)).map j) ↔
        characterLattice.baseChange (algebraBaseMap R q) _ (c.inv ≫ χ) ∈
          roots ((GroupScheme.baseChange (algebraBaseMap R q)).map j₀) := by
    have ht := roots_mem_of_transport_iff
      ((CommGroupScheme.baseChange (algebraBaseMap R q)).mapIso c)
      (Iso.refl ((GroupScheme.baseChange (algebraBaseMap R q)).obj H))
      (i := (GroupScheme.baseChange (algebraBaseMap R q)).map j)
      (j := (GroupScheme.baseChange (algebraBaseMap R q)).map j₀)
      (by
        change (GroupScheme.baseChange (algebraBaseMap R q)).map j ≫ 𝟙 _ =
          (GroupScheme.baseChange (algebraBaseMap R q)).map e.hom ≫
            (GroupScheme.baseChange (algebraBaseMap R q)).map (e.inv ≫ j)
        rw [Category.comp_id, ← Functor.map_comp, ← Category.assoc, e.hom_inv_id,
          Category.id_comp])
      (characterLattice.baseChange (algebraBaseMap R q) T χ)
    simpa only [characterLattice.congr_apply, Functor.mapIso_inv,
      ← characterLattice.baseChange_precomp] using ht.symm
  rw [hf, hf]
  exact coordinate_mem_roots_baseChange_iff H I j₀ (c.inv ≫ χ)

end LocalComparison

namespace IntegralSplitTorusData

variable {R K : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {S : CommGroupScheme (Spec (CommRingCat.of K))}
    {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom G.X.hom]
    {i : S.toGrp ⟶ G} {N : IntegralModel R K G}
    [Smooth N.group.X.hom] (A : IntegralSplitTorusData N i)

private instance rootSupport_specialFibre_affine : IsAffineHom N.specialFibre.X.hom :=
  MorphismProperty.pullback_snd _ _ (inferInstanceAs (IsAffineHom N.group.X.hom))

/-- Character specialization identifies all actual roots of the generic group
with all actual roots of the full special fibre. -/
theorem mem_roots_characterSpecialization_iff (χ : characterLattice S) :
    A.characterSpecialization χ ∈ relativeRoots A.specialFibreInclusion ↔
      χ ∈ relativeRoots i := by
  have hc := integralSplit_mem_roots_baseChange_iff
    (k := IsLocalRing.ResidueField R) (l := K) N.group A.torus A.isSplit A.inclusion
    (A.integralCharacter χ)
  have hg := roots_mem_of_transport_iff A.genericIso N.genericIso A.generic_comm
    (characterLattice.baseChange (Spec.algebraMap R K) A.torus (A.integralCharacter χ))
  rw [A.generic_integralCharacter χ] at hg
  exact hc.trans hg.symm

/-- The canonical character specialization restricts to an equivalence of the
actual roots, with the full special fibre as its target. -/
def fullSpecialFibreRootsEquiv : relativeRoots i ≃ relativeRoots A.specialFibreInclusion :=
  A.characterSpecialization.toEquiv.subtypeEquiv
    (fun χ => (A.mem_roots_characterSpecialization_iff χ).symm)

@[simp] theorem fullSpecialFibreRootsEquiv_apply (a : relativeRoots i) :
    (A.fullSpecialFibreRootsEquiv a).val = A.characterSpecialization a := rfl

end IntegralSplitTorusData

end Langlands.BruhatTits.IntegralModels
