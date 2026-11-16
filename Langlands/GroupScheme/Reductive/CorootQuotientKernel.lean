import Langlands.GroupScheme.Reductive.CorootTorusProjection
import Langlands.GroupScheme.Reductive.FibrewiseRootDatum
import Langlands.GroupScheme.Derived.SplitTorusCommutators
import Langlands.GroupScheme.Derived.RepresentabilityProof
import Langlands.GroupScheme.Derived.SemisimpleProof
import Langlands.GroupScheme.Derived.MaximalTorusProductSurjectivityProof
import Langlands.GroupScheme.Derived.CocenterTorusQuotientData
import Langlands.GroupScheme.Torus.DiagonalizableCharacterProof
import Langlands.AlgebraicGeometry.SurjectiveReducedEpi

/-! # The full kernel of a supplied split coroot quotient over a field -/

noncomputable section
universe u

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeDerived

variable {I J : Type u} [Fintype I] [DecidableEq I]

/-- Evaluation on the coroot quotient pulls back to the same exponent character. -/
theorem corootProjection_comp_evalCharacter
    (R : CommRingCat.{u}) (P : RootDatum J (I → ℤ) (I → ℤ))
    (m : cocenterLattice P) :
    corootProjection R P ≫
        CommGroupScheme.groupHom (DiagonalizableCharacter.evalCharacter R _ m) =
      CommGroupScheme.groupHom (splitTorus.exponentCharacter (Spec R) I m.val) := by
  apply hom_ext_points
  intro U x
  apply (Gm.pointsEquiv (Spec R) U).injective
  rw [Grp.comp_hom_hom, ← Category.assoc,
    DiagonalizableCharacter.evalCharacter_apply, corootProjection_points,
    splitTorus.pointsEquiv_exponentCharacter]

section Field

variable {k : Type u} [Field k]
  {G D : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]
  (t : splitTorus (Spec (CommRingCat.of k)) I ⟶ G)
  [Mono t.hom.hom.left]
  (P : RootDatum J (I → ℤ) (I → ℤ))

omit [DecidableEq I] in
/-- The restriction of any ambient character annihilates the actual coroots. -/
theorem characterRestrict_mem_cocenterLattice
    (hP : IsRootDatumOf t (CoordinateRootDatum.fieldRealization k P))
    {d : D ⟶ G} (hd : IsDerivedSubgroup d) (χ : rationalCharacters G) :
    splitTorus.characterLatticeEquiv k I (characterRestrict t χ) ∈ cocenterLattice P := by
  have hdc : d ≫ χ.toMul = 1 :=
    congrArg Additive.toMul (hd.characterRestrict_eq_zero χ)
  let ψ : characterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I) :=
    characterRestrict t χ
  let m := splitTorus.characterLatticeEquiv k I ψ
  have hm : splitTorus.exponentCharacter (Spec (CommRingCat.of k)) I m = ψ := by
    rw [splitTorus.exponentCharacter_eq_characterLatticeEquiv_symm]
    exact (splitTorus.characterLatticeEquiv k I).symm_apply_apply ψ
  apply (Langlands.RootDatum.mem_corootAnnihilator P Set.univ _).mpr
  intro a _
  have ha := IsRootDatumOf.coroot_mem_cocharactersLandingIn
    (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I)
    (G := G) (H := D) (j := d) t hP hd.1 hd.containsCommutators a
  have hz : (CoordinateRootDatum.fieldRealization k P).coroot a ≫ ψ = 0 := by
    apply Additive.toMul.injective
    apply hom_ext_points
    intro U x
    obtain ⟨y, hy⟩ := ha U x
    change y ≫ d.hom.hom = x ≫ (CommGroupScheme.groupHom
      ((CoordinateRootDatum.fieldRealization k P).coroot a) ≫ t).hom.hom at hy
    simp only [Grp.comp_hom_hom, ← Category.assoc] at hy
    change (x ≫ (CommGroupScheme.groupHom
      ((CoordinateRootDatum.fieldRealization k P).coroot a)).hom.hom) ≫
        (t ≫ χ.toMul).hom.hom = _
    rw [Grp.comp_hom_hom, ← Category.assoc, ← hy, Category.assoc,
      ← Grp.comp_hom_hom, hdc]
    simp
  rw [← CoordinateRootDatum.fieldRealization_pairing k P m (P.coroot a),
    hm, hP.1, ← CoordinateRootDatum.fieldRealization_coroot k P a,
    latticePairing_apply, hz, map_zero]

/-- An epimorphic subgroup product detects equality of homomorphisms. -/
theorem hom_ext_of_epi_subgroupProductMap
    {S : Scheme.{u}} {A B H Q : GroupScheme S}
    (a : A ⟶ H) (b : B ⟶ H) [Epi (subgroupProductMap a b)]
    {f g : H ⟶ Q} (ha : a ≫ f = a ≫ g) (hb : b ≫ f = b ≫ g) :
    f = g := by
  apply Grp.hom_ext
  apply (cancel_epi (subgroupProductMap a b)).mp
  have ha' := congrArg (fun h => h.hom.hom) ha
  have hb' := congrArg (fun h => h.hom.hom) hb
  simp only [Grp.comp_hom_hom] at ha' hb'
  simp only [subgroupProductMap, MonObj.mul_comp, Category.assoc, ha', hb']

/-- Every ambient character factors through a supplied coroot quotient. -/
theorem character_factors_corootQuotient
    (hP : IsRootDatumOf t (CoordinateRootDatum.fieldRealization k P))
    {d : D ⟶ G} (hd : IsDerivedSubgroup d) [Epi (subgroupProductMap d t)]
    (q : G ⟶ (corootQuotient (CommRingCat.of k) P).toGrp)
    (hq : t ≫ q = corootProjection (CommRingCat.of k) P)
    (χ : rationalCharacters G) :
    ∃ ψ : characterLattice (corootQuotient (CommRingCat.of k) P),
      χ.toMul = q ≫ CommGroupScheme.groupHom ψ := by
  let m : cocenterLattice P :=
    ⟨splitTorus.characterLatticeEquiv k I (characterRestrict t χ),
      characterRestrict_mem_cocenterLattice t P hP hd χ⟩
  have hm : splitTorus.exponentCharacter (Spec (CommRingCat.of k)) I m.val =
      characterRestrict t χ := by
    rw [splitTorus.exponentCharacter_eq_characterLatticeEquiv_symm]
    exact (splitTorus.characterLatticeEquiv k I).symm_apply_apply _
  refine ⟨DiagonalizableCharacter.evalCharacter (CommRingCat.of k) _ m, ?_⟩
  apply hom_ext_of_epi_subgroupProductMap d t
  · have hdc : d ≫ χ.toMul = 1 :=
      congrArg Additive.toMul (hd.characterRestrict_eq_zero χ)
    rw [← Category.assoc, hd.comp_eq_one q, MonObj.one_comp]
    exact hdc
  · rw [← Category.assoc, hq, corootProjection_comp_evalCharacter]
    exact congrArg (fun ψ : characterLattice
      (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I) =>
        CommGroupScheme.groupHom ψ) hm.symm

/-- A supplied extension of the coroot projection has the actual derived subgroup
as its full scheme kernel over every field. -/
theorem isDerivedSubgroup_kernelι_of_corootProjection
    (hG : IsConnectedReductive G)
    (ht : IsMaximalTorus (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I) t)
    (hP : IsRootDatumOf t (CoordinateRootDatum.fieldRealization k P))
    (q : G ⟶ (corootQuotient (CommRingCat.of k) P).toGrp)
    (hq : t ≫ q = corootProjection (CommRingCat.of k) P) :
    IsDerivedSubgroup (kernelι q) := by
  let : Smooth G.X.hom := hG.smooth
  let : LocallyOfFiniteType G.X.hom := inferInstance
  obtain ⟨D', d, _, _, hd⟩ := derivedSubgroupRepresentability k G
  have hp := derivedMaximalTorusProductSurjectivity k G D'
    (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I) d t hG hd ht
  let : Epi (subgroupProductMap d t) :=
    hG.epi_subgroupProductMap_of_surjective d t hp.surj
  let Cdata := hd.commutativeQuotientData
  let C := Cdata.1
  let c := Cdata.2.1
  have hC := Cdata.2.2
  let : Smooth C.X.hom := hC.1
  let : IsAffineHom C.X.hom := hC.2.1
  have hc : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range d) c := hC.2.2
  have hs : IsSplitTorus C.toGrp :=
    (isSplitTorus_splitTorus (S := Spec (CommRingCat.of k)) I).of_surjective_hom_to_smooth
      (t ≫ c) (hd.surjective_comp_of_surjective_product t c hp hc.2.1)
  refine ⟨inferInstanceAs (IsClosedImmersion (kernelι q).hom.hom.left),
    le_antisymm ?_ (derivedSubgroup_le_range_kernelι q)⟩
  intro U x hx
  have hxq := (mem_range_kernelι_iff q x).mp hx
  have hxc : x ≫ c.hom.hom = 1 := by
    apply (characterLattice.pointCharactersEquiv C hs U).injective
    rw [map_one]
    apply MonoidHom.ext
    intro χ
    change Gm.pointsEquiv _ U
      ((x ≫ c.hom.hom) ≫ (CommGroupScheme.groupHom χ.toAdd).hom.hom) = 1
    obtain ⟨ψ, hψ⟩ := character_factors_corootQuotient t P hP hd q hq
      (Additive.ofMul (c ≫ CommGroupScheme.groupHom χ.toAdd))
    change c ≫ CommGroupScheme.groupHom χ.toAdd =
      q ≫ CommGroupScheme.groupHom ψ at hψ
    rw [Category.assoc, ← Grp.comp_hom_hom, hψ, Grp.comp_hom_hom,
      ← Category.assoc, hxq, MonObj.one_comp, map_one]
  rw [← hd.2, ← hc.2.2.2]
  exact (mem_range_kernelι_iff c x).mpr hxc

/-- The full kernel of a supplied extension of the coroot projection is semisimple. -/
theorem isSemisimple_kernel_of_corootProjection
    (hG : IsConnectedReductive G)
    (ht : IsMaximalTorus (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I) t)
    (hP : IsRootDatumOf t (CoordinateRootDatum.fieldRealization k P))
    (q : G ⟶ (corootQuotient (CommRingCat.of k) P).toGrp)
    (hq : t ≫ q = corootProjection (CommRingCat.of k) P) :
    IsSemisimple (kernel q) :=
  derivedSubgroupSemisimple k G (kernel q) (kernelι q) hG
    (isDerivedSubgroup_kernelι_of_corootProjection t P hG ht hP q hq)

/-- Compare the full kernel with any specified actual derived subgroup,
compatibly with its inclusion in the ambient field group. -/
def corootQuotientKernelIsoDerived
    (hG : IsConnectedReductive G)
    (ht : IsMaximalTorus (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I) t)
    (hP : IsRootDatumOf t (CoordinateRootDatum.fieldRealization k P))
    (q : G ⟶ (corootQuotient (CommRingCat.of k) P).toGrp)
    (hq : t ≫ q = corootProjection (CommRingCat.of k) P)
    {d : D ⟶ G} (hd : IsDerivedSubgroup d) : kernel q ≅ D :=
  (isDerivedSubgroup_kernelι_of_corootProjection t P hG ht hP q hq).isRepresentedBy
    |>.isoOfIsRepresentedBy hd.isRepresentedBy

end Field

end Langlands.GroupScheme.RelativeDerived
