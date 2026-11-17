import Langlands.GroupScheme.Torus.DiagonalizableHomLocalRestriction
import Langlands.GroupScheme.Torus.DiagonalizableAutomorphismLocality
import Langlands.GroupScheme.Torus.CentralExtensionHopfSpec
import Langlands.AbelianScheme.Tate.BaseChangeCoherence

/-! # Local character surjections for closed diagonalizable inclusions -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Diagonalizable

variable {R R' : CommRingCat.{u}} {Λ Γ : Type u} [AddCommGroup Λ] [AddCommGroup Γ]

/-- Over a nonzero ring, a closed character-restriction map has a surjective
map of full character groups. -/
theorem surjective_of_isClosedSubgroup_restrictMap [Nontrivial R] (p : Λ →+ Γ)
    (hp : IsClosedSubgroup (restrictMap R p)) : Function.Surjective p := by
  classical
  have : IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom R p))) := by
    rw [← restrictMap_left]
    exact hp
  have hsurj := CentralExtensionHopfSpec.surjective_of_isClosedImmersion
    (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom R p))
  intro n
  by_contra hn
  obtain ⟨a, ha⟩ := hsurj (AddMonoidAlgebra.single n 1)
  change (AddMonoidAlgebra.mapDomainRingHom R p) a = AddMonoidAlgebra.single n 1 at ha
  have hz : ((AddMonoidAlgebra.mapDomainRingHom R p) a).coeff n = 0 :=
    Finsupp.mapDomain_of_notMem_range a.coeff n hn
  rw [ha] at hz
  exact (one_ne_zero (α := R))
    (by simpa only [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same] using hz)

/-- A nonempty change of base detects surjectivity of the full character map
when the base-changed restriction is a closed subgroup. -/
theorem surjective_of_closed_baseChange
    {S : Scheme.{u}} [Nonempty S] (b : S ⟶ Spec R) (p : Λ →+ Γ)
    (hp : IsClosedSubgroup ((baseChange b).map (restrictMap R p))) :
    Function.Surjective p := by
  obtain ⟨s⟩ := ‹Nonempty S›
  let c := S.fromSpecResidueField s
  let d := c ≫ b
  let D := (baseChange d).map (restrictMap R p)
  let E := (baseChange c).map ((baseChange b).map (restrictMap R p))
  let eΓ := baseChangeCompIso b c (groupScheme R Γ).toGrp
  let eΛ := baseChangeCompIso b c (groupScheme R Λ).toGrp
  have hn : D ≫ eΛ.hom = eΓ.hom ≫ E :=
    ((Functor.mapGrpNatIso (Over.pullbackComp c b)) ≪≫
      Functor.mapGrpCompIso).hom.naturality (restrictMap R p)
  have hE : IsClosedSubgroup E := hp.baseChange c
  have hD : IsClosedSubgroup D := by
    have h := (IsClosedSubgroup.iso_comp eΓ hE).comp_iso eΛ.symm
    change IsClosedSubgroup ((eΓ.hom ≫ E) ≫ eΛ.inv) at h
    have heq : (eΓ.hom ≫ E) ≫ eΛ.inv = D := by
      rw [← hn, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rwa [heq] at h
  let aΓ := baseChangeIso d Γ
  let aΛ := baseChangeIso d Λ
  have hres : IsClosedSubgroup (restrictMap (S.residueField s) p) := by
    have h := IsClosedSubgroup.iso_comp aΓ.symm (hD.comp_iso aΛ)
    change IsClosedSubgroup (aΓ.inv ≫ D ≫ aΛ.hom) at h
    have hn' : D ≫ aΛ.hom = aΓ.hom ≫ restrictMap (S.residueField s) p :=
      baseChangeIso_restrictMap d p
    have heq : aΓ.inv ≫ D ≫ aΛ.hom = restrictMap (S.residueField s) p := by
      rw [hn', Iso.inv_hom_id_assoc]
    rwa [heq] at h
  exact surjective_of_isClosedSubgroup_restrictMap p hres

/-- Every chosen local restriction of a closed diagonalizable inclusion
comes from a surjection of full character groups. -/
theorem restrictionCharacterMap_surjective [AddGroup.FG Λ]
    (f : (groupScheme R Γ).toGrp ⟶ (groupScheme R Λ).toGrp)
    (hf : IsClosedSubgroup f) (s : (restrictionCover f).I₀) :
    Function.Surjective (restrictionCharacterMap f s) := by
  have : Nonempty ((restrictionCover f).X s) :=
    ⟨⟨s, (exists_open_restriction f s).choose_spec.choose_spec.1⟩⟩
  apply surjective_of_closed_baseChange ((restrictionCover f).f s)
  rw [← restrictionCover_map_eq]
  exact hf.baseChange _

/-- The chosen local character surjection of a closed diagonalizable inclusion. -/
def restrictionSurjection [AddGroup.FG Λ]
    (f : (groupScheme R Γ).toGrp ⟶ (groupScheme R Λ).toGrp)
    (hf : IsClosedSubgroup f) (s : (restrictionCover f).I₀) :
    {p : Λ →+ Γ // Function.Surjective p} :=
  ⟨restrictionCharacterMap f s, restrictionCharacterMap_surjective f hf s⟩

end Langlands.GroupScheme.Diagonalizable
