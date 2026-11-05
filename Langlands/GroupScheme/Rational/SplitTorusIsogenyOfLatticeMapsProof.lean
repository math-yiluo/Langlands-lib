import Langlands.GroupScheme.Rational.SplitTorusIsogenyOfLatticeMapsStatement
import Langlands.GroupScheme.Rational.SplitTorusIsogenyCharacters
import Langlands.GroupScheme.Rational.SplitTorusMonomorphism
import Langlands.GroupScheme.Torus.DiagonalizableFaithfullyFlat
import Langlands.GroupScheme.Torus.SplitLatticeBaseChange
import Mathlib.GroupTheory.FiniteAbelian.Basic

/-! # Proof: injective character and cocharacter maps give an isogeny of split tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- An injective integral linear map between coordinate lattices whose target rank is at most
its source rank has finite cokernel. -/
theorem finite_quotient_range_of_injective_of_card_le {I J : Type*} [Fintype I] [Fintype J]
    (f : (J → ℤ) →ₗ[ℤ] (I → ℤ)) (hf : Function.Injective f)
    (hcard : Fintype.card I ≤ Fintype.card J) :
    Finite ((I → ℤ) ⧸ LinearMap.range f) := by
  have hrange : Module.finrank ℤ (LinearMap.range f) = Fintype.card J := by
    rw [LinearMap.finrank_range_of_inj hf, Module.finrank_fintype_fun_eq_card]
  have hsum := Submodule.finrank_quotient_add_finrank (LinearMap.range f)
  rw [hrange, Module.finrank_fintype_fun_eq_card] at hsum
  have hzero : Module.finrank ℤ ((I → ℤ) ⧸ LinearMap.range f) = 0 := by omega
  apply Module.finite_of_fg_torsion
  intro x
  obtain ⟨a, ha, hax⟩ := Module.finrank_eq_zero_iff.mp hzero x
  exact ⟨⟨a, mem_nonZeroDivisors_of_ne_zero ha⟩, hax⟩

namespace Diagonalizable

/-- Along an injective lattice map with finite cokernel, the map of group algebras is
finite. -/
theorem finite_mapDomainRingHom {R : Type*} [CommRing R] {Λ' Λ : Type*} [AddCommGroup Λ']
    [AddCommGroup Λ] {g : Λ' →+ Λ} (hg : Function.Injective g) [Finite (Λ ⧸ g.range)] :
    (AddMonoidAlgebra.mapDomainRingHom R g).Finite := by
  let := mapDomainAlgebra (g := g) R
  change Module.Finite (AddMonoidAlgebra R Λ') (AddMonoidAlgebra R Λ)
  exact Module.Finite.equiv (LinearEquiv.ofBijective _ (cosetLinearMap_bijective hg R))

end Diagonalizable

namespace splitTorus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable {k : Type u} [Field k] (I J : Type u) [Fintype I] [Fintype J]

local notation "R" => CommRingCat.of k
local notation "S" => Spec R

/-- A map of split tori whose integral character map is injective with finite cokernel is an
isogeny. -/
theorem isIsogeny_of_characterMap (f : splitTorus S I ⟶ splitTorus S J)
    (hinj : Function.Injective (characterMap I J f))
    (hfin : Finite ((I → ℤ) ⧸ LinearMap.range (characterMap I J f))) :
    IsIsogeny f := by
  classical
  let eI := Diagonalizable.splitIso R (AddEquiv.refl (I → ℤ))
  let eJ := Diagonalizable.splitIso R (AddEquiv.refl (J → ℤ))
  have he : f = eI.inv ≫ diagonalizableMap I J f ≫ eJ.hom := by
    rw [diagonalizableMap_splitIso, Iso.inv_hom_id_assoc]
  let g := (characterMap I J f).toAddMonoidHom
  have hg : Function.Injective g := hinj
  have : Finite ((I → ℤ) ⧸ g.range) := hfin
  have hleft : (diagonalizableMap I J f).hom.hom.left =
      Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom k g)) := by
    rw [diagonalizableMap_hom_left, Diagonalizable.incl_toRingHom]
  have hD : IsIsogeny (diagonalizableMap I J f) := by
    have hff := (flat_and_surjective_SpecMap_iff
      (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom k g))).2
      (Diagonalizable.faithfullyFlat_mapDomainRingHom hg k)
    change isogenyProperty (diagonalizableMap I J f).hom.hom.left
    rw [hleft]
    refine ⟨?_, hff.1, hff.2⟩
    exact (IsFinite.SpecMap_iff _).2 (Diagonalizable.finite_mapDomainRingHom hg)
  rw [he]
  exact (isCentralIsogeny_of_isIso eI.inv).isIsogeny.comp
    (hD.comp (isCentralIsogeny_of_isIso eJ.hom).isIsogeny)

end splitTorus

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A homomorphism of split tori with injective character and cocharacter maps is an
isogeny. -/
theorem splitTorusIsogenyOfLatticeMaps : SplitTorusIsogenyOfLatticeMapsStatement.{u} := by
  intro k _ T T' t hT hT' hX hY
  classical
  obtain ⟨I, hI, ⟨eA⟩⟩ := hT
  obtain ⟨J, hJ, ⟨eT⟩⟩ := hT'
  let := Fintype.ofFinite I
  let := Fintype.ofFinite J
  let eA' : T ≅ splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I :=
    CommGroupScheme.isoOfGroupIso eA
  let eT' : T' ≅ splitTorus.commGroupScheme (Spec (CommRingCat.of k)) J :=
    CommGroupScheme.isoOfGroupIso eT
  let q : splitTorus (Spec (CommRingCat.of k)) I ⟶ splitTorus (Spec (CommRingCat.of k)) J :=
    eA.inv ≫ CommGroupScheme.groupHom t ≫ eT.hom
  have ha : (Additive.ofMul q : splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I ⟶
      splitTorus.commGroupScheme (Spec (CommRingCat.of k)) J) = eA'.inv ≫ t ≫ eT'.hom := rfl
  -- The integral character map of `q` is injective.
  have hXq : Function.Injective (splitTorus.characterMap I J q) := by
    intro x y hxy
    obtain ⟨χ, rfl⟩ := (splitTorus.characterLatticeEquiv k J).surjective x
    obtain ⟨ψ, rfl⟩ := (splitTorus.characterLatticeEquiv k J).surjective y
    rw [splitTorus.characterMap_equiv, splitTorus.characterMap_equiv] at hxy
    have h1 := (splitTorus.characterLatticeEquiv k I).injective hxy
    rw [ha] at h1
    simp only [Category.assoc] at h1
    have h2 := hX ((cancel_epi eA'.inv).mp h1)
    rw [(cancel_epi eT'.hom).mp h2]
  -- The integral cocharacter map of `q` is injective.
  have hYq : Function.Injective (splitTorus.cocharacterMap I J q) := by
    intro x y hxy
    change splitTorus.cocharacterLatticeEquiv k J
        ((splitTorus.cocharacterLatticeEquiv k I).symm x ≫ Additive.ofMul q) =
      splitTorus.cocharacterLatticeEquiv k J
        ((splitTorus.cocharacterLatticeEquiv k I).symm y ≫ Additive.ofMul q) at hxy
    have h1 := (splitTorus.cocharacterLatticeEquiv k J).injective hxy
    rw [ha] at h1
    simp only [← Category.assoc] at h1
    have h2 := (cancel_mono eT'.hom).mp h1
    have h3 : (splitTorus.cocharacterLatticeEquiv k I).symm x ≫ eA'.inv =
        (splitTorus.cocharacterLatticeEquiv k I).symm y ≫ eA'.inv := hY h2
    exact (splitTorus.cocharacterLatticeEquiv k I).symm.injective ((cancel_mono eA'.inv).mp h3)
  -- Equal ranks, hence a finite cokernel.
  have hJI : Fintype.card J ≤ Fintype.card I := by
    simpa only [Module.finrank_fintype_fun_eq_card] using
      LinearMap.finrank_le_finrank_of_injective hXq
  have hIJ : Fintype.card I ≤ Fintype.card J := by
    simpa only [Module.finrank_fintype_fun_eq_card] using
      LinearMap.finrank_le_finrank_of_injective hYq
  have hq : IsIsogeny q := splitTorus.isIsogeny_of_characterMap I J q hXq
    (finite_quotient_range_of_injective_of_card_le _ hXq hIJ)
  have ht : CommGroupScheme.groupHom t = eA.hom ≫ q ≫ eT.inv := by
    simp only [q, Iso.hom_inv_id_assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [ht]
  exact (isCentralIsogeny_of_isIso eA.hom).isIsogeny.comp
    (hq.comp (isCentralIsogeny_of_isIso eT.inv).isIsogeny)

end Langlands.GroupScheme
