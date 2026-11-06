import Langlands.GroupScheme.Reductive.PinnedIsomorphismStatement
import Langlands.GroupScheme.Torus.CharacterMapHom

/-! # Actual torus lifts of equivalences between pinned root data -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section CharacterEquivalence

variable {k : Type u} [CommRing k] [IsDomain k]
  {T T' : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Realize a forward equivalence of full character lattices by inverse
character pullback along an actual isomorphism of split tori. -/
def IsSplitTorus.isoOfCharacterEquiv
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    (e : characterLattice T ≃+ characterLattice T') : T ≅ T' where
  hom := hT'.homOfCharacterMap e.symm.toAddMonoidHom
  inv := hT.homOfCharacterMap e.toAddMonoidHom
  hom_inv_id := by
    apply hT.hom_ext_of_characters
    intro χ
    simp only [Category.assoc, IsSplitTorus.homOfCharacterMap_comp,
      Category.id_comp]
    exact e.symm_apply_apply χ
  inv_hom_id := by
    apply hT'.hom_ext_of_characters
    intro χ
    simp only [Category.assoc, IsSplitTorus.homOfCharacterMap_comp,
      Category.id_comp]
    exact e.apply_symm_apply χ

@[simp]
theorem IsSplitTorus.character_congr_isoOfCharacterEquiv
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    (e : characterLattice T ≃+ characterLattice T') :
    characterLattice.congr (hT.isoOfCharacterEquiv hT' e) = e := by
  ext χ
  exact hT.homOfCharacterMap_comp e.toAddMonoidHom χ

omit [IsDomain k] in
/-- The forward full-character map determines a torus isomorphism. -/
theorem IsSplitTorus.iso_ext_of_character_congr
    (hT : IsSplitTorus T.toGrp) {f g : T ≅ T'}
    (h : characterLattice.congr f = characterLattice.congr g) : f = g := by
  apply Iso.ext_inv
  apply hT.hom_ext_of_characters
  intro χ
  exact DFunLike.congr_fun h χ

end CharacterEquivalence

namespace SplitPinning

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  (p : SplitPinning G) (q : SplitPinning H)
  (e : RootPairing.Equiv p.rootDatum q.rootDatum)

/-- The actual torus isomorphism prescribed by a full root-datum equivalence.
This construction does not extend the map to the reductive groups. -/
def torusIsoOfRootDatumEquiv : p.torus ≅ q.torus :=
  p.isSplitTorus.isoOfCharacterEquiv q.isSplitTorus e.weightEquiv.toAddEquiv

@[simp]
theorem torusIsoOfRootDatumEquiv_character :
    (characterLattice.congr (p.torusIsoOfRootDatumEquiv q e)).toIntLinearEquiv =
      e.weightEquiv := by
  ext χ
  exact DFunLike.congr_fun
    (p.isSplitTorus.character_congr_isoOfCharacterEquiv q.isSplitTorus
      e.weightEquiv.toAddEquiv) χ

/-- The prescribed full-character equation forces the forward cocharacter
equation, by the perfect root-datum pairing on the actual lattices. -/
theorem cocharacter_congr_eq_of_character_congr
    (t : p.torus ≅ q.torus)
    (hchar : (characterLattice.congr t).toIntLinearEquiv = e.weightEquiv) :
    (cocharacterLattice.congr t).toIntLinearEquiv = e.coweightEquiv.symm := by
  ext ν
  apply q.rootDatum.flip.toPerfPair.injective
  ext χ
  obtain ⟨ψ, rfl⟩ := e.weightEquiv.surjective χ
  change q.rootDatum.toLinearMap (e.weightEquiv ψ) (cocharacterLattice.congr t ν) =
    q.rootDatum.toLinearMap (e.weightEquiv ψ) (e.coweightEquiv.symm ν)
  have hψ : characterLattice.congr t ψ = e.weightEquiv ψ :=
    DFunLike.congr_fun hchar ψ
  calc
    q.rootDatum.toLinearMap (e.weightEquiv ψ) (cocharacterLattice.congr t ν) =
        latticePairing q.torus (characterLattice.congr t ψ)
          (cocharacterLattice.congr t ν) := by rw [q.isRootDatum.1, hψ]
    _ = latticePairing p.torus ψ ν := latticePairing_congr t ψ ν
    _ = p.rootDatum.toLinearMap ψ ν := by rw [p.isRootDatum.1]
    _ = q.rootDatum.toLinearMap (e.weightEquiv ψ) (e.coweightEquiv.symm ν) := by
      rw [e.toLinearMap_weightEquiv, LinearEquiv.apply_symm_apply]

@[simp]
theorem torusIsoOfRootDatumEquiv_cocharacter :
    (cocharacterLattice.congr (p.torusIsoOfRootDatumEquiv q e)).toIntLinearEquiv =
      e.coweightEquiv.symm :=
  p.cocharacter_congr_eq_of_character_congr q e _
    (p.torusIsoOfRootDatumEquiv_character q e)

theorem torusIsoOfRootDatumEquiv_root (a : p.rootIndex) :
    characterLattice.congr (p.torusIsoOfRootDatumEquiv q e) (p.rootDatum.root a) =
      q.rootDatum.root (e.indexEquiv a) := by
  have h := DFunLike.congr_fun (p.torusIsoOfRootDatumEquiv_character q e)
    (p.rootDatum.root a)
  exact h.trans (e.root_weightMap_apply p.rootDatum q.rootDatum a)

theorem torusIsoOfRootDatumEquiv_coroot (a : p.rootIndex) :
    cocharacterLattice.congr (p.torusIsoOfRootDatumEquiv q e) (p.rootDatum.coroot a) =
      q.rootDatum.coroot (e.indexEquiv a) := by
  have h := DFunLike.congr_fun (p.torusIsoOfRootDatumEquiv_cocharacter q e)
    (p.rootDatum.coroot a)
  refine h.trans ?_
  apply e.coweightEquiv.injective
  rw [LinearEquiv.apply_symm_apply]
  simpa using (e.coroot_coweightMap_apply p.rootDatum q.rootDatum (e.indexEquiv a)).symm

/-- There is exactly one actual torus isomorphism with both prescribed full
lattice maps, irrespective of whether any roots exist. -/
theorem existsUnique_torusIso_of_rootDatumEquiv :
    ∃! t : p.torus ≅ q.torus,
      (characterLattice.congr t).toIntLinearEquiv = e.weightEquiv ∧
      (cocharacterLattice.congr t).toIntLinearEquiv = e.coweightEquiv.symm := by
  refine ⟨p.torusIsoOfRootDatumEquiv q e,
    ⟨p.torusIsoOfRootDatumEquiv_character q e,
      p.torusIsoOfRootDatumEquiv_cocharacter q e⟩, ?_⟩
  intro t ht
  apply p.isSplitTorus.iso_ext_of_character_congr
  ext χ
  exact (DFunLike.congr_fun ht.1 χ).trans
    (DFunLike.congr_fun (p.torusIsoOfRootDatumEquiv_character q e) χ).symm

end SplitPinning

end Langlands.GroupScheme
