import Langlands.GroupScheme.Torus.CharacterIsomorphism

/-! # Homomorphisms into split tori from additive maps of character lattices -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [CommRing k] [IsDomain k]
  {T T' : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Over a domain, every additive map `X(T') → X(T)` out of the character lattice of a split
torus `T'` is pullback of characters along a homomorphism `T ⟶ T'`. The source `T` is an
arbitrary commutative group scheme. -/
theorem IsSplitTorus.exists_hom_of_characterMap (hT' : IsSplitTorus T'.toGrp)
    (F : characterLattice T' →+ characterLattice T) :
    ∃ t : T ⟶ T', ∀ χ : characterLattice T', t ≫ χ = F χ := by
  classical
  obtain ⟨I, hI, ⟨e⟩⟩ := hT'
  let := hI
  let := Fintype.ofFinite I
  let eC : T' ≅ splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I :=
    CommGroupScheme.isoOfGroupIso e
  -- The coordinate characters of `T'` and the coordinates of a character.
  let ψ : I → characterLattice T' := fun i => eC.hom ≫ splitTorus.proj _ I i
  let n : characterLattice T' → I → ℤ := fun χ i =>
    gmEndEquiv k (splitTorus.single _ I i ≫ eC.inv ≫ χ)
  have hn : ∀ (χ : characterLattice T') (i : I),
      splitTorus.single _ I i ≫ eC.inv ≫ χ = n χ i • 𝟙 (Gm (Spec (CommRingCat.of k))) :=
    fun χ i => eq_gmEndEquiv_zsmul k _
  -- Every character is the combination of the coordinate characters with these coordinates.
  have hdecomp : ∀ χ : characterLattice T', χ = ∑ i, n χ i • ψ i := by
    intro χ
    calc χ = eC.hom ≫ 𝟙 _ ≫ eC.inv ≫ χ := by simp
      _ = eC.hom ≫ (∑ i, splitTorus.proj _ I i ≫ splitTorus.single _ I i) ≫ eC.inv ≫ χ := by
          rw [splitTorus.sum_proj_comp_single]
      _ = ∑ i, n χ i • ψ i := by
          rw [Preadditive.sum_comp, Preadditive.comp_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Category.assoc, hn, Preadditive.comp_zsmul, Category.comp_id,
            Preadditive.comp_zsmul]
  let t : T ⟶ T' := (∑ i, F (ψ i) ≫ splitTorus.single _ I i) ≫ eC.inv
  refine ⟨t, fun χ => ?_⟩
  calc t ≫ χ = ∑ i, F (ψ i) ≫ (splitTorus.single _ I i ≫ eC.inv ≫ χ) := by
        simp only [t, Category.assoc, Preadditive.sum_comp]
    _ = ∑ i, n χ i • F (ψ i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hn, Preadditive.comp_zsmul, Category.comp_id]
    _ = F χ := by
        conv_rhs => rw [hdecomp χ]
        rw [map_sum]
        simp only [map_zsmul]

/-- The homomorphism `T ⟶ T'` into a split torus whose character pullback is a given additive
map `X(T') → X(T)`. -/
def IsSplitTorus.homOfCharacterMap (hT' : IsSplitTorus T'.toGrp)
    (F : characterLattice T' →+ characterLattice T) : T ⟶ T' :=
  Classical.choose (hT'.exists_hom_of_characterMap F)

/-- Character pullback along `homOfCharacterMap` is the given map. -/
@[simp]
theorem IsSplitTorus.homOfCharacterMap_comp (hT' : IsSplitTorus T'.toGrp)
    (F : characterLattice T' →+ characterLattice T) (χ : characterLattice T') :
    hT'.homOfCharacterMap F ≫ χ = F χ :=
  Classical.choose_spec (hT'.exists_hom_of_characterMap F) χ

/-- A homomorphism into a split torus with the given character pullback is
`homOfCharacterMap`. -/
theorem IsSplitTorus.eq_homOfCharacterMap (hT' : IsSplitTorus T'.toGrp)
    (F : characterLattice T' →+ characterLattice T) {t : T ⟶ T'}
    (ht : ∀ χ : characterLattice T', t ≫ χ = F χ) : t = hT'.homOfCharacterMap F :=
  hT'.hom_ext_of_characters fun χ => by rw [ht, homOfCharacterMap_comp]

/-- Additive maps `X(T') → X(T)` out of the characters of a split torus correspond exactly to
homomorphisms `T ⟶ T'`: there is exactly one homomorphism with the given character pullback. -/
theorem IsSplitTorus.existsUnique_hom_of_characterMap (hT' : IsSplitTorus T'.toGrp)
    (F : characterLattice T' →+ characterLattice T) :
    ∃! t : T ⟶ T', ∀ χ : characterLattice T', t ≫ χ = F χ :=
  ⟨hT'.homOfCharacterMap F, hT'.homOfCharacterMap_comp F,
    fun _ ht => hT'.eq_homOfCharacterMap F ht⟩

end Langlands.GroupScheme
