import Langlands.GroupScheme.Rational.RelativeWeylCharacterAction
import Langlands.GroupScheme.Torus.SplitLatticeBaseChange

/-! # Detecting isomorphisms of split tori on actual characters -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {A T T' : CommGroupScheme S}

/-- Actual characters separate homomorphisms into a split torus. -/
theorem IsSplitTorus.hom_ext_of_characters (hT : IsSplitTorus T.toGrp)
    {f g : A ⟶ T} (h : ∀ χ : characterLattice T, f ≫ χ = g ≫ χ) : f = g := by
  exact hT.hom_ext_characters h

/-- Bijective pullback of actual characters constructs an isomorphism between split tori.
The construction is valid over every base scheme. -/
theorem IsSplitTorus.exists_iso_of_bijective_characterPullback
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp) (t : T ⟶ T')
    (hchar : Function.Bijective (fun χ : characterLattice T' => t ≫ χ)) :
    ∃ e : T ≅ T', e.hom = t := by
  classical
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let := hI
  let := Fintype.ofFinite I
  let eC : T ≅ splitTorus.commGroupScheme S I := CommGroupScheme.isoOfGroupIso e
  choose ψ hψ using fun i : I => hchar.2 (eC.hom ≫ splitTorus.proj S I i)
  let g : T' ⟶ T := (∑ i, ψ i ≫ splitTorus.single S I i) ≫ eC.inv
  have hleft : t ≫ (∑ i, ψ i ≫ splitTorus.single S I i) = eC.hom := by
    rw [Preadditive.comp_sum]
    simp_rw [← Category.assoc, hψ, Category.assoc]
    rw [← Preadditive.comp_sum, splitTorus.sum_proj_comp_single, Category.comp_id]
  have hfg : t ≫ g = 𝟙 T := by
    dsimp only [g]
    rw [← Category.assoc, hleft, Iso.hom_inv_id]
  have hgf : g ≫ t = 𝟙 T' := by
    apply hT'.hom_ext_of_characters
    intro χ
    apply hchar.1
    calc
      t ≫ ((g ≫ t) ≫ χ) = (t ≫ g) ≫ (t ≫ χ) := by simp only [Category.assoc]
      _ = t ≫ ((𝟙 T') ≫ χ) := by rw [hfg]; simp only [Category.id_comp]
  exact ⟨⟨t, g, hfg, hgf⟩, rfl⟩

/-- The isomorphism associated to a homomorphism with bijective actual character pullback. -/
def IsSplitTorus.isoOfBijectiveCharacterPullback
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp) (t : T ⟶ T')
    (hchar : Function.Bijective (fun χ : characterLattice T' => t ≫ χ)) : T ≅ T' :=
  Classical.choose (hT.exists_iso_of_bijective_characterPullback hT' t hchar)

@[simp]
theorem IsSplitTorus.isoOfBijectiveCharacterPullback_hom
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp) (t : T ⟶ T')
    (hchar : Function.Bijective (fun χ : characterLattice T' => t ≫ χ)) :
    (hT.isoOfBijectiveCharacterPullback hT' t hchar).hom = t :=
  Classical.choose_spec (hT.exists_iso_of_bijective_characterPullback hT' t hchar)

/-- An isomorphism induces bijective pullback on actual characters. -/
theorem characterPullback_bijective_of_isIso (t : T ⟶ T') [IsIso t] :
    Function.Bijective (fun χ : characterLattice T' => t ≫ χ) := by
  constructor
  · intro χ ψ h
    exact (cancel_epi t).mp h
  · intro χ
    exact ⟨inv t ≫ χ, by simp⟩

/-- A homomorphism of split tori is an isomorphism exactly when its actual character pullback
is bijective. -/
theorem IsSplitTorus.isIso_iff_bijective_characterPullback
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp) (t : T ⟶ T') :
    IsIso t ↔ Function.Bijective (fun χ : characterLattice T' => t ≫ χ) := by
  constructor
  · intro ht
    exact characterPullback_bijective_of_isIso t
  · intro hchar
    rw [← hT.isoOfBijectiveCharacterPullback_hom hT' t hchar]
    infer_instance

end Langlands.GroupScheme
