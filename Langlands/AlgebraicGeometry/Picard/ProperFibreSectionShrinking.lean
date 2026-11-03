import Langlands.AlgebraicGeometry.Picard.ProperFibreSectionGeometry
import Langlands.AlgebraicGeometry.Picard.AmpleFiniteAffineOpen

/-! # Shrinking sections that generate along a proper fibre -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open Langlands.SchemeModule Langlands.Scheme.Modules

namespace Langlands.AlgebraicGeometry.Picard

variable {X S : Scheme.{u}} (p : X ⟶ S)

/-- The canonical map from a fibre of a restricted family to the original fibre. -/
def fibreRestrictionMap (V : S.Opens) (s : V.toScheme) :
    (p ∣_ V).fiber s ⟶ p.fiber (V.ι s) :=
  pullback.map _ _ _ _ (p ⁻¹ᵁ V).ι (Spec.map (V.ι.residueFieldMap s)) V.ι
    (morphismRestrict_ι p V)
    (V.ι.SpecMap_residueFieldMap_fromSpecResidueField s).symm

@[reassoc (attr := simp)]
lemma fibreRestrictionMap_fiberι (V : S.Opens) (s : V.toScheme) :
    fibreRestrictionMap p V s ≫ p.fiberι (V.ι s) =
      (p ∣_ V).fiberι s ≫ (p ⁻¹ᵁ V).ι := by
  simp [fibreRestrictionMap, Scheme.Hom.fiberι]

/-- The fibre comparison is affine, by base change of the residue-field map. -/
instance isAffineHom_fibreRestrictionMap (V : S.Opens) (s : V.toScheme) :
    IsAffineHom (fibreRestrictionMap p V s) := by
  have H := isPullback_fiberToSpecResidueField_of_isPullback
    (isPullback_morphismRestrict p V).flip s
  exact MorphismProperty.of_isPullback (P := @IsAffineHom) H.flip inferInstance

/-- Ampleness on a neighbourhood inside a base open gives ampleness on an
actual affine neighbourhood in the original base. -/
lemma exists_ample_neighbourhood_of_restrict (L : LineBundle X) (s : S)
    (V : S.Opens) (hsV : s ∈ V)
    (h : ∃ W : V.toScheme.Opens, (⟨s, hsV⟩ : V.toScheme) ∈ W ∧ IsAffineOpen W ∧
      ((LineBundle.pullback ((p ∣_ V) ⁻¹ᵁ W).ι).obj
        ((LineBundle.pullback (p ⁻¹ᵁ V).ι).obj L)).IsAmple) :
    ∃ W : S.Opens, s ∈ W ∧ IsAffineOpen W ∧
      ((LineBundle.pullback (p ⁻¹ᵁ W).ι).obj L).IsAmple := by
  obtain ⟨W, hsW, hW, hample⟩ := h
  let A : X.Opens := p ⁻¹ᵁ V
  let B : A.toScheme.Opens := (p ∣_ V) ⁻¹ᵁ W
  let W₀ : S.Opens := V.ι ''ᵁ W
  let e : B.toScheme ≅ (p ⁻¹ᵁ W₀).toScheme :=
    A.ι.isoImage B ≪≫ X.isoOfEq (image_morphismRestrict_preimage p V W)
  have he : e.inv ≫ B.ι ≫ A.ι = (p ⁻¹ᵁ W₀).ι := by
    dsimp [e]
    simp only [Category.assoc, Scheme.Hom.isoImage_inv_ι,
      Scheme.isoOfEq_inv_ι]
  refine ⟨W₀, ⟨⟨s, hsV⟩, hsW, rfl⟩, hW.image_of_isOpenImmersion V.ι, ?_⟩
  have h' := hample.pullback_of_isAffineHom e.inv
  apply h'.of_iso
  exact (Scheme.Modules.pullbackComp e.inv B.ι).app
      ((Scheme.Modules.pullback A.ι).obj L.obj) ≪≫
    (Scheme.Modules.pullbackComp (e.inv ≫ B.ι) A.ι).app L.obj ≪≫
    (Scheme.Modules.pullbackCongr he).app L.obj

/-- Sections whose whole opens are affine and cover the specified proper fibre
make the same fixed bundle ample near that fibre. -/
lemma exists_ample_neighbourhood_of_fibre_sections [IsProper p]
    (L : LineBundle X) (s : S) {n d : ℕ} (hn : 0 < n)
    (σ : Fin (d + 1) → L.powSections n)
    (hcover : ∀ x : p.fiber s, ∃ i, x ∈ p.fiberι s ⁻¹ᵁ L.sectionOpen (σ i))
    (haff : ∀ i, IsAffineOpen (p.fiberι s ⁻¹ᵁ L.sectionOpen (σ i))) :
    ∃ V : S.Opens, s ∈ V ∧ IsAffineOpen V ∧
      ((LineBundle.pullback (p ⁻¹ᵁ V).ι).obj L).IsAmple := by
  let G : X.Opens := ⨆ i, L.sectionOpen (σ i)
  have hG : ∀ x : X, p x = s → x ∈ G := by
    intro x hx
    let y : p.fiber s := (p.fiberHomeo s).symm ⟨x, hx⟩
    obtain ⟨i, hi⟩ := hcover y
    have hy : p.fiberι s y = x := p.fiberι_fiberHomeo_symm s ⟨x, hx⟩
    have hi' : x ∈ L.sectionOpen (σ i) := by
      change p.fiberι s y ∈ L.sectionOpen (σ i) at hi
      rwa [hy] at hi
    exact (le_iSup (fun i => L.sectionOpen (σ i)) i) hi'
  obtain ⟨V, hsV, _, hVG⟩ := exists_affine_baseOpen_preimage_le p s G hG
  let A : X.Opens := p ⁻¹ᵁ V
  let L' : LineBundle A.toScheme := (LineBundle.pullback A.ι).obj L
  let s' : V.toScheme := ⟨s, hsV⟩
  let τ : Fin (d + 1) → L'.powSections n := fun i => L.pullbackPowSection A.ι (σ i)
  have hc : ∀ x : A.toScheme, ∃ i, x ∈ L'.sectionOpen (τ i) := by
    intro x
    have hx := hVG x.2
    change A.ι x ∈ (⨆ i, L.sectionOpen (σ i)) at hx
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    refine ⟨i, ?_⟩
    rw [LineBundle.sectionOpen_pullbackPowSection]
    exact hi
  have hA (i : Fin (d + 1)) :
      IsAffineOpen ((p ∣_ V).fiberι s' ⁻¹ᵁ L'.sectionOpen (τ i)) := by
    rw [LineBundle.sectionOpen_pullbackPowSection]
    have heq := congrArg
      (fun g : (p ∣_ V).fiber s' ⟶ X => g ⁻¹ᵁ L.sectionOpen (σ i))
      (fibreRestrictionMap_fiberι p V s')
    simp only [Scheme.Hom.comp_preimage] at heq
    rw [← heq]
    exact (haff i).preimage (fibreRestrictionMap p V s')
  let D : FibrePowerSectionSystem (p ∣_ V) L' s' :=
    ⟨n, hn, d, τ, hc, hA⟩
  exact exists_ample_neighbourhood_of_restrict p L s V hsV D.exists_ample_neighbourhood

end Langlands.AlgebraicGeometry.Picard
