import Langlands.GroupScheme.ArtinianCentralityDetection
import Langlands.GroupScheme.Torus.MultiplicativeTypeAffineInfinitesimalCentrality
import Langlands.GroupScheme.Torus.MultiplicativeTypeInfinitesimalCentralityStatement
import Mathlib.RingTheory.Artinian.Ring

/-! # Fibrewise centrality over Artinian bases, from infinitesimal centrality -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.MultiplicativeTypeArtinianCentralityReduction

open MultiplicativeTypeAffineInfinitesimalCentrality

variable {S : Scheme.{u}} {H G : GroupScheme S}

/-- Centrality on residue fibres implies centrality on every field-valued base change. -/
theorem isCentral_field_baseChange (i : H ⟶ G)
    (hc : ∀ s : S, IsCentral ((GroupScheme.baseChange (S.fromSpecResidueField s)).map i))
    (K : Type u) [Field K] (b : Spec (CommRingCat.of K) ⟶ S) :
    IsCentral ((GroupScheme.baseChange b).map i) := by
  obtain ⟨⟨s, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField K S).symm.surjective b
  exact (isCentral_baseChange_comp_iff _ _ i).mpr ((hc s).baseChange (Spec.map φ))

/-- The actual global-section kernel of a spectrum map is transported by the
canonical spectrum/global-section isomorphism. -/
theorem ker_specMap_appTop {R A : CommRingCat.{u}} (φ : R ⟶ A) :
    RingHom.ker (Spec.map φ).appTop.hom =
      (RingHom.ker φ.hom).map (Scheme.ΓSpecIso R).inv.hom := by
  have hleg : (Spec.map φ).appTop =
      (Scheme.ΓSpecIso R).hom ≫ φ ≫ (Scheme.ΓSpecIso A).inv := by
    rw [Scheme.ΓSpecIso_inv_naturality, Iso.hom_inv_id_assoc]
  rw [hleg]
  change RingHom.ker
    ((Scheme.ΓSpecIso A).inv.hom.comp (φ.hom.comp (Scheme.ΓSpecIso R).hom.hom)) = _
  rw [RingHom.ker_comp_of_injective _
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso A).inv).1,
    ← RingHom.comap_ker]
  exact (Ideal.map_symm (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv).symm

/-- A nilpotent ring kernel gives the locally nilpotent ideal-sheaf condition
of the infinitesimal-centrality statement. -/
theorem locallyNilpotent_specMap {R A : CommRingCat.{u}} (φ : R ⟶ A)
    (hn : IsNilpotent (RingHom.ker φ.hom)) :
    ∀ x : Spec R, ∃ U : (Spec R).affineOpens, x ∈ (U : (Spec R).Opens) ∧
      IsNilpotent ((Spec.map φ).ker.ideal U) := by
  intro x
  refine ⟨⟨⊤, isAffineOpen_top _⟩, trivial, ?_⟩
  rw [Scheme.ker_of_isAffine, Scheme.IdealSheafData.ofIdealTop_ideal,
    ker_specMap_appTop]
  exact (hn.map (Ideal.mapHom (Scheme.ΓSpecIso R).inv.hom)).map (Ideal.mapHom _)

/-- Infinitesimal centrality lifts fibrewise centrality to every local
Artinian base change. -/
theorem isCentral_artinian_baseChange
    (hInf : MultiplicativeTypeInfinitesimalCentralityStatement.{u})
    (hH : RelativeMultiplicativeType.IsMultiplicativeType H)
    [LocallyOfFinitePresentation G.X.hom] (i : H ⟶ G)
    (hc : ∀ s : S, IsCentral ((GroupScheme.baseChange (S.fromSpecResidueField s)).map i))
    (A : Type u) [CommRing A] [IsLocalRing A] [IsArtinianRing A]
    (b : Spec (CommRingCat.of A) ⟶ S) :
    IsCentral ((GroupScheme.baseChange b).map i) := by
  let ρ : CommRingCat.of A ⟶ CommRingCat.of (IsLocalRing.ResidueField A) :=
    CommRingCat.ofHom (IsLocalRing.residue A)
  have : IsClosedImmersion (Spec.map ρ) :=
    IsClosedImmersion.spec_of_surjective _ IsLocalRing.residue_surjective
  have hn : IsNilpotent (RingHom.ker ρ.hom) := by
    change IsNilpotent (RingHom.ker (IsLocalRing.residue A))
    rw [IsLocalRing.ker_residue]
    exact (isArtinianRing_iff_isNilpotent_maximalIdeal A).mp inferInstance
  have : LocallyOfFinitePresentation ((GroupScheme.baseChange b).obj G).X.hom := by
    change LocallyOfFinitePresentation (CategoryTheory.Limits.pullback.snd G.X.hom b)
    infer_instance
  apply hInf _ _ (Spec.map ρ) (locallyNilpotent_specMap ρ hn) _ _
    (hH.baseChange b) ((GroupScheme.baseChange b).map i)
  apply (isCentral_baseChange_comp_iff b (Spec.map ρ) i).mp
  exact isCentral_field_baseChange i hc (IsLocalRing.ResidueField A) (Spec.map ρ ≫ b)

/-- Infinitesimal centrality and local Artinian detection give the fibrewise
criterion when the universal product is locally noetherian. -/
theorem isCentral_of_fibres
    (hInf : MultiplicativeTypeInfinitesimalCentralityStatement.{u})
    (hH : RelativeMultiplicativeType.IsMultiplicativeType H)
    [LocallyOfFinitePresentation G.X.hom]
    [IsLocallyNoetherian (H.X ⊗ G.X).left] (i : H ⟶ G)
    (hc : ∀ s : S, IsCentral ((GroupScheme.baseChange (S.fromSpecResidueField s)).map i)) :
    IsCentral i := by
  apply ArtinianCentrality.isCentral_of_artinian_baseChange_general i
  exact isCentral_artinian_baseChange hInf hH i hc

/-- Over a locally noetherian base, local finite type of the source and local
finite presentation of the ambient group supply the noetherian product. -/
theorem isCentral_of_fibres_of_locallyNoetherian
    (hInf : MultiplicativeTypeInfinitesimalCentralityStatement.{u})
    (hH : RelativeMultiplicativeType.IsMultiplicativeType H)
    [IsLocallyNoetherian S] [LocallyOfFiniteType H.X.hom]
    [LocallyOfFinitePresentation G.X.hom] (i : H ⟶ G)
    (hc : ∀ s : S, IsCentral ((GroupScheme.baseChange (S.fromSpecResidueField s)).map i)) :
    IsCentral i := by
  have : IsLocallyNoetherian G.X.left :=
    LocallyOfFiniteType.isLocallyNoetherian G.X.hom
  have : IsLocallyNoetherian (H.X ⊗ G.X).left := by
    change IsLocallyNoetherian (CategoryTheory.Limits.pullback H.X.hom G.X.hom)
    infer_instance
  exact isCentral_of_fibres hInf hH i hc

/-- The same monomorphic source, bundled as commutative by the conditional
fibrewise criterion. -/
def commGroupSchemeOfFibrewiseCentrality
    (hInf : MultiplicativeTypeInfinitesimalCentralityStatement.{u})
    (hH : RelativeMultiplicativeType.IsMultiplicativeType H)
    [LocallyOfFinitePresentation G.X.hom]
    [IsLocallyNoetherian (H.X ⊗ G.X).left] (i : H ⟶ G) [Mono i.hom.hom]
    (hc : ∀ s : S, IsCentral ((GroupScheme.baseChange (S.fromSpecResidueField s)).map i)) :
    CommGroupScheme S :=
  (isCentral_of_fibres hInf hH i hc).commGroupScheme

@[simp]
theorem commGroupSchemeOfFibrewiseCentrality_toGrp
    (hInf : MultiplicativeTypeInfinitesimalCentralityStatement.{u})
    (hH : RelativeMultiplicativeType.IsMultiplicativeType H)
    [LocallyOfFinitePresentation G.X.hom]
    [IsLocallyNoetherian (H.X ⊗ G.X).left] (i : H ⟶ G) [Mono i.hom.hom]
    (hc : ∀ s : S, IsCentral ((GroupScheme.baseChange (S.fromSpecResidueField s)).map i)) :
    (commGroupSchemeOfFibrewiseCentrality hInf hH i hc).toGrp = H := rfl

end Langlands.GroupScheme.MultiplicativeTypeArtinianCentralityReduction
