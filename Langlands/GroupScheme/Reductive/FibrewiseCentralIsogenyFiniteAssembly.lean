import Langlands.GroupScheme.Reductive.FibrewiseCentralIsogenyAssembly
import Langlands.GroupScheme.Torus.FlatQuasiFiniteSubgroup

/-! # Fibrewise central-isogeny assembly without finite-subgroup spreading -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.FibrewiseCentralIsogenyFiniteAssembly

open FibrewiseCentralIsogenyAssembly

variable {S : Scheme.{u}} {G H : GroupScheme S}

/-- A central kernel of the specified fibrewise isogeny is finite as a flat
locally quasi-finite closed subgroup of the multiplicative-type centre. -/
theorem finite_kernel_of_central
    (hcenter : ReductiveRelativeCenterStatement.{u})
    (hG : IsReductive G) (hH : IsReductive H) (f : G ⟶ H)
    (hs : Surjective f.hom.hom.left) (hc : IsCentral (kernelι f))
    (hk : ∀ s : S,
      IsFinite (kernel ((baseChange (S.fromSpecResidueField s)).map f)).X.hom) :
    IsFinite (kernel f).X.hom := by
  let := hG.smooth
  let := hG.isAffineHom
  let := hH.smooth
  let := hH.isAffineHom
  have hf := FibrewiseCentralIsogenyReduction.flat_and_locallyQuasiFinite_of_finite_kernel_fibres
    hG hH f hs hk
  have : Flat (kernel f).X.hom :=
    MorphismProperty.of_isPullback (kernel_isPullback_scheme f) hf.1
  have : LocallyQuasiFinite (kernel f).X.hom :=
    MorphismProperty.of_isPullback (kernel_isPullback_scheme f) hf.2
  obtain ⟨Z, z, hz, hZm, -⟩ := hcenter S G hG
  exact hZm.isFinite_closedSubgroup (centralKernelFactor f z hz hc)
    (centralKernelFactor_isClosedImmersion f z hz hc)

/-- The relative-centre theorem and global kernel centrality suffice for the
reverse implication; no finite-subgroup spreading theorem is needed. -/
theorem isCentralIsogeny_of_central_kernel
    (hcenter : ReductiveRelativeCenterStatement.{u})
    (hG : IsReductive G) (hH : IsReductive H) (f : G ⟶ H)
    (hs : Surjective f.hom.hom.left) (hc : IsCentral (kernelι f))
    (hk : ∀ s : S,
      IsFinite (kernel ((baseChange (S.fromSpecResidueField s)).map f)).X.hom) :
    IsCentralIsogeny f := by
  let := hG.smooth
  let := hH.smooth
  exact ⟨(FibrewiseCentralIsogenyReduction.isogeny_iff_finite_kernel hG hH f hs hk).mpr
      (finite_kernel_of_central hcenter hG hH f hs hc hk),
    locallyOfFinitePresentation_hom f, hc⟩

/-- The actual finite fppf singleton cover given by a surjection with the
specified fibrewise kernels, once its full kernel is known to be central. -/
def finiteFppfCover
    (hcenter : ReductiveRelativeCenterStatement.{u})
    (hG : IsReductive G) (hH : IsReductive H) (f : G ⟶ H)
    (hs : Surjective f.hom.hom.left) (hc : IsCentral (kernelι f))
    (hk : ∀ s : S,
      IsFinite (kernel ((baseChange (S.fromSpecResidueField s)).map f)).X.hom) :
    H.X.left.Cover (Scheme.precoverage
      (@IsFinite ⊓ (@Flat ⊓ @LocallyOfFinitePresentation))) := by
  have hf := isCentralIsogeny_of_central_kernel hcenter hG hH f hs hc hk
  exact Scheme.Cover.mkOfCovers PUnit (fun _ => G.X.left) (fun _ => f.hom.hom.left)
    (fun y => by obtain ⟨x, hx⟩ := hs.surj y; exact ⟨PUnit.unit, x, hx⟩)
    (fun _ => ⟨hf.isFinite, hf.flat, hf.locallyOfFinitePresentation⟩)

/-- The unchanged published criterion follows from the relative-centre
statement and a global kernel-centrality theorem. -/
theorem criterion_of_kernelCentrality
    (hcenter : ReductiveRelativeCenterStatement.{u})
    (hcentral : ∀ (B : Scheme.{u}) (A C : GroupScheme B),
      IsReductive A → IsReductive C →
      ∀ (f : A ⟶ C), Surjective f.hom.hom.left →
        (∀ s : B,
          IsFinite (kernel ((baseChange (B.fromSpecResidueField s)).map f)).X.hom ∧
          IsCentral (kernelι ((baseChange (B.fromSpecResidueField s)).map f))) →
        IsCentral (kernelι f)) :
    ReductiveFibrewiseCentralIsogenyStatement.{u} := by
  intro B A C hA hC f hs
  constructor
  · exact fun hf s =>
      FibrewiseCentralIsogenyReduction.finite_central_kernel_fibres_of_isCentralIsogeny hf s
  · intro hf
    exact isCentralIsogeny_of_central_kernel hcenter hA hC f hs
      (hcentral B A C hA hC f hs hf) (fun s => (hf s).1)

end Langlands.GroupScheme.FibrewiseCentralIsogenyFiniteAssembly
