import Langlands.GroupScheme.Reductive.FibrewiseCentralIsogenyStatement
import Langlands.GroupScheme.Reductive.BaseChange
import Langlands.GroupScheme.Reductive.FibrewiseIsogenyReduction
import Langlands.GroupScheme.CentralIsogeny.BaseChange
import Langlands.GroupScheme.SmoothConnectedFiniteKernel

/-! # Geometric reductions for the fibrewise central-isogeny criterion -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

namespace FibrewiseCentralIsogenyReduction

variable {S : Scheme.{u}} {G H : GroupScheme S}

/-- The full residue-fibre kernels of a central isogeny are finite and central. -/
theorem finite_central_kernel_fibres_of_isCentralIsogeny
    {f : G ⟶ H} (hf : IsCentralIsogeny f) (s : S) :
    IsFinite (kernel ((baseChange (S.fromSpecResidueField s)).map f)).X.hom ∧
      IsCentral (kernelι ((baseChange (S.fromSpecResidueField s)).map f)) := by
  have hs := hf.baseChange (S.fromSpecResidueField s)
  exact ⟨hs.kernel_isFinite, hs.isCentral_kernelι⟩

/-- A surjective homomorphism from a smooth connected affine field group to a
smooth affine field group is an isogeny when its full kernel is finite. -/
theorem isogeny_of_surjective_of_finite_kernel
    {k : Type u} [Field k]
    {A B : GroupScheme (Spec (CommRingCat.of k))} (f : A ⟶ B)
    [Smooth A.X.hom] [ConnectedSpace A.X.left] [IsAffineHom A.X.hom]
    [Smooth B.X.hom] [IsAffineHom B.X.hom]
    (hs : Surjective f.hom.hom.left) (hk : IsFinite (kernel f).X.hom) :
    IsIsogeny f := by
  let : Surjective f.hom.hom.left := hs
  let : IsFinite (kernel f).X.hom := hk
  let : IsFinite f.hom.hom.left := isFinite_hom_of_finite_kernel f
  let : IsLocallyNoetherian B.X.left :=
    LocallyOfFiniteType.isLocallyNoetherian B.X.hom
  let : IsReduced B.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      k B.X.left B.X.hom
  exact ⟨inferInstance, DominantHomFlat.flat_of_isDominant f, hs⟩

/-- For a surjective homomorphism of reductive groups, finite residue-fibre
kernels already give isogenies on every residue-field fibre. -/
theorem isFibrewiseIsogeny_of_finite_kernel_fibres
    (hG : IsReductive G) (hH : IsReductive H) (f : G ⟶ H)
    (hs : Surjective f.hom.hom.left)
    (hk : ∀ s : S,
      IsFinite (kernel ((baseChange (S.fromSpecResidueField s)).map f)).X.hom) :
    IsFibrewiseIsogeny f := by
  intro s
  have hGs := hG.isConnectedReductive_residueFiber s
  have hHs := hH.isConnectedReductive_residueFiber s
  let := hGs.smooth
  let := hGs.connectedSpace
  let := hGs.isAffineHom
  let := hHs.smooth
  let := hHs.isAffineHom
  have hs' : Surjective ((baseChange (S.fromSpecResidueField s)).map f).hom.hom.left :=
    MorphismProperty.of_isPullback
      (baseChange_map_isPullback (S.fromSpecResidueField s) f).flip hs
  exact isogeny_of_surjective_of_finite_kernel _ hs' (hk s)

/-- The actual residue-fibre homomorphisms, bundled with their isogeny
properties, for a surjective homomorphism with finite residue-fibre kernels. -/
noncomputable def fibreIsogeniesOfFiniteKernels
    (hG : IsReductive G) (hH : IsReductive H) (f : G ⟶ H)
    (hs : Surjective f.hom.hom.left)
    (hk : ∀ s : S,
      IsFinite (kernel ((baseChange (S.fromSpecResidueField s)).map f)).X.hom) :
    ∀ s : S, {φ :
      (baseChange (S.fromSpecResidueField s)).obj G ⟶
        (baseChange (S.fromSpecResidueField s)).obj H // IsIsogeny φ} :=
  fun s => ⟨(baseChange (S.fromSpecResidueField s)).map f,
    isFibrewiseIsogeny_of_finite_kernel_fibres hG hH f hs hk s⟩

/-- The finite residue-fibre kernel hypothesis gives global flatness and local
quasi-finiteness, without requiring fibrewise centrality. -/
theorem flat_and_locallyQuasiFinite_of_finite_kernel_fibres
    (hG : IsReductive G) (hH : IsReductive H) (f : G ⟶ H)
    (hs : Surjective f.hom.hom.left)
    (hk : ∀ s : S,
      IsFinite (kernel ((baseChange (S.fromSpecResidueField s)).map f)).X.hom) :
    Flat f.hom.hom.left ∧ LocallyQuasiFinite f.hom.hom.left := by
  let := hG.smooth
  let := hH.smooth
  have hf := isFibrewiseIsogeny_of_finite_kernel_fibres hG hH f hs hk
  exact ⟨flat_of_isogeny_fibres f hf, locallyQuasiFinite_of_isogeny_fibres f hf⟩

/-- Under the finite residue-fibre kernel hypothesis, the global isogeny
condition is equivalent to finiteness of the actual kernel over the base. -/
theorem isogeny_iff_finite_kernel
    (hG : IsReductive G) (hH : IsReductive H) (f : G ⟶ H)
    (hs : Surjective f.hom.hom.left)
    (hk : ∀ s : S,
      IsFinite (kernel ((baseChange (S.fromSpecResidueField s)).map f)).X.hom) :
    IsIsogeny f ↔ IsFinite (kernel f).X.hom := by
  let := hG.smooth
  let := hG.isAffineHom
  let := hH.smooth
  let := hH.isAffineHom
  exact isogeny_iff_finite_kernel_of_isogeny_fibres f
    (isFibrewiseIsogeny_of_finite_kernel_fibres hG hH f hs hk)

end FibrewiseCentralIsogenyReduction

end Langlands.GroupScheme
