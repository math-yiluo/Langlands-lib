import Langlands.GroupScheme.Torus.RelativeCentralizerSmooth
import Langlands.GroupScheme.Rational.ActionLieRigidity
import Langlands.GroupScheme.SmoothIsomorphismLocus
import Langlands.GroupScheme.Reductive.BaseChange
import Langlands.GroupScheme.Torus.WeightBaseChange
import Langlands.GroupScheme.Torus.MaximalBaseChangeForwardReduction

/-! # Diagonalizable centrality from the adjoint action over arbitrary rings -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

local instance relativeCenterCentrality_affine_baseChange {S T : Scheme.{u}} (b : T ⟶ S)
    (G : GroupScheme S) [IsAffineHom G.X.hom] :
    IsAffineHom ((baseChange b).obj G).X.hom :=
  MorphismProperty.pullback_snd G.X.hom b inferInstance

namespace Lie

/-- Triviality of the adjoint action on every coefficient algebra gives all
Lie invariants after any affine base change. -/
theorem conjugation_lieInvariants_baseChange_eq_top
    {R : Type u} [CommRing R] {G H : GroupScheme (Spec (CommRingCat.of R))}
    [IsAffineHom G.X.hom] (i : H ⟶ G)
    (h : ∀ (A : Type u) [CommRing A] [Algebra R A]
      (t : AffinePoints H A) (X : Additive (lieKernel G A)),
      adjoint G A (t ≫ i.hom.hom) X = X)
    (K : Type u) [CommRing K] [Algebra R K] :
    (AutomorphicAction.conjugation ((baseChange (algebraBaseMap R K)).map i)).lieInvariants =
      ⊤ := by
  apply top_unique
  intro X _ A _ _ t
  let : Algebra R A := ((algebraMap K A).comp (algebraMap R K)).toAlgebra
  let : IsScalarTower R K A := IsScalarTower.of_algebraMap_eq' rfl
  rw [AutomorphicAction.differential_conjugation]
  apply (kernelBaseChangeLinearEquiv R K G A).injective
  rw [kernelBaseChangeLinearEquiv_adjoint, affineBaseChangeEquiv_target]
  exact h A (affineBaseChangeEquiv R K H A t) _

end Lie

namespace Diagonalizable

variable {R : CommRingCat.{u}} {M : Type u} [AddCommGroup M]
  {G : GroupScheme (Spec R)} [IsAffineHom G.X.hom] [IsAffine G.X.left]
  (i : (groupScheme R M).toGrp ⟶ G)

/-- The actual smooth centralizer is the whole group if every residue fibre
has the full invariant Lie module. -/
theorem relativeCentralizer_eq_top_of_residue_lieInvariants_eq_top
    (hG : IsReductive G)
    (hLie : ∀ s : Spec R,
      (AutomorphicAction.conjugation
        ((baseChange ((Spec R).fromSpecResidueField s)).map i)).lieInvariants = ⊤) :
    torusCentralizer i = ⊤ := by
  let c := relativeCentralizerHom i
  have hc := isRepresentedBy_relativeCentralizerHom i
  have hclosed := isClosedSubgroup_relativeCentralizerHom i
  let : Smooth (relativeCentralizerGroupScheme i).X.hom :=
    smooth_relativeCentralizerGroupScheme i hG.smooth
  let : Smooth G.X.hom := hG.smooth
  have : IsIso c := SmoothIsomorphismLocus.isIso_of_group_residueField_fibres c fun s => by
    let b := (Spec R).fromSpecResidueField s
    have hGs := hG.isConnectedReductive_residueFiber s
    let : Smooth ((baseChange b).obj G).X.hom := hGs.smooth
    let : ConnectedSpace ((baseChange b).obj G).X.left := hGs.connectedSpace
    have hcb : (torusCentralizer
        (T := (CommGroupScheme.baseChange b).obj (groupScheme R M))
        ((baseChange b).map i)).IsRepresentedBy ((baseChange b).map c) := by
      rw [torusCentralizer_baseChange]
      exact hc.baseChange b
    have hsb : Smooth ((baseChange b).obj (relativeCentralizerGroupScheme i)).X.hom := by
      change Smooth (CategoryTheory.Limits.pullback.snd _ b)
      infer_instance
    have heq : torusCentralizer
        (T := (CommGroupScheme.baseChange b).obj (groupScheme R M))
        ((baseChange b).map i) = ⊤ := by
      apply RelativeRoot.eq_top_of_smooth_closed_of_tangentSubmodule_eq_top
        ((baseChange b).map c) hcb (hclosed.baseChange b) hsb
      rw [← AutomorphicAction.conjugation_fixedSubgroup_eq_torusCentralizer,
        AutomorphicAction.tangentSubmodule_fixedSubgroup, hLie s]
    have htop : (⊤ : SubgroupFunctor ((baseChange b).obj G)).IsRepresentedBy
        ((baseChange b).map c) := heq ▸ hcb
    rw [← htop.topIso_hom]
    infer_instance
  calc
    torusCentralizer i = SubgroupFunctor.range c := hc.2.symm
    _ = SubgroupFunctor.range (𝟙 G) := by
      simpa only [asIso_hom, Category.comp_id] using
        SubgroupFunctor.range_iso_comp (asIso c) (𝟙 G)
    _ = ⊤ := (SubgroupFunctor.top_isRepresentedBy_id G).2

/-- Trivial adjoint action over all algebras makes the diagonalizable
centralizer the entire group over the original ring. -/
theorem relativeCentralizer_eq_top_of_adjoint_eq
    (hG : IsReductive G)
    (h : ∀ (A : Type u) [CommRing A] [Algebra R A]
      (t : Lie.AffinePoints (groupScheme R M).toGrp A)
      (X : Additive (lieKernel G A)), adjoint G A (t ≫ i.hom.hom) X = X) :
    torusCentralizer i = ⊤ := by
  apply relativeCentralizer_eq_top_of_residue_lieInvariants_eq_top i hG
  intro s
  obtain ⟨f, hf⟩ := Spec.homEquiv.symm.surjective ((Spec R).fromSpecResidueField s)
  let : Algebra R ((Spec R).residueField s) := f.hom.toAlgebra
  rw [← hf]
  exact Lie.conjugation_lieInvariants_baseChange_eq_top i h ((Spec R).residueField s)

/-- A diagonalizable subgroup of a reductive group over an arbitrary ring
is central if it acts trivially on the Lie kernel over every algebra. -/
theorem isCentral_of_adjoint_eq
    (hG : IsReductive G)
    (h : ∀ (A : Type u) [CommRing A] [Algebra R A]
      (t : Lie.AffinePoints (groupScheme R M).toGrp A)
      (X : Additive (lieKernel G A)), adjoint G A (t ≫ i.hom.hom) X = X) :
    IsCentral i := by
  have htop := relativeCentralizer_eq_top_of_adjoint_eq i hG h
  intro U t V a g
  have hg : g ∈ (torusCentralizer i).carrier V := by
    rw [htop]
    trivial
  exact (hg V (𝟙 V) (a ≫ t)).symm

/-- The actual centralizer inclusion as an isomorphism under triviality of
its adjoint action over all coefficient algebras. -/
def relativeCentralizerIsoOfAdjointEq
    (hG : IsReductive G)
    (h : ∀ (A : Type u) [CommRing A] [Algebra R A]
      (t : Lie.AffinePoints (groupScheme R M).toGrp A)
      (X : Additive (lieKernel G A)), adjoint G A (t ≫ i.hom.hom) X = X) :
    relativeCentralizerGroupScheme i ≅ G :=
  (show (⊤ : SubgroupFunctor G).IsRepresentedBy (relativeCentralizerHom i) from
    (relativeCentralizer_eq_top_of_adjoint_eq i hG h) ▸
      isRepresentedBy_relativeCentralizerHom i).topIso

@[simp] theorem relativeCentralizerIsoOfAdjointEq_hom
    (hG : IsReductive G)
    (h : ∀ (A : Type u) [CommRing A] [Algebra R A]
      (t : Lie.AffinePoints (groupScheme R M).toGrp A)
      (X : Additive (lieKernel G A)), adjoint G A (t ≫ i.hom.hom) X = X) :
    (relativeCentralizerIsoOfAdjointEq i hG h).hom = relativeCentralizerHom i :=
  SubgroupFunctor.IsRepresentedBy.topIso_hom _

end Diagonalizable

end Langlands.GroupScheme
