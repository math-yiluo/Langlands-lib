import Langlands.GroupScheme.Reductive.SplitSemisimpleRootSpanNecessity
import Langlands.GroupScheme.Reductive.RootDatumAssembly
import Langlands.GroupScheme.Rational.SplitComponentCharacterTrace

/-! # Semisimple root data from actual integral reflection data -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open Langlands.LinearAlgebra.RationalSpan
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {i : T.toGrp ⟶ G}

/-- An integral cocharacter of a split closed torus in a semisimple group
that annihilates every actual root is zero. -/
theorem IsSemisimple.cocharacter_eq_zero_of_annihilates_relativeRoots
    (hG : IsSemisimple G) (hT : IsSplitTorus T.toGrp) (hi : IsClosedSubgroup i)
    (ν : cocharacterLattice T)
    (hν : ∀ α ∈ relativeRoots i, latticePairing T α ν = 0) : ν = 0 := by
  have := hG.isConnectedReductive.smooth
  have := hG.isConnectedReductive.connectedSpace
  have hc := rootAnnihilatorCentrality k G T hT i ν hν
  have hc0 := rootAnnihilatorCentrality k G T hT i 0 fun α _ => map_zero _
  obtain ⟨Z, z, hz, hfin⟩ := hG.hasFiniteCenter
  have hr := hz.isRepresentedBy
  have ha := hr.liftOfLE_comp _ ((isCentral_iff_range_le_center _).1 hc)
  have hb := hr.liftOfLE_comp _ ((isCentral_iff_range_le_center _).1 hc0)
  have hgm : IsSplitTorus (Gm (Spec (CommRingCat.of k))).toGrp := isSplitTorus_gm
  have := hgm.smooth
  have := hgm.isAffineHom
  have := hgm.connectedSpace
  let q : Z ⟶ Grp.trivial (Over (Spec (CommRingCat.of k))) := default
  have : IsFinite q.hom.hom.left := by
    have hw : q.hom.hom.left = Z.X.hom :=
      (Category.comp_id _).symm.trans (Over.w q.hom.hom)
    rw [hw]
    exact hfin
  have hab := finiteHom_cancel q
    (a := hr.liftOfLE _ ((isCentral_iff_range_le_center _).1 hc))
    (b := hr.liftOfLE _ ((isCentral_iff_range_le_center _).1 hc0))
    (Subsingleton.elim _ _)
  have hi' : CommGroupScheme.groupHom ν ≫ i = CommGroupScheme.groupHom 0 ≫ i := by
    rw [← ha, ← hb, hab]
  have : IsClosedImmersion i.hom.hom.left := hi
  have hl : (CommGroupScheme.groupHom ν).hom.hom.left =
      (CommGroupScheme.groupHom (0 : cocharacterLattice T)).hom.hom.left := by
    rw [← cancel_mono i.hom.hom.left]
    exact congrArg (fun φ => φ.hom.hom.left) hi'
  have hg : CommGroupScheme.groupHom ν = CommGroupScheme.groupHom 0 := by
    apply Grp.hom_ext
    exact Over.OverMorphism.ext hl
  exact congrArg Additive.ofMul hg

/-- The actual roots of any split closed torus in a semisimple group span
its whole rational character space. No root datum or reflection data is assumed. -/
theorem IsSemisimple.relativeRootSpan_eq_top
    (hG : IsSemisimple G) (hT : IsSplitTorus T.toGrp) (hi : IsClosedSubgroup i) :
    relativeRootSpan i = ⊤ := by
  have := hG.isConnectedReductive.smooth
  have : Finite (relativeRoots i) := (hT.finite_relativeRoots i).to_subtype
  have hχ (χ : characterLattice T) : toRat χ ∈ relativeRootSpan i := by
    apply (hT.toRat_mem_ratSpan_iff_annihilator (relativeRoots i) χ).mpr
    intro ν hν
    rw [hG.cocharacter_eq_zero_of_annihilates_relativeRoots hT hi ν hν, map_zero]
  apply top_unique
  intro x _
  induction x using TensorProduct.inductionOn with
  | tmul q χ =>
    simpa only [toRat_apply, smul_tmul', smul_eq_mul, mul_one] using
      Submodule.smul_mem (relativeRootSpan i) q (hχ χ)
  | add x y hx hy =>
    exact Submodule.add_mem _ (hx (by trivial)) (hy (by trivial))

variable [Mono i.hom.hom.left]

/-- For a semisimple ambient group, actual integral normalizer reflections
give a root datum with finite coroot index, without a root-reducedness input. -/
theorem RelativeRootReflectionData.exists_semisimple_rootDatum
    (D : RelativeRootReflectionData i) (hG : IsSemisimple G)
    (hT : IsSplitTorus T.toGrp) (hi : IsClosedSubgroup i) :
    ∃ (J : Type u) (_ : Finite J)
      (P : RootDatum J (characterLattice T) (cocharacterLattice T)),
      IsRootDatumOf i P ∧ Finite (cocharacterLattice T ⧸ P.corootSpan ℤ) := by
  have := hG.isConnectedReductive.smooth
  have hfinite := hT.finite_relativeRoots i
  have hspan : Submodule.span ℚ
      (toRat '' (relativeRoots i ∪ Set.range (torusCharacterRestrict i))) = ⊤ := by
    apply top_unique
    rw [← hG.relativeRootSpan_eq_top hT hi]
    exact Submodule.span_mono (Set.image_mono Set.subset_union_left)
  let P := D.rootDatum hT hfinite hspan
  have hP : IsRootDatumOf i P := D.isRootDatumOf_rootDatum hT hfinite hspan
  have : Finite (relativeRoots i) := hfinite.to_subtype
  have : Module.Finite ℤ (characterLattice T) := hT.finite_characterLattice
  exact ⟨relativeRoots i, inferInstance, P, hP,
    P.finite_quotient_rootSpan_iff_corootSpan.mp (hG.finite_quotient_rootSpan hT hi hP)⟩

/-- The semisimple root-datum and finite-coroot-index construction needs only
actual integral reflection data, in addition to the geometric hypotheses. -/
def SemisimpleReflectionDatumStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsSemisimple G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (_hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G) (hi : IsClosedSubgroup i),
    haveI := hG.isConnectedReductive.isAffineHom
    haveI : IsClosedImmersion i.hom.hom.left := hi
    ∀ (_ : RelativeRootReflectionData i),
      ∃ (J : Type u) (_ : Finite J)
        (P : RootDatum J (characterLattice T) (cocharacterLattice T)),
        IsRootDatumOf i P ∧ Finite (cocharacterLattice T ⧸ P.corootSpan ℤ)

/-- The semisimple reflection-data reduction holds in every characteristic. -/
theorem semisimpleReflectionDatum : SemisimpleReflectionDatumStatement.{u} := by
  intro k _ G hG T hT i hi D
  have := hG.isConnectedReductive.isAffineHom
  have : IsClosedImmersion i.hom.hom.left := hi
  exact D.exists_semisimple_rootDatum hG hT hi

end Langlands.GroupScheme
