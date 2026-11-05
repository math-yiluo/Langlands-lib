import Langlands.AlgebraicGeometry.Picard.ArtinianDualNumberComparison

/-! # Actual automorphisms in Artinian dual-number Picard fibres -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid.ArtinianDualNumberComparison

open Langlands.AlgebraicGeometry.Deformation
open Langlands.AlgebraicGeometry.Modules
open DualNumberThickening

variable {k K : Type u} [CommRing k] [Field K] [Algebra k K]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
  (M : LineBundle (residueSpace (K := K) f))
  (A : ArtinianTestDeformations.Deformations f M (ArtinianTest.dualNumbers k K))

/-- The actual pointed comparison induces the usual pullback on automorphism groups. -/
def autEquiv :
    Aut A ≃* Aut ((pointedEquivalence f M).functor.obj A) :=
  (pointedEquivalence f M).fullyFaithfulFunctor.autMulEquivOfFullyFaithful A

lemma autEquiv_apply (a : Aut A) :
    autEquiv f M A a = (pointedEquivalence f M).functor.mapIso a := rfl

/-- The group comparison keeps the ordinary pullback of the actual bundle automorphism. -/
lemma autEquiv_bundle (a : Aut A) :
    (autEquiv f M A a).hom.right.iso =
      (LineBundle.pullback (spaceIso (K := K) f).hom).mapIso a.hom.right.iso := rfl

/-- Actual Artinian pointed automorphisms are the actual zero-section reduction kernel. -/
def autKernelEquiv :
    Aut A ≃* InfinitesimalAut (residueStructure (K := K) f)
      ((pointedEquivalence f M).functor.obj A).right.of :=
  (autEquiv f M A).trans (pointedAutKernelEquiv
    (residueStructure (K := K) f) M ((pointedEquivalence f M).functor.obj A))

/-- Forgetting the kernel proof gives actual ordinary pullback of the original automorphism. -/
lemma autKernelEquiv_val (a : Aut A) :
    (autKernelEquiv f M A a).val =
      (LineBundle.pullback (spaceIso (K := K) f).hom).mapIso a.hom.right.iso := rfl

/-- Every actual pointed automorphism has a unique residue-fibre global-function coefficient. -/
def autGlobalFunctionsEquiv :
    Aut A ≃* Multiplicative (FieldGlobalFunctions.sections (residueStructure (K := K) f)) :=
  (autEquiv f M A).trans (pointedAutGlobalFunctionsEquiv
    (residueStructure (K := K) f) M ((pointedEquivalence f M).functor.obj A))

/-- The coefficient comparison identifies the actual pulled-back automorphism with `1 + ε a`. -/
lemma autGlobalFunctionsEquiv_formula (a : Aut A) :
    (LineBundle.pullback (spaceIso (K := K) f).hom).mapIso a.hom.right.iso =
      LineBundle.unitAutEquiv
        ((pointedEquivalence f M).functor.obj A).right.of
        (topUnitsEquiv (residueStructure (K := K) f)
          (coefficientUnit (residueStructure (K := K) f) ⊤
            (Multiplicative.toAdd (autGlobalFunctionsEquiv f M A a)))) := by
  have h := pointedAutGlobalFunctionsEquiv_symm_val
    (residueStructure (K := K) f) M ((pointedEquivalence f M).functor.obj A)
    (Multiplicative.toAdd (autGlobalFunctionsEquiv f M A a))
  change ((pointedAutGlobalFunctionsEquiv _ _ _).symm
    ((pointedAutGlobalFunctionsEquiv _ _ _) (autEquiv f M A a))).hom.right.iso = _ at h
  rw [MulEquiv.symm_apply_apply] at h
  exact h

/-- Ordinary pullback coherence for the proved actual epsilon-scaling square. -/
def scalePullbackComparison (c : K) :
    LineBundle.pullback
      ((relativeSpace f).map (ArtinianTest.baseMap (ArtinianTest.dualScale k K c))) ⋙
        LineBundle.pullback (spaceIso (K := K) f).hom ≅
      LineBundle.pullback (spaceIso (K := K) f).hom ⋙
        LineBundle.pullback (scale (residueStructure (K := K) f) c) :=
  (LineBundle.pullbackComp (spaceIso (K := K) f).hom
    ((relativeSpace f).map (ArtinianTest.baseMap (ArtinianTest.dualScale k K c)))) ≪≫
    eqToIso (congrArg LineBundle.pullback (scale_spaceIso (K := K) f c).symm) ≪≫
      (LineBundle.pullbackComp (scale (residueStructure (K := K) f) c)
        (spaceIso (K := K) f).hom).symm

/-- The comparison on the actual bundle of an Artinian pointed deformation. -/
def scaleBundleComparison (c : K) :
    ((pointedEquivalence f M).functor.obj
      ((ArtinianTestDeformations.restrict f M (ArtinianTest.dualScale k K c)).obj A)).right.of ≅
      (LineBundle.pullback (scale (residueStructure (K := K) f) c)).obj
        ((pointedEquivalence f M).functor.obj A).right.of :=
  (scalePullbackComparison f c).app A.right.of

/-- The scaling comparison intertwines actual restriction of pointed automorphisms
and ordinary scaling pullback of the corresponding bundle automorphisms. -/
lemma scaleBundleComparison_naturality (c : K) (a : Aut A) :
    (autKernelEquiv f M
      ((ArtinianTestDeformations.restrict f M (ArtinianTest.dualScale k K c)).obj A)
      ((ArtinianTestDeformations.restrict f M
        (ArtinianTest.dualScale k K c)).mapIso a)).val ≪≫
        scaleBundleComparison f M A c =
      scaleBundleComparison f M A c ≪≫
        (LineBundle.pullback (scale (residueStructure (K := K) f) c)).mapIso
          (autKernelEquiv f M A a).val := by
  rw [autKernelEquiv_val, autKernelEquiv_val]
  simp only [Functor.mapIso_hom]
  rw [ArtinianTestDeformations.restrict_map_iso]
  apply Iso.ext
  exact (scalePullbackComparison f c).hom.naturality a.hom.right.iso.hom

/-- Actual Artinian epsilon restriction multiplies the unique coefficient by `c`,
with the ordinary coherence comparison on the actually pulled-back bundle. -/
lemma restrictAut_coefficient (c : K) (a : Aut A) :
    (autKernelEquiv f M
      ((ArtinianTestDeformations.restrict f M (ArtinianTest.dualScale k K c)).obj A)
      ((ArtinianTestDeformations.restrict f M
        (ArtinianTest.dualScale k K c)).mapIso a)).val ≪≫
        scaleBundleComparison f M A c =
      scaleBundleComparison f M A c ≪≫
        (infinitesimalAutEquiv (residueStructure (K := K) f)
          ((LineBundle.pullback (scale (residueStructure (K := K) f) c)).obj
            ((pointedEquivalence f M).functor.obj A).right.of)
          (Multiplicative.ofAdd (baseSectionMap (residueStructure (K := K) f) ⊤ c *
            (Multiplicative.toAdd (autGlobalFunctionsEquiv f M A a) :
              Γ(residueSpace (K := K) f, ⊤))))).val := by
  rw [scaleBundleComparison_naturality]
  congr 1
  have h : (autKernelEquiv f M A a).val =
      (infinitesimalAutEquiv (residueStructure (K := K) f)
        ((pointedEquivalence f M).functor.obj A).right.of
        (autGlobalFunctionsEquiv f M A a)).val := by
    exact congrArg Subtype.val
      ((infinitesimalAutEquiv (residueStructure (K := K) f)
        ((pointedEquivalence f M).functor.obj A).right.of).apply_symm_apply
          (autKernelEquiv f M A a)).symm
  rw [h]
  exact pullback_infinitesimalAutEquiv _ _ _ _

/-- Commutativity is proved for the original composition law on actual pointed automorphisms. -/
instance artinianAutCommGroup : CommGroup (Aut A) :=
  { (inferInstance : Group (Aut A)) with
    mul_comm := fun a b ↦ (autGlobalFunctionsEquiv f M A).injective (by
      rw [map_mul, map_mul, mul_comm]) }

/-- In additive notation, actual pointed automorphisms are actual global functions. -/
def autAddEquiv :
    Additive (Aut A) ≃+ FieldGlobalFunctions.sections (residueStructure (K := K) f) :=
  (autGlobalFunctionsEquiv f M A).toAdditive

/-- Scalars act on the unique global-function coefficient of an actual automorphism. -/
instance artinianAutSMul : SMul K (Additive (Aut A)) where
  smul c a := (autAddEquiv f M A).symm (c • autAddEquiv f M A a)

lemma autAddEquiv_smul (c : K) (a : Additive (Aut A)) :
    autAddEquiv f M A (c • a) = c • autAddEquiv f M A a :=
  (autAddEquiv f M A).apply_symm_apply _

/-- The module laws retain actual automorphism composition as addition. -/
instance artinianAutModule : Module K (Additive (Aut A)) :=
  Function.Injective.module K (autAddEquiv f M A).toAddMonoidHom
    (autAddEquiv f M A).injective (autAddEquiv_smul f M A)

/-- The actual pointed automorphism module is linearly the actual residue global functions. -/
def autLinearEquiv :
    Additive (Aut A) ≃ₗ[K] FieldGlobalFunctions.sections (residueStructure (K := K) f) :=
  { autAddEquiv f M A with map_smul' := autAddEquiv_smul f M A }

/-- Actual relative Artinian dual-number pointed automorphisms are actual derived H⁰. -/
def autH0LinearEquiv :
    Additive (Aut A) ≃ₗ[K]
      (DerivedSections.relativeCohomology (residueStructure (K := K) f) 0).obj
        (SheafOfModules.unit (residueSpace (K := K) f).ringCatSheaf) :=
  (autLinearEquiv f M A).trans
    ((DerivedSections.relativeCohomologyZeroIso (residueStructure (K := K) f)).app
      (SheafOfModules.unit (residueSpace (K := K) f).ringCatSheaf)).toLinearEquiv.symm

/-- Properness of the original scheme makes every actual pointed automorphism module finite. -/
theorem finiteDimensional_artinianAut [IsProper f] :
    FiniteDimensional K (Additive (Aut A)) := by
  let := FieldGlobalFunctions.finite (residueStructure (K := K) f)
  exact Module.Finite.equiv (autLinearEquiv f M A).symm

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid.ArtinianDualNumberComparison
