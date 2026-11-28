import Langlands.GroupScheme.Rational.PureInnerTwistTorusReduction
import Langlands.GroupScheme.Rational.InducedCocenterCocycleVanishing
import Langlands.GroupScheme.Rational.NumberFieldTotallyComplexInnerTypeA
import Langlands.GroupScheme.Rational.FullOrbitWeilRankOne
import Langlands.GroupScheme.Rational.SplitTorusCentralizerCocenterProof
import Langlands.GroupScheme.SimplyConnected.TypeD4KernelLeafFactors

/-! # Cohomology of the centralizer for a centrally marked trialitarian index -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open Langlands.CentralSimple

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1100000
set_option maxRecDepth 2600

namespace TitsIndexData.AnisotropicKernelIndex

variable {F : Type u} [Field F] {H : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]
  {d : TitsIndexData H} (p : d.AnisotropicKernelIndex)

local notation "E" => SeparableClosure F
local notation "b" => algebraBaseMap F E
local notation "Dgeom" => Functor.obj (GroupScheme.baseChange (algebraBaseMap F (SeparableClosure F))) p.kernel

private theorem factorOrbit_eq_univ
    [IsAffineHom (Dgeom).X.hom] [Smooth (Dgeom).X.hom]
    (D : SimplyConnectedAlmostSimpleProduct Dgeom) (hsem : IsSemisimple Dgeom)
    (q : d.Vertex ≃ Fin 4) (hq : d.IsNumberingOf (CartanMatrix.D 4) (fun i => i.val = 1) q)
    (hno : ¬ ∃ a : d.Vertex, q a ≠ 1 ∧ ∀ σ : E ≃ₐ[F] E, d.star σ a = a)
    (a : p.index.Vertex) :
    D.galoisFactorOrbit (p.index.geometricFactorIndex D hsem a) = Set.univ := by
  let f := p.index.geometricFactorIndex D hsem
  have hsurj : Function.Surjective f :=
    D.rootDatumFactorIndex_surjective_on_base hsem p.index.pinning.toSplitPinning
  apply Set.eq_univ_iff_forall.mpr
  intro j
  obtain ⟨x, rfl⟩ := hsurj j
  let u := p.comparison.vertexEquiv a
  let v := p.comparison.vertexEquiv x
  have hu := (d.zeroVertices_iff_D4_leaf q hq u.val).mp u.property
  have hv := (d.zeroVertices_iff_D4_leaf q hq v.val).mp v.property
  obtain ⟨σ, hσ⟩ := d.star_transitive_on_D4_leaves_of_no_fixed_leaf q hq.1 hno u.val v.val hu hv
  have he := (congrArg Subtype.val (p.comparison.vertexEquiv_star σ a)).trans hσ
  have hx : p.index.star σ a = x := p.comparison.vertexEquiv.injective (Subtype.ext he)
  exact ⟨σ, (p.index.geometricFactorIndex_star D hsem σ a).symm.trans (congrArg f hx)⟩

attribute [local instance] SimplyConnectedAlmostSimpleProduct.factorStabilizerDescent_isAffine
  SimplyConnectedAlmostSimpleProduct.factorStabilizerDescent_locallyOfFiniteType

/-- Transitivity on the leaves identifies the kernel with a single Weil
restriction of a simply connected rank-one group. -/
private theorem exists_kernelWeilRankOne (hsc : IsSimplyConnected H)
    (q : d.Vertex ≃ Fin 4) (hq : d.IsNumberingOf (CartanMatrix.D 4) (fun i => i.val = 1) q)
    (hno : ¬ ∃ a : d.Vertex, q a ≠ 1 ∧ ∀ σ : E ≃ₐ[F] E, d.star σ a = a) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra F K) (_ : FiniteDimensional F K)
      (A : GroupScheme (Spec (CommRingCat.of K))) (_ : IsAffine A.X.left)
      (_ : IsAffineHom A.X.hom) (_ : LocallyOfFiniteType A.X.hom)
      (dA : TitsIndexData A), IsSimplyConnected A ∧ IsAbsolutelyAlmostSimple A ∧
        Nonempty (dA.Vertex ≃ Fin 1) ∧ Nonempty (AffineWeil.groupScheme F K A ≅ p.kernel) := by
  have psc := p.isSimplyConnected hsc
  let : Smooth p.kernel.X.hom := p.index.isSemisimple.isConnectedReductive.smooth
  have pgeom := isSimplyConnectedFieldExtension F E p.kernel psc
  have hsem := pgeom.isSemisimple
  let : Smooth (Dgeom).X.hom := hsem.isConnectedReductive.smooth
  let : IsAffineHom (Dgeom).X.hom := hsem.isConnectedReductive.isAffineHom
  let D := pgeom.almostSimpleProduct
  let a := (p.d4LeafNumbering q hq).symm 0
  let i := p.index.geometricFactorIndex D hsem a
  have hall : D.galoisFactorOrbit i = Set.univ := p.factorOrbit_eq_univ D hsem q hq hno a
  let K := D.factorStabilizerField i
  let A := (D.factorStabilizerDescent i).1
  have hA : IsSimplyConnected A := D.isSimplyConnected_factorStabilizerDescent i
  let : IsAffine A.X.left := inferInstanceAs (IsAffine (D.factorStabilizerDescent i).1.X.left)
  let : IsAffineHom A.X.hom := hA.isSemisimple.isConnectedReductive.isAffineHom
  let : LocallyOfFiniteType A.X.hom :=
    inferInstanceAs (LocallyOfFiniteType (D.factorStabilizerDescent i).1.X.hom)
  let C := p.index.descendedComponentPinning D hsem psc a
  let dA := (C.actualDiagram hA.isSemisimple).index
  let eA : dA.Vertex ≃ Fin 1 := (C.actualVertices hA.isSemisimple).trans
    { toFun := fun _ => 0
      invFun := fun _ => ⟨a, p.index.cartanConnected_refl a⟩
      left_inv := fun x => Subtype.ext
        ((p.cartanConnected_iff_eq_D4_central_mark q hq _ _).mp x.property)
      right_inv := fun _ => Subsingleton.elim _ _ }
  let w := D.orbitWeilInclusion i
  let hw : IsIso w := D.isIso_orbitWeilInclusion_of_full i hall
  exact ⟨K, inferInstance, inferInstance, inferInstance, A, inferInstance, inferInstance,
    inferInstance, dA, hA, D.isAbsolutelyAlmostSimple_factorStabilizerDescent_of_isSepClosed i,
    ⟨eA⟩, ⟨@asIso _ _ _ _ w hw⟩⟩

private theorem isTrivial_kernelCocycle [NumberField F] [IsTotallyComplex F]
    (hn : NumberFieldReducedNormLocalityStatement.{u}) (hsc : IsSimplyConnected H)
    (q : d.Vertex ≃ Fin 4) (hq : d.IsNumberingOf (CartanMatrix.D 4) (fun i => i.val = 1) q)
    (hno : ¬ ∃ a : d.Vertex, q a ≠ 1 ∧ ∀ σ : E ≃ₐ[F] E, d.star σ a = a)
    (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    (ξ : Cocycle p.kernel (GaloisCocycle.cover F L)) : ξ.IsTrivial := by
  obtain ⟨K, _, _, _, A, _, _, _, dA, hA, hAbs, ⟨eA⟩, ⟨e⟩⟩ :=
    p.exists_kernelWeilRankOne hsc q hq hno
  let : NumberField K := NumberField.of_module_finite F K
  have ht := isTrivial_weilTypeAOne_of_totallyComplex hn hA hAbs dA eA
    ((p.isSimplyConnected hsc).of_iso e) (ξ.map e.inv)
  obtain ⟨g, hg⟩ := ht.map e.hom
  refine ⟨g, fun x y => ?_⟩
  have h := hg x y
  change (ξ.toFun x y ≫ e.inv.hom.hom) ≫ e.hom.hom.hom = _ at h
  rw [Category.assoc, ← Grp.comp_hom_hom, e.inv_hom_id, Grp.id_hom_hom, Category.comp_id] at h
  exact h

/-- Reduced-norm locality and Hilbert 90 give full degree-one vanishing in
the centralizer of a maximal split torus for the centrally marked index. -/
theorem isTrivial_centralizerCocycle_D4 [NumberField F] [IsTotallyComplex F]
    (hn : NumberFieldReducedNormLocalityStatement.{u}) (hsc : IsSimplyConnected H)
    (q : d.Vertex ≃ Fin 4) (hq : d.IsNumberingOf (CartanMatrix.D 4) (fun i => i.val = 1) q)
    (hno : ¬ ∃ a : d.Vertex, q a ≠ 1 ∧ ∀ σ : E ≃ₐ[F] E, d.star σ a = a)
    (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    (ξ : Cocycle p.centralizer (GaloisCocycle.cover F L)) : ξ.IsTrivial := by
  have hM := d.centralizer_isConnectedReductive p.represents
  let : IsAffineHom p.centralizer.X.hom := hM.isAffineHom
  obtain ⟨Q, r, hQa, hr, _, _⟩ := cocenterQuotientExistence F p.centralizer p.kernel p.derived hM p.isDerived
  have hQ := splitTorusCentralizerCocenterInduced F H hsc d.splitTorus d.splitInclusion
    d.maximalSplit.1 p.centralizer p.inclusion p.represents p.kernel p.derived p.isDerived Q r hr
  let : IsAffine Q.X.left := hQa
  let : IsAffineHom Q.X.hom := inferInstance
  let : IsAffineHom r.hom.hom.left := IsAffineHom.of_comp _ Q.X.hom
  let : IsClosedImmersion p.derived.hom.hom.left := p.isDerived.1
  let : Mono p.derived.hom.hom := Over.mono_of_mono_left _
  exact ξ.isTrivial_of_inducedTorusQuotient p.derived r p.index.isSemisimple.isConnectedReductive.smooth
    hr hQ (fun L _ _ _ _ ζ => p.isTrivial_kernelCocycle hn hsc q hq hno L ζ)

end TitsIndexData.AnisotropicKernelIndex

/-- For a pure inner form with the centrally marked trialitarian index, the
original cocycle of a quasi-split simply connected group is a coboundary. -/
theorem LocalGroupIso.HasDiscrepancy.isTrivial_of_D4_centralMarking
    {F L : Type u} [Field F] [NumberField F] [IsTotallyComplex F] [Field L]
    [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    {G H : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]
    {ξ : Cocycle G (GaloisCocycle.cover F L)} {e : LocalGroupIso G H (GaloisCocycle.cover F L)}
    (hξ : e.HasDiscrepancy (AutomorphicAction.conjugation (𝟙 G)) ξ)
    (hn : NumberFieldReducedNormLocalityStatement.{u})
    (hsc : IsSimplyConnected G) (hG : IsQuasiSplit G) (hH : IsSimplyConnected H)
    (d : TitsIndexData H) (q : d.Vertex ≃ Fin 4)
    (hq : d.IsNumberingOf (CartanMatrix.D 4) (fun i => i.val = 1) q)
    (hno : ¬ ∃ a : d.Vertex, q a ≠ 1 ∧
      ∀ σ : SeparableClosure F ≃ₐ[F] SeparableClosure F, d.star σ a = a) : ξ.IsTrivial := by
  let p := d.anisotropicKernelIndex
  apply hξ.isTrivial_of_prescribedTwistTorus hsc hG hH.isSemisimple.isConnectedReductive d.maximalTorus
  intro E _ _ _ _ ζ
  have h := p.isTrivial_centralizerCocycle_D4 hn hH q hq hno E (ζ.map (d.centralizerTorus p.represents))
  obtain ⟨f, hf⟩ := h.map p.inclusion
  refine ⟨f, fun x y => ?_⟩
  have he := hf x y
  change (ζ.toFun x y ≫ (d.centralizerTorus p.represents).hom.hom) ≫ p.inclusion.hom.hom = _ at he
  rw [Category.assoc, ← Grp.comp_hom_hom, d.centralizerTorus_comp p.represents] at he
  exact he

end Langlands.GroupScheme
