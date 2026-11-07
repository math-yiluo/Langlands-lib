import Langlands.GroupScheme.CocycleRelativeTrivialization
import Langlands.GroupScheme.SimplyConnected.LocalUnramifiedSplittingStatement
import Langlands.GroupScheme.Rational.HenselianDiscreteQuasiSplitStatement
import Langlands.GroupScheme.Rational.SteinbergAssembly
import Langlands.GroupScheme.Rational.DimensionLEOneTorusCocycleVanishingProof
import Langlands.FieldTheory.HenselianDiscreteDimensionLEOneProof
import Langlands.Geometry.Building.UnramifiedQuasiSplitReduction
import Langlands.GroupScheme.Reductive.AlgebraicExtensionAscent
import Langlands.GroupScheme.BaseChangeReflection
import Langlands.AlgebraicGeometry.Picard.IntermediateFieldBaseChangeLimit
import Mathlib.FieldTheory.SplittingField.Construction

/-! # Finite unramified splitting from quasi-splitness and torus reduction

Over a nonarchimedean local field `F`, a cocycle of a semisimple simply connected group on a
finite Galois cover `Spec M` becomes trivial over a finite unramified extension, provided
connected reductive groups over Henselian discretely valued fields with algebraically closed
residue field are quasi-split, and finite-Galois cocycles of quasi-split semisimple groups have
torus reductions.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry Polynomial
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry.Picard

set_option backward.isDefEq.respectTransparency false in
/-- For an algebraic extension `Ω / k`, a morphism `U ⊗ Spec Ω ⟶ X` over `Spec k`, with `U`
quasi-compact and quasi-separated and `X` locally of finite presentation, factors through
`U ⊗ Spec E` for a finite intermediate field `E`. -/
theorem exists_finIntermediateField_whiskerLeft_comp_eq (k Ω : Type u) [Field k] [Field Ω]
    [Algebra k Ω] [Algebra.IsAlgebraic k Ω]
    (U : Over (Spec (CommRingCat.of k))) [QuasiCompact U.hom] [QuasiSeparated U.hom]
    (X : Over (Spec (CommRingCat.of k))) [LocallyOfFinitePresentation X.hom]
    (g : U ⊗ Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) ⟶ X) :
    ∃ E : FinIntermediateField k Ω,
      ∃ gE : U ⊗ Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k E.1))) ⟶ X,
        U ◁ Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap E.1 Ω)))
            (by simp only [Over.mk_hom]; rw [← Spec.map_comp, algebraMap_comp_algebraMap]) ≫
          gE = g := by
  let D := baseChangeDiagram (Ω := Ω) U.left U.hom
  let c := baseChangeCone (Ω := Ω) U.left U.hom
  let t : D ⟶ (Functor.const _).obj (Spec (CommRingCat.of k)) :=
    { app E := pullback.fst _ _ ≫ U.hom
      naturality E E' a := by simp [D, baseChangeDiagram] }
  have hw : g.left ≫ X.hom = pullback.fst _ _ ≫ U.hom := Over.w g
  have ha : c.π ≫ t = (Functor.const _).map (g.left ≫ X.hom) := by
    rw [hw]
    ext E
    simp [c, t, baseChangeCone]
  obtain ⟨E, h, hh, hh'⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    D t X.hom c (isLimitBaseChangeCone U.left U.hom) g.left ha
  refine ⟨E.unop, Over.homMk h hh', ?_⟩
  apply Over.OverMorphism.ext
  exact hh

set_option backward.isDefEq.respectTransparency false in
/-- Quasi-splitness over Henselian discretely valued fields with algebraically closed residue
field, together with torus reduction of finite-Galois cocycles of quasi-split semisimple groups,
gives the finite unramified splitting of simply connected cocycles over local fields. -/
theorem localSimplyConnectedUnramifiedSplitting_of_steinberg
    (hqs : HenselianDiscreteQuasiSplitStatement.{u})
    (hred : QuasiSplitCocycleTorusReductionStatement.{u}) :
    LocalSimplyConnectedUnramifiedSplittingStatement.{u} := by
  intro F _ _ _ _ G _ hG M _ _ _ _ ξ
  let K := LocalGalois.Separable.inertiaFixedField F
  let U : Over (Spec (CommRingCat.of F)) :=
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap F M)))
  let b₀ : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of F) :=
    Spec.map (CommRingCat.ofHom (algebraMap F K))
  let P : Over (Spec (CommRingCat.of F)) := Over.mk b₀
  -- A trivialization relative to the maximal unramified extension `K`.
  obtain ⟨gK, hgK⟩ : ∃ g : U ⊗ P ⟶ G.X, ξ.IsTrivialOver P g := by
    let GK := (GroupScheme.baseChange b₀).obj G
    have hGK : IsSemisimple GK := hG.isSemisimple.baseChange_of_algebraicExtension
    have hqsK : IsQuasiSplit GK := hqs K (Geometry.Building.MaximalUnramified.valuation F)
      (Geometry.Building.MaximalUnramified.valuation_surjective F)
      (Geometry.Building.MaximalUnramified.valuationSubring_isHenselian F)
      (Geometry.Building.MaximalUnramified.residueField_isAlgClosed F) GK
      hGK.isConnectedReductive
    have hT : HasTrivialTorusCocycles K := dimensionLEOneTorusCocycleVanishing K
      (FieldTheory.henselianDiscreteDimensionLEOne K
        (Geometry.Building.MaximalUnramified.valuation F)
        (Geometry.Building.MaximalUnramified.valuation_surjective F)
        (Geometry.Building.MaximalUnramified.valuationSubring_isHenselian F)
        (Geometry.Building.MaximalUnramified.residueField_isAlgClosed F))
    obtain ⟨p, hp, _⟩ := IsGalois.is_separable_splitting_field F M
    let L := SplittingField (p.map (algebraMap F K))
    have : IsGalois K L :=
      IsGalois.of_separable_splitting_field (p := p.map (algebraMap F K)) hp.map
    let j : M →ₐ[F] L := IsSplittingField.lift M p (by
      rw [IsScalarTower.algebraMap_eq F K L, ← Polynomial.map_map]
      exact SplittingField.splits _)
    let V : Over (Spec (CommRingCat.of K)) :=
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L)))
    let r : (Over.map b₀).obj V ⟶ U := Over.homMk (Spec.map (CommRingCat.ofHom j.toRingHom)) (by
      change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
      ext x
      exact (j.commutes x).trans (IsScalarTower.algebraMap_apply F K L x))
    have htriv : (ξ.baseChange b₀ V r).IsTrivial :=
      cocycle_isTrivial_of_torusReduction hred hT GK hGK hqsK L _
    obtain ⟨f, hf⟩ := Cocycle.exists_of_baseChange_isTrivial b₀ ξ V r htriv
    let s : (Over.map b₀).obj V ⟶ P := Over.homMk V.hom rfl
    obtain ⟨h₁, h₂, h₃⟩ := fieldExtension_fpqc K L
    have : QuasiCompact s.left := h₃
    have : Flat s.left := h₂
    have : Surjective s.left := h₁
    exact ξ.exists_isTrivialOver r s f (fun a b hab => hf a b (congrArg CommaMorphism.left hab))
  -- A finite stage `E` of `K / F`.
  have : QuasiCompact U.hom :=
    inferInstanceAs (QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap F M))))
  have : QuasiSeparated U.hom :=
    inferInstanceAs (QuasiSeparated (Spec.map (CommRingCat.ofHom (algebraMap F M))))
  have : LocallyOfFinitePresentation G.X.hom :=
    let : Smooth G.X.hom := hG.isSemisimple.isConnectedReductive.smooth
    inferInstance
  obtain ⟨E, gE, hgE⟩ := exists_finIntermediateField_whiskerLeft_comp_eq F K U G.X gK
  let PE : Over (Spec (CommRingCat.of F)) :=
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap F E.1)))
  have hE : ξ.IsTrivialOver PE gE := by
    obtain ⟨h₁, h₂, h₃⟩ := fieldExtension_fpqc E.1 K
    let tE : P ⟶ PE := Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap E.1 K)))
      (by
        change Spec.map _ ≫ Spec.map _ = Spec.map _
        rw [← Spec.map_comp, algebraMap_comp_algebraMap])
    have : QuasiCompact tE.left := h₃
    have : Flat tE.left := h₂
    have : Surjective tE.left := h₁
    apply Cocycle.IsTrivialOver.of_whiskerLeft tE
    rw [hgE]
    exact hgK
  -- Transport `E` to an intermediate field of the separable closure.
  let E' : IntermediateField F (SeparableClosure F) := IntermediateField.lift E.1
  let φ : E.1 ≃ₐ[F] E' := IntermediateField.liftAlgEquiv E.1
  have : FiniteDimensional F E.1 := E.2
  have hfin : FiniteDimensional F E' := LinearEquiv.finiteDimensional φ.toLinearEquiv
  let PE' : Over (Spec (CommRingCat.of F)) :=
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap F E')))
  let e : PE' ≅ PE := Over.isoMk (Scheme.Spec.mapIso φ.toRingEquiv.toCommRingCatIso.op) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1)
  refine ⟨E', hfin, IntermediateField.lift_le E.1, U ◁ e.hom ≫ gE, ?_⟩
  have h : ξ.IsTrivialOver PE' (U ◁ e.hom ≫ gE) := Cocycle.IsTrivialOver.of_whiskerLeft e.inv (by
    rwa [← Category.assoc, ← whiskerLeft_comp, e.inv_hom_id, whiskerLeft_id, Category.id_comp])
  intro Z a b hab
  exact h a b hab

end Langlands.GroupScheme
