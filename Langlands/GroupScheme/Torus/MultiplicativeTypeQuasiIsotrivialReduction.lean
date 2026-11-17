import Langlands.GroupScheme.Torus.MultiplicativeTypeQuasiIsotrivialStatement
import Langlands.CommutativeAlgebra.HenselianFiniteEtaleRefinementProof

/-! # Quasi-isotriviality: the henselian assertion from the étale-local one -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.MultiplicativeTypeQuasiIsotrivial

open RelativeMultiplicativeType

/-- A finite étale local algebra over a local ring is faithfully flat, so its spectrum maps
onto the spectrum of the base. -/
theorem surjective_specAlgebraMap_of_finite_etale (A : Type u) [CommRing A] [IsLocalRing A]
    (R' : Type u) [CommRing R'] [IsLocalRing R'] [Algebra A R'] [Algebra.Etale A R']
    [Module.Finite A R'] :
    Surjective (Spec.algebraMap A R') := by
  have : Module.FinitePresentation A R' :=
    Module.FinitePresentation.of_finite_of_finitePresentation A R'
  have : Module.Free A R' := Module.free_of_flat_of_isLocalRing
  have : Module.FaithfullyFlat A R' := inferInstance
  have h := (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap A R'))).2
    (RingHom.faithfullyFlat_algebraMap_iff.2 this)
  exact h.2

/-- If `H` over a henselian local base becomes diagonalizable on an étale cover, it becomes
diagonalizable after base change along a finite étale surjective morphism. -/
theorem exists_finite_etale_of_etale_cover (A : Type u) [CommRing A] [HenselianLocalRing A]
    (H : GroupScheme (Spec (CommRingCat.of A)))
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) (Spec (CommRingCat.of A)))
    (h𝒰 : ∀ i : 𝒰.I₀, IsDiagonalizable ((GroupScheme.baseChange (𝒰.f i)).obj H)) :
    ∃ (S' : Scheme.{u}) (p : S' ⟶ Spec (CommRingCat.of A)),
      IsFinite p ∧ Etale p ∧ Surjective p ∧
        IsDiagonalizable ((GroupScheme.baseChange p).obj H) := by
  let x := IsLocalRing.closedPoint A
  let i := 𝒰.idx x
  obtain ⟨y, hy⟩ := 𝒰.covers x
  let 𝒱 := (𝒰.X i).affineOpenCover
  let j := 𝒱.idx y
  obtain ⟨z, hz⟩ := 𝒱.covers y
  let f : Spec (𝒱.X j) ⟶ Spec (CommRingCat.of A) := 𝒱.f j ≫ 𝒰.f i
  have : Etale (𝒰.f i) := 𝒰.map_prop i
  have hf : Etale f := inferInstance
  have hx : x ∈ Set.range f := ⟨z, by
    simp only [f, Scheme.Hom.comp_apply]
    exact (congrArg (𝒰.f i) hz).trans hy⟩
  obtain ⟨R', hR', hlR', aR', he, hm, g, hfac⟩ :=
    Langlands.CommutativeAlgebra.henselianFiniteEtaleRefinement A (𝒱.X j) f hf hx
  let : CommRing R' := hR'
  let : IsLocalRing R' := hlR'
  let : Algebra A R' := aR'
  let : Algebra.Etale A R' := he
  let : Module.Finite A R' := hm
  refine ⟨Spec (CommRingCat.of R'), Spec.algebraMap A R', ?_, ?_, ?_, ?_⟩
  · exact (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 hm)
  · exact (HasRingHomProperty.Spec_iff (P := @Etale)).2 (RingHom.etale_algebraMap.2 he)
  · exact surjective_specAlgebraMap_of_finite_etale A R'
  · have hcomp : (g ≫ 𝒱.f j) ≫ 𝒰.f i = Spec.algebraMap A R' := by
      rw [Category.assoc]; exact hfac
    exact IsDiagonalizable.of_iso
      (Descent.pullbackComparison (𝒰.f i) (g ≫ 𝒱.f j) _ hcomp H).symm
      ((h𝒰 i).baseChange (g ≫ 𝒱.f j))

/-- If every point of `S` lies in the image of an étale morphism over which `H` becomes
diagonalizable, these morphisms, indexed by the points of `S`, form an étale cover of `S` that
splits `H`. -/
theorem exists_etale_cover_of_pointwise (S : Scheme.{u}) (H : GroupScheme S)
    (h : ∀ s : S, ∃ (U : Scheme.{u}) (f : U ⟶ S), Etale f ∧ s ∈ Set.range f ∧
      IsDiagonalizable ((GroupScheme.baseChange f).obj H)) :
    ∃ 𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S,
      ∀ i : 𝒰.I₀, IsDiagonalizable ((GroupScheme.baseChange (𝒰.f i)).obj H) := by
  choose U f hf hs hd using h
  exact ⟨Scheme.Cover.mkOfCovers S U f (fun s => ⟨s, hs s⟩) hf, hd⟩

/-- The first assertion of `MultiplicativeTypeQuasiIsotrivialStatement` implies the whole
statement: the henselian assertion follows by `exists_finite_etale_of_etale_cover`. -/
theorem multiplicativeTypeQuasiIsotrivial_of_etale
    (h : ∀ (S : Scheme.{u}) (H : GroupScheme S), IsMultiplicativeType H →
      ∃ 𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S,
        ∀ i : 𝒰.I₀, IsDiagonalizable ((GroupScheme.baseChange (𝒰.f i)).obj H)) :
    MultiplicativeTypeQuasiIsotrivialStatement.{u} := by
  refine ⟨h, fun A _ _ H hH => ?_⟩
  obtain ⟨𝒰, h𝒰⟩ := h _ H hH
  exact exists_finite_etale_of_etale_cover A H 𝒰 h𝒰

/-- Pointwise form of `multiplicativeTypeQuasiIsotrivial_of_etale`: it suffices that every
point of the base of a group of multiplicative type has an étale neighbourhood over which the
group becomes diagonalizable. -/
theorem multiplicativeTypeQuasiIsotrivial_of_pointwise
    (h : ∀ (S : Scheme.{u}) (H : GroupScheme S), IsMultiplicativeType H → ∀ s : S,
      ∃ (U : Scheme.{u}) (f : U ⟶ S), Etale f ∧ s ∈ Set.range f ∧
        IsDiagonalizable ((GroupScheme.baseChange f).obj H)) :
    MultiplicativeTypeQuasiIsotrivialStatement.{u} :=
  multiplicativeTypeQuasiIsotrivial_of_etale fun S H hH =>
    exists_etale_cover_of_pointwise S H (h S H hH)

end Langlands.GroupScheme.MultiplicativeTypeQuasiIsotrivial
