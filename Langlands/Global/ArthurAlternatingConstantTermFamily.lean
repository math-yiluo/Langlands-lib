import Langlands.Global.ArthurAlternatingConstantTerm
import Langlands.Global.AdelicNormOneExtension
import Langlands.Global.AdelicNormOneConstantTermDerivative
import Langlands.Global.AdelicConstantTermDirectionalGrowth
import Langlands.Global.EisensteinConstantTerm.Points

/-! # Constant terms of extended norm-one functions

For a standard parabolic subgroup `P` and a continuous left `G(F)`-invariant function `ψ` on
`G(𝔸)¹`, this module records the properties of the constant term along `P` of the extension
`normOneExtension hG ψ` used for families: continuity, joint measurability, the integrated
derivative identity, and a bound of the integral over a family by integrals of `ψ` at the
translates by a compact set of points of the unipotent radical. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u w

open AlgebraicGeometry CategoryTheory MeasureTheory
open scoped CategoryTheory.MonObj ENNReal

namespace Langlands.Global.ArthurTruncation

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  AdelicSubgroupPoints

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom] {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {i : T.toGrp ⟶ G} [Mono i.hom.hom.left] {ν : cocharacterLattice T}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)

local notation "A" => AdelicGroupPoints F G
local notation "G¹" => normOneSubgroup F G

omit [Mono i.hom.hom.left] in
include hi hν in
/-- **Continuity.** -/
theorem continuous_constantTerm_normOneExtension {P : Set (characterLattice T)}
    (hP : P ⊆ simpleRelativeRoots i ν) {ψ : G¹ → ℂ} (hψ : Continuous ψ)
    (hinv : ∀ (g : rationalNormOneSubgroup F G) x, ψ ((g : G¹) * x) = ψ x) :
    Continuous (constantTerm F i ν P (normOneExtension hG ψ)) := by
  let U := Standard.unipotentScheme i ν P
  let j := Standard.unipotentHom i ν P
  have hgeom := (Standard.parabolicStructure i ν hG hi hν P hP).2.2.1
  let : IsAffine U.X.left := @isAffine_of_isAffineHom _ _ U.X.hom
    (Standard.isClosedSubgroup_unipotentHom i ν P).isAffineHom_source inferInstance
  let : IsClosedImmersion j.hom.hom.left := Standard.isClosedSubgroup_unipotentHom i ν P
  exact continuous_subgroupConstantTerm_of_unipotentInvariant j hgeom.1.smooth
    hgeom.1.connectedSpace hgeom.1.isUnipotent _ (continuous_normOneExtension hG hψ)
    (fun q x => by rw [map_rational]; exact normOneExtension_rational_mul hG hinv _ x)

omit [Mono i.hom.hom.left] in
include hi hν in
/-- **Joint measurability for families.** -/
theorem measurable_constantTerm_normOneExtension_family {P : Set (characterLattice T)}
    (hP : P ⊆ simpleRelativeRoots i ν) {Ω : Type w} [MeasurableSpace Ω] {ψ : Ω → G¹ → ℂ}
    (hψ : ∀ o, Continuous (ψ o))
    (hinv : ∀ o (g : rationalNormOneSubgroup F G) x, ψ o ((g : G¹) * x) = ψ o x)
    (hm : Measurable (fun p : Ω × G¹ => ψ p.1 p.2)) :
    Measurable (fun p : Ω × A => constantTerm F i ν P (normOneExtension hG (ψ p.1)) p.2) := by
  let U := Standard.unipotentScheme i ν P
  let j := Standard.unipotentHom i ν P
  have hgeom := (Standard.parabolicStructure i ν hG hi hν P hP).2.2.1
  let : IsAffine U.X.left := @isAffine_of_isAffineHom _ _ U.X.hom
    (Standard.isClosedSubgroup_unipotentHom i ν P).isAffineHom_source inferInstance
  let : IsClosedImmersion j.hom.hom.left := Standard.isClosedSubgroup_unipotentHom i ν P
  let : Smooth U.X.hom := hgeom.1.smooth
  exact measurable_subgroupConstantTerm_family j hgeom.1.connectedSpace hgeom.1.isUnipotent
    (fun o => continuous_normOneExtension hG (hψ o))
    (measurable_normOneExtension_family hG hm)
    (fun o q x => by rw [map_rational]; exact normOneExtension_rational_mul hG (hinv o) _ x)

omit [Mono i.hom.hom.left] in
include hi hν in
/-- **Integrated derivative identity.** -/
theorem isNormOnePathDerivative_constantTerm_normOneExtension {d e : ℕ}
    {hsmooth : SmoothOfRelativeDimension d G.X.hom} (At : NormOneLieAtlas F G hsmooth e)
    {P : Set (characterLattice T)} (hP : P ⊆ simpleRelativeRoots i ν) {ψ : G¹ → ℂ}
    {ψ' : Fin e → G¹ → ℂ} (hψ : Continuous ψ) (hψ' : ∀ l, Continuous (ψ' l))
    (hinv : ∀ (g : rationalNormOneSubgroup F G) x, ψ ((g : G¹) * x) = ψ x)
    (hinv' : ∀ l (g : rationalNormOneSubgroup F G) x, ψ' l ((g : G¹) * x) = ψ' l x)
    (hder : IsNormOnePathDerivative At (normOneExtension hG ψ)
      (fun l => normOneExtension hG (ψ' l))) :
    IsNormOnePathDerivative At (constantTerm F i ν P (normOneExtension hG ψ))
      (fun l => constantTerm F i ν P (normOneExtension hG (ψ' l))) := by
  let U := Standard.unipotentScheme i ν P
  let j := Standard.unipotentHom i ν P
  have hgeom := (Standard.parabolicStructure i ν hG hi hν P hP).2.2.1
  let : IsAffine U.X.left := @isAffine_of_isAffineHom _ _ U.X.hom
    (Standard.isClosedSubgroup_unipotentHom i ν P).isAffineHom_source inferInstance
  let : IsClosedImmersion j.hom.hom.left := Standard.isClosedSubgroup_unipotentHom i ν P
  let : Smooth U.X.hom := hgeom.1.smooth
  exact isNormOnePathDerivative_subgroupConstantTerm j hgeom.1.connectedSpace hgeom.1.isUnipotent
    At (continuous_normOneExtension hG hψ) (fun l => continuous_normOneExtension hG (hψ' l))
    (fun q x => by rw [map_rational]; exact normOneExtension_rational_mul hG hinv _ x)
    (fun l q x => by rw [map_rational]; exact normOneExtension_rational_mul hG (hinv' l) _ x)
    hder

omit [Mono i.hom.hom.left] in
include hi hν in
/-- **Family bound.** There is a compact set `C` of points of the unipotent radical of `P` such
that the integral over a family of the constant terms of the extensions at a norm-one point `x` is
at most the supremum over `h ∈ C` of the integrals of the family at `h x`. -/
theorem exists_lintegral_constantTerm_normOneExtension_le {P : Set (characterLattice T)}
    (hP : P ⊆ simpleRelativeRoots i ν) :
    ∃ C : Set (AdelicGroupPoints F G), IsCompact C ∧ C ⊆ G¹ ∧
      ∀ {Ω : Type w} [MeasurableSpace Ω] (mΩ : Measure Ω) (ψ : Ω → G¹ → ℂ),
        (∀ o, Continuous (ψ o)) →
        (∀ o (g : rationalNormOneSubgroup F G) x, ψ o ((g : G¹) * x) = ψ o x) →
        Measurable (fun p : Ω × G¹ => ψ p.1 p.2) →
        ∀ x : G¹, ∫⁻ o, ‖constantTerm F i ν P (normOneExtension hG (ψ o)) x‖ₑ ∂mΩ ≤
          ⨆ (h : G¹) (_ : (h : A) ∈ C), ∫⁻ o, ‖ψ o (h * x)‖ₑ ∂mΩ := by
  let U := Standard.unipotentScheme i ν P
  let j := Standard.unipotentHom i ν P
  have hgeom := (Standard.parabolicStructure i ν hG hi hν P hP).2.2.1
  let : IsAffine U.X.left := @isAffine_of_isAffineHom _ _ U.X.hom
    (Standard.isClosedSubgroup_unipotentHom i ν P).isAffineHom_source inferInstance
  let : IsClosedImmersion j.hom.hom.left := Standard.isClosedSubgroup_unipotentHom i ν P
  let : Smooth U.X.hom := hgeom.1.smooth
  obtain ⟨C, hC, hbound⟩ :=
    exists_lintegral_enorm_subgroupConstantTerm_le.{u, w} j hgeom.1.connectedSpace hgeom.1.isUnipotent
  have hmem (h : AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j)) :
      h.val ∈ G¹ := unipotent_adelicPoints_mem_normOne j hgeom.1.connectedSpace hgeom.1.isUnipotent h
  refine ⟨Subtype.val '' C, hC.image continuous_subtype_val, ?_, ?_⟩
  · rintro _ ⟨h, -, rfl⟩
    exact hmem h
  intro Ω _ mΩ ψ hψ hinv hm x
  refine (hbound mΩ (fun o => normOneExtension hG (ψ o)) (fun o => continuous_normOneExtension hG (hψ o))
    (measurable_normOneExtension_family hG hm)
    (fun o q y => by rw [map_rational]; exact normOneExtension_rational_mul hG (hinv o) _ y)
    (x : A)).trans ?_
  refine iSup₂_le fun h hh => ?_
  let h₁ : G¹ := ⟨h.val, hmem h⟩
  refine le_iSup₂_of_le (f := fun (h : G¹) (_ : (h : A) ∈ Subtype.val '' C) =>
    ∫⁻ o, ‖ψ o (h * x)‖ₑ ∂mΩ) h₁ ⟨h, hh, rfl⟩ (le_of_eq ?_)
  refine lintegral_congr fun o => ?_
  change ‖normOneExtension hG (ψ o) ((h₁ * x : G¹) : A)‖ₑ = _
  rw [normOneExtension_coe]

end Langlands.Global.ArthurTruncation
