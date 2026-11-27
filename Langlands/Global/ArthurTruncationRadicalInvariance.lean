import Langlands.Global.ArthurTruncationLocalBoundedness
import Langlands.GroupScheme.Rational.StandardLeviIntersectionReduction

/-! # Invariance of the cutoff and constant terms along the actual radicals -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.Global.ArthurTruncation.Idempotence

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
  AdelicGroupPoints ArthurParabolicSpaces

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

section Radicals

variable {U : GroupScheme (Spec (CommRingCat.of F))} [IsAffine U.X.left]
  (j : U ⟶ G) [IsClosedImmersion j.hom.hom.left]

local notation "V" => SubgroupFunctor.range j
local notation "A" => AdelicSubgroupPoints.adelicPoints F G V
local notation "Γ" => AdelicSubgroupPoints.rationalSubgroup F G V
local notation "X" => AdelicSubgroupPoints.RationalQuotient F G V

/-- Normalized unipotent constant terms are left invariant under the actual
adelic unipotent group, by right invariance on its rational quotient. -/
theorem subgroupConstantTerm_unipotent_mul
    (hs : Smooth U.X.hom) (hc : ConnectedSpace U.X.left) (hu : IsUnipotent U)
    (φ : AdelicGroupPoints F G → ℂ)
    (hφ : ∀ r ∈ rationalSubgroup F G, ∀ x, φ (r * x) = φ x)
    (n : A) (g : AdelicGroupPoints F G) :
    subgroupConstantTerm F j φ ((n : AdelicGroupPoints F G) * g) =
      subgroupConstantTerm F j φ g := by
  let : IsClosed (A : Set (AdelicGroupPoints F G)) :=
    AdelicSubgroupPoints.isClosed_adelicPoints_range F G j
  let : CompactSpace X :=
    AdelicSubgroupPoints.compactSpace_rationalQuotient_range_unipotent F j hs hc hu
  let : BorelSpace X := AdelicSubgroupPoints.rationalQuotientBorelSpace F G V
  let m := AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G V
  let e := LeftCosetSpace.rightTranslateHomeomorph Γ n
  have he : MeasurePreserving e m m :=
    AdelicSubgroupPoints.measurePreserving_rightTranslate_of_compactRationalQuotient F G V n
  have hInv (y : AdelicGroupPoints F G) (r : Γ) (v : A) :
      φ ((((r : A) * v : A) : AdelicGroupPoints F G) * y) =
        φ ((v : AdelicGroupPoints F G) * y) := by
    rw [Subgroup.coe_mul, mul_assoc]
    exact hφ _ (rationalImage_le_rationalSubgroup j
      ((mem_rationalSubgroup_range_iff j _).mp r.2)) _
  let f (y : AdelicGroupPoints F G) :=
    LeftCosetSpace.lift Γ (fun v : A => φ ((v : AdelicGroupPoints F G) * y)) (hInv y)
  have hf (y : AdelicGroupPoints F G) (q : X) :
      f y q = φ (((q.out : A) : AdelicGroupPoints F G) * y) := by
    conv_lhs => rw [← Quotient.out_eq q]
    rfl
  have hshift : f ((n : AdelicGroupPoints F G) * g) = f g ∘ e := by
    funext q
    obtain ⟨v, rfl⟩ := LeftCosetSpace.mk_surjective Γ q
    change φ ((v : AdelicGroupPoints F G) * ((n : AdelicGroupPoints F G) * g)) =
      φ (((v : AdelicGroupPoints F G) * n) * g)
    rw [mul_assoc]
  change (∫ q : X, φ (((q.out : A) : AdelicGroupPoints F G) * ((n : AdelicGroupPoints F G) * g))
      ∂m) = ∫ q : X, φ (((q.out : A) : AdelicGroupPoints F G) * g) ∂m
  simp only [← hf, hshift]
  exact he.integral_comp e.measurableEmbedding _

end Radicals

variable {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {i : T.toGrp ⟶ G} [Mono i.hom.hom.left] {ν : cocharacterLattice T}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)

include hG hi hν in
omit [NumberField F] [Mono i.hom.hom.left] [LocallyOfFiniteType G.X.hom] in
theorem unipotentRange_le {S J : Set (characterLattice T)}
    (hSJ : S ⊆ J) (hJ : J ⊆ simpleRelativeRoots i ν) :
    SubgroupFunctor.range (Standard.unipotentHom i ν J) ≤
      SubgroupFunctor.range (Standard.unipotentHom i ν S) := by
  rw [(Standard.isRepresentedBy_unipotentHom i ν J).2, (Standard.isRepresentedBy_unipotentHom i ν S).2]
  exact ((standardParabolicOrder F G hG T i hi ν hν).1 S J (hSJ.trans hJ) hJ).2 hSJ |>.2

include hG hi hν in
omit [NumberField F] [Mono i.hom.hom.left] [LocallyOfFiniteType G.X.hom] in
theorem unipotentRange_isNormalizedBy {S J : Set (characterLattice T)}
    (hSJ : S ⊆ J) (hJ : J ⊆ simpleRelativeRoots i ν) :
    (SubgroupFunctor.range (Standard.unipotentHom i ν J)).IsNormalizedBy
      (SubgroupFunctor.range (Standard.unipotentHom i ν S)) := by
  rw [(Standard.isRepresentedBy_unipotentHom i ν J).2, (Standard.isRepresentedBy_unipotentHom i ν S).2]
  intro X v u hv hu
  have hvS := standardUnipotent_le_standardParabolic i ν S X hv
  have hvJ := ((standardParabolicOrder F G hG T i hi ν hν).1 S J (hSJ.trans hJ) hJ).1.mp hSJ X hvS
  exact StandardLeviIntersection.conj_mem_standardUnipotent i ν hvJ hu

variable {K : Subgroup (AdelicGroupPoints F G)}
  (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
  (hρ : Function.Bijective (restrictToTorus F i ν ∅))

include hG hν in
omit [Mono i.hom.hom.left] [LocallyOfFiniteType G.X.hom] in
/-- Every standard radical belongs to the minimal radical, hence preserves `H₀`. -/
theorem height_radical_mul {S : Set (characterLattice T)}
    (hS : S ⊆ simpleRelativeRoots i ν)
    (n : AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (Standard.unipotentHom i ν S)))
    (g : AdelicGroupPoints F G) :
    height hi hK hρ ((n : AdelicGroupPoints F G) * g) = height hi hK hρ g := by
  have ha : (n : AdelicGroupPoints F G) ∈
      AdelicSubgroupPoints.adelicPoints F G
        (SubgroupFunctor.range (Standard.unipotentHom i ν ∅)) :=
    unipotentRange_le hG hi hν (Set.empty_subset S) hS _ n.2
  obtain ⟨v, hv⟩ := ha
  change map F _ G (Standard.unipotentHom i ν ∅) v = n.val at hv
  have hu := (Standard.parabolicStructure i ν hG hi hν ∅ (Set.empty_subset _)).2.2.1.1.isUnipotent
  have hv' := map_comp_apply_of_hom (p := Standard.parabolicHom i ν ∅)
    (Standard.unipotentToParabolic i ν ∅) (v : AdelicGroupPoints F _)
  rw [Standard.unipotentToParabolic_comp, hv] at hv'
  have hh := hK.height_unipotent_mul hu (Standard.unipotentToParabolic i ν ∅) v g
  rw [← hv'] at hh
  unfold height
  rw [hh]

include hG hi hν in
omit [Mono i.hom.hom.left] in
theorem constantTerm_radical_mul {S : Set (characterLattice T)}
    (hS : S ⊆ simpleRelativeRoots i ν)
    (φ : AdelicGroupPoints F G → ℂ)
    (hφ : ∀ r ∈ rationalSubgroup F G, ∀ y, φ (r * y) = φ y)
    (n : AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (Standard.unipotentHom i ν S)))
    (g : AdelicGroupPoints F G) :
    constantTerm F i ν S φ ((n : AdelicGroupPoints F G) * g) = constantTerm F i ν S φ g := by
  have hU := (Standard.parabolicStructure i ν hG hi hν S hS).2.2.1.1
  exact subgroupConstantTerm_unipotent_mul (Standard.unipotentHom i ν S)
    hU.smooth hU.connectedSpace hU.isUnipotent φ hφ n g

include hν in
theorem cutoffKernel_radical_mul (D : RelativeRootReflectionData i)
    {S : Set (characterLattice T)} (hS : S ⊆ simpleRelativeRoots i ν)
    (Tp : V T) (φ : AdelicGroupPoints F G → ℂ)
    (hφ : ∀ r ∈ rationalSubgroup F G, ∀ y, φ (r * y) = φ y)
    (n : AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (Standard.unipotentHom i ν S)))
    (g : AdelicGroupPoints F G) :
    cutoffKernel hG hi D hK hρ S Tp φ ((n : AdelicGroupPoints F G) * g) =
      cutoffKernel hG hi D hK hρ S Tp φ g := by
  unfold cutoffKernel
  rw [constantTerm_radical_mul hG hi hν hS φ hφ, height_radical_mul hG hi hν hK hρ hS]

end Langlands.Global.ArthurTruncation.Idempotence
