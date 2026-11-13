import Langlands.Representation.CuspidalSupport.RationalSummandInductionMembership
import Langlands.Representation.CuspidalSupport.RationalInertiaBlockIndecomposableStatement
import Langlands.Representation.CuspidalSupport.RationalNormKernelOrbitProof
import Langlands.Representation.CuspidalSupport.RationalNormKernelEndDomainProof
import Langlands.Representation.CuspidalSupport.RationalNormKernelSummand
import Langlands.Representation.Category.CoproductSize
import Langlands.CategoryTheory.Renard.DecompositionCenterIdempotent

/-!
# Renard VI.4.5, Corollary: the inertia block is indecomposable

Let `π` be an irreducible cuspidal representation of `G(F)`, `ρ` an irreducible summand
of its restriction to the common norm kernel `⁰G` (VI.3.2(i)) and `Π = c-Ind ρ`, which
lies in the block `M(G)[π]` (`rationalSummandInduction_mem_block`). A two-factor
decomposition of the block gives an idempotent central element `z`
(`Renard.decompositionIdem`). Its value at `Π` is an idempotent of the domain `End Π`
(VI.4.3), hence `0` or `1`. A central element `c` that vanishes at `Π` and is the
identity at an object `X` forces `X = 0`: otherwise `X` has an irreducible subquotient
`σ` on which `c` is the identity, `σ` is an unramified twist of `π`, so Frobenius
reciprocity and VI.3.2(iii) give a nonzero map `Π → σ`, and naturality of `c` kills it.
Applied to `z` or to `1 - z`, this shows that one of the two factors is zero.

This proof does not use the VI.4.1 equivalence.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

open Aubert.General Aubert.General.RationalPointFamily GroupScheme

section Vanishing

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local instance rationalInertiaBlockIndecomposableTopology :
    TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X

local instance rationalInertiaBlockIndecomposableTopologicalGroup :
    IsTopologicalGroup (GroupScheme.rationalPoints G) :=
  rationalPoint_isTopologicalGroup F G

/-- Let `ρ ↪ π|_{⁰G}` be an irreducible summand of the restriction of an irreducible `π`,
with `Π = c-Ind ρ` in the block `M(G)[π]`. A central element `c` of the block which
vanishes on `Π` and is the identity on an object `X` forces `X` to be zero. -/
theorem isZero_of_catCenter_app_eq_id (hG : GroupScheme.IsConnectedReductive G)
    (π : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G)) (hπ : π.IsIrreducible)
    (ρ : SmoothRep.{0, uF, uV} ℂ (rationalCommonNormKernel G)) (hρ : ρ.IsIrreducible)
    (j : ρ ⟶ SmoothRep.restrictSubgroup (rationalCommonNormKernel G) π)
    (hj : Function.Injective (SmoothRep.hom j))
    (hmem : rationalInertiaBlockProperty G (rationalInertiaBaseLift G π)
      ((Induction.compactInductionFunctor (rationalCommonNormKernel G)).obj
        (SmoothRep.toRep.obj ρ)))
    (c : CatCenter (RationalInertiaBlock G (rationalInertiaBaseLift G π)))
    (hc0 : ∀ u, SmoothRep.hom (c.app ⟨_, hmem⟩).hom u = 0)
    (X : RationalInertiaBlock G (rationalInertiaBaseLift G π)) (hcX : c.app X = 𝟙 X) :
    IsZero X := by
  by_contra hX
  have hnt : Nontrivial X.obj := by
    by_contra hs
    rw [not_nontrivial_iff_subsingleton] at hs
    exact hX (IsZero.of_full_of_faithful_of_isZero
      (rationalInertiaBlockProperty G (rationalInertiaBaseLift G π)).ι X
      ((SmoothRep.isZero_iff_subsingleton X.obj).mpr hs))
  obtain ⟨σ, hσ, hσX⟩ := SmoothRep.exists_isIrreducible_isSubquotient_of_nontrivial X.obj
  obtain ⟨B, i, q, hi, hq⟩ := SmoothRep.isSubquotient_iff_exists.mp hσX
  have hBX : SmoothRep.IsSubquotient B X.obj :=
    SmoothRep.isSubquotient_iff_exists.mpr ⟨B, i, 𝟙 B, hi, Function.surjective_id⟩
  let B' : RationalInertiaBlock G (rationalInertiaBaseLift G π) :=
    ⟨B, rationalInertiaBlockProperty_of_isSubquotient X.property hBX⟩
  let σ' : RationalInertiaBlock G (rationalInertiaBaseLift G π) :=
    ⟨σ, rationalInertiaBlockProperty_of_isSubquotient X.property hσX⟩
  let i' : B' ⟶ X := ObjectProperty.homMk i
  let q' : B' ⟶ σ' := ObjectProperty.homMk q
  have hB : ∀ b, SmoothRep.hom (c.app B').hom b = b := by
    intro b
    apply hi
    have hnat := CatCenter.naturality c i'
    rw [hcX, Category.comp_id] at hnat
    have h1 := congrArg (fun f : B' ⟶ X => SmoothRep.hom f.hom b) hnat
    exact h1.symm
  have hσid : ∀ s, SmoothRep.hom (c.app σ').hom s = s := by
    intro s
    obtain ⟨b, rfl⟩ := hq s
    have h1 := congrArg (fun f : B' ⟶ σ' => SmoothRep.hom f.hom b) (CatCenter.naturality c q')
    change SmoothRep.hom (c.app σ').hom (SmoothRep.hom q b) =
      SmoothRep.hom q (SmoothRep.hom (c.app B').hom b) at h1
    rw [h1, hB]
  obtain ⟨χ, ⟨eσ⟩⟩ := X.property σ hσ hσX
  have hπlift : (rationalInertiaBaseLift G π).IsIrreducible :=
    (SmoothRep.isIrreducible_universeLift_iff.{uF} π).mpr hπ
  have h3 := rationalNormKernelTwistEquivalence F G hG (rationalInertiaBaseLift G π) σ
    hπlift hσ
  obtain ⟨ψ⟩ := h3.1.mpr ⟨χ, ⟨SmoothRep.equivOfIso eσ.symm⟩⟩
  let e := Induction.restrictAlongEquiv (rationalCommonNormKernel G).subtype
    (SmoothRep.universeLiftEquiv.{uF} π)
  let φ : Representation.IntertwiningMap ρ.representation
      (σ.representation.comp (rationalCommonNormKernel G).subtype) :=
    ψ.toIntertwiningMap.comp (e.toIntertwiningMap.comp (SmoothRep.hom j))
  have hφ : Function.Injective φ := ψ.injective.comp (e.injective.comp hj)
  let _ : Representation.IsIrreducible ρ.representation := hρ
  let _ : Nontrivial ρ :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (rationalCommonNormKernel G))
      ρ.representation.asModule
  obtain ⟨v, hv⟩ := exists_ne (0 : ρ)
  let Q : RationalInertiaBlock G (rationalInertiaBaseLift G π) := ⟨_, hmem⟩
  let f : Q.obj ⟶ σ := SmoothRep.ofHom
    (Induction.cosetSum (rationalCommonNormKernel G) (isOpen_rationalCommonNormKernel G)
      σ.representation ρ.representation φ)
  let f' : Q ⟶ σ' := ObjectProperty.homMk f
  let u : Q.obj := Induction.unitMap (rationalCommonNormKernel G)
    (isOpen_rationalCommonNormKernel G) ρ.representation ρ.isSmooth v
  have h1 := congrArg (fun g : Q ⟶ σ' => SmoothRep.hom g.hom u) (CatCenter.naturality c f')
  change SmoothRep.hom (c.app σ').hom (SmoothRep.hom f u) =
    SmoothRep.hom f (SmoothRep.hom (c.app Q).hom u) at h1
  have h2 : SmoothRep.hom (c.app Q).hom u = 0 := hc0 u
  rw [hσid, h2, map_zero] at h1
  change Induction.cosetSum (rationalCommonNormKernel G) (isOpen_rationalCommonNormKernel G)
    σ.representation ρ.representation φ
      (Induction.unitMap (rationalCommonNormKernel G) (isOpen_rationalCommonNormKernel G)
        ρ.representation ρ.isSmooth v) = 0 at h1
  rw [Induction.cosetSum_comp_unitMap] at h1
  exact hv (hφ (h1.trans (map_zero φ).symm))

end Vanishing

/-- Renard VI.4.5, Corollary: the inertia block `M(G)[π]` of an irreducible cuspidal `π`
is indecomposable. -/
theorem rationalInertiaBlockIndecomposable :
    RationalInertiaBlockIndecomposableStatement.{uF, uV} := by
  intro F _ _ _ _ G hG S i hi _ _ _ ν hν hStandard hRoots hU h π hπ hcusp P hP
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := hG.smooth
  let _ : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
  have : IsTopologicalGroup (GroupScheme.rationalPoints G) :=
    rationalPoint_isTopologicalGroup F G
  obtain ⟨W, hW⟩ := (rationalNormKernelOrbit F G hG π hπ).1
  let ρ := restrictionSummand (rationalCommonNormKernel G) π W
  have hρ : ρ.IsIrreducible := restrictionSummand_isIrreducible _ π W hW
  have hmem := rationalSummandInduction_mem_block G hG π hπ ρ hρ
    (restrictionSummandι _ π W) (restrictionSummandι_injective _ π W)
  let Q : RationalInertiaBlock G (rationalInertiaBaseLift G π) := ⟨_, hmem⟩
  have : IsDomain (End Q.obj) := rationalNormKernelEnd_isDomain F G hG ρ hρ
  let z := Renard.decompositionIdem hP
  let eQ : End Q.obj := (z.app Q).hom
  have hidem : IsIdempotentElem eQ := by
    have h1 := congrArg (fun c : CatCenter (RationalInertiaBlock G
      (rationalInertiaBaseLift G π)) => (c.app Q).hom)
      (Renard.decompositionIdem_isIdempotentElem hP)
    change (z.app Q ≫ z.app Q).hom = (z.app Q).hom at h1
    exact h1
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp hidem with h0 | h1
  · refine ⟨true, fun X hX => isZero_of_catCenter_app_eq_id G hG π hπ ρ hρ
      (restrictionSummandι _ π W) (restrictionSummandι_injective _ π W) hmem z ?_ X
      (Renard.decompositionIdem_app_of_true hP hX)⟩
    intro u
    change SmoothRep.hom eQ u = 0
    rw [h0]
    rfl
  · refine ⟨false, fun X hX => isZero_of_catCenter_app_eq_id G hG π hπ ρ hρ
      (restrictionSummandι _ π W) (restrictionSummandι_injective _ π W) hmem (1 - z) ?_ X ?_⟩
    · intro u
      change SmoothRep.hom ((1 - z).app Q).hom u = 0
      rw [CatCenter.app_sub]
      change SmoothRep.hom ((1 : End Q.obj) - eQ) u = 0
      rw [h1]
      change u - u = 0
      exact sub_self u
    · rw [CatCenter.app_sub, Renard.decompositionIdem_app_of_false hP hX, sub_zero]
      rfl

end Langlands.CuspidalSupport
