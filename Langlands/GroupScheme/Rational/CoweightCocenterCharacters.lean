import Langlands.GroupScheme.Rational.CoweightSubgroupCoroots
import Langlands.GroupScheme.Rational.CocenterCorootCharacters
import Langlands.GroupScheme.Rational.DerivedRootDatumComparison
import Langlands.GroupScheme.Rational.DerivedTorusCentralComplement

/-! # Actual cocenter characters selected by a supplied coweight -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u v w z

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {G M D : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    [IsAffineHom M.X.hom] [LocallyOfFiniteType M.X.hom]
    [IsAffineHom D.X.hom] [LocallyOfFiniteType D.X.hom]
    {T S Q : CommGroupScheme (Spec (CommRingCat.of k))}
    {i : T.toGrp ⟶ G} {t : T.toGrp ⟶ M}
    {J : Type v} {K : Type w} {L : Type z}
    {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
    {R : RootDatum K (characterLattice T) (cocharacterLattice T)}
    {U : RootDatum L (characterLattice S) (cocharacterLattice S)}

/-- The image of the actual derived coroot span is the ambient zero-root
coroot span for the same supplied coweight. The central complement is
constructed from the actual centralizer datum. -/
theorem IsRootDatumOf.map_derived_corootSpan_eq_coweight_zero
    (hP : IsRootDatumOf i P) (hR : IsRootDatumOf t R)
    (j : M ⟶ G) (hcomp : t ≫ j = i)
    (hM : IsConnectedReductive M) (d : D ⟶ M) (hd : IsDerivedSubgroup d)
    (a : S.toGrp ⟶ D) (ha : IsMaximalTorus a)
    (ht : IsMaximalTorus t) (φ : S ⟶ T)
    (hsquare : CommGroupScheme.groupHom φ ≫ t = a ≫ d)
    (hT : IsSplitTorus T.toGrp) (hS : IsSplitTorus S.toGrp)
    (hi : IsClosedSubgroup i) (hU : IsRootDatumOf a U)
    (ν : cocharacterLattice T)
    (hroots : relativeRoots t =
      {α | α ∈ relativeRoots i ∧ latticePairing T α ν = 0}) :
    (U.corootSpan ℤ).map (RealTorusSpace.cocharacterMapInt φ) =
      Submodule.span ℤ (P.coroot '' {p | P.root' p ν = 0}) := by
  have : Smooth M.X.hom := hM.smooth
  have : Mono t.hom.hom.left := ht.2.1.mono
  have : Finite (weylImage t) :=
    splitTorusWeylImageFinite k M T hT t ht.2.1
  let Z := derivedTorusCentralComplement φ a t d hM hd
    (ht.isMaximalSplitTorus hT) (ha.isMaximalSplitTorus hS) hsquare.symm hR
  have := Z.flat
  have := Z.surjective
  exact (hR.map_corootSpan_derived φ Z.map a t d hsquare.symm hS Z.isSplit
    Z.isCentral hd hT hU).trans
      (hP.corootSpan_eq_coweight_zero hR j hcomp hT hi ν hroots)

namespace characterLattice

/-- Actual cocenter characters are canonically identified, by actual
pullback, with the annihilator of the supplied coweight's zero-root coroots.
The integral coroot-span comparison is constructed from the actual data. -/
def cocenterCoweightAnnihilatorEquiv
    (hP : IsRootDatumOf i P) (hR : IsRootDatumOf t R)
    (j : M ⟶ G) (hcomp : t ≫ j = i)
    (hM : IsConnectedReductive M) (d : D ⟶ M) (hd : IsDerivedSubgroup d)
    (hD : IsSemisimple D)
    (a : S.toGrp ⟶ D) (ha : IsMaximalTorus a)
    (ht : IsMaximalTorus t) (φ : S ⟶ T)
    (hsquare : CommGroupScheme.groupHom φ ≫ t = a ≫ d)
    (q : M ⟶ Q.toGrp)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range d) q)
    (hT : IsSplitTorus T.toGrp) (hS : IsSplitTorus S.toGrp)
    (hQ : IsSplitTorus Q.toGrp)
    (hi : IsClosedSubgroup i) (hU : IsRootDatumOf a U)
    (hprod : Surjective (subgroupProductMap d t).left)
    (hI : IsTorus (subgroupIntersection t d))
    (ν : cocharacterLattice T)
    (hroots : relativeRoots t =
      {α | α ∈ relativeRoots i ∧ latticePairing T α ν = 0}) :
    characterLattice Q ≃ₗ[ℤ] Langlands.RootDatum.corootAnnihilator P
      {p | P.root' p ν = 0} :=
  cocenterCorootAnnihilatorEquiv d hd hD t ht.2.1 a ha φ hsquare q hq
    hT hS hQ hprod hI P U {p | P.root' p ν = 0} hP.1 hU
    (hP.map_derived_corootSpan_eq_coweight_zero hR j hcomp hM d hd a ha ht φ
      hsquare hT hS hi hU ν hroots)

/-- The actual cocenter character pullback is injective, with image the
annihilator of all ambient coroots whose roots vanish on the supplied
coweight. No coroot-span comparison is assumed. -/
theorem cocenter_coweight_character_comparison
    (hP : IsRootDatumOf i P) (hR : IsRootDatumOf t R)
    (j : M ⟶ G) (hcomp : t ≫ j = i)
    (hM : IsConnectedReductive M) (d : D ⟶ M) (hd : IsDerivedSubgroup d)
    (hD : IsSemisimple D)
    (a : S.toGrp ⟶ D) (ha : IsMaximalTorus a)
    (ht : IsMaximalTorus t) (φ : S ⟶ T)
    (hsquare : CommGroupScheme.groupHom φ ≫ t = a ≫ d)
    (q : M ⟶ Q.toGrp)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range d) q)
    (hT : IsSplitTorus T.toGrp) (hS : IsSplitTorus S.toGrp)
    (hQ : IsSplitTorus Q.toGrp)
    (hi : IsClosedSubgroup i) (hU : IsRootDatumOf a U)
    (hprod : Surjective (subgroupProductMap d t).left)
    (hI : IsTorus (subgroupIntersection t d))
    (ν : cocharacterLattice T)
    (hroots : relativeRoots t =
      {α | α ∈ relativeRoots i ∧ latticePairing T α ν = 0}) :
    Function.Injective (precompose (Additive.ofMul (t ≫ q) : T ⟶ Q)) ∧
      ∀ x, x ∈ (precompose (Additive.ofMul (t ≫ q) : T ⟶ Q)).toIntLinearMap.range ↔
        ∀ p, P.root' p ν = 0 → P.toLinearMap x (P.coroot p) = 0 := by
  let e := cocenterCoweightAnnihilatorEquiv hP hR j hcomp hM d hd hD a ha ht φ hsquare
    q hq hT hS hQ hi hU hprod hI ν hroots
  have he (χ : characterLattice Q) :
      (e χ).val =
        (precompose (Additive.ofMul (t ≫ q) : T ⟶ Q)).toIntLinearMap χ := rfl
  constructor
  · intro χ ψ h
    apply e.injective
    apply Subtype.ext
    rw [he, he]
    exact h
  · intro x
    constructor
    · rintro ⟨χ, rfl⟩
      have hx := (e χ).property
      simpa only [Langlands.RootDatum.mem_corootAnnihilator, he, Set.mem_ofPred_eq]
        using hx
    · intro hx
      have hx' : x ∈ Langlands.RootDatum.corootAnnihilator P {p | P.root' p ν = 0} := by
        simpa only [Langlands.RootDatum.mem_corootAnnihilator, Set.mem_ofPred_eq] using hx
      obtain ⟨χ, hχ⟩ := e.surjective ⟨x, hx'⟩
      refine ⟨χ, ?_⟩
      simpa only [he] using congrArg Subtype.val hχ

end characterLattice

end Langlands.GroupScheme
