import Langlands.GroupScheme.Rational.GaloisBorelFaceRoots
import Langlands.GroupScheme.Reductive.InnerStarWeights
import Langlands.GroupScheme.Reductive.RootDatumHomLattices
import Langlands.GroupScheme.Torus.CharacterIsomorphism
import Langlands.GroupScheme.Torus.InducedProducts
import Langlands.GroupScheme.Absolute.RegularPerturbation
import Langlands.LinearAlgebra.RootDatumSimpleCorootEquiv

/-! # The torus product for complementary derived Levi faces -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.RootDatumSimpleCorootEquiv

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 750000

section Bases

variable {E : Type u} [Field E] {T T₁ T₂ : CommGroupScheme (Spec (CommRingCat.of E))}
  {I I₁ I₂ : Type*}

private theorem character_ext_of_latticePairing_basis
    (hT : IsSplitTorus T.toGrp) (B : Module.Basis I ℤ (cocharacterLattice T))
    {χ ψ : characterLattice T} (h : ∀ a, latticePairing T χ (B a) = latticePairing T ψ (B a)) :
    χ = ψ :=
  hT.isPerfPair_latticePairing.bijective_left.injective (B.ext h)

/-- Character restriction is bijective when the images of the two
cocharacter bases together form a basis of the target. -/
theorem character_restriction_bijective_of_bases
    (hT : IsSplitTorus T.toGrp) (hT₁ : IsSplitTorus T₁.toGrp) (hT₂ : IsSplitTorus T₂.toGrp)
    (f₁ : T₁ ⟶ T) (f₂ : T₂ ⟶ T)
    (B : Module.Basis I ℤ (cocharacterLattice T))
    (B₁ : Module.Basis I₁ ℤ (cocharacterLattice T₁))
    (B₂ : Module.Basis I₂ ℤ (cocharacterLattice T₂))
    (e : I₁ ⊕ I₂ ≃ I)
    (h₁ : ∀ a, B₁ a ≫ f₁ = B (e (Sum.inl a)))
    (h₂ : ∀ a, B₂ a ≫ f₂ = B (e (Sum.inr a))) :
    Function.Bijective (fun χ : characterLattice T => (f₁ ≫ χ, f₂ ≫ χ)) := by
  constructor
  · intro χ ψ h
    apply character_ext_of_latticePairing_basis hT B
    intro a
    obtain ⟨b, rfl⟩ := e.surjective a
    rcases b with b | b
    · have hχ : f₁ ≫ χ = f₁ ≫ ψ := congrArg Prod.fst h
      rw [← h₁, ← latticePairing_precomp, ← latticePairing_precomp, hχ]
    · have hχ : f₂ ≫ χ = f₂ ≫ ψ := congrArg Prod.snd h
      rw [← h₂, ← latticePairing_precomp, ← latticePairing_precomp, hχ]
  · rintro ⟨χ₁, χ₂⟩
    let w := Sum.elim (fun a => latticePairing T₁ χ₁ (B₁ a)) (fun a => latticePairing T₂ χ₂ (B₂ a))
    obtain ⟨χ, hχ⟩ := hT.isPerfPair_latticePairing.bijective_left.surjective
      (B.constr ℤ (w ∘ e.symm))
    refine ⟨χ, Prod.ext ?_ ?_⟩
    · apply character_ext_of_latticePairing_basis hT₁ B₁
      intro a
      rw [latticePairing_precomp, h₁, show latticePairing T χ = _ from hχ, Module.Basis.constr_basis]
      simp [w]
    · apply character_ext_of_latticePairing_basis hT₂ B₂
      intro a
      rw [latticePairing_precomp, h₂, show latticePairing T χ = _ from hχ, Module.Basis.constr_basis]
      simp [w]

end Bases

section TorusProducts

variable {F E : Type u} [Field F] [Field E] [Algebra F E]
  {T T₁ T₂ : CommGroupScheme (Spec (CommRingCat.of F))}

local notation "b" => algebraBaseMap F E
local notation "BC" => CommGroupScheme.baseChange b
local notation "P" => CommGroupScheme.prod T₁ T₂

/-- A product map of tori is an isomorphism if its two character restrictions
jointly give an equivalence over a common splitting field. -/
theorem isIso_torusProduct_of_character_restrictions
    (f₁ : T₁ ⟶ T) (f₂ : T₂ ⟶ T)
    (hT : IsSplitTorus ((BC).obj T).toGrp)
    (hT₁ : IsSplitTorus ((BC).obj T₁).toGrp) (hT₂ : IsSplitTorus ((BC).obj T₂).toGrp)
    (hb : Function.Bijective (fun χ : characterLattice ((BC).obj T) =>
      ((BC).map f₁ ≫ χ, (BC).map f₂ ≫ χ))) :
    IsIso (CommGroupScheme.prodFst T₁ T₂ ≫ f₁ + CommGroupScheme.prodSnd T₁ T₂ ≫ f₂) := by
  let μ : P ⟶ T := CommGroupScheme.prodFst T₁ T₂ ≫ f₁ +
    CommGroupScheme.prodSnd T₁ T₂ ≫ f₂
  have hP : IsSplitTorus ((BC).obj P).toGrp :=
    IsSplitTorus.of_iso (baseChangeTensorIso b T₁.toGrp T₂.toGrp)
      (hT₁.tensor hT₂)
  let e := characterLattice.baseChangeProdEquiv b T₁ T₂
  have hcoord (χ : characterLattice ((BC).obj T)) :
      e ((BC).map μ ≫ χ) = ((BC).map f₁ ≫ χ, (BC).map f₂ ≫ χ) := by
    have h₁ : CommGroupScheme.prodInl T₁ T₂ ≫ μ = f₁ := by
      simp [μ, Preadditive.comp_add, ← Category.assoc]
    have h₂ : CommGroupScheme.prodInr T₁ T₂ ≫ μ = f₂ := by
      simp [μ, Preadditive.comp_add, ← Category.assoc]
    change (((BC).map _ ≫ ((BC).map μ ≫ χ)), ((BC).map _ ≫ ((BC).map μ ≫ χ))) = _
    rw [← Category.assoc, ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp, h₁, h₂]
  have hbij : Function.Bijective (fun χ : characterLattice ((BC).obj T) => (BC).map μ ≫ χ) := by
    have he := e.symm.bijective.comp hb
    convert he using 1
    funext χ
    change (BC).map μ ≫ χ = e.symm ((BC).map f₁ ≫ χ, (BC).map f₂ ≫ χ)
    rw [← hcoord χ, AddEquiv.symm_apply_apply]
  let : IsIso ((BC).map μ) :=
    (hP.isIso_iff_bijective_characterPullback hT ((BC).map μ)).mpr hbij
  let : IsIso ((GroupScheme.baseChange b).map (CommGroupScheme.groupHom μ)) := by
    change IsIso (CommGroupScheme.groupHom ((BC).map μ))
    exact ⟨⟨CommGroupScheme.groupHom (inv ((BC).map μ)),
      congrArg CommGroupScheme.groupHom (IsIso.hom_inv_id ((BC).map μ)),
      congrArg CommGroupScheme.groupHom (IsIso.inv_hom_id ((BC).map μ))⟩⟩
  obtain ⟨hs, hf, hq⟩ := fieldExtension_fpqc F E
  let : Surjective b := hs
  let : Flat b := hf
  let : QuasiCompact b := hq
  let : IsIso (CommGroupScheme.groupHom μ) := isIso_of_baseChange b _
  exact CommGroupScheme.isIso_of_groupHom_isIso μ

end TorusProducts

namespace GaloisBorelFaceDerived

variable {F E : Type u} [Field F] [Field E] [Algebra F E]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {p : GaloisPinningData F E G}
  {ν₁ ν₂ : cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap F E)).obj p.torus)}
  {L₁ : GaloisBorelFaceDerived p ν₁} {L₂ : GaloisBorelFaceDerived p ν₂}
  (R₁ : RootModel L₁) (R₂ : RootModel L₂)

local notation "b" => algebraBaseMap F E
local notation "BC" => CommGroupScheme.baseChange b

attribute [local instance] derivedAffine derivedFiniteType

include R₁ R₂

omit [LocallyOfFiniteType G.X.hom] in
private theorem character_restriction_bijective
    (hsc : IsSimplyConnected G)
    (hpart : ∀ a : p.base.support, p.rootDatum.root' a.val ν₂ = 0 ↔
      p.rootDatum.root' a.val ν₁ ≠ 0) :
    Function.Bijective (fun χ : characterLattice ((BC).obj p.torus) =>
      ((BC).map L₁.torusMap ≫ χ, (BC).map L₂.torusMap ≫ χ)) := by
  classical
  let c (a : p.base.support) : Prop := p.rootDatum.root' a.val ν₁ = 0
  let r := R₂.simpleEquiv.trans (Equiv.subtypeEquivRight hpart)
  let e := (Equiv.sumCongr R₁.simpleEquiv r).trans (Equiv.sumCompl c)
  let B := simpleCorootBasis p.base (p.corootSpan_eq_top_of_simplyConnected hsc)
  let B₁ := simpleCorootBasis R₁.face.base
    (R₁.pinning.corootSpan_eq_top_of_simplyConnected L₁.isSimplyConnected)
  let B₂ := simpleCorootBasis R₂.face.base
    (R₂.pinning.corootSpan_eq_top_of_simplyConnected L₂.isSimplyConnected)
  refine character_restriction_bijective_of_bases p.isSplitTorus R₁.isSplit R₂.isSplit
    ((BC).map L₁.torusMap) ((BC).map L₂.torusMap) B B₁ B₂ e ?_ ?_
  · intro a
    change (simpleCorootBasis _ _) a ≫ _ = (simpleCorootBasis _ _) _
    simp only [simpleCorootBasis_apply]
    exact R₁.coroot_comp_torusMap a
  · intro a
    change (simpleCorootBasis _ _) a ≫ _ = (simpleCorootBasis _ _) _
    simp only [simpleCorootBasis_apply]
    exact R₂.coroot_comp_torusMap a

omit [LocallyOfFiniteType G.X.hom] in
/-- Multiplication of the two derived-Levi maximal tori is an isomorphism
onto the original torus when their simple coroots partition the base. -/
theorem isIso_torusProduct
    (hsc : IsSimplyConnected G)
    (hpart : ∀ a : p.base.support, p.rootDatum.root' a.val ν₂ = 0 ↔
      p.rootDatum.root' a.val ν₁ ≠ 0) :
    IsIso (CommGroupScheme.prodFst L₁.torus L₂.torus ≫ L₁.torusMap +
      CommGroupScheme.prodSnd L₁.torus L₂.torus ≫ L₂.torusMap) := by
  exact isIso_torusProduct_of_character_restrictions L₁.torusMap L₂.torusMap
    p.isSplitTorus R₁.isSplit R₂.isSplit (character_restriction_bijective R₁ R₂ hsc hpart)

end GaloisBorelFaceDerived
end Langlands.GroupScheme
