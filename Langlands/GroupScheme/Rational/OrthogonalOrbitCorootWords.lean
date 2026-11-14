import Langlands.Algebra.RankOneRelationProducts
import Langlands.GroupScheme.Rational.NegativeRootPartnerGalois
import Langlands.GroupScheme.Rational.OrthogonalSimpleRootCommutation

/-! # Coroot words over orthogonal sets of simple roots -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.Algebra

namespace Langlands.GroupScheme

namespace SplitPinning

section Split

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] {p : SplitPinning G}

/-- The rank-one relation data of a normalized simple-root map and its negative partner. -/
def rankData (x : p.NormalizedSimpleRootParametrizations) (a : p.base.support) :
    RankOneRelation.Data k (rationalPoints G) :=
  (x a).linked.rankOneData (NormalizedRootParametrization.pairing_root_coroot (a := a))

variable (x : p.NormalizedSimpleRootParametrizations)

theorem rankData_xp (a : p.base.support) (c : k) :
    (rankData x a).xp c = (x a).toRootParametrization.rationalPoint c :=
  (x a).xpPoint_linked c

theorem rankData_xm (a : p.base.support) (c : k) :
    (rankData x a).xm c = (x a).negPoint c := rfl

theorem rankData_h (a : p.base.support) (t : kˣ) :
    (rankData x a).h t =
      LinkedRootParametrization.cocharacterPoint p.inclusion (p.rootDatum.coroot a) t := rfl

/-- The root elements of distinct members of a pairwise orthogonal set of simple roots
commute. -/
theorem rootsCommute_of_orthogonal (O : Set p.base.support)
    (hO : ∀ a ∈ O, ∀ b ∈ O, a ≠ b → p.rootDatum.IsOrthogonal a b) :
    RankOneRelation.RootsCommute (fun a : O => rankData x a) := by
  intro a b hab c d
  have hne : (a : p.base.support) ≠ b := fun h => hab (Subtype.ext h)
  have horth := hO a a.2 b b.2 hne
  have hcomm := orthogonalSimpleRootCommutation k G p a b hne horth
    (Over.mk (𝟙 (Spec (CommRingCat.of k))))
  have hp : ∀ (e : p.base.support) (c : k), (rankData x e).xp c ∈
      (RelativeRoot.subgroup p.inclusion (p.rootDatum.root e)).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of k)))) ⊔
      (RelativeRoot.subgroup p.inclusion (-(p.rootDatum.root e))).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := fun e c => by
    rw [rankData_xp]
    exact Subgroup.mem_sup_left ((x e).toRootParametrization.rationalPoint_mem c)
  have hm : ∀ (e : p.base.support) (c : k), (rankData x e).xm c ∈
      (RelativeRoot.subgroup p.inclusion (p.rootDatum.root e)).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of k)))) ⊔
      (RelativeRoot.subgroup p.inclusion (-(p.rootDatum.root e))).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := fun e c => by
    rw [rankData_xm]
    exact Subgroup.mem_sup_right ((x e).negPoint_mem c)
  exact ⟨hcomm _ _ (hp a c) (hp b d), hcomm _ _ (hp a c) (hm b d),
    hcomm _ _ (hm a c) (hp b d), hcomm _ _ (hm a c) (hm b d)⟩

end Split

section Galois

open GaloisPointComparison

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (i : T.toGrp ⟶ G)

local instance orthogonalOrbitCorootWordsIsAffineHom :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

variable (p : Langlands.GroupScheme.SplitPinning
    ((GroupScheme.baseChange (algebraBaseMap k K)).obj G))
    (eT : p.torus ≅ ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))
    (hT : p.inclusion = CommGroupScheme.groupHom eT.hom ≫
      (GroupScheme.baseChange (algebraBaseMap k K)).map i)
    (x : p.NormalizedSimpleRootParametrizations)
    {ρ : (K ≃ₐ[k] K) →* Equiv.Perm p.base.support}
    (hx : RootMapsGaloisCompatible k K p x ρ)
    (hroot : ∀ (σ : K ≃ₐ[k] K) (a : p.base.support),
      characterLattice.congr eT (p.rootDatum.root (ρ σ a)) =
        characterLattice.galoisRepresentation k K T σ
          (characterLattice.congr eT (p.rootDatum.root a)))
    (O : Set p.base.support) (hOs : ∀ (σ : K ≃ₐ[k] K) a, a ∈ O ↔ ρ σ a ∈ O)
    (hO : ∀ a ∈ O, ∀ b ∈ O, a ≠ b → p.rootDatum.IsOrthogonal a b)

/-- A family of scalars on the simple roots that is equivariant for the Galois action. -/
def IsGaloisEquivariant (ρ : (K ≃ₐ[k] K) →* Equiv.Perm p.base.support)
    (c : p.base.support → K) : Prop :=
  ∀ (σ : K ≃ₐ[k] K) (a : p.base.support), c (ρ σ a) = σ (c a)

variable [Fintype O]

/-- The product over `O` of the positive root elements with coordinates `c`. -/
def orbitXp (c : p.base.support → K) :
    rationalPoints ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) :=
  RankOneRelation.prodHom (rootsCommute_of_orthogonal x O hO)
    (fun a => ⟨(rankData x a).xp (c a), (rankData x a).xp_mem _⟩)

/-- The product over `O` of the negative root elements with coordinates `c`. -/
def orbitXm (c : p.base.support → K) :
    rationalPoints ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) :=
  RankOneRelation.prodHom (rootsCommute_of_orthogonal x O hO)
    (fun a => ⟨(rankData x a).xm (c a), (rankData x a).xm_mem _⟩)

include hx hOs in
/-- Equivariant coordinates give Galois-fixed positive orbit products. -/
theorem orbitXp_rationalConjugate {c : p.base.support → K}
    (hc : IsGaloisEquivariant k K p ρ c) (σ : K ≃ₐ[k] K) :
    rationalConjugate k K G σ (orbitXp k K p x O hO c) = orbitXp k K p x O hO c := by
  apply RankOneRelation.map_prodHom_of_perm _ (rationalConjugate k K G σ).toMonoidHom
    ((ρ σ).subtypePerm (fun a => (hOs σ a).symm))
  intro a
  simp only [MulEquiv.coe_toMonoidHom, rankData_xp, Equiv.Perm.subtypePerm_apply]
  rw [RootMapsGaloisCompatible.rationalPoint k K hx σ a, hc σ a]

include hT hx hroot hOs in
/-- Equivariant coordinates give Galois-fixed negative orbit products. -/
theorem orbitXm_rationalConjugate {c : p.base.support → K}
    (hc : IsGaloisEquivariant k K p ρ c) (σ : K ≃ₐ[k] K) :
    rationalConjugate k K G σ (orbitXm k K p x O hO c) = orbitXm k K p x O hO c := by
  apply RankOneRelation.map_prodHom_of_perm _ (rationalConjugate k K G σ).toMonoidHom
    ((ρ σ).subtypePerm (fun a => (hOs σ a).symm))
  intro a
  simp only [MulEquiv.coe_toMonoidHom, rankData_xm, Equiv.Perm.subtypePerm_apply]
  have h := RootMapsGaloisCompatible.negPointFamily_rationalConjugate k K i p eT hT hx hroot σ a
    (c a)
  simp only [negPointFamily] at h
  rw [h, hc σ a]

/-- The product over `O` of the coroot values at units `u`. -/
def orbitCoroot (u : p.base.support → Kˣ) :
    rationalPoints ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) :=
  RankOneRelation.prodHom (rootsCommute_of_orthogonal x O hO)
    (fun a => ⟨(rankData x a).h (u a), (rankData x a).h_mem _⟩)

/-- The orbit coroot product is a word in four orbit root products. -/
theorem orbitCoroot_eq_word (u : p.base.support → Kˣ) :
    orbitCoroot k K p x O hO u =
      (orbitXm k K p x O hO (fun a => (u a : K)⁻¹ * ((u a : K) - 1)))⁻¹ *
        orbitXp k K p x O hO (fun _ => 1) *
        orbitXm k K p x O hO (fun a => (u a : K) - 1) *
        (orbitXp k K p x O hO (fun a => (u a : K)⁻¹))⁻¹ :=
  RankOneRelation.prodHom_h (rootsCommute_of_orthogonal x O hO) (fun a : O => u a)

/-- Field operations preserve Galois equivariance of coordinate families. -/
theorem IsGaloisEquivariant.word {u : p.base.support → Kˣ}
    (hu : IsGaloisEquivariant k K p ρ (fun a => (u a : K))) :
    IsGaloisEquivariant k K p ρ (fun a => (u a : K)⁻¹ * ((u a : K) - 1)) ∧
      IsGaloisEquivariant k K p ρ (fun _ => (1 : K)) ∧
      IsGaloisEquivariant k K p ρ (fun a => (u a : K) - 1) ∧
      IsGaloisEquivariant k K p ρ (fun a => (u a : K)⁻¹) := by
  refine ⟨fun σ a => ?_, fun σ a => ?_, fun σ a => ?_, fun σ a => ?_⟩
  · simp only [hu σ a, map_mul, map_inv₀, map_sub, map_one]
  · simp only [map_one]
  · simp only [hu σ a, map_sub, map_one]
  · simp only [hu σ a, map_inv₀]

end Galois

end SplitPinning

end Langlands.GroupScheme
