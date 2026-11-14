import Langlands.GroupScheme.GaloisPointDescent
import Langlands.GroupScheme.GaloisPointRational
import Langlands.Geometry.Building.RootFunctionFieldRestriction
import Langlands.GroupScheme.Rational.OrthogonalOrbitCorootWords
import Langlands.GroupScheme.Rational.RelativeRootGroupAbsoluteGenerationProof
import Langlands.GroupScheme.Rational.RootGeneratedSubgroup

/-! # Descent of orthogonal-orbit coroot words to root-generated rational points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Algebra.RankOneRelation

variable {k H : Type*} [Field k] [Group H] {J : Type*} [Fintype J] {D : J → Data k H}

/-- A product of factors lying in a subgroup lies in that subgroup. -/
theorem prodHom_mem (hD : RootsCommute D) (K : Subgroup H) (f : ∀ i, (D i).rootSubgroup)
    (hf : ∀ i, (f i : H) ∈ K) : prodHom hD f ∈ K := by
  rw [prodHom, Subgroup.noncommPiCoprod_apply]
  exact Subgroup.noncommProd_mem _ _ fun i _ => hf i

end Langlands.Algebra.RankOneRelation

namespace Langlands.GroupScheme

namespace GaloisPointComparison

variable (k K : Type u) [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- A rational point of the base change fixed by every coefficient automorphism is the
extension of a rational point. -/
theorem exists_rationalExtend_eq_of_fixed {g : rationalPoints (baseChanged k K G)}
    (hg : ∀ σ : K ≃ₐ[k] K, rationalConjugate k K G σ g = g) :
    ∃ g₀ : rationalPoints G, rationalExtend k K G g₀ = g := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hx : baseChangeCoeffEquiv k K G g ∈ GaloisPoint.fixedSubgroup k K G := fun σ => by
    rw [← baseChangeCoeffEquiv_rationalConjugate, hg σ]
  obtain ⟨y, hy⟩ := (GaloisPoint.mem_range_extend_iff k K G _).mpr hx
  refine ⟨(rationalCoeffEquiv k G).symm y, ?_⟩
  apply (baseChangeCoeffEquiv k K G).injective
  rw [baseChangeCoeffEquiv_rationalExtend, MulEquiv.apply_symm_apply, hy]

/-- A Galois-fixed rational point of the base change lying in the base change of a relative
root group is the extension of a rational point of that root group. -/
theorem exists_mem_rootGroupPoints_of_fixed [Smooth G.X.hom]
    {S : CommGroupScheme (Spec (CommRingCat.of k))} (i : S.toGrp ⟶ G)
    (hS : IsSplitTorus S.toGrp) (a : characterLattice S) (ha : a ≠ 0)
    {g : rationalPoints (baseChanged k K G)}
    (hg : ∀ σ : K ≃ₐ[k] K, rationalConjugate k K G σ g = g)
    (hmem : g ∈ Langlands.Geometry.Building.rootGroupPoints
      (S := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj S)
      ((GroupScheme.baseChange (algebraBaseMap k K)).map i)
      (characterLattice.baseChange (algebraBaseMap k K) S a)) :
    ∃ g₀ ∈ Langlands.Geometry.Building.rootGroupPoints i a, rationalExtend k K G g₀ = g := by
  obtain ⟨g₀, rfl⟩ := exists_rationalExtend_eq_of_fixed k K hg
  exact ⟨g₀, (Langlands.Geometry.Building.rationalExtend_mem_rootGroupPoints_iff i hS a ha
    g₀).mp hmem, rfl⟩

end GaloisPointComparison

/-- The image of the root-generated subgroup `G(k)^+` in the rational points of the base
change `G_K`, under extension of rational points. -/
def relativeRootGeneratedExtension (k K : Type u) [Field k] [Field K] [Algebra k K]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {S : CommGroupScheme (Spec (CommRingCat.of k))} (i : S.toGrp ⟶ G) :
    Subgroup (rationalPoints (GaloisPointComparison.baseChanged k K G)) :=
  (relativeRootGeneratedSubgroup i).map (GaloisPointComparison.rationalExtend k K G)

namespace SplitPinning

open GaloisPointComparison

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {S : CommGroupScheme (Spec (CommRingCat.of k))} (i : S.toGrp ⟶ G)

local instance orthogonalOrbitDescentIsAffineHom :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

variable (p : Langlands.GroupScheme.SplitPinning
    ((GroupScheme.baseChange (algebraBaseMap k K)).obj G))
    (x : p.NormalizedSimpleRootParametrizations)
    (O : Set p.base.support) (hO : ∀ a ∈ O, ∀ b ∈ O, a ≠ b → p.rootDatum.IsOrthogonal a b)
    [Fintype O]
    (g : (CommGroupScheme.baseChange (algebraBaseMap k K)).obj S ⟶ p.torus)
    (hg : CommGroupScheme.groupHom g ≫ p.inclusion =
      (GroupScheme.baseChange (algebraBaseMap k K)).map i)
    (a : characterLattice S)
    (hres : ∀ b ∈ O, g ≫ p.rootDatum.root b =
      characterLattice.baseChange (algebraBaseMap k K) S a)

include hg hres in
/-- Positive orbit products lie in the base change of the relative root group of `a`. -/
theorem orbitXp_mem_rootGroupPoints (c : p.base.support → K) :
    orbitXp k K p x O hO c ∈ Langlands.Geometry.Building.rootGroupPoints
      (S := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj S)
      ((GroupScheme.baseChange (algebraBaseMap k K)).map i)
      (characterLattice.baseChange (algebraBaseMap k K) S a) := by
  apply Langlands.Algebra.RankOneRelation.prodHom_mem
  intro b
  have h := RelativeRoot.subgroup_le_subgroup_comp_torusHom g p.inclusion
    (p.rootDatum.root b) _ ((x b).toRootParametrization.rationalPoint_mem (c b))
  rw [hg, hres b b.2] at h
  change (rankData x b).xp (c b) ∈ _
  rw [rankData_xp]
  exact h

include hg hres in
/-- Negative orbit products lie in the base change of the relative root group of `-a`. -/
theorem orbitXm_mem_rootGroupPoints (c : p.base.support → K) :
    orbitXm k K p x O hO c ∈ Langlands.Geometry.Building.rootGroupPoints
      (S := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj S)
      ((GroupScheme.baseChange (algebraBaseMap k K)).map i)
      (characterLattice.baseChange (algebraBaseMap k K) S (-a)) := by
  apply Langlands.Algebra.RankOneRelation.prodHom_mem
  intro b
  have h := RelativeRoot.subgroup_le_subgroup_comp_torusHom g p.inclusion
    (-p.rootDatum.root b) _ ((x b).negPoint_mem (c b))
  rw [hg, Preadditive.comp_neg, hres b b.2, ← map_neg] at h
  change (rankData x b).xm (c b) ∈ _
  rw [rankData_xm]
  exact h

variable [FiniteDimensional k K] [IsGalois k K] [Smooth G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of k))} (iT : T.toGrp ⟶ G)
    (eT : p.torus ≅ ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))
    (hT : p.inclusion = CommGroupScheme.groupHom eT.hom ≫
      (GroupScheme.baseChange (algebraBaseMap k K)).map iT)
    {ρ : (K ≃ₐ[k] K) →* Equiv.Perm p.base.support}
    (hx : RootMapsGaloisCompatible k K p x ρ)
    (hroot : ∀ (σ : K ≃ₐ[k] K) (b : p.base.support),
      characterLattice.congr eT (p.rootDatum.root (ρ σ b)) =
        characterLattice.galoisRepresentation k K T σ
          (characterLattice.congr eT (p.rootDatum.root b)))
    (hOs : ∀ (σ : K ≃ₐ[k] K) b, b ∈ O ↔ ρ σ b ∈ O)
    (hS : IsSplitTorus S.toGrp) (ha0 : a ≠ 0)

include hx hOs hg hres hS ha0 in
/-- Equivariant positive orbit products are extensions of rational points of `U_a`. -/
theorem exists_orbitXp_eq_rationalExtend {c : p.base.support → K}
    (hc : IsGaloisEquivariant k K p ρ c) :
    ∃ g₀ ∈ Langlands.Geometry.Building.rootGroupPoints i a,
      rationalExtend k K G g₀ = orbitXp k K p x O hO c :=
  exists_mem_rootGroupPoints_of_fixed k K i hS a ha0
    (fun σ => orbitXp_rationalConjugate k K p x hx O hOs hO hc σ)
    (orbitXp_mem_rootGroupPoints k K i p x O hO g hg a hres c)

include hT hx hroot hOs hg hres hS ha0 in
/-- Equivariant negative orbit products are extensions of rational points of `U_{-a}`. -/
theorem exists_orbitXm_eq_rationalExtend {c : p.base.support → K}
    (hc : IsGaloisEquivariant k K p ρ c) :
    ∃ g₀ ∈ Langlands.Geometry.Building.rootGroupPoints i (-a),
      rationalExtend k K G g₀ = orbitXm k K p x O hO c :=
  exists_mem_rootGroupPoints_of_fixed k K i hS (-a) (neg_ne_zero.mpr ha0)
    (fun σ => orbitXm_rationalConjugate k K iT p eT hT x hx hroot O hOs hO hc σ)
    (orbitXm_mem_rootGroupPoints k K i p x O hO g hg a hres c)

include hT hx hroot hOs hg hres hS ha0 in
/-- **Orthogonal orbits.** For a Galois-stable pairwise orthogonal set `O` of simple roots
restricting to the relative roots `±a`, the product of the coroot values at an equivariant unit
family is the extension of a rational point of the root-generated subgroup. -/
theorem orbitCoroot_mem_map_relativeRootGeneratedSubgroup
    (ha : a ∈ relativeRoots i) (ha' : -a ∈ relativeRoots i)
    {u : p.base.support → Kˣ} (hu : IsGaloisEquivariant k K p ρ (fun b => (u b : K))) :
    orbitCoroot k K p x O hO u ∈ relativeRootGeneratedExtension k K i := by
  obtain ⟨h1, h2, h3, h4⟩ := IsGaloisEquivariant.word k K p hu
  have hp : ∀ {c : p.base.support → K}, IsGaloisEquivariant k K p ρ c →
      orbitXp k K p x O hO c ∈ (relativeRootGeneratedSubgroup i).map (rationalExtend k K G) := by
    intro c hc
    obtain ⟨g₀, hg₀, h⟩ := exists_orbitXp_eq_rationalExtend k K i p x O hO g hg a hres hx hOs
      hS ha0 hc
    exact ⟨g₀, relativeRoot_subgroup_le_generated i ha hg₀, h⟩
  have hm : ∀ {c : p.base.support → K}, IsGaloisEquivariant k K p ρ c →
      orbitXm k K p x O hO c ∈ (relativeRootGeneratedSubgroup i).map (rationalExtend k K G) := by
    intro c hc
    obtain ⟨g₀, hg₀, h⟩ := exists_orbitXm_eq_rationalExtend k K i p x O hO g hg a hres iT eT hT
      hx hroot hOs hS ha0 hc
    exact ⟨g₀, relativeRoot_subgroup_le_generated i ha' hg₀, h⟩
  rw [orbitCoroot_eq_word]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hm h1))
    (hp h2)) (hm h3)) (Subgroup.inv_mem _ (hp h4))

end SplitPinning

end Langlands.GroupScheme
