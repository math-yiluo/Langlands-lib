import Langlands.GroupScheme.Rational.RankOneParabolicConjugacy
import Langlands.GroupScheme.Descent.GaloisParabolicOrbitMatching
import Langlands.GroupScheme.Rational.SubgroupConjugacyDescent
import Langlands.GroupScheme.Rational.ParabolicNormalizerAssembly
import Langlands.GroupScheme.Reductive.FieldExtensionProof
import Langlands.GroupScheme.SubgroupBaseChange
import Langlands.GroupScheme.Derived.CentralIntersectionReduction

/-! # Rank-one Galois descent of an inverse-orbit-matched standard parabolic

See the paired Markdown file for statements, provenance and proofs. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace SubgroupFunctor

variable {S : Scheme.{u}} {G H : GroupScheme S}

/-- The range of a composite lies in `Φ` exactly when the range of the first map lies in
the preimage of `Φ` under the second. -/
theorem range_comp_le_iff {K : GroupScheme S} (f : K ⟶ H) (g : H ⟶ G) (Φ : SubgroupFunctor G) :
    range (f ≫ g) ≤ Φ ↔ range f ≤ Φ.comap g := by
  constructor
  · intro h T x hx
    obtain ⟨y, rfl⟩ := mem_range.mp hx
    rw [mem_comap]
    exact h T (mem_range.mpr ⟨y, by rw [Grp.comp_hom_hom, Category.assoc]⟩)
  · intro h T x hx
    obtain ⟨y, rfl⟩ := mem_range.mp hx
    have hy := h T (mem_range.mpr ⟨y, rfl⟩)
    rw [mem_comap] at hy
    rw [Grp.comp_hom_hom, ← Category.assoc]
    exact hy

end SubgroupFunctor

section Descent

variable {F L : Type u} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L]
  [IsGalois F L] {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {TF : CommGroupScheme (Spec (CommRingCat.of F))}
  {T : CommGroupScheme (Spec (CommRingCat.of L))}
  [IsAffineHom ((GroupScheme.baseChange (algebraBaseMap F L)).obj G).X.hom]

omit [FiniteDimensional F L] [IsGalois F L]
  [IsAffineHom ((GroupScheme.baseChange (algebraBaseMap F L)).obj G).X.hom] in
/-- The base change of the minimal standard ground-field parabolic is a parabolic subgroup
of the base-changed group. -/
theorem isParabolicSubgroup_baseChange_standardParabolicHom_empty
    (hG : IsConnectedReductive G) (iF : TF.toGrp ⟶ G) (hiF : IsMaximalSplitTorus iF)
    (νF : cocharacterLattice TF) (hνF : IsGenericCocharacter iF νF) :
    IsParabolicSubgroup ((GroupScheme.baseChange (algebraBaseMap F L)).map
      (Standard.parabolicHom iF νF ∅)) := by
  have hpF : IsParabolicSubgroup (Standard.parabolicHom iF νF ∅) :=
    isParabolicSubgroup_of_range_eq_dynamicParabolic hG _
      (Standard.isClosedSubgroup_parabolicHom iF νF ∅) (CommGroupScheme.groupHom νF ≫ iF)
      ((Standard.isRepresentedBy_parabolicHom iF νF ∅).2.trans
        (standardParabolicEndpoints F G hG TF iF hiF νF hνF).1)
  exact parabolic_baseChange_of_structural_statements parabolicDynamic
    connectedReductiveFieldExtensionStatement hG hpF (algebraBaseMap F L)

omit [FiniteDimensional F L] [IsGalois F L]
  [IsAffineHom ((GroupScheme.baseChange (algebraBaseMap F L)).obj G).X.hom] in
/-- The range of the base-changed minimal standard inclusion is the base change of the
minimal standard parabolic. -/
theorem range_baseChange_standardParabolicHom
    (iF : TF.toGrp ⟶ G) (νF : cocharacterLattice TF) (J : Set (characterLattice TF)) :
    SubgroupFunctor.range ((GroupScheme.baseChange (algebraBaseMap F L)).map
      (Standard.parabolicHom iF νF J)) =
      (standardParabolic iF νF J).baseChange (algebraBaseMap F L) := by
  rw [SubgroupFunctor.range_baseChangeHom, (Standard.isRepresentedBy_parabolicHom iF νF J).2]

/-- **Rank-one descent of a matched parabolic.** Over a finite Galois extension `L/F`, let a
family `J` of simple-root subsets for a split maximal torus of `G_L` satisfy Springer's
inverse-orbit matching after conjugation by `q⁻¹`, with `J 1 = Δ \ {α}`. If `G` has
`F`-rank one, there is a rational point `δ ∈ G(F)` such that the minimal standard parabolic
`P(ν)` of `G_L` is carried into the base change of the minimal standard `F`-parabolic by
the inner automorphism of `δ q⁻¹`. -/
theorem exists_rational_minimalParabolic_le_comap_of_inverse_orbit_matching
    (hG : IsConnectedReductive G) (iF : TF.toGrp ⟶ G) (hiF : IsMaximalSplitTorus iF)
    (νF : cocharacterLattice TF) (hνF : IsGenericCocharacter iF νF)
    (αF : characterLattice TF) (hαF : simpleRelativeRoots iF νF = {αF})
    (hGL : IsConnectedReductive ((GroupScheme.baseChange (algebraBaseMap F L)).obj G))
    (i : T.toGrp ⟶ (GroupScheme.baseChange (algebraBaseMap F L)).obj G)
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
    (J : (L ≃ₐ[F] L) → Set (characterLattice T)) (hJ : ∀ σ, J σ ⊆ simpleRelativeRoots i ν)
    (α : characterLattice T) (hJ1 : J 1 = simpleRelativeRoots i ν \ {α})
    (hα : α ∈ simpleRelativeRoots i ν)
    (q : rationalPoints ((GroupScheme.baseChange (algebraBaseMap F L)).obj G))
    (hmatch : ∀ σ : L ≃ₐ[F] L,
      SubgroupFunctor.range
        (radicalGaloisHom (Standard.parabolicHom i ν (J σ⁻¹) ≫
          (((GroupScheme.baseChange (algebraBaseMap F L)).obj G).innerIso q⁻¹).hom) σ) =
      SubgroupFunctor.range (Standard.parabolicHom i ν (J 1) ≫
        (((GroupScheme.baseChange (algebraBaseMap F L)).obj G).innerIso q⁻¹).hom)) :
    ∃ δ : rationalPoints G,
      Dynamic.parabolic (G := (GroupScheme.baseChange (algebraBaseMap F L)).obj G)
          (CommGroupScheme.groupHom ν ≫ i) ≤
        ((standardParabolic iF νF ∅).baseChange (algebraBaseMap F L)).comap
          (((GroupScheme.baseChange (algebraBaseMap F L)).obj G).innerIso
            (baseChangeBasePoint (algebraBaseMap F L) G δ * q⁻¹)).hom := by
  classical
  let : Fintype (L ≃ₐ[F] L) := Fintype.ofFinite _
  let GE := (GroupScheme.baseChange (algebraBaseMap F L)).obj G
  let e := GE.innerIso q⁻¹
  let p := Standard.finiteParabolicIntersectionHom i ν J
  let P := fun σ : L ≃ₐ[F] L =>
    SubgroupFunctor.range (Standard.parabolicHom i ν (J σ) ≫ e.hom)
  have hp : IsParabolicSubgroup (p ≫ e.hom) :=
    (Standard.isParabolicSubgroup_finiteParabolicIntersectionHom i ν hGL hi hν J).comp_iso e
  have hr : SubgroupFunctor.range (p ≫ e.hom) = SubgroupFunctor.intersection P :=
    Standard.range_finiteParabolicIntersectionHom_comp_iso i ν hGL hi hν J hJ e
  have hm : ∀ σ : L ≃ₐ[F] L,
      SubgroupFunctor.galoisTransport F L G σ (P σ⁻¹) = P 1 := by
    intro σ
    change SubgroupFunctor.descentTransport (algebraBaseMap F L)
      (galoisBaseMap F L σ) (galoisBaseMap_over F L σ) G
        (SubgroupFunctor.range (Standard.parabolicHom i ν (J σ⁻¹) ≫ e.hom)) = _
    rw [SubgroupFunctor.descentTransport_range]
    exact hmatch σ
  have hinv : ∀ σ : L ≃ₐ[F] L,
      SubgroupFunctor.range (radicalGaloisHom (p ≫ e.hom) σ) =
        SubgroupFunctor.range (p ≫ e.hom) := by
    intro σ
    unfold radicalGaloisHom
    rw [← SubgroupFunctor.descentTransport_range]
    change SubgroupFunctor.galoisTransport F L G σ
      (SubgroupFunctor.range (p ≫ e.hom)) = _
    rw [hr]
    exact SubgroupFunctor.galoisTransport_intersection_eq_of_inverse_orbit_matching G P hm σ
  let D := Descent.parabolicGaloisDescent hp hinv
  have hDL : SubgroupFunctor.range ((GroupScheme.baseChange (algebraBaseMap F L)).map
      D.inclusion) = SubgroupFunctor.range (p ≫ e.hom) := by
    rw [D.recovery]
    exact SubgroupFunctor.range_iso_comp _ _
  -- the range of `p` is recovered from the range of `p ≫ e.hom`
  have hpe : SubgroupFunctor.range p =
      (SubgroupFunctor.range (p ≫ e.hom)).comap e.hom := by
    rw [SubgroupFunctor.range_comp_iso, ← SubgroupFunctor.comap_comp, Iso.hom_inv_id,
      SubgroupFunctor.comap_id]
  -- the descended parabolic is proper
  have hne : SubgroupFunctor.range D.inclusion ≠ ⊤ := by
    intro htop
    have h1 : SubgroupFunctor.range p = ⊤ := by
      rw [hpe, ← hDL, SubgroupFunctor.range_baseChangeHom, htop,
        SubgroupFunctor.top_baseChange, SubgroupFunctor.comap_top]
    have h2 : standardParabolic i ν (J 1) = ⊤ := by
      refine le_antisymm (fun _ _ _ => trivial) ?_
      intro U x _
      have hx : x ∈ (SubgroupFunctor.range p).carrier U := by rw [h1]; trivial
      rw [Standard.range_finiteParabolicIntersectionHom i ν hGL hi hν J hJ,
        SubgroupFunctor.mem_intersection] at hx
      exact hx 1
    have hsub : simpleRelativeRoots i ν ⊆ J 1 :=
      ((standardParabolicOrder L GE hGL T i hi ν hν).1 _ _ (Set.Subset.refl _) (hJ 1)).1.mpr
        (by rw [(standardParabolicEndpoints L GE hGL T i hi ν hν).2.2.1, h2])
    have hmem := hsub hα
    rw [hJ1] at hmem
    exact hmem.2 rfl
  obtain ⟨δ, hδ⟩ := exists_range_eq_comap_standardParabolic_empty_of_rankOne hG iF hiF νF
    hνF αF hαF D.inclusion D.parabolic hne
  refine ⟨δ, ?_⟩
  have hL : SubgroupFunctor.range (p ≫ e.hom) =
      ((standardParabolic iF νF ∅).baseChange (algebraBaseMap F L)).comap
        (GE.innerIso (baseChangeBasePoint (algebraBaseMap F L) G δ)).hom := by
    rw [← hDL, SubgroupFunctor.range_baseChangeHom, hδ, SubgroupFunctor.comap_baseChange,
      baseChange_innerIso_hom]
  have hmin : Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) ≤ SubgroupFunctor.range p := by
    rw [← (standardParabolicEndpoints L GE hGL T i hi ν hν).1,
      show SubgroupFunctor.range p =
        standardParabolic i ν (simpleRelativeRoots i ν ∩ Finset.univ.inf J) from
        (Standard.isRepresentedBy_parabolicHom i ν _).2]
    exact ((standardParabolicOrder L GE hGL T i hi ν hν).1 _ _ (Set.empty_subset _)
      Set.inter_subset_left).1.mp (Set.empty_subset _)
  rw [hpe, hL, ← SubgroupFunctor.comap_comp, ← innerIso_mul_hom] at hmin
  exact hmin

/-- **Rank-one coset form.** With a fixed rational point `m₀` carrying `P(ν)` into the base
change of the minimal standard `F`-parabolic, the matched conjugator `q` satisfies
`δ q⁻¹ = π m₀` for a rational point `δ ∈ G(F)` and a rational point `π` of the base change
of the minimal standard `F`-parabolic. -/
theorem exists_rational_mul_eq_of_inverse_orbit_matching
    (hG : IsConnectedReductive G) (iF : TF.toGrp ⟶ G) (hiF : IsMaximalSplitTorus iF)
    (νF : cocharacterLattice TF) (hνF : IsGenericCocharacter iF νF)
    (αF : characterLattice TF) (hαF : simpleRelativeRoots iF νF = {αF})
    (hGL : IsConnectedReductive ((GroupScheme.baseChange (algebraBaseMap F L)).obj G))
    (i : T.toGrp ⟶ (GroupScheme.baseChange (algebraBaseMap F L)).obj G)
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
    (m₀ : rationalPoints ((GroupScheme.baseChange (algebraBaseMap F L)).obj G))
    (hm₀ : Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) ≤
        ((standardParabolic iF νF ∅).baseChange (algebraBaseMap F L)).comap
          (((GroupScheme.baseChange (algebraBaseMap F L)).obj G).innerIso m₀).hom)
    (J : (L ≃ₐ[F] L) → Set (characterLattice T)) (hJ : ∀ σ, J σ ⊆ simpleRelativeRoots i ν)
    (α : characterLattice T) (hJ1 : J 1 = simpleRelativeRoots i ν \ {α})
    (hα : α ∈ simpleRelativeRoots i ν)
    (q : rationalPoints ((GroupScheme.baseChange (algebraBaseMap F L)).obj G))
    (hmatch : ∀ σ : L ≃ₐ[F] L,
      SubgroupFunctor.range
        (radicalGaloisHom (Standard.parabolicHom i ν (J σ⁻¹) ≫
          (((GroupScheme.baseChange (algebraBaseMap F L)).obj G).innerIso q⁻¹).hom) σ) =
      SubgroupFunctor.range (Standard.parabolicHom i ν (J 1) ≫
        (((GroupScheme.baseChange (algebraBaseMap F L)).obj G).innerIso q⁻¹).hom)) :
    ∃ δ : rationalPoints G,
      ∃ π ∈ (SubgroupFunctor.range ((GroupScheme.baseChange (algebraBaseMap F L)).map
          (Standard.parabolicHom iF νF ∅))).rationalPoints,
        baseChangeBasePoint (algebraBaseMap F L) G δ * q⁻¹ = π * m₀ := by
  obtain ⟨δ, hδ⟩ := exists_rational_minimalParabolic_le_comap_of_inverse_orbit_matching hG iF
    hiF νF hνF αF hαF hGL i hi ν hν J hJ α hJ1 hα q hmatch
  have hj := isParabolicSubgroup_baseChange_standardParabolicHom_empty (L := L) hG iF hiF νF hνF
  rw [← range_baseChange_standardParabolicHom] at hδ hm₀
  obtain ⟨π, hπ, h⟩ := exists_mul_eq_of_minimalParabolic_le_comap hGL i hi ν hν _ hj m₀
    (baseChangeBasePoint (algebraBaseMap F L) G δ * q⁻¹) hm₀ hδ
  exact ⟨δ, π, hπ, h⟩

end Descent

end Langlands.GroupScheme
