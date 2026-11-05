import Langlands.Geometry.Building.ChamberOrderedInjective
import Langlands.Geometry.Building.ChamberIwahoriStatement
import Langlands.Geometry.Building.ChamberProductInjective
import Langlands.Geometry.Building.AffineChamberSeparation
import Langlands.Geometry.Building.ApartmentRootReflections
import Langlands.Geometry.Building.IwahoriWeyl
import Langlands.GroupScheme.Rational.GenericCocharacter
import Mathlib.Data.Set.Finite.Lemmas

/-! # Intersections over the affine Weyl orbit of a chamber

The saturation argument uses only ordered-root injectivity on rational points
for the supplied torus embedding. Compatibility wrappers retain the original
global Dynamic product interface.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme

namespace Langlands.GroupScheme.RelativeRoot

/-- Ordered multiplication of the actual positive root groups is injective on
rational points, for every cocharacter and injective root enumeration of this
one torus embedding. -/
def OrderedRootPointInjectivity
    {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (i : S.toGrp ⟶ G) : Prop :=
  ∀ (ν : cocharacterLattice S) (n : ℕ) (a : Fin n → characterLattice S),
    Function.Injective a → Set.range a = indivisiblePositiveRoots i ν →
      Function.Injective (fun x : ∀ r, (subgroup i (a r)).carrier (Over.mk (𝟙 _)) =>
        (List.ofFn fun r => (x r : rationalPoints G)).prod)

/-- The published global Dynamic statement supplies the local rational-point
injectivity used in chamber saturation. -/
theorem orderedRootPointInjectivity_of_dynamicRootOrderedProduct
    (hprod : DynamicRootOrderedProductStatement.{u})
    {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (hG : IsConnectedReductive G) {i : S.toGrp ⟶ G}
    (hi : IsMaximalSplitTorus i) : OrderedRootPointInjectivity i := by
  intro ν n a ha hrange
  exact orderedRootSubgroupPoints_injective_of_statement
    hprod hG hi ν a ha hrange (Over.mk (𝟙 _))

end Langlands.GroupScheme.RelativeRoot

namespace Langlands.Geometry.Building

namespace KPApartmentData

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
    {ω : kˣ → ℝ} (D : KPApartmentData i ω)

/-- A root element of nonnegative depth on an entire affine Weyl orbit of a
chamber point is trivial: its own affine-root reflection reverses its depth. -/
theorem eq_one_of_forall_mem_filtration_affineWeylOrbit
    (hsys : AffineRootSystem.IsAffineRootSystemWithRankZero D.affineRoots)
    (hAS4 : ∀ ψ ∈ D.extendedAffineRoots,
      ψ ∈ D.affineRoots ∨ (2 : ℝ) • ψ ∈ D.affineRoots)
    {C : Set D.Apartment} (hC : AffineRootSystem.IsChamber D.affineRoots C)
    {x : D.Apartment} (hx : x ∈ C)
    {a : characterLattice S} (ha : a ∈ relativeRoots i)
    {g : rationalPoints G}
    (hg : ∀ w : AffineRootSystem.affineWeylGroup D.affineRoots,
      g ∈ D.filtration ((w : D.Apartment ≃ᵃ[ℝ] D.Apartment) x) a 0) : g = 1 := by
  by_contra hne
  have hgx : g ∈ D.filtration x a 0 := by simpa using hg 1
  obtain ⟨ψ, hψ, -, hval⟩ := D.exists_extendedAffineRoot_of_ne_one x ha hgx.1 hne
  have hx0 : (0 : ℝ) ≤ ψ x := by
    simpa only [hval x, ← WithTop.coe_zero, WithTop.coe_le_coe] using hgx.2
  have hxpos : 0 < ψ x := lt_of_le_of_ne hx0
    (D.extendedAffineRoot_ne_zero_of_mem_chamber hAS4 hC hx hψ).symm
  obtain ⟨psi1, hpsi1, c, hc, heq⟩ :
      ∃ psi1 ∈ D.affineRoots, ∃ c : ℝ, 0 < c ∧ psi1 = c • ψ := by
    rcases hAS4 ψ hψ with h | h
    · exact ⟨ψ, h, 1, by norm_num, (one_smul ℝ ψ).symm⟩
    · exact ⟨(2 : ℝ) • ψ, h, 2, by norm_num, rfl⟩
  obtain ⟨v, hv⟩ := hsys.exists_isCoroot psi1 hpsi1
  let w : AffineRootSystem.affineWeylGroup D.affineRoots :=
    ⟨AffineRootSystem.affineReflection psi1 hv.1,
      AffineRootSystem.affineReflection_mem_affineWeylGroup hpsi1 hv⟩
  have hwy : (0 : ℝ) ≤ ψ ((w : D.Apartment ≃ᵃ[ℝ] D.Apartment) x) := by
    simpa only [hval _, ← WithTop.coe_zero, WithTop.coe_le_coe] using (hg w).2
  have heta (y : D.Apartment) : psi1 y = c * ψ y := by rw [heq]; rfl
  have hflip : c * ψ ((w : D.Apartment ≃ᵃ[ℝ] D.Apartment) x) = -(c * ψ x) := by
    simpa only [heta] using AffineRootSystem.apply_affineReflection psi1 hv.1 x
  nlinarith

/-- Ordered-root uniqueness identifies coordinates across chamber points.
The affine Weyl orbit then forces every coordinate to be the identity. -/
theorem eq_one_of_forall_mem_range_orderedChamberBlockProduct_of_orderedRootInjectivity
    (hinj : RelativeRoot.OrderedRootPointInjectivity i)
    (hsys : AffineRootSystem.IsAffineRootSystemWithRankZero D.affineRoots)
    (hAS4 : ∀ ψ ∈ D.extendedAffineRoots,
      ψ ∈ D.affineRoots ∨ (2 : ℝ) • ψ ∈ D.affineRoots)
    {C : Set D.Apartment} (hC : AffineRootSystem.IsChamber D.affineRoots C)
    {x : D.Apartment} (hx : x ∈ C)
    (ν : cocharacterLattice S) {n : ℕ} (a : Fin n → characterLattice S)
    (ha : Function.Injective a)
    (hrange : Set.range a = RelativeRoot.indivisiblePositiveRoots i ν)
    {g : rationalPoints G}
    (hg : ∀ w : AffineRootSystem.affineWeylGroup D.affineRoots,
      g ∈ Set.range (D.orderedChamberBlockProduct
        ((w : D.Apartment ≃ᵃ[ℝ] D.Apartment) x) false a)) : g = 1 := by
  have hroot (r : Fin n) : a r ∈ relativeRoots i :=
    (show a r ∈ RelativeRoot.indivisiblePositiveRoots i ν from
      hrange ▸ Set.mem_range_self r).1.1
  have hgx : g ∈ Set.range (D.orderedChamberBlockProduct x false a) := by
    simpa using hg 1
  obtain ⟨t, ht⟩ := hgx
  let t' : ∀ r, rootGroupPoints i (a r) := fun r =>
    ⟨t r, D.chamberRootBlock_subset_rootGroupPoints x false (hroot r) (t r).property⟩
  have hmem (r : Fin n) (w : AffineRootSystem.affineWeylGroup D.affineRoots) :
      (t r : rationalPoints G) ∈
        D.filtration ((w : D.Apartment ≃ᵃ[ℝ] D.Apartment) x) (a r) 0 := by
    obtain ⟨s, hs⟩ := hg w
    let s' : ∀ r, rootGroupPoints i (a r) := fun r =>
      ⟨s r, D.chamberRootBlock_subset_rootGroupPoints _ false (hroot r) (s r).property⟩
    have hcoords : t' = s' :=
      hinj ν n a ha hrange (ht.trans hs.symm)
    have heq : (t r : rationalPoints G) = (s r : rationalPoints G) :=
      congrArg (fun z => (z r : rationalPoints G)) hcoords
    rw [heq]
    exact (D.chamberRootBlock_eq_rootGroup _ false (hroot r)).subset (s r).property
  have htone (r : Fin n) : (t r : rationalPoints G) = 1 :=
    D.eq_one_of_forall_mem_filtration_affineWeylOrbit hsys hAS4 hC hx (hroot r) (hmem r)
  rw [← ht]
  simp [orderedChamberBlockProduct, htone]

/-- Compatibility form with the published global Dynamic product premise. -/
theorem eq_one_of_forall_mem_range_orderedChamberBlockProduct
    (hprod : RelativeRoot.DynamicRootOrderedProductStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hsys : AffineRootSystem.IsAffineRootSystemWithRankZero D.affineRoots)
    (hAS4 : ∀ ψ ∈ D.extendedAffineRoots,
      ψ ∈ D.affineRoots ∨ (2 : ℝ) • ψ ∈ D.affineRoots)
    {C : Set D.Apartment} (hC : AffineRootSystem.IsChamber D.affineRoots C)
    {x : D.Apartment} (hx : x ∈ C)
    (ν : cocharacterLattice S) {n : ℕ} (a : Fin n → characterLattice S)
    (ha : Function.Injective a)
    (hrange : Set.range a = RelativeRoot.indivisiblePositiveRoots i ν)
    {g : rationalPoints G}
    (hg : ∀ w : AffineRootSystem.affineWeylGroup D.affineRoots,
      g ∈ Set.range (D.orderedChamberBlockProduct
        ((w : D.Apartment ≃ᵃ[ℝ] D.Apartment) x) false a)) : g = 1 :=
  D.eq_one_of_forall_mem_range_orderedChamberBlockProduct_of_orderedRootInjectivity
    (RelativeRoot.orderedRootPointInjectivity_of_dynamicRootOrderedProduct hprod hG hi)
    hsys hAS4 hC hx ν a ha hrange hg

end KPApartmentData

namespace ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G)

private theorem iwahoriUnipotentFactors_eq {C E : Set P.Apartment}
    (ν : cocharacterLattice P.S)
    (p : P.iwahoriUnipotentPoints (-ν) C × P.centralizerZero ×
      P.iwahoriUnipotentPoints ν C)
    (q : P.iwahoriUnipotentPoints (-ν) E × P.centralizerZero ×
      P.iwahoriUnipotentPoints ν E)
    (hpq : P.iwahoriUnipotentProduct C ν p = P.iwahoriUnipotentProduct E ν q) :
    (p.1 : rationalPoints G) = q.1 ∧
      (p.2.2 : rationalPoints G) = q.2.2 := by
  let Uminus := (Dynamic.unipotent (CommGroupScheme.groupHom (-ν) ≫ P.i)).carrier
    (Over.mk (𝟙 _))
  let Uplus := (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ P.i)).carrier
    (Over.mk (𝟙 _))
  let lift (C : Set P.Apartment)
      (p : P.iwahoriUnipotentPoints (-ν) C × P.centralizerZero ×
        P.iwahoriUnipotentPoints ν C) : Uminus × centralizerPoints P.i × Uplus :=
    (⟨p.1, p.1.property.1⟩,
      ⟨rationalPoints.map P.centralizer.j (p.2.1 : rationalPoints P.centralizer.Z),
        map_mem_centralizerPoints P.centralizer.isRepresentedBy _⟩,
      ⟨p.2.2, p.2.2.property.1⟩)
  have h : lift C p = lift E q :=
    unipotentTripleProduct_injective P.i ν Uminus Uplus
      (fun z : centralizerPoints P.i => (z : rationalPoints G))
      Subtype.val_injective le_rfl le_rfl (fun z => z.property) hpq
  exact ⟨congrArg (fun r => (r.1 : rationalPoints G)) h,
    congrArg (fun r => (r.2.2 : rationalPoints G)) h⟩

/-- Full chamber decompositions have the same ambient factors at all orbit
chambers. Ordered-root uniqueness and reflection remove both unipotent factors. -/
theorem mem_centralizerZero_of_forall_mem_parahoric_affineWeylOrbit_of_orderedRootInjectivity
    (hP : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    (hinj : RelativeRoot.OrderedRootPointInjectivity P.i)
    (hdec : P.ChamberIwahoriDecompositionStatement)
    {C : Set P.Apartment} (hC : AffineRootSystem.IsChamber P.affineRoots C)
    {g : rationalPoints G}
    (hg : ∀ w : AffineRootSystem.affineWeylGroup P.affineRoots,
      g ∈ P.parahoric ((w : P.Apartment ≃ᵃ[ℝ] P.Apartment) '' C)) :
    g ∈ P.centralizerZero.map (rationalPoints.map P.centralizer.j) := by
  classical
  have : Smooth G.X.hom := P.isConnectedReductive.smooth
  obtain ⟨ν, hν⟩ :=
    P.isMaximalSplitTorus.isSplitSubtorus.1.exists_genericCocharacter P.i
  obtain ⟨x, hxreg, hxC⟩ := hC
  have hC : AffineRootSystem.IsChamber P.affineRoots C := ⟨x, hxreg, hxC⟩
  have hx : x ∈ C := hxC ▸ (AffineRootSystem.facetRel_equivalence P.affineRoots).refl x
  have hIw (w : AffineRootSystem.affineWeylGroup P.affineRoots) :
      P.ChamberIwahoriConclusion ((w : P.Apartment ≃ᵃ[ℝ] P.Apartment) '' C)
        ((w : P.Apartment ≃ᵃ[ℝ] P.Apartment) x) ν :=
    (hdec hP _ _ ν (hC.image_affineWeylGroup w) (Set.mem_image_of_mem _ hx) hν).2.1
  have hbase : P.ChamberIwahoriConclusion C x ν := (hdec hP C x ν hC hx hν).2.1
  obtain ⟨p, hp⟩ := (show g ∈ Set.range (P.iwahoriUnipotentProduct C ν) by
    rw [hbase.2.2.2.2.2.1]
    simpa using hg 1)
  have hU (w : AffineRootSystem.affineWeylGroup P.affineRoots) :
      (p.1 : rationalPoints G) ∈
        P.iwahoriUnipotentPoints (-ν) ((w : P.Apartment ≃ᵃ[ℝ] P.Apartment) '' C) ∧
      (p.2.2 : rationalPoints G) ∈
        P.iwahoriUnipotentPoints ν ((w : P.Apartment ≃ᵃ[ℝ] P.Apartment) '' C) := by
    obtain ⟨q, hq⟩ := (show g ∈ Set.range (P.iwahoriUnipotentProduct
        ((w : P.Apartment ≃ᵃ[ℝ] P.Apartment) '' C) ν) by
      rw [(hIw w).2.2.2.2.2.1]
      exact hg w)
    have heq := P.iwahoriUnipotentFactors_eq ν p q (hp.trans hq.symm)
    exact ⟨heq.1 ▸ q.1.property, heq.2 ▸ q.2.2.property⟩
  have hfinite (nu1 : cocharacterLattice P.S) :
      (RelativeRoot.indivisiblePositiveRoots P.i nu1).Finite :=
    (P.isMaximalSplitTorus.1.1.finite_relativeRoots P.i).subset (fun _ ha => ha.1.1)
  obtain ⟨nneg, aneg, haneg, hrneg⟩ := (hfinite (-ν)).fin_param
  obtain ⟨npos, apos, hapos, hrpos⟩ := (hfinite ν).fin_param
  have hblocks (w : AffineRootSystem.affineWeylGroup P.affineRoots) :=
    (hIw w).2.2.2.2.2.2 false nneg npos aneg apos haneg hrneg hapos hrpos
  have hminus : (p.1 : rationalPoints G) = 1 :=
    P.apartment.eq_one_of_forall_mem_range_orderedChamberBlockProduct_of_orderedRootInjectivity
      hinj
      hP.isAffineRootSystem_affineRoots hP.mem_or_two_smul_mem hC hx
      (-ν) aneg haneg hrneg (fun w => by
        rw [(hblocks w).2.1]
        exact (hU w).1)
  have hplus : (p.2.2 : rationalPoints G) = 1 :=
    P.apartment.eq_one_of_forall_mem_range_orderedChamberBlockProduct_of_orderedRootInjectivity
      hinj
      hP.isAffineRootSystem_affineRoots hP.mem_or_two_smul_mem hC hx
      ν apos hapos hrpos (fun w => by
        rw [(hblocks w).2.2.2.1]
        exact (hU w).2)
  refine ⟨(p.2.1 : rationalPoints P.centralizer.Z), p.2.1.property, ?_⟩
  simpa only [iwahoriUnipotentProduct, hminus, hplus, one_mul, mul_one] using hp

/-- The affine Weyl orbit of one chamber has full-parahoric intersection
exactly the actual centralizer-zero image, under the retained product inputs. -/
theorem iInf_parahoric_affineWeylOrbit_eq_centralizerZeroImage_of_orderedRootInjectivity
    (hP : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    (hinj : RelativeRoot.OrderedRootPointInjectivity P.i)
    (hdec : P.ChamberIwahoriDecompositionStatement)
    {C : Set P.Apartment} (hC : AffineRootSystem.IsChamber P.affineRoots C) :
    (⨅ w : AffineRootSystem.affineWeylGroup P.affineRoots,
      P.parahoric ((w : P.Apartment ≃ᵃ[ℝ] P.Apartment) '' C)) =
        P.centralizerZero.map (rationalPoints.map P.centralizer.j) := by
  apply le_antisymm
  · intro g hg
    exact P.mem_centralizerZero_of_forall_mem_parahoric_affineWeylOrbit_of_orderedRootInjectivity
      hP hinj hdec hC (Subgroup.mem_iInf.1 hg)
  · exact le_iInf fun w => P.map_centralizerZero_le_parahoric _

/-- Rank-one factorization lifts every affine Weyl transformation to the actual
zero-component normalizer, with equality of the original apartment actions. -/
theorem exists_normalizerZeroComponent_lift_affineWeyl_of_rankOneFactorization
    (hP : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    (hrank : RelativeRoot.HasRankOneFactorization P.i)
    (w : AffineRootSystem.affineWeylGroup P.affineRoots) :
    ∃ n : P.normalizerZeroComponent,
      P.apartment.normalizerAffineEquiv (n : normalizerPoints P.i) =
        (w : P.Apartment ≃ᵃ[ℝ] P.Apartment) := by
  obtain ⟨n, hn, hnw⟩ :=
    P.affineWeylGroup_le_simplyConnectedNormalizer_map_of_apartment hP hrank w.property
  exact ⟨⟨n, P.zeroDatum.simplyConnectedImage_le_zeroSubgroup hn⟩, hnw⟩

/-- The parahorics of the actual restricted-normalizer translates of a chamber
intersect in exactly the actual centralizer-zero image. -/
theorem iInf_parahoric_normalizerZeroComponent_eq_centralizerZeroImage_of_orderedRootInjectivity
    (hP : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    (hrank : RelativeRoot.HasRankOneFactorization P.i)
    (hinj : RelativeRoot.OrderedRootPointInjectivity P.i)
    (hdec : P.ChamberIwahoriDecompositionStatement)
    {C : Set P.Apartment} (hC : AffineRootSystem.IsChamber P.affineRoots C) :
    (⨅ n : P.normalizerZeroComponent,
      P.parahoric ((n : normalizerPoints P.i) • C)) =
        P.centralizerZero.map (rationalPoints.map P.centralizer.j) := by
  apply le_antisymm
  · intro g hg
    apply P.mem_centralizerZero_of_forall_mem_parahoric_affineWeylOrbit_of_orderedRootInjectivity
      hP hinj hdec hC
    intro w
    obtain ⟨n, hnw⟩ :=
      P.exists_normalizerZeroComponent_lift_affineWeyl_of_rankOneFactorization hP hrank w
    have hn := Subgroup.mem_iInf.1 hg n
    change g ∈ P.parahoric (P.apartment.normalizerAffineEquiv
      (n : normalizerPoints P.i) '' C) at hn
    simpa only [hnw] using hn
  · exact le_iInf fun n => P.map_centralizerZero_le_parahoric _

/-- The conditional saturation implication uses actual normalizer points and
the original zero-subgroup premise, as in the published saturation input. -/
theorem mem_centralizerZero_of_forall_mem_parahoric_normalizerZeroComponent_of_orderedRootInjectivity
    (hP : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    (hrank : RelativeRoot.HasRankOneFactorization P.i)
    (hinj : RelativeRoot.OrderedRootPointInjectivity P.i)
    (hdec : P.ChamberIwahoriDecompositionStatement)
    {C : Set P.Apartment} (hC : AffineRootSystem.IsChamber P.affineRoots C)
    {g : rationalPoints G}
    (hg : ∀ n : normalizerPoints P.i, (n : rationalPoints G) ∈ P.zeroSubgroup →
      g ∈ P.parahoric (n • C)) :
    g ∈ P.centralizerZero.map (rationalPoints.map P.centralizer.j) := by
  rw [← P.iInf_parahoric_normalizerZeroComponent_eq_centralizerZeroImage_of_orderedRootInjectivity
    hP hrank hinj hdec hC]
  exact Subgroup.mem_iInf.2 fun n => hg n n.property

/-- The identity on ambient rational points identifies the intersection of
actual chamber translates with the actual centralizer-zero image. -/
def chamberConjugateParahoricEquivCentralizerZeroImage_of_orderedRootInjectivity
    (hP : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    (hrank : RelativeRoot.HasRankOneFactorization P.i)
    (hinj : RelativeRoot.OrderedRootPointInjectivity P.i)
    (hdec : P.ChamberIwahoriDecompositionStatement)
    {C : Set P.Apartment} (hC : AffineRootSystem.IsChamber P.affineRoots C) :
    ↥(⨅ n : P.normalizerZeroComponent,
      P.parahoric ((n : normalizerPoints P.i) • C)) ≃*
        P.centralizerZero.map (rationalPoints.map P.centralizer.j) :=
  MulEquiv.subgroupCongr
    (P.iInf_parahoric_normalizerZeroComponent_eq_centralizerZeroImage_of_orderedRootInjectivity
      hP hrank hinj hdec hC)

/-- The chamber-intersection equivalence preserves the ambient rational point. -/
@[simp] theorem chamberConjugateParahoricEquivCentralizerZeroImage_of_orderedRootInjectivity_apply_coe
    (hP : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    (hrank : RelativeRoot.HasRankOneFactorization P.i)
    (hinj : RelativeRoot.OrderedRootPointInjectivity P.i)
    (hdec : P.ChamberIwahoriDecompositionStatement)
    {C : Set P.Apartment} (hC : AffineRootSystem.IsChamber P.affineRoots C)
    (g : ↥(⨅ n : P.normalizerZeroComponent,
      P.parahoric ((n : normalizerPoints P.i) • C))) :
    ((P.chamberConjugateParahoricEquivCentralizerZeroImage_of_orderedRootInjectivity
      hP hrank hinj hdec hC g :
      P.centralizerZero.map (rationalPoints.map P.centralizer.j)) : rationalPoints G) = g :=
  rfl

/-- Compatibility form with the published global Dynamic product premise. -/
theorem mem_centralizerZero_of_forall_mem_parahoric_affineWeylOrbit
    (hP : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    (hprod : RelativeRoot.DynamicRootOrderedProductStatement.{u})
    (hdec : P.ChamberIwahoriDecompositionStatement)
    {C : Set P.Apartment} (hC : AffineRootSystem.IsChamber P.affineRoots C)
    {g : rationalPoints G}
    (hg : ∀ w : AffineRootSystem.affineWeylGroup P.affineRoots,
      g ∈ P.parahoric ((w : P.Apartment ≃ᵃ[ℝ] P.Apartment) '' C)) :
    g ∈ P.centralizerZero.map (rationalPoints.map P.centralizer.j) :=
  P.mem_centralizerZero_of_forall_mem_parahoric_affineWeylOrbit_of_orderedRootInjectivity hP
    (RelativeRoot.orderedRootPointInjectivity_of_dynamicRootOrderedProduct
      hprod P.isConnectedReductive P.isMaximalSplitTorus) hdec hC hg

/-- Compatibility form with the published global Dynamic product premise. -/
theorem iInf_parahoric_affineWeylOrbit_eq_centralizerZeroImage
    (hP : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    (hprod : RelativeRoot.DynamicRootOrderedProductStatement.{u})
    (hdec : P.ChamberIwahoriDecompositionStatement)
    {C : Set P.Apartment} (hC : AffineRootSystem.IsChamber P.affineRoots C) :
    (⨅ w : AffineRootSystem.affineWeylGroup P.affineRoots,
      P.parahoric ((w : P.Apartment ≃ᵃ[ℝ] P.Apartment) '' C)) =
        P.centralizerZero.map (rationalPoints.map P.centralizer.j) :=
  P.iInf_parahoric_affineWeylOrbit_eq_centralizerZeroImage_of_orderedRootInjectivity hP
    (RelativeRoot.orderedRootPointInjectivity_of_dynamicRootOrderedProduct
      hprod P.isConnectedReductive P.isMaximalSplitTorus) hdec hC

/-- Compatibility form with the published global Dynamic product premise. -/
theorem iInf_parahoric_normalizerZeroComponent_eq_centralizerZeroImage
    (hP : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    (hrank : RelativeRoot.HasRankOneFactorization P.i)
    (hprod : RelativeRoot.DynamicRootOrderedProductStatement.{u})
    (hdec : P.ChamberIwahoriDecompositionStatement)
    {C : Set P.Apartment} (hC : AffineRootSystem.IsChamber P.affineRoots C) :
    (⨅ n : P.normalizerZeroComponent,
      P.parahoric ((n : normalizerPoints P.i) • C)) =
        P.centralizerZero.map (rationalPoints.map P.centralizer.j) :=
  P.iInf_parahoric_normalizerZeroComponent_eq_centralizerZeroImage_of_orderedRootInjectivity hP hrank
    (RelativeRoot.orderedRootPointInjectivity_of_dynamicRootOrderedProduct
      hprod P.isConnectedReductive P.isMaximalSplitTorus) hdec hC

/-- Compatibility form with the published global Dynamic product premise. -/
theorem mem_centralizerZero_of_forall_mem_parahoric_normalizerZeroComponent
    (hP : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    (hrank : RelativeRoot.HasRankOneFactorization P.i)
    (hprod : RelativeRoot.DynamicRootOrderedProductStatement.{u})
    (hdec : P.ChamberIwahoriDecompositionStatement)
    {C : Set P.Apartment} (hC : AffineRootSystem.IsChamber P.affineRoots C)
    {g : rationalPoints G}
    (hg : ∀ n : normalizerPoints P.i, (n : rationalPoints G) ∈ P.zeroSubgroup →
      g ∈ P.parahoric (n • C)) :
    g ∈ P.centralizerZero.map (rationalPoints.map P.centralizer.j) :=
  P.mem_centralizerZero_of_forall_mem_parahoric_normalizerZeroComponent_of_orderedRootInjectivity hP hrank
    (RelativeRoot.orderedRootPointInjectivity_of_dynamicRootOrderedProduct
      hprod P.isConnectedReductive P.isMaximalSplitTorus) hdec hC hg

/-- Compatibility form with the published global Dynamic product premise. -/
def chamberConjugateParahoricEquivCentralizerZeroImage
    (hP : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    (hrank : RelativeRoot.HasRankOneFactorization P.i)
    (hprod : RelativeRoot.DynamicRootOrderedProductStatement.{u})
    (hdec : P.ChamberIwahoriDecompositionStatement)
    {C : Set P.Apartment} (hC : AffineRootSystem.IsChamber P.affineRoots C) :
    ↥(⨅ n : P.normalizerZeroComponent,
      P.parahoric ((n : normalizerPoints P.i) • C)) ≃*
        P.centralizerZero.map (rationalPoints.map P.centralizer.j) :=
  P.chamberConjugateParahoricEquivCentralizerZeroImage_of_orderedRootInjectivity hP hrank
    (RelativeRoot.orderedRootPointInjectivity_of_dynamicRootOrderedProduct
      hprod P.isConnectedReductive P.isMaximalSplitTorus) hdec hC

/-- The chamber-intersection equivalence preserves the ambient rational point. -/
@[simp] theorem chamberConjugateParahoricEquivCentralizerZeroImage_apply_coe
    (hP : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    (hrank : RelativeRoot.HasRankOneFactorization P.i)
    (hprod : RelativeRoot.DynamicRootOrderedProductStatement.{u})
    (hdec : P.ChamberIwahoriDecompositionStatement)
    {C : Set P.Apartment} (hC : AffineRootSystem.IsChamber P.affineRoots C)
    (g : ↥(⨅ n : P.normalizerZeroComponent,
      P.parahoric ((n : normalizerPoints P.i) • C))) :
    ((P.chamberConjugateParahoricEquivCentralizerZeroImage hP hrank hprod hdec hC g :
      P.centralizerZero.map (rationalPoints.map P.centralizer.j)) : rationalPoints G) = g :=
  rfl

end ParahoricBuildingData

end Langlands.Geometry.Building
