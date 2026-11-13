import Langlands.Geometry.Building.QuasiSplitAdjointSimpleRootTransitivityStatement
import Langlands.Geometry.Building.QuasiSplitR1RootFieldCoordinatesReduction
import Langlands.Geometry.Building.RootGroupTorusValueAction
import Langlands.GroupScheme.Rational.SimpleRootValueCharacter
import Langlands.GroupScheme.Torus.EquivariantCharacterValueDescent
import Langlands.GroupScheme.Reductive.AdjointRootSpan
import Langlands.GroupScheme.Rational.QuasiSplitMaximalTorusCentralizerProof
import Langlands.GroupScheme.Rational.MaximalSplitTorusConjugacyProof
import Langlands.GroupScheme.Reductive.RootDatumExistence
import Langlands.GroupScheme.Rational.RelativeRootSystemProof
import Langlands.GroupScheme.Rational.PositiveRootInduction
import Langlands.GroupScheme.Rational.RelativeRootStandardCocharacter
import Langlands.GroupScheme.Adjoint.GeometricBaseChange
import Langlands.GroupScheme.Reductive.FieldExtensionProof
import Langlands.GroupScheme.Reductive.FiniteCenterBaseChange

/-! # Simple-root transitivity of `Z(k)` in quasi-split adjoint groups

Proof of `QuasiSplitAdjointSimpleRootTransitivityStatement`. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Geometry.Building

open Langlands.GroupScheme

attribute [local instance] rootsGaloisAction

local instance (k K : Type u) [Field k] [Field K] [Algebra k K]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom] :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

/-- A rational torus point realizing a Galois-equivariant family of character values, read
through the root values used in `RootGroupTorusValueAction`. -/
theorem exists_rationalPoint_rootOrbitCharacterValue
    (k K : Type u) [Field k] [Field K] [Algebra k K] [IsGalois k K]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] (j : T.toGrp ⟶ G)
    (hK : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T).toGrp)
    (φ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T) →+
      Additive Kˣ)
    (hφ : ∀ (σ : K ≃ₐ[k] K)
        (χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)),
      (((φ (characterLattice.galoisRepresentation k K T σ χ)).toMul : Kˣ) : K) =
        σ (((φ χ).toMul : Kˣ) : K)) :
    ∃ z : rationalPoints T.toGrp,
      ∀ β : roots (T := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
          (G := (GroupScheme.baseChange (algebraBaseMap k K)).obj G)
          ((GroupScheme.baseChange (algebraBaseMap k K)).map j),
        (rootOrbitCharacterValue k K j β (GaloisPointComparison.rationalCoeffEquiv k T.toGrp z) :
          K) = (((φ β.val).toMul : Kˣ) : K) := by
  obtain ⟨h, hh⟩ := exists_rationalPoint_characterValue_eq_of_equivariant k K T hK φ hφ
  refine ⟨(GaloisPointComparison.rationalCoeffEquiv k T.toGrp).symm h, fun β => ?_⟩
  rw [MulEquiv.apply_symm_apply, rootOrbitCharacterValue_coe, hh]

/-- A rational torus point whose root values on the fibers of `b` and `2b` are `1`
commutes with `U_b(k)`. -/
theorem commute_of_rootOrbitCharacterValue_eq_one_of_fibers
    (k K : Type u) [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    {S T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] [Smooth G.X.hom]
    [IsAffineHom T.toGrp.X.hom] [LocallyOfFiniteType T.toGrp.X.hom]
    (f : S ⟶ T) (j : T.toGrp ⟶ G)
    (hG : IsConnectedReductive G) (hjm : IsMaximalTorus j) (hjc : IsClosedSubgroup j)
    (hi : IsMaximalSplitTorus (CommGroupScheme.groupHom f ≫ j))
    (hcent : (torusCentralizer (CommGroupScheme.groupHom f ≫ j)).IsRepresentedBy j)
    (hK : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T).toGrp)
    {J : Type u} [Finite J]
    {P : RootDatum J (characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))
      (cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))}
    (hP : IsRootDatumOf (T := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
      ((GroupScheme.baseChange (algebraBaseMap k K)).map j) P)
    (hmult : ∀ a ∈ relativeRoots (CommGroupScheme.groupHom f ≫ j), ∀ n : ℕ,
      n • a ∈ relativeRoots (CommGroupScheme.groupHom f ≫ j) → n = 1 ∨ n = 2)
    {b : characterLattice S} (hb : b ∈ relativeRoots (CommGroupScheme.groupHom f ≫ j))
    (z : rationalPoints T.toGrp)
    (hz : ∀ r : roots (T := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
          (G := (GroupScheme.baseChange (algebraBaseMap k K)).obj G)
          ((GroupScheme.baseChange (algebraBaseMap k K)).map j),
        (r ∈ rootRestrictionFiber k K j f b ∨ r ∈ rootRestrictionFiber k K j f (2 • b)) →
        rootOrbitCharacterValue k K j r (GaloisPointComparison.rationalCoeffEquiv k T.toGrp z) = 1)
    {g : rationalPoints G} (hg : g ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ j) b) :
    Commute (rationalPoints.map j z) g := by
  have hS : IsSplitTorus S.toGrp := hi.1.1
  obtain ⟨β, hβ⟩ := rootRestrictionFiber_nonempty k K j f hS hK ⟨b, hb⟩
  have horbit := rootOrbit_eq_restrictionFiber_of_torusCentralizer k K f j hi hjc hcent hK hP b hβ
  by_cases h2 : 2 • b ∈ relativeRoots (CommGroupScheme.groupHom f ≫ j)
  · obtain ⟨β₂, hβ₂⟩ := rootRestrictionFiber_nonempty k K j f hS hK ⟨2 • b, h2⟩
    have horbit₂ :=
      rootOrbit_eq_restrictionFiber_of_torusCentralizer k K f j hi hjc hcent hK hP (2 • b) hβ₂
    have hhigh : ∀ n : ℕ, 3 ≤ n → n • b ∉ relativeRoots (CommGroupScheme.groupHom f ≫ j) :=
      fun n hn hnb => by rcases hmult b hb n hnb with h | h <;> omega
    exact commute_of_rootOrbitCharacterValue_eq_one_of_multipliable k K f j hG hjm hS hcent hK
      hb.1 hhigh β horbit h2 β₂ horbit₂ z (hz β (Or.inl hβ)) (hz β₂ (Or.inr hβ₂)) hg
  · have hhigh : RelativeRoot.HasNoHigherRoots (CommGroupScheme.groupHom f ≫ j) b :=
      fun n hn hnb => by
        rcases hmult b hb n hnb with h | h
        · omega
        · exact h2 (h ▸ hnb)
    exact commute_of_rootOrbitCharacterValue_eq_one k K f j hG hjm hS hcent hK hb hhigh β
      horbit z (hz β (Or.inl hβ)) hg

/-- **The transitivity clause for one simple root**, in the torus setup `f ≫ j : S → T → G`.
Given `u, u' ∈ U_a(k) ∖ U_{2a}(k)` for a simple relative root `a`, a rational point `z` of the
centralizer torus `T` commutes with `U_b(k)` for the other simple roots `b` and carries `u` into
`u' U_{2a}(k)`. -/
theorem exists_simpleRoot_conj
    (k K : Type u) [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    {S T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] [Smooth G.X.hom]
    [IsAffineHom T.toGrp.X.hom] [LocallyOfFiniteType T.toGrp.X.hom]
    (f : S ⟶ T) (j : T.toGrp ⟶ G)
    (hG : IsConnectedReductive G) (hjm : IsMaximalTorus j) (hjc : IsClosedSubgroup j)
    (hi : IsMaximalSplitTorus (CommGroupScheme.groupHom f ≫ j))
    (hcent : (torusCentralizer (CommGroupScheme.groupHom f ≫ j)).IsRepresentedBy j)
    (hK : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T).toGrp)
    {J : Type u} [Finite J]
    (P : RootDatum J (characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))
      (cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)))
    (hP : IsRootDatumOf (T := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
      ((GroupScheme.baseChange (algebraBaseMap k K)).map j) P)
    (hPred : P.IsReduced) (hspan : P.rootSpan ℤ = ⊤)
    (hmult : ∀ a ∈ relativeRoots (CommGroupScheme.groupHom f ≫ j), ∀ n : ℕ,
      n • a ∈ relativeRoots (CommGroupScheme.groupHom f ≫ j) → n = 1 ∨ n = 2)
    (ν : cocharacterLattice S) (hν : IsGenericCocharacter (CommGroupScheme.groupHom f ≫ j) ν)
    {a : characterLattice S} (ha : a ∈ simpleRelativeRoots (CommGroupScheme.groupHom f ≫ j) ν)
    {u u' : rationalPoints G}
    (hu : u ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ j) a)
    (hu' : u' ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ j) a)
    (hu2 : u ∉ doubleRootGroupPoints (CommGroupScheme.groupHom f ≫ j) a)
    (hu2' : u' ∉ doubleRootGroupPoints (CommGroupScheme.groupHom f ≫ j) a) :
    ∃ z : rationalPoints T.toGrp,
      (∀ b ∈ simpleRelativeRoots (CommGroupScheme.groupHom f ≫ j) ν, b ≠ a →
        ∀ g ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ j) b,
          Commute (rationalPoints.map j z) g) ∧
      ∃ w ∈ doubleRootGroupPoints (CommGroupScheme.groupHom f ≫ j) a,
        rationalPoints.map j z * u * (rationalPoints.map j z)⁻¹ = u' * w := by
  have hS : IsSplitTorus S.toGrp := hi.1.1
  have hsub : simpleRelativeRoots (CommGroupScheme.groupHom f ≫ j) ν ⊆
      relativeRoots (CommGroupScheme.groupHom f ≫ j) := fun _ hb =>
    positiveRelativeRoots_subset_relativeRoots _ _ (simpleRelativeRoots_subset_positive _ _ hb)
  have haR := hsub ha
  obtain ⟨β, hβ⟩ := rootRestrictionFiber_nonempty k K j f hS hK ⟨a, haR⟩
  have horbit := rootOrbit_eq_restrictionFiber_of_torusCentralizer k K f j hi hjc hcent hK hP a hβ
  -- the root value `c` and the conjugation property, in both cases
  obtain ⟨c, hc, hconj⟩ : ∃ c : rootOrbitField k K j β, c ≠ 0 ∧ ∀ z : rationalPoints T.toGrp,
      rootOrbitCharacterValue k K j β (GaloisPointComparison.rationalCoeffEquiv k T.toGrp z) =
          c →
        ∃ w ∈ doubleRootGroupPoints (CommGroupScheme.groupHom f ≫ j) a,
          rationalPoints.map j z * u * (rationalPoints.map j z)⁻¹ = u' * w := by
    by_cases h2 : 2 • a ∈ relativeRoots (CommGroupScheme.groupHom f ≫ j)
    · have hd : doubleRootGroupPoints (CommGroupScheme.groupHom f ≫ j) a =
          rootGroupPoints (CommGroupScheme.groupHom f ≫ j) (2 • a) := by
        simp only [doubleRootGroupPoints, h2, ite_true]
      rw [hd] at hu2 hu2' ⊢
      have hhigh : ∀ n : ℕ, 3 ≤ n → n • a ∉ relativeRoots (CommGroupScheme.groupHom f ≫ j) :=
        fun n hn hna => by rcases hmult a haR n hna with h | h <;> omega
      exact exists_rootOrbitCharacterValue_conj_eq_mul k K f j hG hjm hS hcent hK haR.1 hhigh β
        horbit hu hu' hu2 hu2'
    · have hd : doubleRootGroupPoints (CommGroupScheme.groupHom f ≫ j) a = ⊥ := by
        simp only [doubleRootGroupPoints, h2, ite_false]
      rw [hd, Subgroup.mem_bot] at hu2 hu2'
      have hhigh : RelativeRoot.HasNoHigherRoots (CommGroupScheme.groupHom f ≫ j) a :=
        fun n hn hna => by
          rcases hmult a haR n hna with h | h
          · omega
          · exact h2 (h ▸ hna)
      obtain ⟨c, hc, h⟩ := exists_rootOrbitCharacterValue_conj_eq k K f j hG hjm hS hcent hK haR
        hhigh β horbit hu hu' hu2 hu2'
      refine ⟨c, hc, fun z hz => ⟨1, ?_, by rw [mul_one]; exact h z hz⟩⟩
      rw [hd]
      exact Subgroup.one_mem _
  have hcK : (c : K) ≠ 0 := fun h => hc (Subtype.ext h)
  obtain ⟨φ, hφ, hφa, hφb⟩ := exists_simpleRootValueCharacter k K S T G f j hjm hjc hi hcent hK J P hP hPred hspan ν hν a ha
    β hβ (Units.mk0 (c : K) hcK) c.2
  obtain ⟨z, hz⟩ := exists_rationalPoint_rootOrbitCharacterValue k K j hK φ hφ
  refine ⟨z, fun b hb hba g hg => ?_, hconj z ?_⟩
  · refine commute_of_rootOrbitCharacterValue_eq_one_of_fibers k K f j hG hjm hjc hi hcent hK hP
      hmult (hsub hb) z (fun r hr => ?_) hg
    apply Subtype.ext
    rw [hz r, hφb b hb hba r hr]
    rfl
  · apply Subtype.ext
    rw [hz β, hφa]
    rfl

/-- **Simple-root transitivity of `Z(k)` in quasi-split adjoint groups.** -/
theorem quasiSplitAdjointSimpleRootTransitivity :
    QuasiSplitAdjointSimpleRootTransitivityStatement.{u} := by
  intro k _ G _ hG hadj S i hi Z j hj
  obtain ⟨s, rfl⟩ : ∃ s : S.toGrp ⟶ Z, s ≫ j = i :=
    ⟨hj.factorHom i (range_le_torusCentralizer i), hj.factorHom_comp i _⟩
  have hZ : IsTorus Z := isTorus_of_quasiSplit_torusCentralizer
    quasiSplitTorusCentralizerExistence maximalSplitTorusConjugacy hG hi hj
  have hGr := hG.isConnectedReductive
  let : Smooth G.X.hom := hGr.smooth
  let : LocallyOfFiniteType G.X.hom := inferInstance
  have hjc : IsClosedSubgroup j := IsSplitTorus.isClosedSubgroup_torusCentralizer hi.1.1 _ hj
  let T : CommGroupScheme (Spec (CommRingCat.of k)) := { Z with comm := hZ.isCommMonObj }
  let jT : T.toGrp ⟶ G := j
  let f : S ⟶ T := Additive.ofMul s
  let : IsAffineHom T.toGrp.X.hom := hjc.isAffineHom
  let : LocallyOfFiniteType T.toGrp.X.hom := hjc.locallyOfFiniteType
  have hself : torusCentralizer jT = SubgroupFunctor.range jT :=
    le_antisymm ((torusCentralizer_le_of_factor jT (s ≫ j) s rfl).trans hj.2.symm.le)
      (range_le_torusCentralizer jT)
  have hjm : IsMaximalTorus jT := isMaximalTorus_of_torusCentralizer_eq hZ hjc hself
  obtain ⟨K, _, _, _, _, hK⟩ := torusFiniteGaloisSplitting k Z hZ
  have : Algebra.IsAlgebraic k K := Algebra.IsAlgebraic.of_finite k K
  have hjmK := isMaximalTorus_baseChange_of_torusCentralizer_eq K hZ hjc hself
  obtain ⟨J, _, P, hP, hPred⟩ := rootDatumExistence K
    ((GroupScheme.baseChange (algebraBaseMap k K)).obj G)
    (hGr.baseChange_of_algebraicExtension (K := K))
    ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T) hK
    ((GroupScheme.baseChange (algebraBaseMap k K)).map jT) hjmK
  have hadjK : IsAdjoint ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) :=
    ⟨⟨connectedReductiveFieldExtensionStatement k K G hGr,
      hadj.isSemisimple.hasFiniteCenter.baseChange (algebraBaseMap k K)⟩,
      center_eq_bot_baseChange (algebraBaseMap k K) hadj.center_eq_bot⟩
  have hspan : P.rootSpan ℤ = ⊤ := IsAdjoint.rootSpan_eq_top hadjK hK hjmK P hP hPred
  let : Mono (s ≫ j).hom.hom.left := hi.isSplitSubtorus.mono
  have hR := relativeRootSystem k G hGr S (s ≫ j) hi
  have hS : IsSplitTorus S.toGrp := hi.1.1
  have hmult : ∀ a ∈ relativeRoots (s ≫ j), ∀ n : ℕ, n • a ∈ relativeRoots (s ≫ j) →
      n = 1 ∨ n = 2 :=
    fun a ha n hn => hR.eq_one_or_two_of_nsmul_mem ha hn
  obtain ⟨ν, hν⟩ := hS.exists_genericCocharacter (s ≫ j)
  have hsub : simpleRelativeRoots (s ≫ j) ν ⊆ relativeRoots (s ≫ j) := fun _ ha =>
    positiveRelativeRoots_subset_relativeRoots _ _ (simpleRelativeRoots_subset_positive _ _ ha)
  have hfin : (simpleRelativeRoots (s ≫ j) ν).Finite := (hS.finite_relativeRoots _).subset hsub
  refine ⟨hfin.toFinset, fun a ha => hsub (hfin.mem_toFinset.mp ha), fun b hb => ?_, ?_⟩
  · rw [hfin.coe_toFinset]
    exact relativeRoots_subset_addSubgroupClosure_simpleRelativeRoots (s ≫ j) ν hν
      (fun _ hα => hR.neg_mem_relativeRoots (s ≫ j) hS hα) hb
  · intro a ha u hu u' hu' hu2 hu2'
    obtain ⟨z, hz, w, hw, hzw⟩ := exists_simpleRoot_conj k K f jT hGr hjm hjc hi hj hK P
      hP hPred hspan hmult ν hν (hfin.mem_toFinset.mp ha) hu hu' hu2 hu2'
    exact ⟨z, fun b hb hba g hg => hz b (hfin.mem_toFinset.mp hb) hba g hg, w, hw, hzw⟩

end Langlands.Geometry.Building
