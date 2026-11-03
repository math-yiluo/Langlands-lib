import Langlands.GroupScheme.Rational.RelativeTitsBorelReduction
import Langlands.GroupScheme.Rational.RelativeTitsNondegeneracy
import Langlands.GroupScheme.Rational.RootRankOneFactorizationStatement
import Langlands.GroupScheme.Rational.RootSubgroupConjugation
import Langlands.GroupScheme.Rational.RootSubgroupPositive
import Langlands.GroupScheme.Rational.RelativeWeylCharacterAction
import Langlands.GroupScheme.Rational.RootFiniteness
import Langlands.GroupScheme.Rational.ReflectionNegation
import Langlands.Group.TitsSystemMulCell

/-! # The relative Tits multiplication axiom from the rank-one factorization

For a simple relative root `a` with reflection `s`, the multiplication axiom
`s B w ⊆ B w B ∪ B s w B` of the relative Tits data follows from
`Langlands.Group.TitsSystem.mul_mem_cell_of_rankOne` with `U = U_a(k)` and
`P = {w | ⟨w⁻¹ a, ν⟩ > 0}`. The inputs are the rank-one factorization
`RelativeRoot.HasRankOneFactorization i` (Kaletha–Prasad 2.11.17), uniqueness of the reflection
of a simple root, the minimal endpoint identity `P_∅(k) = P(ν)(k)`, and the factorization
`HasSimpleRootParabolicFactorization`: every `b ∈ P_∅(k)` is a product `b' u` with
`u ∈ U_a(k)` and `b'` conjugated into `P_∅(k)` by every representative of `s`. None of these
inputs is proved here.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}

/-- For every simple relative root `a` and every relative reflection `s` in `a`, every point
`b ∈ P_∅(k)` is a product `b' * u` with `u ∈ U_a(k)` and with `n * b' * n⁻¹ ∈ P_∅(k)` for every
representative `n ∈ N(k)` of `s`. Classically `P_∅(k) = Z(k) V_a(k) U_(a)(k)`, where `V_a` is the
unipotent radical of the standard parabolic subgroup of `{a}`, and the representatives of `s`
normalize `Z(k) V_a(k)` (Borel–Tits 5.16, proof). -/
def HasSimpleRootParabolicFactorization (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
    [IsAffineHom G.X.hom] (ν : cocharacterLattice T) : Prop :=
  ∀ a ∈ simpleRelativeRoots i ν, ∀ s : relativeWeylGroup i, IsRelativeReflection i a s →
    ∀ b ∈ standardParabolicPoints i ν ∅,
      ∃ b' : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
        (∀ n : normalizerPoints i,
          QuotientGroup.mk' ((centralizerPoints i).subgroupOf (normalizerPoints i)) n = s →
          (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) * b' *
              (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)⁻¹ ∈
            standardParabolicPoints i ν ∅) ∧
        ∃ u ∈ (RelativeRoot.subgroup i a).carrier (Over.mk (𝟙 _)), b = b' * u

variable {i : T.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom] {ν : cocharacterLattice T}

/-- A relative reflection in `-a` is a relative reflection in `a`. -/
theorem IsRelativeReflection.of_neg {a : characterLattice T} {w : relativeWeylGroup i}
    (ha : a ∈ relativeRoots i) (h : IsRelativeReflection i (-a) w) :
    IsRelativeReflection i a w := by
  obtain ⟨hna, f, hf, hw⟩ := h
  have hv : (⟨toRat (-a), toRat_mem_ratSpan hna⟩ : relativeRootSpan i) =
      -⟨toRat a, toRat_mem_ratSpan ha⟩ := by
    ext
    simp [map_neg]
  have hf' : (-f) ⟨toRat a, toRat_mem_ratSpan ha⟩ = 2 := by
    rw [hv, map_neg] at hf
    simpa using hf
  refine ⟨ha, -f, hf', ?_⟩
  rw [hw]
  ext x
  simp only [Module.reflection_apply, hv, LinearMap.neg_apply, neg_smul, smul_neg]

/-- The inverse of a relative reflection in `a` is a relative reflection in `a`. -/
theorem IsRelativeReflection.inv {a : characterLattice T} {w : relativeWeylGroup i}
    (h : IsRelativeReflection i a w) : IsRelativeReflection i a w⁻¹ := by
  obtain ⟨ha, f, hf, hw⟩ := h
  exact ⟨ha, f, hf, by rw [map_inv, hw, Module.reflection_inv]⟩

/-- **The relative Tits multiplication axiom from the rank-one factorization.** For a split
torus and a generic cocharacter, the minimal endpoint identity `P_∅(k) = P(ν)(k)`, the rank-one
factorization, the factorization `HasSimpleRootParabolicFactorization` and uniqueness of the
relative reflection of each simple root give the field `mul_mem_cell` of the relative Tits
data. -/
theorem relativeTits_mul_mem_cell_of_rankOneFactorization (hT : IsSplitTorus T.toGrp)
    (hν : IsGenericCocharacter i ν)
    (hB : standardParabolicPoints i ν ∅ =
      (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _)))
    (hrank : RelativeRoot.HasRankOneFactorization i)
    (hfac : HasSimpleRootParabolicFactorization i ν)
    (huniq : ∀ a ∈ simpleRelativeRoots i ν, ∀ w w' : relativeWeylGroup i,
      IsRelativeReflection i a w → IsRelativeReflection i a w' → w = w') :
    ∀ s ∈ simpleRelativeReflections i ν, ∀ n m : normalizerPoints i,
      QuotientGroup.mk' ((centralizerPoints i).subgroupOf (normalizerPoints i)) n = s →
      ∀ b ∈ standardParabolicPoints i ν ∅,
        (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) * b * m ∈
          Langlands.Group.TitsSystem.cell (standardParabolicPoints i ν ∅)
              (QuotientGroup.mk' ((centralizerPoints i).subgroupOf (normalizerPoints i)))
              (QuotientGroup.mk' ((centralizerPoints i).subgroupOf (normalizerPoints i)) m) ∪
            Langlands.Group.TitsSystem.cell (standardParabolicPoints i ν ∅)
              (QuotientGroup.mk' ((centralizerPoints i).subgroupOf (normalizerPoints i)))
              (s * QuotientGroup.mk' ((centralizerPoints i).subgroupOf (normalizerPoints i)) m) := by
  intro s hs n m hn b hb
  obtain ⟨a, ha, has⟩ := hs
  have haR : a ∈ relativeRoots i := has.mem_relativeRoots
  have hpos : 0 < latticePairing T a ν := ha.1.2
  -- points of `U_a(k)` lie in `B`
  have hUB : ∀ x ∈ (RelativeRoot.subgroup i a).carrier (Over.mk (𝟙 _)),
      x ∈ standardParabolicPoints i ν ∅ := fun x hx =>
    RelativeRoot.subgroup_le_standardParabolic_empty i ν ha _ hx
  -- `s` is an involution
  have hinv : s⁻¹ = s := huniq a ha _ _ has.inv has
  have hss : s * s = 1 := by
    calc s * s = s⁻¹ * s := by rw [hinv]
      _ = 1 := inv_mul_cancel s
  -- the action of `s` on `a`
  have hsa : relativeWeylCharacterAction i s a = -a := by
    obtain ⟨n₀, rfl⟩ := QuotientGroup.mk_surjective s
    rw [relativeWeylCharacterAction_mk]
    exact IsRelativeReflection.weylAction_apply_self i hT _ has
  refine Langlands.Group.TitsSystem.mul_mem_cell_of_rankOne hss
    (B' := {b' | ∀ n : normalizerPoints i,
      QuotientGroup.mk' ((centralizerPoints i).subgroupOf (normalizerPoints i)) n = s →
      (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) * b' *
          (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)⁻¹ ∈ standardParabolicPoints i ν ∅})
    (U := ((RelativeRoot.subgroup i a).carrier (Over.mk (𝟙 _)) :
      Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)))
    (P := {w | 0 < latticePairing T (relativeWeylCharacterAction i w⁻¹ a) ν})
    ?_ ?_ ?_ ?_ ?_ n m hn hb
  · -- every `b ∈ B` is `b' * u` with `b' ∈ B'` and `u ∈ U`, i.e. `B ⊆ B' U`
    intro b hb
    obtain ⟨b', hb', u, hu, rfl⟩ := hfac a ha s has b hb
    exact ⟨b', hb', u, hu, rfl⟩
  · -- `B'` is conjugated into `B`
    exact fun n hn b' hb' => hb' n hn
  · -- rank one: `n U_a(k) n⁻¹ = U_{-a}(k) ⊆ B ∪ B s B`
    intro n hn u hu
    have hna : weylAction i n a = -a := by
      apply IsRelativeReflection.weylAction_apply_self i hT _
      rw [← hn] at has
      exact has
    have hv := RelativeRoot.normalizer_conj_mem i a n hu
    simp only [GroupScheme.constantPoint_self, hna] at hv
    by_cases hv1 : (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) * u *
        (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)⁻¹ = 1
    · left
      rw [hv1]
      exact (standardParabolicPoints i ν ∅).one_mem
    · have hnaR : -a ∈ relativeRoots i := IsRelativeReflection.neg_mem_relativeRoots i has hT
      obtain ⟨⟨p, hp, -⟩, hprop⟩ := hrank (-a) hnaR _ hv hv1
      obtain ⟨-, -, hrefl, -⟩ := hprop p hp
      have h1 : p.1 ∈ (RelativeRoot.subgroup i a).carrier (Over.mk (𝟙 _)) := by
        simpa only [neg_neg] using hp.1
      have h2 : p.2 ∈ (RelativeRoot.subgroup i a).carrier (Over.mk (𝟙 _)) := by
        simpa only [neg_neg] using hp.2.1
      have hm := huniq a ha _ _ (hrefl.of_neg haR) has
      right
      refine ⟨⟨_, hp.2.2⟩, hm, p.1⁻¹, (standardParabolicPoints i ν ∅).inv_mem (hUB _ h1),
        p.2⁻¹, (standardParabolicPoints i ν ∅).inv_mem (hUB _ h2), ?_⟩
      simp only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel, mul_one]
  · -- `m⁻¹ U_a(k) m ⊆ B` when `⟨w⁻¹ a, ν⟩ > 0`
    intro w hw m hm u hu
    have hc := RelativeRoot.normalizer_conj_mem i a m⁻¹ hu
    simp only [GroupScheme.constantPoint_self, InvMemClass.coe_inv, inv_inv] at hc
    have hact : weylAction i m⁻¹ a = relativeWeylCharacterAction i w⁻¹ a := by
      rw [← hm, ← map_inv]
      rfl
    rw [hact] at hc
    rw [hB]
    exact Dynamic.unipotent_le_parabolic _ _
      (RelativeRoot.subgroup_le_dynamicUnipotent i ν hw _ hc)
  · -- every `w` has `⟨w⁻¹ a, ν⟩ > 0` or `⟨(s w)⁻¹ a, ν⟩ > 0`
    intro w
    have hcR : relativeWeylCharacterAction i w⁻¹ a ∈ relativeRoots i := by
      obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective w⁻¹
      rw [← hm, relativeWeylCharacterAction_mk]
      exact weylAction_mapsTo_relativeRoots i m haR
    rcases lt_or_gt_of_ne (hν _ hcR) with hlt | hgt
    · right
      change 0 < latticePairing T (relativeWeylCharacterAction i (s * w)⁻¹ a) ν
      rw [mul_inv_rev, hinv, map_mul, LinearEquiv.mul_apply, hsa, map_neg, map_neg,
        LinearMap.neg_apply]
      omega
    · exact Or.inl hgt

/-- Under the published Coxeter realization, a simple relative root has at most one relative
reflection. -/
theorem HasRelativeWeylCoxeterSystem.eq_of_isRelativeReflection_of_mem_simple
    (h : HasRelativeWeylCoxeterSystem i ν) (hT : IsSplitTorus T.toGrp) :
    ∀ a ∈ simpleRelativeRoots i ν, ∀ w w' : relativeWeylGroup i,
      IsRelativeReflection i a w → IsRelativeReflection i a w' → w = w' := by
  obtain ⟨hfin, -, M, cs, hcs⟩ := h
  intro a ha w w' hw hw'
  exact (hcs.eq_simple_of_isRelativeReflection hT ⟨a, ha⟩ hw).trans
    (hcs.eq_simple_of_isRelativeReflection hT ⟨a, ha⟩ hw').symm

/-- The cell axioms from the rank-one factorization, `HasSimpleRootParabolicFactorization`,
uniqueness of simple reflections and the nondegeneracy field `conj_not_le`. -/
theorem hasRelativeTitsCellAxioms_of_rankOneFactorization (hT : IsSplitTorus T.toGrp)
    (hν : IsGenericCocharacter i ν)
    (hB : standardParabolicPoints i ν ∅ =
      (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _)))
    (hrank : RelativeRoot.HasRankOneFactorization i)
    (hfac : HasSimpleRootParabolicFactorization i ν)
    (huniq : ∀ a ∈ simpleRelativeRoots i ν, ∀ w w' : relativeWeylGroup i,
      IsRelativeReflection i a w → IsRelativeReflection i a w' → w = w')
    (hconj : ∀ s ∈ simpleRelativeReflections i ν, ∀ n : normalizerPoints i,
      QuotientGroup.mk' ((centralizerPoints i).subgroupOf (normalizerPoints i)) n = s →
      ∃ b ∈ standardParabolicPoints i ν ∅,
        (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) * b *
          (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)⁻¹ ∉
            standardParabolicPoints i ν ∅) :
    HasRelativeTitsCellAxioms i ν :=
  ⟨relativeTits_mul_mem_cell_of_rankOneFactorization hT hν hB hrank hfac huniq, hconj⟩

/-- **Reduction of the relative Tits system to the published structural statements, the
rank-one factorization, `HasSimpleRootParabolicFactorization` and nondegeneracy.** -/
theorem relativeTitsSystemStatement_of_rankOneFactorization
    (hcox : RelativeWeylCoxeterStatement.{u}) (hE : StandardParabolicEndpointsStatement.{u})
    (hBr : RationalBruhatStatement.{u}) (hrank : RootRankOneFactorizationStatement.{u})
    (hfac : ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
      (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
      (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T),
      haveI := hG.isAffineHom
      haveI := hi.isSplitSubtorus.mono
      IsGenericCocharacter i ν → HasSimpleRootParabolicFactorization i ν)
    (hconj : ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
      (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
      (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T),
      haveI := hG.isAffineHom
      haveI := hi.isSplitSubtorus.mono
      IsGenericCocharacter i ν →
        ∀ s ∈ simpleRelativeReflections i ν, ∀ n : normalizerPoints i,
          QuotientGroup.mk' ((centralizerPoints i).subgroupOf (normalizerPoints i)) n = s →
          ∃ b ∈ standardParabolicPoints i ν ∅,
            (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) * b *
              (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)⁻¹ ∉
                standardParabolicPoints i ν ∅) :
    RelativeTitsSystemStatement.{u} := by
  refine relativeTitsSystemStatement_of_statements hcox hE hBr ?_
  intro k _ G hG T i hi ν
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  intro hν
  have hT : IsSplitTorus T.toGrp := hi.isSplitSubtorus.1
  have hB : standardParabolicPoints i ν ∅ =
      (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := by
    rw [standardParabolicPoints, (hE k G hG T i hi ν hν).1]
  exact hasRelativeTitsCellAxioms_of_rankOneFactorization hT hν hB (hrank k G hG T i hi)
    (hfac k G hG T i hi ν hν)
    ((hcox k G hG T i hi ν hν).eq_of_isRelativeReflection_of_mem_simple hT)
    (hconj k G hG T i hi ν hν)

end Langlands.GroupScheme
