import Langlands.Global.AdelicIntertwiningContinuationReduction
import Langlands.Global.AdelicIntertwiningAutomorphyStatement
import Langlands.Global.AdelicIntertwiningCompactEquivariance
import Langlands.Global.AdelicIntertwiningIntegrability
import Langlands.Global.AdelicEisensteinFiniteCompactChangeProof
import Langlands.Automorphic.GroupSchemeHarishChandraFinitenessStatement

/-! # Finite span of intertwining operators from uniform automorphy and finiteness

Bernstein–Lapid §8.2, Lemma: for `φ ∈ 𝒜_P` the values `M(w, λ)φ` lie in one
finite-dimensional space of automorphic forms on `V(𝔸)M'(F) \ G(𝔸)`. This file proves
`IntertwiningFiniteSpanStatement` from

* `IntertwiningUniformAutomorphyStatement`: for `λ` regular enough, `M(w, λ)φ` is automorphic
  on `V(𝔸)M'(F) \ G(𝔸)`, and one ideal of finite codimension of the center annihilates all of
  them;
* `ParabolicHarishChandraFinitenessStatement`: Harish-Chandra's finiteness theorem on
  `V(𝔸)M'(F) \ G(𝔸)`.

The level at the finite places and the types under the infinite compact subgroup are the same
for all `λ`, because the operator commutes with right translation by `K`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.FiniteVectors

/-- The finite part `K ∩ G(𝔸_f)` of a maximal compact subgroup `K` of `G(𝔸)` is open: it
contains the finite projection of `K`, which is open. -/
private theorem isOpen_comap_ofFinite_of_maximalCompact {F : Type u} [Field F] [NumberField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom] {K : Subgroup (AdelicGroupPoints F G)}
    (hK : IsMaximalCompactSubgroup F G K) :
    IsOpen ((K.comap (ofFinite F G).toMonoidHom : Subgroup (FiniteAdelicGroupPoints F G)) :
      Set (FiniteAdelicGroupPoints F G)) := by
  refine Subgroup.isOpen_mono (H₁ := K.map (finite F G).toMonoidHom) ?_
    (IsMaximalCompactSubgroup.isOpen_finite F G K hK)
  rintro y ⟨k, hk, rfl⟩
  have hprod := IsMaximalCompactSubgroup.eq_comap_prod F G K hK
  change ofFinite F G (finite F G k) ∈ K
  rw [hprod, Subgroup.mem_comap, Subgroup.mem_prod]
  constructor
  · change infinite F G (ofFinite F G (finite F G k)) ∈ K.map (infinite F G).toMonoidHom
    rw [infinite_ofFinite]
    exact Subgroup.one_mem _
  · change finite F G (ofFinite F G (finite F G k)) ∈ K.map (finite F G).toMonoidHom
    rw [finite_ofFinite]
    exact ⟨k, hk, rfl⟩

/-- Regularity of a parameter is monotone in the threshold. -/
private theorem isRegularParameter_of_le {F : Type u} [Field F] [NumberField F]
    {G P M : GroupScheme (Spec (CommRingCat.of F))} {A : CommGroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
    {r : ParabolicRootPresentation p l a}
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    {hA : IsSplitTorus A.toGrp} {hT : IsSplitTorus r.data.T.toGrp} {R R' : ℝ}
    {lam : ComplexCharacterParameter F P} (h : r.IsRegularParameter hA hT R' lam)
    (hR : R ≤ R') : r.IsRegularParameter hA hT R lam :=
  fun α hα => lt_of_le_of_lt hR (h α hα)

section Slices

variable {F : Type u} [Field F] [NumberField F]
  {G P U M Q V M' : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [IsAffine Q.X.left] [IsAffine V.X.left]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left]
  {q : Q ⟶ G} [IsClosedImmersion q.hom.hom.left]
  {K : Subgroup (AdelicGroupPoints F G)}

/-- The infinite compact orbit coordinates of `φ`: for a basis `b` of the span of the right
translates of `φ` by `K_∞`, the `i`-th coordinate of the translate of `φ` by `k`. -/
private def orbitCoordinates (φ : AdelicGroupPoints F G → ℂ)
    [Module.Finite ℂ (orbitSubrepresentation (functionInfiniteSubgroupAction F G
      (K.comap (ofInfinite F G).toMonoidHom)) φ).toSubmodule]
    (i : Fin (Module.finrank ℂ (orbitSubrepresentation (functionInfiniteSubgroupAction F G
      (K.comap (ofInfinite F G).toMonoidHom)) φ).toSubmodule))
    (k : K.comap (ofInfinite F G).toMonoidHom) : ℂ :=
  (Module.finBasis ℂ (orbitSubrepresentation (functionInfiniteSubgroupAction F G
      (K.comap (ofInfinite F G).toMonoidHom)) φ).toSubmodule).repr
    ((orbitSubrepresentation (functionInfiniteSubgroupAction F G
      (K.comap (ofInfinite F G).toMonoidHom)) φ).toRepresentation k
      ⟨φ, self_mem_orbitSpan _ φ⟩) i

/-- Where the intertwining integral converges at every point, every function
`k ↦ M(w, λ)φ(g k)` on `K_∞` is a linear combination of the orbit coordinates of `φ`. -/
private theorem intertwiningOperator_slice_mem_span
    (hK : IsIwasawaCompact p K) (hQ : IsIwasawaCompact q K)
    (iU : U ⟶ P) (l : M ⟶ P) (iV : V ⟶ Q) [IsClosedImmersion (iV ≫ q).hom.hom.left]
    (c : M' ⟶ M) (π' : Q ⟶ M') (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X)
    (φ : AdelicGroupPoints F G → ℂ)
    [Module.Finite ℂ (orbitSubrepresentation (functionInfiniteSubgroupAction F G
      (K.comap (ofInfinite F G).toMonoidHom)) φ).toSubmodule]
    (lam : ComplexCharacterParameter F P)
    (hint : ∀ g, Integrable (hK.intertwiningIntegrand iU (iV ≫ q) w φ lam g)
      (intertwiningMeasure F p iU (iV ≫ q) (innerAdelicPoint F G w)))
    (g : AdelicGroupPoints F G) :
    (fun k : K.comap (ofInfinite F G).toMonoidHom =>
        hK.intertwiningOperator hQ iU l iV c π' w φ lam (g * ofInfinite F G k)) ∈
      Submodule.span ℂ (Set.range (orbitCoordinates (K := K) φ)) := by
  let Rr := functionInfiniteSubgroupAction F G (K.comap (ofInfinite F G).toMonoidHom)
  let W := (orbitSubrepresentation Rr φ).toSubmodule
  let ρ := (orbitSubrepresentation Rr φ).toRepresentation
  let b := Module.finBasis ℂ W
  let v₀ : W := ⟨φ, self_mem_orbitSpan Rr φ⟩
  let T := hK.intertwiningCompactMap hQ iU l iV c π' w lam φ hint
  have hfun : (fun k : K.comap (ofInfinite F G).toMonoidHom =>
        hK.intertwiningOperator hQ iU l iV c π' w φ lam (g * ofInfinite F G k)) =
      ∑ i, (T (b i) g) • orbitCoordinates (K := K) φ i := by
    funext k
    have h2 : Rr k (T v₀) = T (ρ k v₀) :=
      (Representation.IntertwiningMap.isIntertwining ρ Rr T k v₀).symm
    have h3 : ρ k v₀ = ∑ i, b.repr (ρ k v₀) i • b i := (b.sum_repr _).symm
    have h4 : T (ρ k v₀) = ∑ i, b.repr (ρ k v₀) i • T (b i) := by
      conv_lhs => rw [h3]
      rw [map_sum]
      simp only [map_smul]
    change Rr k (T v₀) g = _
    rw [h2, h4]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm]
    rfl
  rw [hfun]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end Slices

/-- **Bernstein–Lapid §8.2, Lemma**, from uniform automorphy of the intertwining operators and
Harish-Chandra's finiteness theorem on `V(𝔸)M'(F) \ G(𝔸)`. -/
theorem intertwiningFiniteSpan_of_uniformAutomorphy
    (hauto : IntertwiningUniformAutomorphyStatement.{u})
    (hHC : ParabolicHarishChandraFinitenessStatement.{u}) :
    IntertwiningFiniteSpanStatement.{u} := by
  intro F _ _ G P M U Q M' V A _ _ _ _ _ _ p _ iU l a r _ _ _ hA hT q _ iV l' _ π' w c
    hG hU hQ hV hl' hiso hπ hW K hK hK' N d rho hsmooth hcalc φ hmax hrho hφ
  obtain ⟨R₁, J, hJ, hR₁⟩ := hauto F G P M U Q M' V A p iU l a r hA hT q iV l' π' w c
    hG hU hQ hV hl' hiso hπ hW K hK hK' rho hsmooth hcalc φ hmax hrho hφ
  obtain ⟨R₂, hR₂⟩ := intertwiningIntegrability F G P M U Q M' V A p iU l a r hA hT q iV l' w c
    hG hU hQ hV hl' hiso hW K hK rho hsmooth hcalc φ hmax hrho hφ
  obtain ⟨L₀, hL₀, hfix⟩ := hφ.2.1.2.2
  let Rr := functionInfiniteSubgroupAction F G (K.comap (ofInfinite F G).toMonoidHom)
  have : Module.Finite ℂ (orbitSubrepresentation Rr φ).toSubmodule := hφ.2.2.1
  let E : Submodule ℂ (K.comap (ofInfinite F G).toMonoidHom → ℂ) :=
    Submodule.span ℂ (Set.range (orbitCoordinates (K := K) φ))
  have hE : FiniteDimensional ℂ E :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  let L := L₀ ⊓ K.comap (ofFinite F G).toMonoidHom
  have hL : IsOpen (L : Set (FiniteAdelicGroupPoints F G)) :=
    hL₀.inter (isOpen_comap_ofFinite_of_maximalCompact hmax)
  have hfin := hHC F G Q M' V q iV l' hG hQ hV hl' hiso K hmax hK' rho hsmooth hcalc hrho
    J hJ L hL E hE
  let R₀ := max R₁ R₂
  let S : Set (AdelicGroupPoints F G → ℂ) := {f | ∃ lam, r.IsRegularParameter hA hT R₀ lam ∧
    hK.intertwiningOperator hK' iU l iV c π' w φ lam = f}
  have hS : ∀ f ∈ S, IsAutomorphicFunctionOn F G hsmooth hcalc
      (parabolicQuotientSubgroup F q iV l') (K.comap (ofInfinite F G).toMonoidHom) rho f := by
    rintro _ ⟨lam, hlam, rfl⟩
    exact (hR₁ lam (isRegularParameter_of_le hlam (le_max_left _ _))).1
  have hsub : ∀ X : Set (AdelicGroupPoints F G → ℂ), FiniteDimensional ℂ (Submodule.span ℂ X) →
      S ⊆ X → FiniteDimensional ℂ (Submodule.span ℂ S) := fun X hX hSX =>
    Submodule.finiteDimensional_of_le (Submodule.span_mono hSX)
  have hSfin : FiniteDimensional ℂ (Submodule.span ℂ S) := by
    refine hsub _ hfin ?_
    rintro _ ⟨lam, hlam, rfl⟩
    have h₁ := hR₁ lam (isRegularParameter_of_le hlam (le_max_left _ _))
    have h₂ := hR₂ lam (isRegularParameter_of_le hlam (le_max_right _ _))
    exact ⟨h₁.1, hK.intertwiningOperator_fixedByFiniteLevel hK' iU l iV c π' w lam L
      inf_le_right (fun b hb g => hfix b hb.1 g), h₁.2,
      fun g => intertwiningOperator_slice_mem_span hK hK' iU l iV c π' w φ lam h₂ g⟩
  obtain ⟨s, hsS, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset S).mp
    ((Submodule.fg_iff_finiteDimensional _).mpr hSfin)
  have hrange : Set.range (fun i : Fin s.card => ((s.equivFin.symm i : s) :
      AdelicGroupPoints F G → ℂ)) = (s : Set (AdelicGroupPoints F G → ℂ)) := by
    ext f
    constructor
    · rintro ⟨i, rfl⟩
      exact (s.equivFin.symm i).2
    · intro hf
      exact ⟨s.equivFin ⟨f, hf⟩, by simp⟩
  refine ⟨s.card, fun i => ((s.equivFin.symm i : s) : AdelicGroupPoints F G → ℂ),
    fun i => hS _ (hsS (s.equivFin.symm i).2), R₀, fun lam hlam => ?_⟩
  have hmem : hK.intertwiningOperator hK' iU l iV c π' w φ lam ∈ Submodule.span ℂ S :=
    Submodule.subset_span ⟨lam, hlam, rfl⟩
  rw [hspan] at hmem
  rw [hrange]
  exact hmem

end Langlands.Global
