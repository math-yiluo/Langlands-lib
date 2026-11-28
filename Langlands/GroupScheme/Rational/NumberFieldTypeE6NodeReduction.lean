import Langlands.GroupScheme.Rational.TypeE6NodeMarkingFromRoots
import Langlands.GroupScheme.Rational.NumberFieldTotallyComplexOuterTypeAMiddleObstruction
import Langlands.GroupScheme.Rational.NumberFieldTypeE6QuadraticLeviReduction
import Langlands.GroupScheme.Rational.TypeE6BranchCocharacter
import Langlands.GroupScheme.SimplyConnected.LocalRankOneE6Exclusion
import Langlands.GroupScheme.SimplyConnected.FactorCartanComponent
import Langlands.GroupScheme.SimplyConnected.StarOrbitWeights
import Langlands.GroupScheme.Reductive.SeparablyClosedAlmostSimpleAbsoluteProof
import Langlands.GroupScheme.Reductive.SplitLeviTitsComparison

/-! # The central E6 vertex over totally complex fields from the outer type A middle class -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NumberField
open scoped BigOperators

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false in
/-- A simply connected group with an actual Tits index whose Cartan diagram is connected is
absolutely almost simple: every geometric almost-simple factor contains a simple vertex, and
Cartan-connected vertices lie in the same factor. -/
private theorem absolutelyAlmostSimple_of_cartanConnected
    {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (hsc : IsSimplyConnected G) (d : TitsIndexData G) (a : d.Vertex)
    (hconn : ∀ b, d.CartanConnected a b) : IsAbsolutelyAlmostSimple G := by
  let E := SeparableClosure k
  let G_E := (GroupScheme.baseChange (algebraBaseMap k E)).obj G
  have hscE : IsSimplyConnected G_E := isSimplyConnectedFieldExtension k E G hsc
  let hsem := hscE.isSemisimple
  let : IsAffineHom G_E.X.hom := hsem.isConnectedReductive.isAffineHom
  let : Smooth G_E.X.hom := hsem.isConnectedReductive.smooth
  let P := hscE.almostSimpleProduct
  let p := d.pinning.toSplitPinning
  have hfactor (i : P.Index) : ∃ b : d.Vertex, d.geometricFactorIndex P hsem b = i := by
    let t := P.factorMaximalTorus hsem.isConnectedReductive p.inclusion
      p.isSplitTorus p.isMaximalTorus i
    let hpart := (P.isAlmostSimple i).isSemisimple.isConnectedReductive
    let : IsAffineHom (P.factor i).X.hom := hpart.isAffineHom
    obtain ⟨J, hJ, R, hR, hRred⟩ :=
      rootDatumExistence E (P.factor i) hpart t.torus t.split t.subgroupHom t.isMaximalTorus
    let : Finite J := hJ
    let : R.IsReduced := hRred
    obtain ⟨α, hα⟩ :=
      (P.isAlmostSimple i).relativeRoots_nonempty_of_split_maximalTorus t.subgroupHom
        t.split t.isMaximalTorus
    let : Nonempty J := ⟨hR.relativeRootIndex ⟨α, hα⟩⟩
    let B := t.inducedBase P hsem p hR
    obtain ⟨x⟩ : Nonempty B.support := B.support_nonempty.to_subtype
    let y := t.simpleRootIndexEquiv P hsem p hR x
    exact ⟨y.val, y.property⟩
  let : Subsingleton P.Index := ⟨by
    intro i j
    obtain ⟨b, rfl⟩ := hfactor i
    obtain ⟨c, rfl⟩ := hfactor j
    exact (d.geometricFactorIndex_eq_of_cartanConnected P hsem (hconn b)).symm.trans
      (d.geometricFactorIndex_eq_of_cartanConnected P hsem (hconn c))⟩
  let : Unique P.Index := uniqueOfSubsingleton (d.geometricFactorIndex P hsem a)
  have hE : IsAlmostSimple G_E :=
    (P.isAlmostSimple (default : P.Index)).of_iso (P.iso ≪≫ productUniqueIso P.factor)
  exact IsAbsolutelyAlmostSimple.of_fieldExtension (K := E)
    (separablyClosedAlmostSimpleAbsolute E G_E hE)

/-- Every vertex of an actual index numbered by a Cartan matrix of type `A` is
Cartan-connected to the vertex numbered `0`. -/
private theorem cartanConnected_of_typeA
    {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (d : TitsIndexData G) {n : ℕ} (q : d.Vertex ≃ Fin (n + 1))
    (hA : ∀ a b, d.cartan a b = CartanMatrix.A (n + 1) (q a) (q b)) (b : d.Vertex) :
    d.CartanConnected (q.symm 0) b := by
  have hstep (i : ℕ) (hi : i + 1 < n + 1) :
      d.CartanConnected (q.symm ⟨i, by omega⟩) (q.symm ⟨i + 1, hi⟩) := by
    apply d.cartanConnected_of_cartan_ne_zero
    rw [hA, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    simp [CartanMatrix.A, Matrix.of_apply]
  have hall (i : ℕ) (hi : i < n + 1) : d.CartanConnected (q.symm 0) (q.symm ⟨i, hi⟩) := by
    induction i with
    | zero => exact d.cartanConnected_refl _
    | succ i ih => exact TitsIndexData.CartanConnected.trans d (ih (by omega)) (hstep i hi)
  have h := hall (q b).val (q b).isLt
  rwa [Fin.eta, Equiv.symm_apply_apply] at h

/-- The integral fundamental weight of an actual E6 index at the central vertex `3` lies in
the integral root span: it is the sum of the simple roots with coefficients
`(2, 3, 4, 6, 4, 2)`. -/
private theorem typeE6_nodeWeight_mem_rootSpan
    {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (d : TitsIndexData G) (e : d.Vertex ≃ Fin 6) (hsc : IsSimplyConnected G)
    (hE : ∀ a b, d.cartan a b = CartanMatrix.E 6 (e a) (e b)) :
    d.absoluteFundamentalCharacter hsc (e.symm 3) ∈ d.pinning.rootDatum.rootSpan ℤ := by
  classical
  let P := d.pinning.rootDatum
  let a (i : Fin 6) : d.pinning.rootIndex := (e.symm i).val
  let c : Fin 6 → ℤ := ![2, 3, 4, 6, 4, 2]
  have hnumb (i j : Fin 6) : P.pairing (a i) (a j) = CartanMatrix.E 6 i j := by
    change d.cartan (e.symm i) (e.symm j) = _
    simpa using hE (e.symm i) (e.symm j)
  have hsum : ∀ j : Fin 6, (∑ i : Fin 6, c i * CartanMatrix.E 6 i j) =
      if j = 3 then 1 else 0 := by decide
  have hx : d.absoluteFundamentalCharacter hsc (e.symm 3) = ∑ i : Fin 6, c i • P.root (a i) := by
    apply IntegralWeylVector.eq_of_pairing_simple_eq P d.pinning.base
      (d.pinning_corootSpan_eq_top hsc)
    intro b
    let j := e b
    have hj : b = e.symm j := (e.symm_apply_apply b).symm
    rw [hj]
    change P.toLinearMap (d.absoluteFundamentalCharacter hsc (e.symm 3)) (P.coroot (a j)) = _
    rw [show P.toLinearMap (d.absoluteFundamentalCharacter hsc (e.symm 3)) (P.coroot (a j)) =
        (if e.symm j = e.symm 3 then 1 else 0) from
      Langlands.RootDatum.fundamentalWeightBasis_pairing P d.pinning.base _ _ _]
    simp only [Equiv.apply_eq_iff_eq, map_sum, LinearMap.sum_apply, map_zsmul,
      LinearMap.smul_apply, zsmul_eq_mul, P.root_coroot_eq_pairing]
    change (if j = 3 then 1 else 0) = ∑ i, c i * P.pairing (a i) (a j)
    simpa only [hnumb] using (hsum j).symm
  rw [hx]
  exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _
    (Submodule.subset_span (Set.mem_range_self (a i))))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 2000000 in
/-- Let the zero vertices of an actual simply connected E6 index be the vertices
`δ 0, …, δ n` forming a chain of type `A_{n+1}` through the central vertex `δ mid = 3`, and
let some element of the absolute Galois group exchange the two long arms. Then the actual
anisotropic kernel is absolutely almost simple of outer type `A_{n+1}`, and its integral
fundamental weight at the kernel vertex of `3` has zero Tits obstruction. -/
private theorem outerKernel_middle {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (d : TitsIndexData G) (e : d.Vertex ≃ Fin 6) (hsc : IsSimplyConnected G)
    (hE : ∀ a b, d.cartan a b = CartanMatrix.E 6 (e a) (e b))
    {n : ℕ} (δ : Fin (n + 1) → Fin 6) (hδ : Function.Injective δ)
    (hz : ∀ a, a ∈ d.zeroVertices ↔ ∃ i, δ i = e a)
    (hA : ∀ i j, CartanMatrix.E 6 (δ i) (δ j) = CartanMatrix.A (n + 1) i j)
    (mid : Fin (n + 1)) (hmid : δ mid = 3) (i₀ : Fin (n + 1))
    (hi₀ : Langlands.CartanE6Root.symmetry (δ i₀) ≠ δ i₀)
    (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k)
    (hσ : ∀ j, d.star σ (e.symm j) = e.symm (Langlands.CartanE6Root.symmetry j)) :
    let p := d.anisotropicKernelIndex
    IsAbsolutelyAlmostSimple p.kernel ∧
      ∃ q : p.index.Vertex ≃ Fin (n + 1),
        (∀ a b, p.index.cartan a b = CartanMatrix.A (n + 1) (q a) (q b)) ∧
        (∃ (τ : SeparableClosure k ≃ₐ[k] SeparableClosure k) (a : p.index.Vertex),
          p.index.star τ a ≠ a) ∧
        ∃ weight : p.index.pinning.starFixedWeights,
          weight.val =
            p.index.absoluteFundamentalCharacter (p.isSimplyConnected hsc) (q.symm mid) ∧
          p.index.pinning.titsObstruction (p.isSimplyConnected hsc) weight = 0 := by
  classical
  intro p
  let P (j : Fin 6) : Prop := ∃ i, δ i = j
  let eZero : d.zeroVertices ≃ {j : Fin 6 // P j} := Equiv.subtypeEquiv e hz
  let z : Fin (n + 1) ≃ {j : Fin 6 // P j} :=
    Equiv.ofBijective (fun i => ⟨δ i, i, rfl⟩) (by
      constructor
      · intro i j h
        exact hδ (congrArg Subtype.val h)
      · rintro ⟨j, i, rfl⟩
        exact ⟨i, rfl⟩)
  let q : p.index.Vertex ≃ Fin (n + 1) := p.comparison.vertexEquiv.trans (eZero.trans z.symm)
  have hq (a : p.index.Vertex) : e (p.comparison.vertexEquiv a).val = δ (q a) :=
    (congrArg Subtype.val (z.apply_symm_apply (eZero (p.comparison.vertexEquiv a)))).symm
  have hD (a b : p.index.Vertex) :
      p.index.cartan a b = CartanMatrix.A (n + 1) (q a) (q b) := by
    rw [← p.comparison.vertexEquiv_cartan, hE, hq a, hq b, hA]
  have hval (a : p.index.Vertex) : (p.comparison.vertexEquiv a).val = e.symm (δ (q a)) :=
    e.injective (by rw [hq, Equiv.apply_symm_apply])
  refine ⟨absolutelyAlmostSimple_of_cartanConnected (p.isSimplyConnected hsc) p.index
    (q.symm 0) (cartanConnected_of_typeA p.index q hD), q, hD, ⟨σ, q.symm i₀, ?_⟩, ?_⟩
  · intro hfix
    have h := congrArg (fun a => (p.comparison.vertexEquiv a).val) hfix
    rw [p.comparison.vertexEquiv_star] at h
    change d.star σ (p.comparison.vertexEquiv (q.symm i₀)).val =
      (p.comparison.vertexEquiv (q.symm i₀)).val at h
    rw [hval, Equiv.apply_symm_apply, hσ] at h
    exact hi₀ (e.symm.injective h)
  have hfixed3 (τ : SeparableClosure k ≃ₐ[k] SeparableClosure k) :
      d.star τ (e.symm 3) = e.symm 3 := by
    let f (j : Fin 6) := e (d.star τ (e.symm j))
    have hf (i j : Fin 6) : CartanMatrix.E 6 (f i) (f j) = CartanMatrix.E 6 i j := by
      rw [← hE, d.cartan_star, hE]
      simp
    apply e.injective
    rcases Langlands.CartanE6Root.eq_id_or_symmetry_of_preserves f hf with hid | hsym
    · rw [Equiv.apply_symm_apply]
      exact hid 3
    · rw [Equiv.apply_symm_apply]
      exact (hsym 3).trans (by decide)
  let x := d.absoluteFundamentalCharacter hsc (e.symm 3)
  have hfix : d.pinning.IsStarFixedWeight x := by
    intro τ
    change (d.pinning.starAction τ).val.weightEquiv
      (d.absoluteFundamentalCharacter hsc (e.symm 3)) = _
    rw [d.absoluteFundamentalCharacter_star, hfixed3 τ]
  let μ : d.pinning.starFixedWeights := ⟨x, (d.pinning.mem_starFixedWeights _).mpr hfix⟩
  let η := p.leviComparison.starFixedRestriction
    (p.index.pinning.corootSpan_eq_top_of_simplyConnected (p.isSimplyConnected hsc)) μ
  have hzero : e.symm 3 ∈ d.zeroVertices := (hz _).mpr ⟨mid, by simp [hmid]⟩
  let v : d.zeroVertices := ⟨e.symm 3, hzero⟩
  have hv : p.comparison.vertexEquiv (q.symm mid) = v := by
    apply Subtype.ext
    rw [hval, Equiv.apply_symm_apply, hmid]
  refine ⟨η, ?_, ?_⟩
  · change p.leviComparison.weightRestriction x = _
    rw [p.leviComparison_weightRestriction]
    have h := p.comparison.weightRestriction_fundamentalWeight_zero
      (d.pinning_corootSpan_eq_top hsc)
      (p.index.pinning_corootSpan_eq_top (p.isSimplyConnected hsc))
      (p.comparison.vertexEquiv (q.symm mid))
    rw [Equiv.symm_apply_apply] at h
    change p.comparison.weightRestriction
        (d.absoluteFundamentalCharacter hsc (p.comparison.vertexEquiv (q.symm mid)).val) =
      p.index.absoluteFundamentalCharacter (p.isSimplyConnected hsc) (q.symm mid) at h
    rw [hv] at h
    exact h
  · exact (p.titsObstruction_eq hsc μ).symm.trans
      (d.pinning.titsObstruction_eq_zero_of_mem_rootSpan_unconditional hsc μ
        (typeE6_nodeWeight_mem_rootSpan d e hsc hE))

/-- Over a totally complex number field, the distinguished vertices `1` and `3` of the E6
index follow from the distinguished short-arm vertex and the nonvanishing of the middle Tits
class of anisotropic outer forms of type `A_{2m+1}`. -/
def NumberFieldTypeE6DistinguishedVerticesReductionStatement : Prop :=
  NumberFieldTotallyComplexTypeE6BranchDistinguishedStatement.{u} →
    NumberFieldTotallyComplexOuterTypeAMiddleObstructionStatement.{u} →
    NumberFieldTotallyComplexTypeE6DistinguishedVerticesStatement.{u}

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
/-- The distinguished short-arm vertex and the nonzero middle Tits class of anisotropic outer
type `A_{2m+1}` give the distinguished vertices `1` and `3` of every actual E6 index over a
totally complex number field. If `3` were not distinguished, the marking would be `{1}` or,
for an outer form, `{0, 1, 5}`; the inner marking `{1}` is impossible over every field, and
for the outer markings the anisotropic kernel of type `A_5` or `A_3` would have zero middle
obstruction. -/
theorem numberFieldTypeE6DistinguishedVerticesReduction :
    NumberFieldTypeE6DistinguishedVerticesReductionStatement.{u} := by
  classical
  intro hbranch houter K _ _ hK G _ _ d e hsc habs hE
  have h1 : e.symm 1 ∈ d.distinguishedVertices := hbranch K hK G d e hsc habs hE
  refine ⟨h1, ?_⟩
  by_contra h3
  obtain ⟨h2, h4, h50, hswap⟩ := typeE6NodeMarking K G d e hE hsc h1 h3
  let p := d.anisotropicKernelIndex
  by_cases h0 : e.symm 0 ∈ d.distinguishedVertices
  · -- Outer form with the endpoints marked: the kernel has type `A_3`.
    obtain ⟨σ, hσ⟩ := hswap h0
    have h5 : e.symm 5 ∈ d.distinguishedVertices := h50.mpr h0
    have hz (a : d.Vertex) : a ∈ d.zeroVertices ↔ ∃ i, (![2, 3, 4] : Fin 3 → Fin 6) i = e a := by
      have hd : a ∈ d.zeroVertices ↔ a ∉ d.distinguishedVertices := by
        simp [TitsIndexData.distinguishedVertices]
      rw [hd]
      obtain ⟨j, rfl⟩ := e.symm.surjective a
      rw [Equiv.apply_symm_apply]
      fin_cases j <;> simp [h0, h1, h2, h3, h4, h5] <;> decide
    obtain ⟨hsimple, q, hD, hstar, w, hw, hobs⟩ :=
      outerKernel_middle d e hsc hE (n := 2) ![2, 3, 4] (by decide) hz (by decide)
        1 (by decide) 0 (by decide) σ hσ
    exact houter K hK p.kernel p.index 1 q (p.isSimplyConnected hsc) hsimple hD hstar
      p.anisotropic w hw hobs
  · -- Only the short-arm vertex is marked.
    have h5 : e.symm 5 ∉ d.distinguishedVertices := fun h => h0 (h50.mp h)
    have hmarks (a : d.Vertex) : a ∈ d.distinguishedVertices ↔ (e a).val = 1 := by
      obtain ⟨j, rfl⟩ := e.symm.surjective a
      rw [Equiv.apply_symm_apply]
      fin_cases j <;> simp [h0, h1, h2, h3, h4, h5]
    by_cases htriv : d.StarIsTrivial
    · exact d.not_hasRankOneE6BranchIndex hsc ⟨⟨e, hE, hmarks⟩, htriv⟩
    · -- Outer form: the kernel has type `A_5`.
      obtain ⟨σ, a, ha⟩ : ∃ (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K) (a : d.Vertex),
          d.star σ a ≠ a := by
        by_contra hn
        push Not at hn
        exact htriv hn
      have hσ : ∀ j, d.star σ (e.symm j) = e.symm (Langlands.CartanE6Root.symmetry j) := by
        let f (j : Fin 6) := e (d.star σ (e.symm j))
        have hf (i j : Fin 6) : CartanMatrix.E 6 (f i) (f j) = CartanMatrix.E 6 i j := by
          rw [← hE, d.cartan_star, hE]
          simp
        rcases Langlands.CartanE6Root.eq_id_or_symmetry_of_preserves f hf with hid | hsym
        · exfalso
          apply ha
          have h := hid (e a)
          simpa [f] using congrArg e.symm h
        · intro j
          apply e.injective
          simpa [f] using hsym j
      have hz (a : d.Vertex) :
          a ∈ d.zeroVertices ↔ ∃ i, (![0, 2, 3, 4, 5] : Fin 5 → Fin 6) i = e a := by
        have hd : a ∈ d.zeroVertices ↔ a ∉ d.distinguishedVertices := by
          simp [TitsIndexData.distinguishedVertices]
        rw [hd, hmarks]
        generalize e a = j
        fin_cases j <;> decide
      obtain ⟨hsimple, q, hD, hstar, w, hw, hobs⟩ :=
        outerKernel_middle d e hsc hE (n := 4) ![0, 2, 3, 4, 5] (by decide) hz (by decide)
          2 (by decide) 0 (by decide) σ hσ
      exact houter K hK p.kernel p.index 2 q (p.isSimplyConnected hsc) hsimple hD hstar
        p.anisotropic w hw hobs

end Langlands.GroupScheme
