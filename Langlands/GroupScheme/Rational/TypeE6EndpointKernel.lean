import Langlands.LinearAlgebra.CartanE6Root
import Langlands.GroupScheme.SimplyConnected.FactorCartanComponent
import Langlands.GroupScheme.SimplyConnected.TitsObstructionRootVanishing
import Langlands.GroupScheme.Reductive.SeparablyClosedAlmostSimpleAbsoluteProof
import Langlands.GroupScheme.Reductive.SplitLeviTitsComparison
import Langlands.GroupScheme.SimplyConnected.StarOrbitWeights

/-! # The D4 kernel of the endpoint-marked E6 index -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped BigOperators

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false in
private theorem absolutelyAlmostSimple_of_connectedCartan
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

private theorem typeE6_branchWeight_mem_rootSpan
    {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (d : TitsIndexData G) (e : d.Vertex ≃ Fin 6) (hsc : IsSimplyConnected G)
    (hE : ∀ a b, d.cartan a b = CartanMatrix.E 6 (e a) (e b)) :
    d.absoluteFundamentalCharacter hsc (e.symm 1) ∈ d.pinning.rootDatum.rootSpan ℤ := by
  classical
  let P := d.pinning.rootDatum
  let a (i : Fin 6) : d.pinning.rootIndex := (e.symm i).val
  have hnumb (i j : Fin 6) : P.pairing (a i) (a j) = CartanMatrix.E 6 i j := by
    change d.cartan (e.symm i) (e.symm j) = _
    simpa using hE (e.symm i) (e.symm j)
  have hsum : ∀ j : Fin 6, (∑ i : Fin 6, Langlands.CartanE6Root.coefficients i *
      CartanMatrix.E 6 i j) = if j = 1 then 1 else 0 := by decide
  have hx : d.absoluteFundamentalCharacter hsc (e.symm 1) =
      ∑ i : Fin 6, Langlands.CartanE6Root.coefficients i • P.root (a i) := by
    apply IntegralWeylVector.eq_of_pairing_simple_eq P d.pinning.base
      (d.pinning_corootSpan_eq_top hsc)
    intro b
    let j := e b
    have hj : b = e.symm j := (e.symm_apply_apply b).symm
    rw [hj]
    change P.toLinearMap (d.absoluteFundamentalCharacter hsc (e.symm 1)) (P.coroot (a j)) = _
    rw [show P.toLinearMap (d.absoluteFundamentalCharacter hsc (e.symm 1)) (P.coroot (a j)) =
        (if e.symm j = e.symm 1 then 1 else 0) from
      Langlands.RootDatum.fundamentalWeightBasis_pairing P d.pinning.base _ _ _]
    simp only [Equiv.apply_eq_iff_eq, map_sum, LinearMap.sum_apply, map_zsmul,
      LinearMap.smul_apply, zsmul_eq_mul, P.root_coroot_eq_pairing]
    change (if j = 1 then 1 else 0) =
      ∑ i, Langlands.CartanE6Root.coefficients i * P.pairing (a i) (a j)
    simpa only [hnumb] using (hsum j).symm
  rw [hx]
  exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _
    (Submodule.subset_span (Set.mem_range_self (a i))))

/-- The actual kernel of the E6 index marked at the two long-arm endpoints
is simply connected and absolutely almost simple of classical type D4.
The nonfork vertices are fixed by the full star action, and the Tits
obstruction vanishes at the vector fundamental weight. -/
def TypeE6EndpointKernelStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (d : TitsIndexData G) (e : d.Vertex ≃ Fin 6)
    (hsc : IsSimplyConnected G),
    (∀ a b, d.cartan a b = CartanMatrix.E 6 (e a) (e b)) →
    (∀ a, a ∈ d.distinguishedVertices ↔ e a = 0 ∨ e a = 5) →
    let p := d.anisotropicKernelIndex
    IsAbsolutelyAlmostSimple p.kernel ∧
      ∃ q : p.index.Vertex ≃ Fin 4,
        (∀ a b, p.index.cartan a b = CartanMatrix.D 4 (q a) (q b)) ∧
        (∀ (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k) (a : p.index.Vertex),
          (q a).val + 2 < 4 → p.index.star σ a = a) ∧
        ∃ weight : p.index.pinning.starFixedWeights,
          weight.val = p.index.absoluteFundamentalCharacter (p.isSimplyConnected hsc) (q.symm 0) ∧
          p.index.pinning.titsObstruction (p.isSimplyConnected hsc) weight = 0

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 2000000 in
theorem typeE6EndpointKernel : TypeE6EndpointKernelStatement.{u} := by
  classical
  intro k _ G _ _ d e hsc hE hmark p
  let ea (i : Fin 6) := e.symm i
  have hfixed (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k) (i : Fin 6)
      (hi : i = 1 ∨ i = 3) : d.star σ (ea i) = ea i := by
    let f (i : Fin 6) := e (d.star σ (ea i))
    have hf (i j : Fin 6) : CartanMatrix.E 6 (f i) (f j) = CartanMatrix.E 6 i j := by
      rw [← hE, d.cartan_star, hE]
      simp [ea]
    apply e.injective
    rcases Langlands.CartanE6Root.eq_id_or_symmetry_of_preserves f hf with hid | hsym
    · simpa [f, ea] using hid i
    · rcases hi with rfl | rfl
      · exact (hsym 1).trans ((by decide : Langlands.CartanE6Root.symmetry 1 = 1).trans
          (e.apply_symm_apply 1).symm)
      · exact (hsym 3).trans ((by decide : Langlands.CartanE6Root.symmetry 3 = 3).trans
          (e.apply_symm_apply 3).symm)
  have hz (a : d.Vertex) : a ∈ d.zeroVertices ↔ e a ≠ 0 ∧ e a ≠ 5 := by
    simpa only [TitsIndexData.distinguishedVertices, Set.mem_compl_iff, not_not, not_or]
      using not_congr (hmark a)
  let eZero : d.zeroVertices ≃ {j : Fin 6 // j ≠ 0 ∧ j ≠ 5} := Equiv.subtypeEquiv e hz
  let δ : Fin 4 → Fin 6 := ![1, 3, 2, 4]
  have hδ (i : Fin 4) : δ i ≠ 0 ∧ δ i ≠ 5 := by
    have h : ∀ i : Fin 4, δ i ≠ 0 ∧ δ i ≠ 5 := by decide
    exact h i
  let z : Fin 4 ≃ {j : Fin 6 // j ≠ 0 ∧ j ≠ 5} :=
    Equiv.ofBijective (fun i => ⟨δ i, hδ i⟩) (by
      constructor
      · have hi : ∀ i j : Fin 4, δ i = δ j → i = j := by decide
        exact fun i j h => hi i j (congrArg Subtype.val h)
      · have hs : ∀ j : Fin 6, j ≠ 0 → j ≠ 5 → ∃ i : Fin 4, δ i = j := by decide
        rintro ⟨j, h₀, h₅⟩
        obtain ⟨i, hi⟩ := hs j h₀ h₅
        exact ⟨i, Subtype.ext hi⟩)
  let q : p.index.Vertex ≃ Fin 4 := p.comparison.vertexEquiv.trans (eZero.trans z.symm)
  have hq (a : p.index.Vertex) : e (p.comparison.vertexEquiv a).val = δ (q a) :=
    (congrArg Subtype.val (z.apply_symm_apply (eZero (p.comparison.vertexEquiv a)))).symm
  have hD (a b : p.index.Vertex) : p.index.cartan a b = CartanMatrix.D 4 (q a) (q b) := by
    rw [← p.comparison.vertexEquiv_cartan, hE, hq a, hq b]
    have h : ∀ i j : Fin 4, CartanMatrix.E 6 (δ i) (δ j) = CartanMatrix.D 4 i j := by decide
    exact h _ _
  have hstar (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k) (a : p.index.Vertex)
      (ha : (q a).val + 2 < 4) : p.index.star σ a = a := by
    have hδfix : ∀ i : Fin 4, i.val + 2 < 4 → δ i = 1 ∨ δ i = 3 := by decide
    apply p.comparison.vertexEquiv.injective
    rw [p.comparison.vertexEquiv_star]
    apply Subtype.ext
    change d.star σ (p.comparison.vertexEquiv a).val = _
    have hn : (p.comparison.vertexEquiv a).val = ea (δ (q a)) := e.injective
      (by simpa [ea] using hq a)
    rw [hn]
    exact hfixed σ _ (hδfix _ ha)
  have hconn (b : p.index.Vertex) : p.index.CartanConnected (q.symm 1) b := by
    apply p.index.cartanConnected_of_cartan_ne_zero
    rw [hD, q.apply_symm_apply]
    have hrow : ∀ i : Fin 4, CartanMatrix.D 4 1 i ≠ 0 := by decide
    exact hrow _
  refine ⟨absolutelyAlmostSimple_of_connectedCartan (p.isSimplyConnected hsc)
    p.index (q.symm 1) hconn, q, hD, hstar, ?_⟩
  let x := d.absoluteFundamentalCharacter hsc (ea 1)
  have hfix : d.pinning.IsStarFixedWeight x := by
    intro σ
    change (d.pinning.starAction σ).val.weightEquiv (d.absoluteFundamentalCharacter hsc (ea 1)) = _
    rw [d.absoluteFundamentalCharacter_star, hfixed σ 1 (Or.inl rfl)]
  let μ : d.pinning.starFixedWeights := ⟨x, (d.pinning.mem_starFixedWeights _).mpr hfix⟩
  let η := p.leviComparison.starFixedRestriction
    (p.index.pinning_corootSpan_eq_top (p.isSimplyConnected hsc)) μ
  have hzero : (ea 1) ∈ d.zeroVertices := (hz _).mpr (by simp [ea])
  let v : d.zeroVertices := ⟨ea 1, hzero⟩
  have hv : p.comparison.vertexEquiv (q.symm 0) = v := by
    apply Subtype.ext
    apply e.injective
    rw [hq, q.apply_symm_apply]
    simp [δ, v, ea]
  refine ⟨η, ?_, ?_⟩
  · change p.leviComparison.weightRestriction x = _
    rw [p.leviComparison_weightRestriction]
    have h := p.comparison.weightRestriction_fundamentalWeight_zero
      (d.pinning_corootSpan_eq_top hsc)
      (p.index.pinning_corootSpan_eq_top (p.isSimplyConnected hsc))
      (p.comparison.vertexEquiv (q.symm 0))
    rw [Equiv.symm_apply_apply] at h
    change p.comparison.weightRestriction
        (d.absoluteFundamentalCharacter hsc (p.comparison.vertexEquiv (q.symm 0)).val) =
      p.index.absoluteFundamentalCharacter (p.isSimplyConnected hsc) (q.symm 0) at h
    rw [hv] at h
    exact h
  · exact (p.titsObstruction_eq hsc μ).symm.trans
      (d.pinning.titsObstruction_eq_zero_of_mem_rootSpan_unconditional hsc μ
        (typeE6_branchWeight_mem_rootSpan d e hsc hE))

end Langlands.GroupScheme
