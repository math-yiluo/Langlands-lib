import Langlands.Representation.Hecke.IwahoriHeckeDecompositionStatement
import Langlands.Representation.Hecke.IwahoriHeckeCore
import Langlands.BruhatTits.Cartan.AvailableCartanProof
import Langlands.BruhatTits.SpecialCompact.AvailableCompactCore
import Langlands.Representation.Jacquet.StandardCasselmanUniformAsymptotics
import Langlands.Representation.Jacquet.StandardCentralContraction
import Langlands.Representation.Plancherel.RenardDominantValuation
import Langlands.Geometry.Building.CocharacterUniformizerProof
import Langlands.GroupScheme.Rational.RootSupportFiniteness

/-!
# Proof of Renard V.5.3 for actual reductive groups

The theorem `iwahoriHeckeDecomposition` proves the published proposition
`IwahoriHeckeDecompositionStatement`. It instantiates the group-theoretic core
`Langlands.Representation.Hecke.IwahoriHeckeCore` with the minimal standard parabolic `P_∅`:
the Iwahori factorization and contraction clauses of the `J = ∅` basis member, the uniformizer
powers `ϖ^y = i(y(ϖ))` (dominant ones lie in the chambers `C_A` and `C_A^+` of the split
component), the finite lattice transversal `F₀`, and the Cartan decomposition
`G = P_x j(Z(F)^+) P_x`, which gives `G = K₀ j(C̃⁺) K₀`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Hecke

open HeckeAlgebra.Corner

set_option maxHeartbeats 1000000 in
/-- **Renard V.5.3.** The two product Lemmas, the Corollary, the finiteness Lemma (module
form, both sides), the Theorem `H(G, K) = ∑ H₀ A D_k H₀` and the Remark, together with the
finite-dimensional subalgebra `H₀ = H(K₀, K)`. -/
theorem iwahoriHeckeDecomposition : IwahoriHeckeDecompositionStatement.{u} := by
  intro F _ _ _ _ G hG
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : Smooth G.X.hom := hG.smooth
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  intro _ _ _ 𝔅 h𝔅 B ν hν x hx K₀ K hK hKK₀ hnorm hbasis F₀ hF₀ haar _ j dom Cplus Ctilde a
  classical
  -- basic structure
  have hi : IsMaximalSplitTorus B.i := B.isMaximalSplitTorus
  have hΦ : (positiveRelativeRoots B.i ν).Finite :=
    hi.isSplitSubtorus.1.finite_positiveRelativeRoots B.i ν
  have : Finite (positiveRelativeRoots B.i ν) := hΦ.to_subtype
  have : Finite F₀ := hF₀.1.to_subtype
  have hK₀c : IsCompact (K₀ : Set (rationalPoints G)) :=
    (BruhatTits.SpecialCompact.availableCompactCore (𝔅.datum F G hG) h𝔅.groupAxioms ν hν x
      hx).2.1.1
  -- the minimal parabolic and its basis member
  obtain ⟨A, q, hA, hIw, hcon⟩ := hbasis ∅ (Set.empty_subset _)
  have hstd : IsStandardCocharacter B.i ν ∅ ν :=
    ⟨Set.empty_subset _, by simp, fun α hα _ => hα.1.2⟩
  let c : cocharacterLattice B.S → rationalPoints G := fun y =>
    Aubert.General.uniformizerPowers B.i (.ofAdd y)
  have hchamber : ∀ y : cocharacterLattice B.S,
      (∀ α ∈ positiveRelativeRoots B.i ν, 0 ≤ latticePairing B.S α y) →
      c y ∈ BruhatTits.SpecialCompact.standardComponentCA B.i q ∧
        c y ∈ BruhatTits.SpecialCompact.standardComponentCAplus B.i ν ∅ q := fun y hy =>
    BruhatTits.SpecialCompact.uniformizerPowers_mem_standardComponentChambers hi ⟨ν, hstd⟩ hA y
      (fun _ h => by simp at h) (fun β hβ => hy β hβ.1)
  -- the Iwahori factorization and contraction data of `K` for `P_∅`
  let M := standardLeviPoints B.i ν ∅
  let N := standardUnipotentPoints B.i ν ∅
  let Nb := BruhatTits.SpecialCompact.standardOppositeUnipotentPoints B.i ν ∅
  have hdec : ∀ k ∈ K, ∃ n ∈ ((K.toSubgroup ⊓ N : Subgroup (rationalPoints G)) : Set _),
      ∃ m ∈ ((K.toSubgroup ⊓ M : Subgroup (rationalPoints G)) : Set _),
      ∃ nb ∈ ((K.toSubgroup ⊓ Nb : Subgroup (rationalPoints G)) : Set _), k = n * m * nb := by
    intro k hk
    obtain ⟨⟨nb, m, n⟩, hprod⟩ := hIw.2 ⟨k⁻¹, K.inv_mem hk⟩
    have h : (nb : rationalPoints G) * m * n = k⁻¹ := congrArg Subtype.val hprod
    refine ⟨(n : rationalPoints G)⁻¹, inv_mem n.2, (m : rationalPoints G)⁻¹, inv_mem m.2,
      (nb : rationalPoints G)⁻¹, inv_mem nb.2, ?_⟩
    rw [← inv_inv k, ← h]
    group
  have hconjM : ∀ y : cocharacterLattice B.S,
      (∀ α ∈ positiveRelativeRoots B.i ν, 0 ≤ latticePairing B.S α y) →
      ∀ m ∈ ((K.toSubgroup ⊓ M : Subgroup (rationalPoints G)) : Set _),
        c y * m * (c y)⁻¹ ∈ K ∧ (c y)⁻¹ * m * c y ∈ K := by
    intro y hy m hm
    have heq := hcon.1 (c y) (hchamber y hy).1
    constructor
    · have hm' : c y * m * (c y)⁻¹ ∈
          ((K.toSubgroup ⊓ M : Subgroup (rationalPoints G)) : Set _) := by
        rw [← heq]
        exact ⟨m, hm, rfl⟩
      exact (Subgroup.mem_inf.1 hm').1
    · rw [← heq] at hm
      obtain ⟨m', hm', rfl⟩ := hm
      have h : (c y)⁻¹ * (c y * m' * (c y)⁻¹) * c y = m' := by group
      rw [h]
      exact (Subgroup.mem_inf.1 hm').1
  have hconjN : ∀ y : cocharacterLattice B.S,
      (∀ α ∈ positiveRelativeRoots B.i ν, 0 ≤ latticePairing B.S α y) →
      ∀ n ∈ ((K.toSubgroup ⊓ N : Subgroup (rationalPoints G)) : Set _),
        c y * n * (c y)⁻¹ ∈ ((K.toSubgroup ⊓ N : Subgroup (rationalPoints G)) : Set _) :=
    fun y hy n hn => (hcon.2.1 (c y) (hchamber y hy).2).1 ⟨n, hn, rfl⟩
  have hconjNb : ∀ y : cocharacterLattice B.S,
      (∀ α ∈ positiveRelativeRoots B.i ν, 0 ≤ latticePairing B.S α y) →
      ∀ nb ∈ ((K.toSubgroup ⊓ Nb : Subgroup (rationalPoints G)) : Set _),
        (c y)⁻¹ * nb * c y ∈ ((K.toSubgroup ⊓ Nb : Subgroup (rationalPoints G)) : Set _) := by
    intro y hy nb hnb
    have h := (hcon.2.1 (c y) (hchamber y hy).2).2 ⟨nb, hnb, rfl⟩
    simpa only [inv_inv] using h
  let L : IwahoriLatticeData K (cocharacterLattice B.S) (positiveRelativeRoots B.i ν) :=
    { Kn := ((K.toSubgroup ⊓ N : Subgroup (rationalPoints G)) : Set _)
      Km := ((K.toSubgroup ⊓ M : Subgroup (rationalPoints G)) : Set _)
      Knb := ((K.toSubgroup ⊓ Nb : Subgroup (rationalPoints G)) : Set _)
      Kn_subset := fun _ h => (Subgroup.mem_inf.1 h).1
      Km_subset := fun _ h => (Subgroup.mem_inf.1 h).1
      Knb_subset := fun _ h => (Subgroup.mem_inf.1 h).1
      decomp := hdec
      c := c
      c_add := fun y y' => by simp only [c, ofAdd_add, map_mul]
      pair := fun α => (latticePairing B.S α.1).toAddMonoidHom
      conj_Km := fun y hy => hconjM y fun α hα => hy ⟨α, hα⟩
      conj_Kn := fun y hy => hconjN y fun α hα => hy ⟨α, hα⟩
      conj_Knb := fun y hy => hconjNb y fun α hα => hy ⟨α, hα⟩ }
  -- the centralizer side
  let σ : cocharacterLattice B.S → rationalPoints B.centralizer.Z := fun y =>
    rationalPoints.map B.centralizer.s
      (Plancherel.RenardCartan.uniformizerSection B.S (Multiplicative.ofAdd y))
  have hjs : ∀ y, j (σ y) = c y := by
    intro y
    change rationalPoints.map B.centralizer.j (rationalPoints.map B.centralizer.s _) =
      rationalPoints.map B.i _
    have h := B.centralizer.comp_eq
    calc rationalPoints.map B.centralizer.j (rationalPoints.map B.centralizer.s
          (Plancherel.RenardCartan.uniformizerSection B.S (Multiplicative.ofAdd y))) =
        rationalPoints.map (B.centralizer.s ≫ B.centralizer.j)
          (Plancherel.RenardCartan.uniformizerSection B.S (Multiplicative.ofAdd y)) := by
          simp only [rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc]
      _ = _ := by rw [h]
  let cv := BruhatTits.Cartan.centralizerValuation B.centralizer.s B.centralizer.bijective
  have hval : ∀ (y : cocharacterLattice B.S) (f : rationalPoints B.centralizer.Z)
      (α : characterLattice B.S),
      RealTorusSpace.eval B.S α (cv (σ y * f)).toAdd =
        (latticePairing B.S α y : ℝ) + RealTorusSpace.eval B.S α (cv f).toAdd := by
    intro y f α
    rw [map_mul, toAdd_mul, map_add,
      Plancherel.RenardCartan.centralizerValuation_uniformizerSection,
      RealTorusSpace.eval_tmul, one_mul]
  let fe : F₀ → rationalPoints G := fun f => j f.1
  let e : positiveRelativeRoots B.i ν → F₀ → ℝ := fun α f =>
    RealTorusSpace.eval B.S α.1 (cv f.1).toAdd
  have hCt : ∀ t', t' ∈ Ctilde ↔ ∃ y, ∃ f : F₀, t' = σ y * f.1 ∧
      ∀ α : positiveRelativeRoots B.i ν, 0 ≤ (L.pair α y : ℝ) + e α f := by
    intro t'
    constructor
    · rintro ⟨ht, hdom⟩
      obtain ⟨c', hc', f, hf, rfl⟩ := (Plancherel.RenardCartan.mem_tildeC0 _ _ _).1 ht
      obtain ⟨y, rfl⟩ := (Plancherel.RenardCartan.mem_C0 _ _ _).1 hc'
      refine ⟨y, ⟨f, hf⟩, rfl, fun α => ?_⟩
      have h := hdom α.1 α.2
      change 0 ≤ RealTorusSpace.eval B.S α.1 (cv (σ y * f)).toAdd at h
      rw [hval] at h
      exact h
    · rintro ⟨y, f, rfl, hadm⟩
      refine ⟨(Plancherel.RenardCartan.mem_tildeC0 _ _ _).2
        ⟨σ y, (Plancherel.RenardCartan.mem_C0 _ _ _).2 ⟨y, rfl⟩, f.1, f.2, rfl⟩, ?_⟩
      intro α hα
      change 0 ≤ RealTorusSpace.eval B.S α (cv (σ y * f.1)).toAdd
      rw [hval]
      exact hadm ⟨α, hα⟩
  have hCp : ∀ z, z ∈ Cplus ↔ ∃ y : cocharacterLattice B.S,
      (∀ α ∈ positiveRelativeRoots B.i ν, 0 ≤ latticePairing B.S α y) ∧ σ y = z := by
    intro z
    change z ∈ (Plancherel.RenardCartan.C0 B.S B.centralizer.s : Set _) ∩
      BruhatTits.Cartan.dominantCentralizer B.i ν B.centralizer.s B.centralizer.bijective ↔ _
    rw [← Plancherel.RenardCartan.C0Plus_eq_inter_dominant]
    exact Iff.rfl
  -- dominant uniformizer powers commute with `j(Z(F))`
  have hcomm : ∀ y, (∀ α, 0 ≤ L.pair α y) → ∀ f : F₀, Commute (L.c y) (fe f) := by
    intro y hy f
    obtain ⟨x', -, hx'⟩ := Subgroup.mem_map.1 (hchamber y fun α hα => hy ⟨α, hα⟩).1
    have hm : j f.1 ∈ standardLeviPoints B.i ν ∅ := by
      have h := map_mem_centralizerPoints B.centralizer.isRepresentedBy f.1
      rw [← torusCentralizer_carrier_base] at h
      exact torusCentralizer_le_standardLevi B.i ν ∅ _ h
    have h := hA.map_commute_standardLeviPoints B.i ν x' hm
    rw [hx'] at h
    exact h.symm
  -- `j(Z(F)^1) ⊆ K₀` and `P_x ⊆ K₀`
  have hjK₀ : ∀ u ∈ Plancherel.rationalCommonNormKernel B.centralizer.Z, j u ∈ K₀ :=
    fun u hu => B.isOmegaCompatible.map_mem_compactStabilizer hu x
  have hPK₀ : ∀ p ∈ B.parahoricAt x, p ∈ K₀ := fun p hp =>
    B.parahoricAt_le_compactStabilizer
      h𝔅.groupAxioms.affineRootSystem.apartmentAxioms.topologyCompatible x hp
  -- every dominant `d` is `t' u` with `t' ∈ C̃⁺` and `u ∈ Z(F)^1`
  have hdecomp : ∀ d ∈ dom, ∃ t' ∈ Ctilde,
      ∃ u ∈ Plancherel.rationalCommonNormKernel B.centralizer.Z, t' * u = d := by
    intro d hd
    let rr := (Plancherel.rationalCharacterValuation B.centralizer.Z).rangeRestrict
    obtain ⟨f, hf⟩ := hF₀.2.2 (Plancherel.RenardCartan.latticeResidue B.centralizer.s d)
    have hdiff : rr d / rr f.1 ∈ Plancherel.RenardCartan.splitValuationImage B.centralizer.s :=
      (QuotientGroup.eq_iff_div_mem
        (N := Plancherel.RenardCartan.splitValuationImage B.centralizer.s)).mp hf.symm
    obtain ⟨σ', hσ'⟩ := hdiff
    obtain ⟨y, hy, -⟩ := (CocharacterUniformizer.isUniformizerLatticeSection F B.S
      hi.isSplitSubtorus.1).2.2 σ'
    have hker : ∀ w ∈ Plancherel.rationalCommonNormKernel B.centralizer.Z, rr w = 1 := by
      intro w hw
      rw [← Plancherel.rationalCharacterValuation_ker] at hw
      exact Subtype.ext (MonoidHom.mem_ker.1 hw)
    have hσy : rr (σ y.toAdd) = rr d / rr f.1 := by
      rw [← hσ']
      have h1 := hker _ (map_mem_rationalCommonNormKernel B.centralizer.s hy)
      have h2 : rationalPoints.map B.centralizer.s σ' =
          rationalPoints.map B.centralizer.s
              (σ' * (CocharacterUniformizer.latticeSection F B.S y)⁻¹) *
            rationalPoints.map B.centralizer.s (CocharacterUniformizer.latticeSection F B.S y) := by
        rw [← map_mul, inv_mul_cancel_right]
      change rr (rationalPoints.map B.centralizer.s
        (CocharacterUniformizer.latticeSection F B.S y)) =
          rr (rationalPoints.map B.centralizer.s σ')
      rw [h2, map_mul, h1, one_mul]
    have hval' : rr (σ y.toAdd * f.1) = rr d := by
      rw [map_mul, hσy, div_mul_cancel]
    refine ⟨σ y.toAdd * f.1, ?_, (σ y.toAdd * f.1)⁻¹ * d, ?_, mul_inv_cancel_left _ _⟩
    · refine ⟨(Plancherel.RenardCartan.mem_tildeC0 _ _ _).2
        ⟨σ y.toAdd, (Plancherel.RenardCartan.mem_C0 _ _ _).2 ⟨y.toAdd, rfl⟩, f.1, f.2, rfl⟩, ?_⟩
      exact (Plancherel.RenardCartan.dominantCentralizer_mem_iff_of_characterValuation_eq
        B.centralizer.s B.centralizer.bijective B.i ν (congrArg Subtype.val hval')).2 hd
    · rw [← Plancherel.rationalCharacterValuation_ker, MonoidHom.mem_ker]
      have h : rr ((σ y.toAdd * f.1)⁻¹ * d) = 1 := by
        rw [map_mul, map_inv, hval', inv_mul_cancel]
      exact congrArg Subtype.val h
  -- the Cartan decomposition `G = K₀ j(C̃⁺) K₀`
  have hcartan : ∀ g : rationalPoints G, ∃ p₁ ∈ K₀, ∃ t ∈ j '' Ctilde, ∃ p₂ ∈ K₀,
      g = p₁ * t * p₂ := by
    intro g
    have hC := (BruhatTits.Cartan.parahoricCartanConclusions_of_satisfiesGroupAxioms
      (𝔅.datum F G hG) h𝔅.groupAxioms ν hν x hx).1
    have hg : g ∈ (Set.univ : Set (rationalPoints G)) := Set.mem_univ g
    rw [hC] at hg
    obtain ⟨w, hw, p₂, hp₂, rfl⟩ := Set.mem_mul.1 hg
    obtain ⟨p₁, hp₁, v, hv, rfl⟩ := Set.mem_mul.1 hw
    obtain ⟨d, hd, rfl⟩ := hv
    obtain ⟨t', ht', u, hu, rfl⟩ := hdecomp d hd
    have hp₁' : p₁ ∈ K₀ := hPK₀ p₁ hp₁
    have hp₂' : p₂ ∈ K₀ := hPK₀ p₂ hp₂
    have hu' : j u ∈ K₀ := hjK₀ u hu
    refine ⟨p₁, hp₁', j t', ⟨t', ht', rfl⟩, j u * p₂, K₀.mul_mem hu' hp₂', ?_⟩
    change p₁ * j (t' * u) * p₂ = p₁ * j t' * (j u * p₂)
    rw [map_mul]
    group
  -- item 3
  have h3 : ∀ z₁ ∈ Cplus, ∀ z₂ ∈ Cplus, a (j z₁) * a (j z₂) = a (j (z₁ * z₂)) := by
    intro z₁ hz₁ z₂ hz₂
    obtain ⟨y₁, hy₁, rfl⟩ := (hCp z₁).1 hz₁
    obtain ⟨y₂, hy₂, rfl⟩ := (hCp z₂).1 hz₂
    have h := L.massIndicator_mul_dominant hK haar (fun α => hy₁ α.1 α.2)
      (fun α => hy₂ α.1 α.2)
    rw [L.c_add] at h
    rw [map_mul, hjs, hjs]
    exact h
  have hσcomm : ∀ y₁ y₂, σ y₁ * σ y₂ = σ y₂ * σ y₁ := by
    intro y₁ y₂
    simp only [σ, ← map_mul, mul_comm]
  -- item 5 and item 7 finiteness data
  have hspan : ∀ S : Set (HeckeAlgebra.Corner haar K hK),
      (∀ t' ∈ Ctilde, a (j t') ∈ Submodule.span ℂ S) →
      Submodule.span ℂ {u | ∃ x₁ ∈ K₀, ∃ s ∈ S, ∃ x₂ ∈ K₀, u = a x₁ * s * a x₂} = ⊤ :=
    fun S hS => span_sandwich_eq_top K hK haar K₀ hnorm (j '' Ctilde) hcartan S
      (by rintro _ ⟨t', ht', rfl⟩; exact hS t' ht')
  refine ⟨⟨?_, ?_, ?_⟩, ?_, h3, ?_, ?_, ?_, ?_⟩
  -- item 1
  · exact FiniteDimensional.span_of_finite ℂ (finite_image_massIndicator K hK haar hK₀c)
  · exact (linearIndepOn_range_massIndicator K hK haar).mono (Set.image_subset_range _ _)
  · intro x₁ hx₁ x₂ hx₂
    change massIndicator K hK haar x₁ = massIndicator K hK haar x₂ ↔ _
    rw [massIndicator_eq_iff, TestFunction.mem_doubleCosetSet]
    constructor
    · rintro ⟨k₁, hk₁, k₂, hk₂, h⟩
      have h' : x₁⁻¹ * x₂ = k₂⁻¹ * (x₂⁻¹ * k₁⁻¹ * x₂⁻¹⁻¹) := by
        rw [h]
        group
      rw [h']
      exact K.mul_mem (K.inv_mem hk₂) (hnorm _ (K₀.inv_mem hx₂) _ (K.inv_mem hk₁))
    · intro h
      refine ⟨1, K.one_mem, x₂⁻¹ * x₁, ?_, by group⟩
      simpa using K.inv_mem h
  -- item 2
  · intro g x₁ hx₁
    refine ⟨massIndicator_mul_of_normalizes K hK haar fun k hk => ?_,
      massIndicator_mul_of_normalizes' K hK haar (hnorm x₁ hx₁)⟩
    simpa using hnorm _ (K₀.inv_mem hx₁) k hk
  -- item 4
  · have hgen : ∀ u ∈ a '' (j '' Cplus), ∀ v ∈ a '' (j '' Cplus), Commute u v := by
      rintro _ ⟨_, ⟨z₁, hz₁, rfl⟩, rfl⟩ _ ⟨_, ⟨z₂, hz₂, rfl⟩, rfl⟩
      change a (j z₁) * a (j z₂) = a (j z₂) * a (j z₁)
      rw [h3 z₁ hz₁ z₂ hz₂, h3 z₂ hz₂ z₁ hz₁]
      obtain ⟨y₁, -, rfl⟩ := (hCp z₁).1 hz₁
      obtain ⟨y₂, -, rfl⟩ := (hCp z₂).1 hz₂
      rw [hσcomm]
    intro u hu v hv
    exact (Algebra.commute_of_mem_adjoin_of_forall_mem_commute hv fun w hw =>
      (Algebra.commute_of_mem_adjoin_of_forall_mem_commute hu fun w' hw' =>
        hgen w hw w' hw').symm).eq
  -- item 5
  · obtain ⟨T, hTfin, hTadm, hT⟩ := L.exists_finite_left hK haar fe e
    let emb : cocharacterLattice B.S × F₀ → rationalPoints B.centralizer.Z :=
      fun p => σ p.1 * p.2.1
    obtain ⟨n, t, ht⟩ := (hTfin.image emb).fin_embedding
    refine ⟨n, t, fun k => ?_, ?_⟩
    · have hk : t k ∈ emb '' T := ht ▸ Set.mem_range_self k
      obtain ⟨p, hp, hpk⟩ := hk
      rw [← hpk]
      exact (hCt _).2 ⟨p.1, p.2, rfl, hTadm p hp⟩
    · intro t' ht'
      obtain ⟨y, f, rfl, hadm⟩ := (hCt t').1 ht'
      obtain ⟨p, hp, z, hz, heq⟩ := hT y f hadm
      have hk : emb p ∈ Set.range t := ht ▸ Set.mem_image_of_mem emb hp
      obtain ⟨k, hk⟩ := hk
      apply Submodule.subset_span
      refine ⟨σ z, (hCp _).2 ⟨z, fun α hα => hz ⟨α, hα⟩, rfl⟩, k, ?_⟩
      rw [hk]
      simp only [emb, map_mul, hjs]
      exact heq.symm
  -- item 6
  · intro n D hD
    have h := hspan {y | ∃ z ∈ Cplus, ∃ k, y = a (j z) * D k} hD
    rw [eq_top_iff] at h ⊢
    refine h.trans (Submodule.span_mono ?_)
    rintro _ ⟨x₁, hx₁, _, ⟨z, hz, k, rfl⟩, x₂, hx₂, rfl⟩
    exact ⟨x₁, hx₁, z, hz, k, x₂, hx₂, by simp only [mul_assoc]⟩
  -- item 7
  · obtain ⟨T, hTfin, hTadm, hT⟩ := L.exists_finite_right hK haar fe e hcomm
    let emb : cocharacterLattice B.S × F₀ → rationalPoints B.centralizer.Z :=
      fun p => σ p.1 * p.2.1
    obtain ⟨n, t, ht⟩ := (hTfin.image emb).fin_embedding
    have hmem : ∀ t' ∈ Ctilde, a (j t') ∈ Submodule.span ℂ
        {y | ∃ z ∈ Cplus, ∃ k, y = a (j (t k)) * a (j z)} := by
      intro t' ht'
      obtain ⟨y, f, rfl, hadm⟩ := (hCt t').1 ht'
      obtain ⟨p, hp, z, hz, heq⟩ := hT y f hadm
      have hk : emb p ∈ Set.range t := ht ▸ Set.mem_image_of_mem emb hp
      obtain ⟨k, hk⟩ := hk
      apply Submodule.subset_span
      refine ⟨σ z, (hCp _).2 ⟨z, fun α hα => hz ⟨α, hα⟩, rfl⟩, k, ?_⟩
      rw [hk]
      simp only [emb, map_mul, hjs]
      exact heq.symm
    refine ⟨n, t, fun k => ?_, hmem, ?_⟩
    · have hk : t k ∈ emb '' T := ht ▸ Set.mem_range_self k
      obtain ⟨p, hp, hpk⟩ := hk
      rw [← hpk]
      exact (hCt _).2 ⟨p.1, p.2, rfl, hTadm p hp⟩
    · have h := hspan {y | ∃ z ∈ Cplus, ∃ k, y = a (j (t k)) * a (j z)} hmem
      rw [eq_top_iff] at h ⊢
      refine h.trans (Submodule.span_mono ?_)
      rintro _ ⟨x₁, hx₁, _, ⟨z, hz, k, rfl⟩, x₂, hx₂, rfl⟩
      exact ⟨x₁, hx₁, k, z, hz, x₂, hx₂, by simp only [mul_assoc]⟩

end Langlands.Hecke
