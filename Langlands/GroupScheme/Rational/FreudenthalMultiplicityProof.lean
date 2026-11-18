import Langlands.GroupScheme.Rational.FreudenthalMultiplicityStatement
import Langlands.GroupScheme.Rational.PairLieWeightDataProof
import Langlands.GroupScheme.Rational.HighestWeightRootEndpoint
import Langlands.GroupScheme.Rational.PathFundamentalWeights
import Langlands.GroupScheme.Rational.SplitTorusIsogenyCocharacterLinear
import Langlands.GroupScheme.Reductive.GroundFieldRadical
import Langlands.GroupScheme.Reductive.UnipotentFieldExtensionProof
import Langlands.GroupScheme.Reductive.CharZeroSemisimplicity.TangentStability
import Langlands.GroupScheme.AffineLinearEmbeddingProof
import Langlands.GroupScheme.Torus.SurjectionIsogenySectionProof
import Langlands.LinearAlgebra.FreudenthalCasimirCore
import Langlands.LinearAlgebra.SimpleReflectionWords

/-! # Freudenthal's multiplicity formula for a split reductive group in characteristic zero

The proof instantiates the abstract recursion `LinearAlgebra.FreudenthalCasimirCoreStatement`
(proved in `Langlands.LinearAlgebra.FreudenthalCasimirCore`) with the pair Lie algebra of a
closed linear embedding `σ` of the group and the given highest-weight representation `r`,
acting on the product of the two coordinate spaces, and with the irreducible subspace
`0 × kⁿ`. The group-side hypotheses come from `pairLieWeightDataStatement`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Module

attribute [local instance 100] LieRing.ofAssociativeRing

namespace Langlands.GroupScheme

namespace FreudenthalMultiplicity

variable {k : Type*} [Field k] {M M' X : Type*} [AddCommGroup M] [Module k M]
  [AddCommGroup M'] [Module k M']

/-- Componentwise independent families give an independent family of products. -/
theorem iSupIndep_prod {A : X → Submodule k M} {B : X → Submodule k M'} (hA : iSupIndep A)
    (hB : iSupIndep B) : iSupIndep fun μ => (A μ).prod (B μ) := by
  intro μ
  dsimp only
  rw [Submodule.disjoint_def]
  rintro ⟨u, w⟩ hμ hsup
  have hle : (⨆ (ν) (_ : ν ≠ μ), (A ν).prod (B ν)) ≤
      (⨆ (ν) (_ : ν ≠ μ), A ν).prod (⨆ (ν) (_ : ν ≠ μ), B ν) := by
    refine iSup₂_le fun ν hν x hx => Submodule.mem_prod.mpr ⟨?_, ?_⟩
    · exact (le_iSup₂_of_le ν hν le_rfl : A ν ≤ ⨆ (ν) (_ : ν ≠ μ), A ν)
        (Submodule.mem_prod.mp hx).1
    · exact (le_iSup₂_of_le ν hν le_rfl : B ν ≤ ⨆ (ν) (_ : ν ≠ μ), B ν)
        (Submodule.mem_prod.mp hx).2
  obtain ⟨hu, hw⟩ := Submodule.mem_prod.mp (hle hsup)
  obtain ⟨hu', hw'⟩ := Submodule.mem_prod.mp hμ
  have h1 : u = 0 := Submodule.disjoint_def.mp (hA μ) u hu' hu
  have h2 : w = 0 := Submodule.disjoint_def.mp (hB μ) w hw' hw
  rw [h1, h2]
  rfl

/-- Componentwise spanning families give a spanning family of products. -/
theorem iSup_prod_eq_top {A : X → Submodule k M} {B : X → Submodule k M'}
    (hA : ⨆ μ, A μ = ⊤) (hB : ⨆ μ, B μ = ⊤) : ⨆ μ, (A μ).prod (B μ) = ⊤ := by
  have hl : ∀ u : M, (u, (0 : M')) ∈ ⨆ μ, (A μ).prod (B μ) := by
    intro u
    have hu : u ∈ ⨆ μ, A μ := by
      rw [hA]
      exact Submodule.mem_top
    refine Submodule.iSup_induction A
      (motive := fun u => (u, (0 : M')) ∈ ⨆ μ, (A μ).prod (B μ)) hu
      (fun μ u hu => Submodule.mem_iSup_of_mem μ (Submodule.mem_prod.mpr ⟨hu, zero_mem _⟩))
      (zero_mem _) (fun u u' h h' => ?_)
    simpa using add_mem h h'
  have hr : ∀ w : M', ((0 : M), w) ∈ ⨆ μ, (A μ).prod (B μ) := by
    intro w
    have hw : w ∈ ⨆ μ, B μ := by
      rw [hB]
      exact Submodule.mem_top
    refine Submodule.iSup_induction B
      (motive := fun w => ((0 : M), w) ∈ ⨆ μ, (A μ).prod (B μ)) hw
      (fun μ w hw => Submodule.mem_iSup_of_mem μ (Submodule.mem_prod.mpr ⟨zero_mem _, hw⟩))
      (zero_mem _) (fun w w' h h' => ?_)
    simpa using add_mem h h'
  rw [eq_top_iff]
  rintro ⟨u, w⟩ -
  simpa using add_mem (hl u) (hr w)

/-- The dimension of a product of submodules. -/
theorem finrank_prod_submodule [FiniteDimensional k M] [FiniteDimensional k M']
    (A : Submodule k M) (B : Submodule k M') :
    finrank k (A.prod B) = finrank k A + finrank k B := by
  rw [(Submodule.prodEquiv A B).finrank_eq, Module.finrank_prod]

/-- Intersecting a product with `0 × M'` keeps only the second factor. -/
theorem bot_prod_top_inf_prod (A : Submodule k M) (B : Submodule k M') :
    (⊥ : Submodule k M).prod ⊤ ⊓ A.prod B = (⊥ : Submodule k M).prod B := by
  ext ⟨u, w⟩
  simp only [Submodule.mem_inf, Submodule.mem_prod, Submodule.mem_bot, Submodule.mem_top,
    and_true]
  constructor
  · exact fun h => ⟨h.1, h.2.2⟩
  · rintro ⟨rfl, hw⟩
    exact ⟨rfl, zero_mem _, hw⟩

theorem finrank_bot_prod_top_inf_prod [FiniteDimensional k M] [FiniteDimensional k M']
    (A : Submodule k M) (B : Submodule k M') :
    finrank k ↥((⊥ : Submodule k M).prod ⊤ ⊓ A.prod B) = finrank k B := by
  rw [bot_prod_top_inf_prod, finrank_prod_submodule, finrank_bot, zero_add]

theorem bot_prod_top_inf_prod_eq_bot_iff (A : Submodule k M) (B : Submodule k M') :
    (⊥ : Submodule k M).prod ⊤ ⊓ A.prod B = ⊥ ↔ B = ⊥ := by
  rw [bot_prod_top_inf_prod, Submodule.prod_eq_bot_iff]
  simp

theorem prod_ne_bot_of_left {A : Submodule k M} {B : Submodule k M'} (hA : A ≠ ⊥) :
    A.prod B ≠ ⊥ := by
  rw [Ne, Submodule.prod_eq_bot_iff]
  exact fun h => hA h.1

end FreudenthalMultiplicity

open FreudenthalMultiplicity MatrixRepresentation Langlands.LinearAlgebra in
/-- **Freudenthal's multiplicity formula** for a split pinning of a group scheme over a field of
characteristic zero. The form is `GramDual.form` attached to the weight multiplicities of the
product of a closed linear embedding and the given representation. -/
theorem freudenthalMultiplicityStatement : FreudenthalMultiplicityStatement.{u} := by
  intro k _ _ G _ p n r lam hlam
  have hred := p.isConnectedReductive
  have : Smooth G.X.hom := hred.smooth
  have : ConnectedSpace G.X.left := hred.connectedSpace
  have : LocallyOfFiniteType G.X.hom := inferInstance
  have hrad : HasTrivialUnipotentRadical G :=
    hred.hasTrivialUnipotentRadical_of_unipotentFieldExtension unipotentFieldExtensionStatement
  obtain ⟨N, σ, hσ⟩ := affineLinearEmbeddingStatement k G inferInstance inferInstance
  obtain ⟨hgr, hcoch, hzero, hnonroot, hroot, hfaith⟩ :=
    pairLieWeightDataStatement k G p N n σ r hσ
  obtain ⟨hfree, hfin⟩ := TorusSurjectionIsogenySection.characterLattice_free_finite
    p.isSplitTorus
  have : IsAddTorsionFree (characterLattice p.torus) := .of_isTorsionFree ℤ _
  obtain ⟨I, hI, ⟨e⟩⟩ := p.isSplitTorus.exists_cocharacterCoordinates
  let _ : Fintype I := Fintype.ofFinite I
  classical
  let yb : Basis I ℤ (cocharacterLattice p.torus) := (Pi.basisFun ℤ I).map e.symm
  let P := p.rootDatum.toLinearMap
  let W := p.pairWeightSpace σ r
  let V : Submodule k ((Fin N → k) × (Fin n → k)) := (⊥ : Submodule k (Fin N → k)).prod ⊤
  let m : characterLattice p.torus → ℕ := fun ν => finrank k (W ν)
  have hWi : iSupIndep W := iSupIndep_prod (p.iSupIndep_representationWeightSpace σ)
    (p.iSupIndep_representationWeightSpace r)
  have hWt : ⨆ μ, W μ = ⊤ := iSup_prod_eq_top (p.iSup_representationWeightSpace_eq_top σ)
    (p.iSup_representationWeightSpace_eq_top r)
  have hfVW : ∀ μ, finrank k ↥(V ⊓ W μ) = finrank k (p.representationWeightSpace r μ) :=
    fun μ => finrank_bot_prod_top_inf_prod _ _
  have hVWbot : ∀ μ, V ⊓ W μ = ⊥ ↔ p.representationWeightSpace r μ = ⊥ :=
    fun μ => bot_prod_top_inf_prod_eq_bot_iff _ _
  have hY : ∀ y, y ≠ 0 → ∃ μ, W μ ≠ ⊥ ∧ P μ y ≠ 0 := by
    intro y hy
    obtain ⟨μ, hμ, hP⟩ := hfaith y hy
    exact ⟨μ, prod_ne_bot_of_left hμ, hP⟩
  have hm : (Function.support m).Finite := by
    refine (WeightGraded.finite_ne_bot hWi).subset fun ν hν h => hν ?_
    change finrank k (W ν) = 0
    rw [h, finrank_bot]
  have hmY : ∀ y, y ≠ 0 → ∃ ν, m ν ≠ 0 ∧ P ν y ≠ 0 := by
    intro y hy
    obtain ⟨μ, h1, h2⟩ := hY y hy
    exact ⟨μ, fun h => h1 (Submodule.finrank_eq_zero.mp h), h2⟩
  have hX : ∀ χ, χ ≠ 0 → ∃ y, P χ y ≠ 0 := by
    intro χ hχ
    by_contra h
    push Not at h
    refine hχ ((LinearMap.IsPerfPair.bijective_left P).injective ?_)
    rw [map_zero]
    exact LinearMap.ext h
  -- the subspace `0 × kⁿ` is stable and irreducible under the pair Lie algebra
  have hVstab : ∀ x ∈ pairLieAlgebra σ r, ∀ v ∈ V, x v ∈ V := by
    intro x hx v hv
    obtain ⟨X, rfl⟩ := (mem_pairLieAlgebra σ r x).mp hx
    obtain ⟨hv1, -⟩ := Submodule.mem_prod.mp hv
    rw [Submodule.mem_bot] at hv1
    refine Submodule.mem_prod.mpr ⟨?_, Submodule.mem_top⟩
    rw [pairTangent_apply, LinearMap.prodMap_apply, hv1, map_zero]
    exact Submodule.zero_mem _
  have hVirr : ∀ K : Submodule k ((Fin N → k) × (Fin n → k)), K ≤ V →
      (∀ x ∈ pairLieAlgebra σ r, ∀ v ∈ K, x v ∈ K) → K ≠ ⊥ → K = V := by
    intro K hKV hK hKne
    have hfst : ∀ u ∈ K, u.1 = 0 := fun u hu =>
      (Submodule.mem_bot k).mp (Submodule.mem_prod.mp (hKV hu)).1
    let K' : Submodule k (Fin n → k) := K.map (LinearMap.snd k (Fin N → k) (Fin n → k))
    have hK'stab : r.IsStableSubspace K' := by
      refine (isStableSubspace_iff_tangentMatrix r K').mpr fun Y v hv => ?_
      obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hv
      refine Submodule.mem_map.mpr ⟨pairTangent σ r (Additive.ofMul Y) u,
        hK _ ⟨_, rfl⟩ u hu, ?_⟩
      rw [pairTangent_apply, LinearMap.snd_apply, LinearMap.prodMap_apply, toMul_ofMul,
        Matrix.toLin'_apply]
      rfl
    rcases hlam.1.2 K' hK'stab with h | h
    · refine absurd ?_ hKne
      rw [eq_bot_iff]
      intro u hu
      have h2 : u.2 = 0 := by
        have : u.2 ∈ K' := Submodule.mem_map.mpr ⟨u, hu, rfl⟩
        rwa [h, Submodule.mem_bot] at this
      rw [Submodule.mem_bot]
      exact Prod.ext (hfst u hu) h2
    · refine le_antisymm hKV fun v hv => ?_
      obtain ⟨hv1, -⟩ := Submodule.mem_prod.mp hv
      have : v.2 ∈ K' := by
        rw [h]
        exact Submodule.mem_top
      obtain ⟨u, hu, hu2⟩ := Submodule.mem_map.mp this
      have huv : u = v := Prod.ext ((hfst u hu).trans ((Submodule.mem_bot k).mp hv1).symm) hu2
      rwa [← huv]
  -- positivity facts at the highest weight
  have hpos : ∀ j : p.rootIndex, p.rootDatum.root j ∈ p.positiveRootMonoid →
      V ⊓ W (lam + p.rootDatum.root j) = ⊥ := by
    intro j hj
    rw [hVWbot]
    by_contra hne
    have h := hlam.2.2.2 _ hne
    rw [sub_add_cancel_left] at h
    exact WeylCharacter.neg_root_notMem_of_mem p.base hj h
  have hneg : ∀ j : p.rootIndex, p.rootDatum.root j ∉ p.positiveRootMonoid →
      V ⊓ W (lam - p.rootDatum.root j) = ⊥ := by
    intro j hj
    rw [hVWbot]
    by_contra hne
    have h := hlam.2.2.2 _ hne
    rw [sub_sub_cancel] at h
    exact hj h
  have hcore := freudenthalCasimirCoreStatement k ((Fin N → k) × (Fin n → k))
    (characterLattice p.torus) (cocharacterLattice p.torus) I p.rootIndex P yb W
    (pairLieAlgebra σ r) (⇑p.rootDatum.root) V lam
    (fun j => p.rootDatum.root j ∈ p.positiveRootMonoid) hWi hWt hgr hcoch hzero hnonroot
    hroot hY (fun j => p.rootDatum.ne_zero j) p.rootDatum.root.injective
    (fun j => ⟨p.rootDatum.reflectionPerm j j, by
      rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self]⟩)
    (pairLieAlgebra_nilpotentIdeal_eq_bot hrad σ hσ r) hVstab hVirr
    (by rw [hfVW]; exact hlam.2.2.1) hpos hneg
  refine ⟨GramDual.form P yb m, GramDual.form_comm P yb hm, ?_,
    fun χ hχ => GramDual.form_pos P yb hm hmY hX hχ, ?_⟩
  · intro i x y
    have hs : ∀ (χ : characterLattice p.torus) (y : cocharacterLattice p.torus),
        P ((p.rootDatum.reflection i).toEquiv χ) y = P χ (p.rootDatum.coreflection i y) := by
      intro χ y
      simp only [LinearEquiv.coe_toEquiv, RootPairing.reflection_apply,
        RootPairing.coreflection_apply, P, map_sub, map_zsmul, LinearMap.sub_apply,
        LinearMap.smul_apply, smul_eq_mul, RootPairing.coroot', RootPairing.root',
        LinearMap.flip_apply]
      ring
    have hms : ∀ ν, m ((p.rootDatum.reflection i).toEquiv ν) = m ν := by
      intro ν
      change finrank k ↥((p.representationWeightSpace σ (p.rootDatum.reflection i ν)).prod
          (p.representationWeightSpace r (p.rootDatum.reflection i ν))) =
        finrank k ↥((p.representationWeightSpace σ ν).prod (p.representationWeightSpace r ν))
      rw [finrank_prod_submodule, finrank_prod_submodule,
        p.finrank_representationWeightSpace_root_reflection σ ν i,
        p.finrank_representationWeightSpace_root_reflection r ν i]
    exact GramDual.form_apply_apply_eq P yb hm hmY (p.rootDatum.reflection i).toEquiv
      (p.rootDatum.coreflection i).toLinearMap hs hms x y
  · intro μ
    have h := hcore μ
    simp only [hfVW] at h
    exact h

end Langlands.GroupScheme
