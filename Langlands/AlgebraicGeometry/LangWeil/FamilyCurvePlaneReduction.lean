import Langlands.AlgebraicGeometry.LangWeil.AffineCurvePlaneComparison
import Langlands.AlgebraicGeometry.LangWeil.CurvePlaneCharts
import Langlands.AlgebraicGeometry.LangWeil.CurvePlaneNoetherianInduction
import Langlands.AlgebraicGeometry.LangWeil.CurvePlaneZeroDimensional
import Langlands.AlgebraicGeometry.LangWeil.FamilyCurvePlaneComparisonStatement
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber

/-!
# Reduction of the plane-model comparison to affine curve algebras

The affine core `AffineCurvePlaneComparison` compares the points of one curve algebra over a
Noetherian domain with the zeros of a plane curve, away from a nonzero element of the domain.
This file deduces `FamilyCurvePlaneComparisonStatement` from it.

Over an affine open `S₀` of the base, for every prime `p` of `A = Γ(S, S₀)` one chart `c₁` of
the family meets the fibre over `p`; the core applied to `A ⧸ p` and `c₁` counts the points in
`c₁`. Since the fibre over `p` is irreducible of dimension one, every chart of a finite cover
contains a principal open inside `c₁` whose complement has zero-dimensional fibre over `p`, and
these complements have boundedly many points near `p`. Noetherian induction on `A` makes the
bound uniform, and a finite affine cover of the base finishes the proof.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.LangWeil.CurvePlane

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.SchemeFiberGeometry

section Ring

/-- Primality of the nilradical is transported backwards along ring isomorphisms. -/
theorem nilradical_isPrime_of_ringEquiv {T T' : Type*} [CommRing T] [CommRing T']
    (e : T ≃+* T') [(nilradical T').IsPrime] : (nilradical T).IsPrime := by
  have h : nilradical T = (nilradical T').comap e := by
    ext x
    rw [Ideal.mem_comap, mem_nilradical, mem_nilradical]
    exact (IsNilpotent.map_iff e.injective).symm
  rw [h]
  exact Ideal.IsPrime.comap _

/-- Primality of the nilradical passes from `A ⊗[R] B` to `A ⊗[S] (S ⊗[R] B)`. -/
theorem nilradical_isPrime_cancelBaseChange (R S A B : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [CommRing A] [Algebra R A] [Algebra S A] [IsScalarTower R S A] [CommRing B]
    [Algebra R B] [(nilradical (A ⊗[R] B)).IsPrime] :
    (nilradical (A ⊗[S] (S ⊗[R] B))).IsPrime :=
  nilradical_isPrime_of_ringEquiv (Algebra.TensorProduct.cancelBaseChange R S A A B).toRingEquiv

end Ring

variable {S : Scheme.{u}} {S₀ : S.Opens} (hS₀ : IsAffineOpen S₀)

/-- The plane-model bound at level `B` for the points over `S` of `Y` with values in a field
`κ` which is an algebra over the sections on `S₀`: if `κ` is finite with more than `B`
elements, a geometrically irreducible plane polynomial of bidegree at most `B` has zero count
within `B` of the point count. -/
def PointBound (Y : Over S) (B : ℕ) (κ : Type u) [Field κ] [Algebra Γ(S, S₀) κ] : Prop :=
  Finite κ → B < Nat.card κ → ∃ P : MvPolynomial (Fin 2) κ,
    Irreducible (MvPolynomial.map (algebraMap κ (AlgebraicClosure κ)) P) ∧
    0 < P.degreeOf 0 ∧ P.degreeOf 0 ≤ B ∧ 0 < P.degreeOf 1 ∧ P.degreeOf 1 ≤ B ∧
    |(Nat.card (testObj hS₀ κ ⟶ Y) : ℝ) -
        (Nat.card {v : Fin 2 → κ // MvPolynomial.eval v P = 0} : ℝ)| ≤ B

theorem PointBound.mono {Y : Over S} {B B' : ℕ} {κ : Type u} [Field κ] [Algebra Γ(S, S₀) κ]
    (hBB' : B ≤ B') (h : PointBound hS₀ Y B κ) : PointBound hS₀ Y B' κ := by
  intro hfin hlt
  obtain ⟨P, hirr, h0, h0le, h1, h1le, hc⟩ := h hfin (lt_of_le_of_lt hBB' hlt)
  exact ⟨P, hirr, h0, h0le.trans hBB', h1, h1le.trans hBB',
    hc.trans (by exact_mod_cast hBB')⟩

variable {Y : Over S}

/-- A point of a chart lies over the image of a prime of the base ring exactly when its prime
contracts to that prime. -/
theorem chart_apply_eq_iff (c : Chart S₀ Y) (w : Spec (CommRingCat.of c.Ring))
    (p : PrimeSpectrum Γ(S, S₀)) :
    Y.hom (c.fromSpec w) = hS₀.fromSpec p ↔
      PrimeSpectrum.comap (algebraMap Γ(S, S₀) c.Ring) w = p := by
  have h : Y.hom (c.fromSpec w) =
      hS₀.fromSpec (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, S₀) c.Ring)) w) := by
    rw [← Scheme.Hom.comp_apply, c.fromSpec_hom hS₀, Scheme.Hom.comp_apply]
  rw [h]
  exact (Scheme.Hom.isOpenEmbedding hS₀.fromSpec).injective.eq_iff

/-- A point of a chart over `p` comes from a prime of the fibre ring over `p`. -/
theorem exists_fiber_prime (c : Chart S₀ Y) (p : PrimeSpectrum Γ(S, S₀))
    (w : Spec (CommRingCat.of c.Ring)) (hw : Y.hom (c.fromSpec w) = hS₀.fromSpec p) :
    ∃ W : PrimeSpectrum (p.asIdeal.Fiber c.Ring),
      PrimeSpectrum.comap (Algebra.TensorProduct.includeRight.toRingHom :
        c.Ring →+* p.asIdeal.Fiber c.Ring) W = w :=
  ⟨PrimeSpectrum.preimageEquivFiber Γ(S, S₀) c.Ring p ⟨w, (chart_apply_eq_iff hS₀ c w p).mp hw⟩,
    congrArg Subtype.val ((PrimeSpectrum.preimageEquivFiber Γ(S, S₀) c.Ring p).symm_apply_apply
      ⟨w, (chart_apply_eq_iff hS₀ c w p).mp hw⟩)⟩

theorem nontrivial_fiber_of_mem (c : Chart S₀ Y) (p : PrimeSpectrum Γ(S, S₀)) {x : Y.left}
    (hx : x ∈ c.U) (hxp : Y.hom x = hS₀.fromSpec p) : Nontrivial (p.asIdeal.Fiber c.Ring) := by
  have hx' : x ∈ Set.range c.fromSpec := by rw [c.range_fromSpec]; exact hx
  obtain ⟨w, rfl⟩ := hx'
  obtain ⟨W, -⟩ := exists_fiber_prime hS₀ c p w hxp
  exact nontrivial_of_ne 0 1 fun h => W.isPrime.ne_top
    ((Ideal.eq_top_iff_one _).mpr (h ▸ W.asIdeal.zero_mem))

/-- For a chart `c` and a chart `c₁` meeting the fibre over a prime `p`, some principal open of
`c` lies in `c₁`, and its closed complement in `c` has zero-dimensional fibre over `p`. -/
theorem exists_basicOpen_le_fiber_krullDimLE_zero [LocallyOfFiniteType Y.hom]
    [GeometricallyIrreducible Y.hom] (hdim : ∀ s, HasPureDimension (Y.hom.fiber s) 1)
    (p : PrimeSpectrum Γ(S, S₀)) (c₁ : Chart S₀ Y)
    (hc₁ : ∃ x ∈ c₁.U, Y.hom x = hS₀.fromSpec p) (c : Chart S₀ Y) :
    ∃ h : c.Ring, Y.left.basicOpen (U := c.U) h ≤ c₁.U ∧
      Ring.KrullDimLE 0 (p.asIdeal.ResidueField ⊗[Γ(S, S₀)] (c.Ring ⧸ Ideal.span {h})) := by
  classical
  by_cases hne : ∃ y ∈ c.U, Y.hom y = hS₀.fromSpec p
  · have hirr : IsPreirreducible (Y.hom ⁻¹' {hS₀.fromSpec p}) := by
      rw [← Scheme.Hom.range_fiberι, ← Set.image_univ]
      exact ((IrreducibleSpace.isIrreducible_univ _).image _
        (Y.hom.fiberι _).continuous.continuousOn).isPreirreducible
    obtain ⟨x, hxc₁, hx⟩ := hc₁
    obtain ⟨y, hyc, hy⟩ := hne
    obtain ⟨z, hzS, hzc, hzc₁⟩ := hirr _ _ c.U.isOpen c₁.U.isOpen ⟨y, hy, hyc⟩ ⟨x, hx, hxc₁⟩
    have hzS' : Y.hom z = hS₀.fromSpec p := hzS
    obtain ⟨h, hle, hzh⟩ : ∃ h : c.Ring, Y.left.basicOpen (U := c.U) h ≤ c.U ⊓ c₁.U ∧
        z ∈ Y.left.basicOpen (U := c.U) h :=
      c.isAffine.exists_basicOpen_le (V := c.U ⊓ c₁.U) ⟨z, hzc, hzc₁⟩ hzc
    have hz' : z ∈ Set.range c.fromSpec := by rw [c.range_fromSpec]; exact hzc
    obtain ⟨w, rfl⟩ := hz'
    have hwh : w ∈ PrimeSpectrum.basicOpen (h : c.Ring) :=
      (SetLike.ext_iff.mp (c.isAffine.fromSpec_preimage_basicOpen h) w).mp hzh
    obtain ⟨W, hWw⟩ := exists_fiber_prime hS₀ c p w hzS'
    have : Nontrivial (p.asIdeal.Fiber c.Ring) :=
      nontrivial_of_ne 0 1 fun h => W.isPrime.ne_top
        ((Ideal.eq_top_iff_one _).mpr (h ▸ W.asIdeal.zero_mem))
    have hnil : ¬IsNilpotent ((1 : p.asIdeal.ResidueField) ⊗ₜ[Γ(S, S₀)] (h : c.Ring)) := by
      intro hn
      have hmem : (1 : p.asIdeal.ResidueField) ⊗ₜ[Γ(S, S₀)] (h : c.Ring) ∈ W.asIdeal :=
        nilradical_le_prime W.asIdeal (mem_nilradical.mpr hn)
      apply (PrimeSpectrum.mem_basicOpen _ _).mp hwh
      rw [← hWw]
      exact hmem
    have := chart_nilradical_isPrime hS₀ c p.asIdeal.ResidueField
    have hdim1 := ringKrullDim_eq_of_hasPureRingDimension
      (chart_hasPureRingDimension_fiber hS₀ hdim c p)
    have : Ring.KrullDimLE 1 (p.asIdeal.ResidueField ⊗[Γ(S, S₀)] c.Ring) := by
      rw [Ring.krullDimLE_iff]
      exact hdim1.le
    exact ⟨h, hle.trans inf_le_right, fiber_quotient_krullDimLE_zero _ hnil⟩
  · refine ⟨0, ?_, ?_⟩
    · exact (Scheme.basicOpen_zero Y.left c.U).trans_le bot_le
    · have : Subsingleton (p.asIdeal.ResidueField ⊗[Γ(S, S₀)] c.Ring) := by
        by_contra hnt
        rw [not_subsingleton_iff_nontrivial] at hnt
        obtain ⟨W⟩ := (inferInstance : Nonempty (PrimeSpectrum (p.asIdeal.Fiber c.Ring)))
        let w := (PrimeSpectrum.preimageEquivFiber Γ(S, S₀) c.Ring p).symm W
        have hmem : c.fromSpec w.1 ∈ (c.U : Set Y.left) := by
          rw [← c.range_fromSpec]
          exact ⟨_, rfl⟩
        exact hne ⟨c.fromSpec w.1, hmem, (chart_apply_eq_iff hS₀ c w.1 p).mpr w.2⟩
      exact fiber_krullDimLE_zero_of_subsingleton _ _

include hS₀ in
/-- The nilradical hypothesis of the core for a chart meeting the fibre over `p`, after
reduction modulo `p`. -/
theorem core_nilradical_isPrime [LocallyOfFiniteType Y.hom] [GeometricallyIrreducible Y.hom]
    (c₁ : Chart S₀ Y) (p : PrimeSpectrum Γ(S, S₀)) [Nontrivial (p.asIdeal.Fiber c₁.Ring)] :
    (nilradical (AlgebraicClosure p.asIdeal.ResidueField ⊗[Γ(S, S₀) ⧸ p.asIdeal]
      ((Γ(S, S₀) ⧸ p.asIdeal) ⊗[Γ(S, S₀)] c₁.Ring))).IsPrime := by
  have : Nontrivial (AlgebraicClosure p.asIdeal.ResidueField ⊗[p.asIdeal.ResidueField]
      (p.asIdeal.ResidueField ⊗[Γ(S, S₀)] c₁.Ring)) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_right
      p.asIdeal.ResidueField _ _
      (algebraMap p.asIdeal.ResidueField (AlgebraicClosure p.asIdeal.ResidueField)).injective
  have : Nontrivial (AlgebraicClosure p.asIdeal.ResidueField ⊗[Γ(S, S₀)] c₁.Ring) :=
    (Algebra.TensorProduct.cancelBaseChange Γ(S, S₀) p.asIdeal.ResidueField
      (AlgebraicClosure p.asIdeal.ResidueField) (AlgebraicClosure p.asIdeal.ResidueField)
      c₁.Ring).symm.toEquiv.nontrivial
  have := chart_nilradical_isPrime hS₀ c₁ (AlgebraicClosure p.asIdeal.ResidueField)
  exact nilradical_isPrime_cancelBaseChange Γ(S, S₀) (Γ(S, S₀) ⧸ p.asIdeal)
    (AlgebraicClosure p.asIdeal.ResidueField) c₁.Ring

include hS₀ in
/-- The dimension hypothesis of the core for a chart meeting the fibre over `p`, after
reduction modulo `p`. -/
theorem core_ringKrullDim_eq_one [LocallyOfFiniteType Y.hom] [GeometricallyIrreducible Y.hom]
    (hdim : ∀ s, HasPureDimension (Y.hom.fiber s) 1) (c₁ : Chart S₀ Y)
    (p : PrimeSpectrum Γ(S, S₀)) [Nontrivial (p.asIdeal.Fiber c₁.Ring)] :
    ringKrullDim (p.asIdeal.ResidueField ⊗[Γ(S, S₀) ⧸ p.asIdeal]
      ((Γ(S, S₀) ⧸ p.asIdeal) ⊗[Γ(S, S₀)] c₁.Ring)) = 1 := by
  have := chart_nilradical_isPrime hS₀ c₁ p.asIdeal.ResidueField
  rw [ringKrullDim_eq_of_ringEquiv (Algebra.TensorProduct.cancelBaseChange Γ(S, S₀)
    (Γ(S, S₀) ⧸ p.asIdeal) p.asIdeal.ResidueField p.asIdeal.ResidueField
    c₁.Ring).toRingEquiv, ringKrullDim_eq_of_hasPureRingDimension
      (chart_hasPureRingDimension_fiber hS₀ hdim c₁ p)]
  exact Nat.cast_one

include hS₀ in
/-- The core applied to a chart meeting the fibre over `p`, over the domain `Γ(S, S₀) ⧸ p`,
compares the points of the chart with the zeros of a plane curve near `p`. -/
theorem exists_chart_core_bound [LocallyOfFiniteType Y.hom] [GeometricallyIrreducible Y.hom]
    [IsNoetherianRing Γ(S, S₀)] (hdim : ∀ s, HasPureDimension (Y.hom.fiber s) 1)
    (hcore : AffineCurvePlaneComparison.{u}) (c₁ : Chart S₀ Y) (p : PrimeSpectrum Γ(S, S₀))
    [Nontrivial (p.asIdeal.Fiber c₁.Ring)] :
    ∃ a₀ ∉ p.asIdeal, ∃ B₀ : ℕ, ∀ (κ : Type u) [Field κ] [Finite κ] [Algebra Γ(S, S₀) κ],
      (∀ x ∈ p.asIdeal, algebraMap Γ(S, S₀) κ x = 0) → algebraMap Γ(S, S₀) κ a₀ ≠ 0 →
      B₀ < Nat.card κ → ∃ F : MvPolynomial (Fin 2) κ,
        Irreducible (MvPolynomial.map (algebraMap κ (AlgebraicClosure κ)) F) ∧
        0 < F.degreeOf 0 ∧ F.degreeOf 0 ≤ B₀ ∧ 0 < F.degreeOf 1 ∧ F.degreeOf 1 ≤ B₀ ∧
        |(Nat.card (c₁.Ring →ₐ[Γ(S, S₀)] κ) : ℝ) -
          (Nat.card {v : Fin 2 → κ // MvPolynomial.eval v F = 0} : ℝ)| ≤ B₀ := by
  have := chart_finiteType hS₀ c₁
  obtain ⟨a', ha', B₀, hB₀⟩ := hcore (Γ(S, S₀) ⧸ p.asIdeal)
    ((Γ(S, S₀) ⧸ p.asIdeal) ⊗[Γ(S, S₀)] c₁.Ring) p.asIdeal.ResidueField
    (core_nilradical_isPrime hS₀ c₁ p) (core_ringKrullDim_eq_one hS₀ hdim c₁ p)
  obtain ⟨a₀, rfl⟩ := Ideal.Quotient.mk_surjective a'
  refine ⟨a₀, fun hmem => ha' (Ideal.Quotient.eq_zero_iff_mem.mpr hmem), B₀, ?_⟩
  intro κ _ _ _ hκ ha₀κ hlt
  let : Algebra (Γ(S, S₀) ⧸ p.asIdeal) κ :=
    (Ideal.Quotient.lift p.asIdeal (algebraMap Γ(S, S₀) κ) hκ).toAlgebra
  have : IsScalarTower Γ(S, S₀) (Γ(S, S₀) ⧸ p.asIdeal) κ :=
    IsScalarTower.of_algebraMap_eq fun x => (Ideal.Quotient.lift_mk _ _ _).symm
  have hκ₀ : algebraMap (Γ(S, S₀) ⧸ p.asIdeal) κ (Ideal.Quotient.mk p.asIdeal a₀) ≠ 0 := by
    rwa [RingHom.algebraMap_toAlgebra, Ideal.Quotient.lift_mk]
  rw [Nat.card_congr (Algebra.TensorProduct.liftEquivRight Γ(S, S₀) (Γ(S, S₀) ⧸ p.asIdeal)
    c₁.Ring κ)]
  exact hB₀ κ hκ₀ hlt

/-- The local step of the Noetherian induction: near a prime `p` of the base ring, the core
comparison for one chart meeting the fibre over `p`, together with the zero-dimensional fibres
of the boundary pieces of a finite chart cover, gives a plane-model bound. -/
theorem exists_prime_bound [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [GeometricallyIrreducible Y.hom] [IsNoetherianRing Γ(S, S₀)]
    (hdim : ∀ s, HasPureDimension (Y.hom.fiber s) 1) (hcore : AffineCurvePlaneComparison.{u})
    (p : PrimeSpectrum Γ(S, S₀)) :
    ∃ a ∉ p.asIdeal, ∃ B : ℕ, ∀ (κ : Type u) [Field κ] [Algebra Γ(S, S₀) κ],
      (∀ x ∈ p.asIdeal, algebraMap Γ(S, S₀) κ x = 0) → algebraMap Γ(S, S₀) κ a ≠ 0 →
      PointBound hS₀ Y B κ := by
  classical
  -- a chart meeting the fibre over `p`
  obtain ⟨x₀, hx₀⟩ := Y.hom.surjective (hS₀.fromSpec p)
  have hx₀S : x₀ ∈ Y.hom ⁻¹ᵁ S₀ := by
    change Y.hom x₀ ∈ (S₀ : Set S)
    rw [hx₀, ← hS₀.range_fromSpec]
    exact ⟨_, rfl⟩
  obtain ⟨U₁, hU₁, hx₀U₁, hU₁le⟩ := exists_isAffineOpen_mem_and_subset hx₀S
  let c₁ : Chart S₀ Y := ⟨U₁, hU₁, hU₁le⟩
  have hc₁ : ∃ x ∈ c₁.U, Y.hom x = hS₀.fromSpec p := ⟨x₀, hx₀U₁, hx₀⟩
  -- a finite chart cover of the preimage of `S₀`
  obtain ⟨t, ht, htU⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp
    (Y.hom.isCompact_preimage hS₀.isCompact)
  have : Fintype t := ht.fintype
  let c : t → Chart S₀ Y := fun i => ⟨i.1.1, i.1.2, by
    rw [htU]
    exact le_iSup₂_of_le (f := fun (j : Y.left.affineOpens) (_ : j ∈ t) => (j : Y.left.Opens))
      i.1 i.2 le_rfl⟩
  have hcov : Y.hom ⁻¹ᵁ S₀ ≤ ⨆ i, (c i).U :=
    htU.le.trans (iSup₂_le fun j hj => le_iSup_of_le (⟨j, hj⟩ : t) le_rfl)
  -- the boundary pieces have boundedly many points near `p`
  choose h hh hdim0 using fun i =>
    exists_basicOpen_le_fiber_krullDimLE_zero hS₀ hdim p c₁ hc₁ (c i)
  have hN : ∀ i, ∃ a ∉ p.asIdeal, ∃ N : ℕ, ∀ (κ : Type u) [Field κ] [Algebra Γ(S, S₀) κ],
      (∀ x ∈ p.asIdeal, algebraMap Γ(S, S₀) κ x = 0) → algebraMap Γ(S, S₀) κ a ≠ 0 →
        Finite ((c i).Ring ⧸ Ideal.span {h i} →ₐ[Γ(S, S₀)] κ) ∧
        Nat.card ((c i).Ring ⧸ Ideal.span {h i} →ₐ[Γ(S, S₀)] κ) ≤ N := fun i => by
    have := chart_finiteType hS₀ (c i)
    have := hdim0 i
    exact exists_card_algHom_le_of_fiber_krullDimLE_zero p.asIdeal
  choose a ha N hN using hN
  -- the core on the chart `c₁`
  have : Nontrivial (p.asIdeal.Fiber c₁.Ring) := nontrivial_fiber_of_mem hS₀ c₁ p hx₀U₁ hx₀
  obtain ⟨a₀, ha₀, B₀, hB₀⟩ := exists_chart_core_bound hS₀ hdim hcore c₁ p
  have hprod : ∏ i, a i ∉ p.asIdeal := fun hmem => by
    obtain ⟨i, -, hi⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
    exact ha i hi
  refine ⟨a₀ * ∏ i, a i, fun hmem => (p.isPrime.mem_or_mem hmem).elim ha₀ hprod,
    B₀ + ∑ i, N i, ?_⟩
  intro κ _ _ hκ haκ hfin hlt
  rw [map_mul] at haκ
  have haiκ : ∀ i, algebraMap Γ(S, S₀) κ (a i) ≠ 0 := by
    have hne := right_ne_zero_of_mul haκ
    rw [map_prod, Finset.prod_ne_zero_iff] at hne
    exact fun i => hne i (Finset.mem_univ i)
  obtain ⟨F, hirr, h0, h0le, h1, h1le, hcard⟩ :=
    hB₀ κ hκ (left_ne_zero_of_mul haκ) (lt_of_le_of_lt (Nat.le_add_right _ _) hlt)
  obtain ⟨hlow, hup⟩ := card_points_bounds hS₀ κ c hcov c₁ h hh
  have hsum : ∑ i, Nat.card ((c i).Ring ⧸ Ideal.span {h i} →ₐ[Γ(S, S₀)] κ) ≤ ∑ i, N i :=
    Finset.sum_le_sum fun i _ => (hN i κ hκ (haiκ i)).2
  refine ⟨F, hirr, h0, h0le.trans (Nat.le_add_right _ _), h1, h1le.trans (Nat.le_add_right _ _),
    ?_⟩
  have hlow' : (Nat.card (c₁.Ring →ₐ[Γ(S, S₀)] κ) : ℝ) ≤ Nat.card (testObj hS₀ κ ⟶ Y) := by
    exact_mod_cast hlow
  have hup' : (Nat.card (testObj hS₀ κ ⟶ Y) : ℝ) ≤
      Nat.card (c₁.Ring →ₐ[Γ(S, S₀)] κ) + ∑ i, (N i : ℝ) := by
    exact_mod_cast hup.trans (Nat.add_le_add_left hsum _)
  have hN0 : (0 : ℝ) ≤ ∑ i, (N i : ℝ) := by positivity
  rw [abs_le] at hcard ⊢
  push_cast
  constructor <;> linarith [hcard.1, hcard.2]

/-- Over an affine open with Noetherian sections, one plane-model bound works for all fields. -/
theorem exists_affine_bound [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [GeometricallyIrreducible Y.hom] [IsNoetherianRing Γ(S, S₀)]
    (hdim : ∀ s, HasPureDimension (Y.hom.fiber s) 1) (hcore : AffineCurvePlaneComparison.{u}) :
    ∃ B : ℕ, ∀ (κ : Type u) [Field κ] [Algebra Γ(S, S₀) κ], PointBound hS₀ Y B κ :=
  exists_uniform_of_forall_prime (fun B κ _ _ => PointBound hS₀ Y B κ)
    (fun _ _ _ _ _ hBB' h => PointBound.mono hS₀ hBB' h)
    fun p hp => exists_prime_bound hS₀ hdim hcore ⟨p, hp⟩

/-- Points of `X` over the `S`-point defined by an algebra over sections on `S₀` are morphisms
over `S`. -/
def pointsEquiv {X : Scheme.{u}} (f : X ⟶ S) (κ : Type u) [CommRing κ] [Algebra Γ(S, S₀) κ] :
    {x : Spec (CommRingCat.of κ) ⟶ X // x ≫ f = testMap hS₀ κ} ≃
      (testObj hS₀ κ ⟶ Over.mk f) where
  toFun x := Over.homMk x.1 x.2
  invFun y := ⟨y.left, Over.w y⟩
  left_inv _ := rfl
  right_inv _ := Over.OverMorphism.ext rfl

/-- A point of `S` with values in a field and image in an affine open `S₀` is the structure
morphism of an algebra over the sections on `S₀`. -/
theorem exists_algebra_testMap (κ : Type u) [Field κ] (s : Spec (CommRingCat.of κ) ⟶ S)
    (hs : Set.range s ⊆ S₀) : ∃ _ : Algebra Γ(S, S₀) κ, testMap hS₀ κ = s := by
  let g := IsOpenImmersion.lift hS₀.fromSpec s (by rw [hS₀.range_fromSpec]; exact hs)
  have hg : g ≫ hS₀.fromSpec = s := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨φ, hφ⟩ := Spec.map_surjective g
  refine ⟨φ.hom.toAlgebra, ?_⟩
  rw [← hg, ← hφ]
  rfl

/-- The plane-model comparison for curve families follows from the affine core. -/
theorem familyCurvePlaneComparison_of_core (hcore : AffineCurvePlaneComparison.{u}) :
    FamilyCurvePlaneComparisonStatement.{u} := by
  intro _ S X f _ _ hft hqc hgi hdim
  have : IsNoetherianRing (ULift.{u} ℤ) := isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  have : IsLocallyNoetherian S :=
    LocallyOfFiniteType.isLocallyNoetherian (specULiftZIsTerminal.from S)
  have : LocallyOfFiniteType (Over.mk f).hom := hft
  have : QuasiCompact (Over.mk f).hom := hqc
  have : GeometricallyIrreducible (Over.mk f).hom := hgi
  have hloc : ∀ U : S.affineOpens, ∃ B : ℕ, ∀ (κ : Type u) [Field κ] [Algebra Γ(S, U) κ],
      PointBound U.2 (Over.mk f) B κ := fun U => by
    have : IsNoetherianRing Γ(S, U) := IsLocallyNoetherian.component_noetherian U
    exact exists_affine_bound U.2 hdim hcore
  choose Bf hBf using hloc
  obtain ⟨t, ht, htU⟩ :=
    (isCompact_iff_finite_and_eq_biUnion_affineOpens (U := (⊤ : S.Opens))).mp
      (by rw [TopologicalSpace.Opens.coe_top]; exact isCompact_univ)
  refine ⟨∑ U ∈ ht.toFinset, Bf U + 1, Nat.succ_pos _, ?_⟩
  intro κ _ _ s hκ
  let z₀ : Spec (CommRingCat.of κ) := IsLocalRing.closedPoint κ
  have hz : s z₀ ∈ (⊤ : S.Opens) := trivial
  rw [htU] at hz
  obtain ⟨U, hUt, hzU⟩ : ∃ U ∈ t, s z₀ ∈ (U : S.Opens) := by
    simpa [TopologicalSpace.Opens.mem_iSup] using hz
  have hrange : Set.range s ⊆ (U : S.Opens) := by
    rintro _ ⟨z, rfl⟩
    rwa [Subsingleton.elim (α := PrimeSpectrum κ) z z₀]
  obtain ⟨_, hsU⟩ := exists_algebra_testMap U.2 κ s hrange
  subst hsU
  have hBU : Bf U ≤ ∑ U ∈ ht.toFinset, Bf U + 1 :=
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (ht.mem_toFinset.mpr hUt)).trans
      (Nat.le_succ _)
  obtain ⟨F, hirr, h0, h0le, h1, h1le, hc⟩ := hBf U κ inferInstance (lt_of_le_of_lt hBU hκ)
  refine ⟨F, hirr, h0, h0le.trans hBU, h1, h1le.trans hBU, ?_⟩
  rw [Nat.card_congr (pointsEquiv U.2 f κ)]
  exact hc.trans (by exact_mod_cast hBU)

end Langlands.AlgebraicGeometry.LangWeil.CurvePlane
