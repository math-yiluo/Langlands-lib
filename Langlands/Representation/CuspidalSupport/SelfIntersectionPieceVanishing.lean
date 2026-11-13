import Langlands.Representation.Exponents.ActualGeometricFullPieceNaturality
import Langlands.Representation.Geometric.FullIntersectionIrreducible
import Langlands.Representation.Exponents.LeviNormalizerQuotientProof
import Langlands.Representation.Exponents.LeviSupercuspidalInductionSupport

/-! # Natural maps from the non-identity self-intersection pieces vanish -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance selfPieceAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {P M N : GroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P} {hp : IsParabolicSubgroup p}
  {hr : LeviSubgroup.IsGeometricUnipotentRadical r} {hl : IsRationalLeviSubgroup l}
  {hmul : IsIso (subgroupMultiplication l r)} {z : rationalPoints G}

set_option maxHeartbeats 800000 in
/-- Let `D` be an intersection datum of the geometric lemma for `r_P ∘ i_P` at a double coset
`P(F) z P(F)` with `z⁻¹ ∉ M(F)`. Let `σ` be a supercuspidal representation of `M(F)` in which
no element `t` with `t ^ n ∉ ⁰M(F)` for all `n > 0` fixes a nonzero vector. Then every
morphism from the piece `D.pieceFunctor σ` to `σ` that commutes with all endomorphisms of `σ`
is zero. -/
theorem pieceFunctor_hom_eq_zero_of_not_mem (hG : IsConnectedReductive G)
    (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul p l r hp hr hl hmul z)
    (hz : z⁻¹ ∉ pointImage (l ≫ p))
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, max u v} ℂ (rationalPoints M))
    (hsc : haveI := hl.isConnectedReductive.isAffineHom
      letI := leviPointTopology l hl
      haveI := leviPoints_locallyCompactSpace p l hp hl
      haveI := leviPoints_nonarchimedeanGroup p l hp hl
      IsSupercuspidal σ)
    (hfix : letI := leviPointTopology l hl
      ∀ t : rationalPoints M,
      (∀ n : ℕ, 0 < n → t ^ n ∉ Plancherel.rationalCommonNormKernel M) →
        ∀ v : σ, σ.representation t v = v → v = 0)
    (g : letI := leviPointTopology l hl; D.pieceFunctor.obj σ ⟶ SmoothRep.toRep.obj σ)
    (hg : letI := leviPointTopology l hl
      ∀ a : σ ⟶ σ, D.pieceFunctor.map a ≫ g = g ≫ SmoothRep.toRep.map a) :
    g = 0 := by
  have := hl.isConnectedReductive.isAffineHom
  let := leviPointTopology l hl
  have := leviPoints_locallyCompactSpace p l hp hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  suffices hv : ∀ y, g.hom y = 0 by
    exact Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext hv))
  by_cases hp' : IsIso D.p'
  swap
  · have := D.subsingleton_pieceFunctor_obj σ
      (hsc _ _ _ D.p' D.l' D.r' D.hp' D.hl' D.hr' D.hmul' hp')
    intro y
    rw [Subsingleton.elim y 0, map_zero]
  have := D.isIso_q'_of_isIso_p'_of_iso (Iso.refl M)
  let φ := D.fullLeviConjugacy.val
  have hφ : φ.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso z⁻¹).hom := D.fullLeviConjugacy.property
  -- Faithfulness of `N_G(M)/M` on norms gives a central `c` whose norm `φ` moves.
  obtain ⟨c, hc, χ, hχ⟩ : ∃ c ∈ Subgroup.center (rationalPoints M),
      ∃ χ : rationalCharacters M,
        (Plancherel.rationalNormCharacters M χ).toMul (rationalPoints.map φ.hom c) ≠
          (Plancherel.rationalNormCharacters M χ).toMul c := by
    by_contra hne
    push Not at hne
    exact hz (leviNormalizerNormFixing k G hG P M p l hp hl z⁻¹ φ hφ hne)
  let ψ := D.fullLeviPointsEquiv
  have hψ : ψ c = rationalPoints.map φ.hom c := D.fullLeviPointsEquiv_apply c
  let E := D.fullPieceEquiv σ
  let T : σ → σ := fun v => g.hom (E.symm v)
  -- `T` is twisted-equivariant.
  have hTtwist (x : rationalPoints M) (v : σ) :
      T (σ.representation (ψ.symm x) v) = σ.representation x (T v) := by
    have h1 := Representation.IntertwiningMap.isIntertwining _ _ E.symm.toIntertwiningMap x v
    change E.symm (σ.representation (ψ.symm x) v) = _ at h1
    change g.hom (E.symm (σ.representation (ψ.symm x) v)) = _
    rw [h1]
    exact Rep.hom_comm_apply g x _
  -- `T` commutes with every endomorphism of `σ`.
  have hTnat (a : σ ⟶ σ) (v : σ) : T (SmoothRep.hom a v) = SmoothRep.hom a (T v) := by
    have h1 : E.symm (SmoothRep.hom a v) = (D.pieceFunctor.map a).hom (E.symm v) := by
      have h0 := D.fullPieceEquiv_naturality a (E.symm v)
      change E ((D.pieceFunctor.map a).hom (E.symm v)) = SmoothRep.hom a (E (E.symm v)) at h0
      rw [Representation.Equiv.apply_symm_apply] at h0
      rw [← h0, Representation.Equiv.symm_apply_apply]
    change g.hom (E.symm (SmoothRep.hom a v)) = _
    rw [h1]
    have h2 := congrArg (fun f => f.hom (E.symm v)) (hg a)
    exact h2
  -- `σ(c)` is an endomorphism of `σ`.
  have hcomm (m : rationalPoints M) (v : σ) :
      σ.representation c (σ.representation m v) = σ.representation m (σ.representation c v) := by
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul,
      Subgroup.mem_center_iff.mp hc m]
  let cE : σ ⟶ σ := SmoothRep.ofHom
    ⟨σ.representation c, fun m => LinearMap.ext fun v => hcomm m v⟩
  -- `t = c⁻¹ ψ(c)` has no power in `⁰M(F)`.
  let t := c⁻¹ * ψ c
  have ht : ∀ n : ℕ, 0 < n → t ^ n ∉ Plancherel.rationalCommonNormKernel M := by
    intro n hn hmem
    let Nχ := (Plancherel.rationalNormCharacters M χ).toMul
    have h1 : Nχ (t ^ n) = 1 := (Plancherel.mem_rationalCommonNormKernel M _).mp hmem χ
    have hx : (Nχ c)⁻¹ * Nχ (ψ c) ≠ 1 := by
      rw [Ne, inv_mul_eq_one, hψ]
      exact fun h => hχ h.symm
    apply hx
    rw [map_pow, map_mul, map_inv] at h1
    apply Units.ext
    have h2 := congrArg (fun u : NNReal ˣ => (u : NNReal)) h1
    simp only [Units.val_pow_eq_pow_val, Units.val_one] at h2
    rw [Units.val_one]
    exact (pow_eq_one_iff_of_nonneg zero_le hn.ne').mp h2
  intro y
  have hTv : T (E y) = 0 := by
    apply hfix t ht
    have h1 := hTnat cE (E y)
    have h2 := hTtwist (ψ c) (E y)
    rw [ψ.symm_apply_apply] at h2
    change T (σ.representation c (E y)) = σ.representation c (T (E y)) at h1
    change σ.representation (c⁻¹ * ψ c) (T (E y)) = T (E y)
    rw [map_mul, Module.End.mul_apply, ← h2, h1, ← Module.End.mul_apply, ← map_mul,
      inv_mul_cancel, map_one, Module.End.one_apply]
  change g.hom (E.symm (E y)) = 0 at hTv
  rwa [Representation.Equiv.symm_apply_apply] at hTv

end Langlands.Aubert.General.RepresentedParabolic
