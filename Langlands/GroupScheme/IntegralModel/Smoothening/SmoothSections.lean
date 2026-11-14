import Langlands.GroupScheme.IntegralModel.Smoothening.TensorDensity
import Langlands.CommutativeAlgebra.HenselianSections
import Langlands.AlgebraicGeometry.SmoothReducedProof
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_geometricallyIntegral_of_isAlgClosed
import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! # Divisibility of functions on smooth schemes over a strictly Henselian DVR

Let `R` be a Henselian local ring with algebraically closed residue field `k`.

* On a smooth `R`-algebra `C`, the values at `R`-points detect the maximal ideal:
  a nonzero element of the reduced finitely generated `k`-algebra `k ⊗[R] C` is
  nonzero at a `k`-point (Nullstellensatz), and `k`-points lift to `R`-points
  (Hensel).
* For a scheme `Y` over `Spec R`, flatness makes the global functions a
  torsion-free, hence (over a discrete valuation ring) flat, `R`-module.
* For a smooth scheme `Y` over a discrete valuation ring `R`, a global function
  `c` is divisible by `s ≠ 0` as soon as `s` divides `χ c` for every `R`-algebra
  map `χ` from the global functions to `R`: this holds on every affine open, and
  the local quotients glue by torsion-freeness. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace IsLocalRing
open scoped TensorProduct

namespace Langlands.GroupScheme.IntegralModel.Smoothening

section Nullstellensatz

open P2MW.S_AlgebraicGeometry_geometricallyIntegral_of_isAlgClosed.GeomIntegralOfIsAlgClosed in
/-- A nonzero element of a reduced finitely generated algebra over an algebraically
closed field is nonzero at some rational point. -/
theorem exists_algHom_ne_zero_of_isReduced {k : Type u} [Field k] [IsAlgClosed k]
    {D : Type u} [CommRing D] [_root_.IsReduced D] [Algebra k D] [Algebra.FiniteType k D]
    {r : D} (hr : r ≠ 0) : ∃ φ : D →ₐ[k] k, φ r ≠ 0 := by
  have : IsJacobsonRing D := isJacobsonRing_of_finiteType (A := k)
  have hbot : (⊥ : Ideal D).jacobson = ⊥ := IsJacobsonRing.out' ⊥ Ideal.isRadical_bot
  have hr' : r ∉ (⊥ : Ideal D).jacobson := by
    rw [hbot]
    exact fun h => hr (Ideal.mem_bot.1 h)
  rw [Ideal.jacobson, Ideal.mem_sInf] at hr'
  push Not at hr'
  obtain ⟨m, ⟨-, hm⟩, hrm⟩ := hr'
  exact ⟨pointOfMaximal k m, fun h => hrm ((pointOfMaximal_eq_zero_iff m r).1 h)⟩

end Nullstellensatz

section Hensel

variable {R : Type u} [CommRing R] [HenselianLocalRing R] [IsAlgClosed (ResidueField R)]

/-- On a smooth algebra over a Henselian local ring with algebraically closed residue
field, the values at `R`-points detect the maximal ideal. -/
theorem detectsMaximal_of_smooth (C : Type u) [CommRing C] [Algebra R C] [Algebra.Smooth R C] :
    DetectsMaximal (fun χ : C →ₐ[R] R => χ.toLinearMap) := by
  intro c hc
  rw [← one_tmul_eq_zero_iff]
  by_contra h
  have : _root_.IsReduced (ResidueField R ⊗[R] C) :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_of_domain
      (ResidueField R) _
  obtain ⟨φ, hφ⟩ := exists_algHom_ne_zero_of_isReduced (k := ResidueField R) h
  obtain ⟨σ, hσ⟩ := Langlands.CommutativeAlgebra.HenselianSections.exists_lift_of_smooth
    (K := ResidueField R) (residue_surjective)
    ((φ.restrictScalars R).comp Algebra.TensorProduct.includeRight)
  apply hφ
  have h1 := congrArg (fun f : C →ₐ[R] ResidueField R => f c) hσ
  simp only [AlgHom.comp_apply, Algebra.TensorProduct.includeRight_apply,
    AlgHom.restrictScalars_apply, Algebra.ofId_apply, ResidueField.algebraMap_eq] at h1
  rw [← h1]
  exact (residue_eq_zero_iff _).2 (hc σ)

/-- On a smooth algebra over a Henselian discrete valuation ring with algebraically
closed residue field, an element is divisible by `s ≠ 0` once `s` divides its value at
every `R`-point. -/
theorem exists_eq_smul_of_smooth_algebra [IsDomain R] [IsDiscreteValuationRing R]
    (C : Type u) [CommRing C] [Algebra R C] [Algebra.Smooth R C] {s : R} (hs : s ≠ 0)
    (c : C) (hc : ∀ χ : C →ₐ[R] R, s ∣ χ c) : ∃ c' : C, c = s • c' :=
  (detectsMaximal_of_smooth C).exists_eq_smul hs c hc

end Hensel

section Gluing

variable {X : Scheme.{u}}

/-- The restriction of global functions to an open subset. -/
abbrev topRes (U : X.Opens) : Γ(X, ⊤) ⟶ Γ(X, U) :=
  X.presheaf.map (homOfLE le_top).op

theorem map_topRes {U V : X.Opens} (i : V ⟶ U) (σ : Γ(X, ⊤)) :
    X.presheaf.map i.op (topRes U σ) = topRes V σ := by
  rw [topRes, topRes, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

theorem topRes_top (σ : Γ(X, ⊤)) : topRes (X := X) ⊤ σ = σ := by
  change X.presheaf.map (𝟙 (op ⊤)) σ = σ
  rw [CategoryTheory.Functor.map_id]
  rfl

/-- If a global function is a non-zero-divisor on every affine open, it is a
non-zero-divisor on every open. -/
theorem eq_zero_of_mul_eq_zero (σ : Γ(X, ⊤))
    (hσ : ∀ U : X.affineOpens, ∀ t : Γ(X, U), topRes U.1 σ * t = 0 → t = 0)
    (W : X.Opens) (t : Γ(X, W)) (ht : topRes W σ * t = 0) : t = 0 := by
  let ι := {U : X.affineOpens // (U : X.Opens) ≤ W}
  refine X.sheaf.eq_of_locally_eq' (fun i : ι => (i.1 : X.Opens)) W (fun i => homOfLE i.2)
    ?_ t 0 fun i => ?_
  · intro x hx
    obtain ⟨U, hU, hxU, hUW⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens hx
    exact Opens.mem_iSup.2 ⟨⟨⟨U, hU⟩, hUW⟩, hxU⟩
  · rw [map_zero]
    apply hσ i.1
    have := congrArg (X.presheaf.map (homOfLE i.2).op) ht
    rwa [map_mul, map_zero, map_topRes] at this

/-- Divisibility of a global function by a global non-zero-divisor is local on affine
opens. -/
theorem exists_eq_mul_of_affine (σ c : Γ(X, ⊤))
    (hσ : ∀ U : X.affineOpens, ∀ t : Γ(X, U), topRes U.1 σ * t = 0 → t = 0)
    (hc : ∀ U : X.affineOpens, ∃ t : Γ(X, U), topRes U.1 c = topRes U.1 σ * t) :
    ∃ c' : Γ(X, ⊤), c = σ * c' := by
  choose t ht using hc
  have key : ∀ (U : X.affineOpens) (W : X.Opens) (i : W ⟶ U.1),
      topRes W σ * X.presheaf.map i.op (t U) = topRes W c := by
    intro U W i
    rw [← map_topRes i σ, ← map_mul, ← ht U, map_topRes]
  have hcompat : TopCat.Presheaf.IsCompatible X.presheaf
      (fun U : X.affineOpens => (U : X.Opens)) t := by
    intro U V
    rw [← sub_eq_zero]
    refine eq_zero_of_mul_eq_zero σ hσ _ _ ?_
    rw [mul_sub, key U _ (Opens.infLELeft _ _), key V _ (Opens.infLERight _ _), sub_self]
  obtain ⟨c', hc', -⟩ := X.sheaf.existsUnique_gluing' (fun U : X.affineOpens => (U : X.Opens))
    ⊤ (fun U => homOfLE le_top) (iSup_affineOpens_eq_top X).ge t hcompat
  let c'' : Γ(X, ⊤) := c'
  have hc'' : ∀ U : X.affineOpens, topRes U.1 c'' = t U := hc'
  refine ⟨c'', X.sheaf.eq_of_locally_eq' (fun U : X.affineOpens => (U : X.Opens)) ⊤
    (fun U => homOfLE le_top) (iSup_affineOpens_eq_top X).ge c (σ * c'') fun U => ?_⟩
  change topRes U.1 c = topRes U.1 (σ * c'')
  rw [map_mul, ht U, hc'' U]

end Gluing

section Base

variable {R : Type u} [CommRing R] (Y : Over (Spec (CommRingCat.of R)))

/-- The `R`-algebra structure on the functions on an open subset of a scheme over
`Spec R`, through the restriction of global functions. -/
abbrev openAlgebra (U : Y.left.Opens) : Algebra R Γ(Y.left, U) :=
  ((topRes U).hom.comp (algebraMap R ((algΓ (CommRingCat.of R)).obj Y).unop)).toAlgebra

/-- The restriction to an open subset as an `R`-algebra map. -/
def topResAlgHom (U : Y.left.Opens) :
    letI := openAlgebra Y U
    ((algΓ (CommRingCat.of R)).obj Y).unop →ₐ[R] Γ(Y.left, U) :=
  letI := openAlgebra Y U
  { toRingHom := (topRes U).hom
    commutes' := fun _ => rfl }

theorem smooth_openAlgebra [Smooth Y.hom] (U : Y.left.affineOpens) :
    letI := openAlgebra Y U.1
    Algebra.Smooth R Γ(Y.left, U.1) := by
  let := openAlgebra Y U.1
  rw [← RingHom.smooth_algebraMap]
  have h := HasRingHomProperty.appLE @Smooth Y.hom ‹_› ⟨⊤, isAffineOpen_top _⟩ U
    (fun _ _ => trivial)
  have hiso : RingHom.Smooth (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom :=
    RingHom.Smooth.of_bijective (ConcreteCategory.bijective_of_isIso _)
  exact hiso.comp h

theorem flat_openAlgebra [Flat Y.hom] (U : Y.left.affineOpens) :
    letI := openAlgebra Y U.1
    Module.Flat R Γ(Y.left, U.1) := by
  let := openAlgebra Y U.1
  rw [← RingHom.flat_algebraMap_iff]
  have h := HasRingHomProperty.appLE @Flat Y.hom ‹_› ⟨⊤, isAffineOpen_top _⟩ U
    (fun _ _ => trivial)
  have hiso : RingHom.Flat (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom :=
    RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _)
  exact hiso.comp h

variable [IsDomain R]

/-- On a flat scheme over a domain, nonzero scalars are non-zero-divisors on the
functions on every open subset. -/
theorem eq_zero_of_algebraMap_mul_eq_zero [Flat Y.hom] {s : R} (hs : s ≠ 0)
    (W : Y.left.Opens) (t : Γ(Y.left, W))
    (ht : topRes W (algebraMap R ((algΓ (CommRingCat.of R)).obj Y).unop s) * t = 0) :
    t = 0 := by
  refine eq_zero_of_mul_eq_zero _ (fun U t ht => ?_) W t ht
  let := openAlgebra Y U.1
  have := flat_openAlgebra Y U
  have h : s • t = 0 := by
    rw [Algebra.smul_def]
    exact ht
  exact (smul_eq_zero_iff_right hs).1 h

/-- The global functions of a flat scheme over a domain are torsion-free. -/
instance isTorsionFree_sections [Flat Y.hom] :
    Module.IsTorsionFree R ((algΓ (CommRingCat.of R)).obj Y).unop where
  isSMulRegular r hr x y h := by
    rw [← sub_eq_zero]
    have h0 : algebraMap R ((algΓ (CommRingCat.of R)).obj Y).unop r * (x - y) = 0 := by
      rw [mul_sub, ← Algebra.smul_def, ← Algebra.smul_def]
      exact sub_eq_zero.2 h
    have e : ∀ σ τ : Γ(Y.left, ⊤), σ * τ = 0 → topRes ⊤ σ * τ = 0 := fun σ τ h => by
      rw [topRes_top]
      exact h
    exact eq_zero_of_algebraMap_mul_eq_zero Y hr.ne_zero ⊤ _ (e _ _ h0)

/-- Over a discrete valuation ring, the global functions of a flat scheme are flat. -/
instance flat_sections [IsDiscreteValuationRing R] [Flat Y.hom] :
    Module.Flat R ((algΓ (CommRingCat.of R)).obj Y).unop :=
  inferInstance

/-- On a smooth scheme over a Henselian discrete valuation ring with algebraically
closed residue field, a global function is divisible by `s ≠ 0` once `s` divides its
value under every `R`-algebra map from the global functions to `R`. -/
theorem exists_eq_smul_of_smooth [IsDiscreteValuationRing R] [HenselianLocalRing R]
    [IsAlgClosed (ResidueField R)] [Smooth Y.hom] {s : R} (hs : s ≠ 0)
    (c : ((algΓ (CommRingCat.of R)).obj Y).unop)
    (hc : ∀ χ : ((algΓ (CommRingCat.of R)).obj Y).unop →ₐ[R] R, s ∣ χ c) :
    ∃ c', c = s • c' := by
  have hloc : ∀ U : Y.left.affineOpens, ∃ t : Γ(Y.left, U.1),
      topRes U.1 c = topRes U.1 (algebraMap R ((algΓ (CommRingCat.of R)).obj Y).unop s) * t := by
    intro U
    let := openAlgebra Y U.1
    have := smooth_openAlgebra Y U
    obtain ⟨t, ht⟩ := (detectsMaximal_of_smooth Γ(Y.left, U.1)).exists_eq_smul hs
      (topResAlgHom Y U.1 c) fun χ => hc (χ.comp (topResAlgHom Y U.1))
    exact ⟨t, by rw [Algebra.smul_def] at ht; exact ht⟩
  obtain ⟨c', hc'⟩ := exists_eq_mul_of_affine (X := Y.left) _ c
    (fun U t ht => eq_zero_of_algebraMap_mul_eq_zero Y hs U.1 t ht) hloc
  let d : ((algΓ (CommRingCat.of R)).obj Y).unop := c'
  exact ⟨d, by rw [Algebra.smul_def]; exact hc'⟩

end Base

end Langlands.GroupScheme.IntegralModel.Smoothening
