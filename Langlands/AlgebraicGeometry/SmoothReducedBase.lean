import Mathlib
import Langlands.AlgebraicGeometry.SmoothReducedProof

/-!
# Smooth algebras and schemes over a reduced base are reduced

The Library module `Langlands.AlgebraicGeometry.SmoothReducedProof` proves that a smooth algebra
over a domain is reduced, and that a scheme smooth over a field is reduced. This module removes
the domain hypothesis: a smooth algebra over any reduced commutative ring is reduced, and a scheme
smooth over a reduced scheme is reduced.

The proof first treats a noetherian reduced base `B`. It has finitely many minimal primes `p`, and
`B` embeds into `∏ B ⧸ p`. A smooth `B`-algebra `S` is flat, so `S` embeds into
`(∏ B ⧸ p) ⊗[B] S ≅ ∏ (B ⧸ p) ⊗[B] S`. Each factor is smooth over the domain `B ⧸ p`, so it is
reduced. For an arbitrary reduced base, Mathlib's noetherian descent
`Algebra.Smooth.exists_subalgebra_fg` writes the algebra as a base change of a smooth algebra over
a finitely generated, hence noetherian, subring. Mathlib's
`IsReduced.tensorProduct_of_flat_of_forall_fg` then reduces to finitely generated subalgebras of
the base, which are noetherian again.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.SmoothReducedBase

universe u v

/-- A smooth algebra over a noetherian reduced ring is reduced. -/
theorem isReduced_of_smooth_of_isNoetherianRing (B : Type u) (S : Type v) [CommRing B]
    [IsNoetherianRing B] [_root_.IsReduced B] [CommRing S] [Algebra B S] [Algebra.Smooth B S] :
    _root_.IsReduced S := by
  let ι := minimalPrimes B
  have : Finite ι := (minimalPrimes.finite_of_isNoetherianRing B).to_subtype
  let : Fintype ι := Fintype.ofFinite ι
  classical
  let f : B →ₗ[B] (∀ p : ι, B ⧸ (p : Ideal B)) :=
    LinearMap.pi fun p => (Ideal.Quotient.mkₐ B (p : Ideal B)).toLinearMap
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro b hb
    have hb' : ∀ p : ι, b ∈ (p : Ideal B) := fun p => by
      have := congrFun (LinearMap.mem_ker.mp hb) p
      simpa [f, Ideal.Quotient.eq_zero_iff_mem] using this
    have : b ∈ sInf (minimalPrimes B) := Submodule.mem_sInf.mpr fun p hp => hb' ⟨p, hp⟩
    rw [Ideal.sInf_minimalPrimes, Ideal.radical_bot_of_isReduced] at this
    simpa using this
  have hinj : Function.Injective (f.rTensor S) :=
    Module.Flat.rTensor_preserves_injective_linearMap f hf
  have hred (p : ι) : _root_.IsReduced ((B ⧸ (p : Ideal B)) ⊗[B] S) := by
    have : (p : Ideal B).IsPrime := Ideal.IsMinimalPrime.isPrime p.2
    exact SmoothReducedProof.isReduced_of_smooth_of_domain (B ⧸ (p : Ideal B)) _
  constructor
  intro x hx
  have h1 (p : ι) : (1 : B ⧸ (p : Ideal B)) ⊗ₜ[B] x = 0 := by
    have := hred p
    exact (hx.map (Algebra.TensorProduct.includeRight :
      S →ₐ[B] (B ⧸ (p : Ideal B)) ⊗[B] S)).eq_zero
  have h2 : f.rTensor S ((1 : B) ⊗ₜ[B] x) = 0 := by
    apply (TensorProduct.piLeft B S fun p : ι => B ⧸ (p : Ideal B)).injective
    rw [map_zero]
    funext p
    simpa [f] using h1 p
  have h3 : (1 : B) ⊗ₜ[B] x = 0 := hinj (h2.trans (map_zero _).symm)
  simpa using congrArg (TensorProduct.lid B S) h3

/-- A smooth algebra over a reduced ring is reduced. -/
theorem isReduced_of_smooth (R : Type u) (A : Type v) [CommRing R] [_root_.IsReduced R]
    [CommRing A] [Algebra R A] [Algebra.Smooth R A] : _root_.IsReduced A := by
  obtain ⟨A₀, B₀, _, _, hfg, hsm, ⟨e⟩⟩ := Algebra.Smooth.exists_subalgebra_fg ℤ R A
  have : Algebra.FiniteType ℤ A₀ := (Subalgebra.fg_iff_finiteType A₀).mp hfg
  have : IsNoetherianRing A₀ := Algebra.FiniteType.isNoetherianRing ℤ A₀
  have : _root_.IsReduced A₀ := isReduced_of_injective A₀.val Subtype.val_injective
  have : _root_.IsReduced B₀ := isReduced_of_smooth_of_isNoetherianRing A₀ B₀
  have hBR : _root_.IsReduced (B₀ ⊗[A₀] R) := by
    apply IsReduced.tensorProduct_of_flat_of_forall_fg
    intro D hD
    have : Algebra.FiniteType A₀ D := (Subalgebra.fg_iff_finiteType D).mp hD
    have : IsNoetherianRing D := Algebra.FiniteType.isNoetherianRing A₀ D
    have : _root_.IsReduced D := isReduced_of_injective D.val Subtype.val_injective
    have : _root_.IsReduced (D ⊗[A₀] B₀) :=
      isReduced_of_smooth_of_isNoetherianRing D (D ⊗[A₀] B₀)
    exact isReduced_of_injective (Algebra.TensorProduct.comm A₀ B₀ D).toRingHom
      (Algebra.TensorProduct.comm A₀ B₀ D).injective
  have hRB : _root_.IsReduced (R ⊗[A₀] B₀) :=
    isReduced_of_injective (Algebra.TensorProduct.comm A₀ R B₀).toRingHom
      (Algebra.TensorProduct.comm A₀ R B₀).injective
  exact isReduced_of_injective e.toRingHom e.injective

/-- A scheme smooth over the spectrum of a reduced ring is reduced. -/
theorem isReduced_of_smooth_over_spec (R : CommRingCat.{u}) [_root_.IsReduced R]
    (X : Scheme.{u}) (p : X ⟶ Spec R) [Smooth p] : IsReduced X := by
  apply +allowSynthFailures @IsReduced.of_openCover X X.affineCover
  intro i
  let q := X.affineCover.f i ≫ p
  have : Smooth q := inferInstance
  let g : R ⟶ Γ(X.affineCover.X i, ⊤) := (Scheme.ΓSpecIso R).inv ≫ q.appTop
  have hg : g.hom.Smooth := RingHom.Smooth.comp
    (RingHom.Smooth.of_bijective (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv.bijective)
    (HasRingHomProperty.appTop @Smooth q inferInstance)
  algebraize [g.hom]
  have : Algebra.Smooth R Γ(X.affineCover.X i, ⊤) := (RingHom.smooth_algebraMap).mp hg
  have : _root_.IsReduced Γ(X.affineCover.X i, ⊤) := isReduced_of_smooth R _
  exact isReduced_of_isAffine_isReduced _

set_option backward.isDefEq.respectTransparency false in
/-- A scheme smooth over a reduced scheme is reduced. -/
theorem isReduced_of_smooth_of_isReduced {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f]
    [IsReduced S] : IsReduced X := by
  apply +allowSynthFailures @IsReduced.of_openCover (𝒰 := S.affineCover.pullback₁ f)
  intro i
  have : IsReduced (S.affineCover.X i) := isReduced_of_isOpenImmersion (S.affineCover.f i)
  have : _root_.IsReduced (S.affineOpenCover.X i) := (affine_isReduced_iff _).mp this
  exact isReduced_of_smooth_over_spec (S.affineOpenCover.X i) _ (pullback.snd _ _)

end Langlands.AlgebraicGeometry.SmoothReducedBase
