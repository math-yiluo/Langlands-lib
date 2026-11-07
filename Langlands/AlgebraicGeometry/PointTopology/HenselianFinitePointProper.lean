import Langlands.AlgebraicGeometry.PointTopology.HenselianRootContinuity
import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeMaps
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Finite maps of affine schemes are proper on rational points

Over a henselian valued field `K` that is algebraically closed in its completion, a finite map
of `K`-algebras `A → B` induces a proper map `B(K) → A(K)` of rational points with the
evaluation topology; hence so does a finite morphism of affine schemes over `K`. This is the
affine case of Conrad's Corollary 5.12 (printed p.20), where Conrad reduces to
`B = A[t]/(h)` and uses continuity of roots.
-/

noncomputable section

universe u

open Polynomial Filter Topology CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

namespace HenselianFinitePointProper

variable {K : Type u} [NontriviallyNormedField K]

local notation "K̂" => UniformSpace.Completion K

/-- **Finite algebra maps are proper on rational points.** -/
theorem isProperMap_precomp_of_finite (hK : IsHenselianValuedField K)
    (hcl : algebraicClosure K K̂ = ⊥) {A B : Type u} [CommRing A] [CommRing B] [Algebra K A]
    [Algebra K B] (θ : A →ₐ[K] B) (hθ : θ.toRingHom.Finite) :
    IsProperMap (AlgPoint.precomp (S := K) θ) := by
  classical
  let _ : Algebra A B := θ.toRingHom.toAlgebra
  have : Module.Finite A B := hθ
  have hint : Algebra.IsIntegral A B := inferInstance
  obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType A B).out
  rw [isProperMap_iff_ultrafilter_of_t2]
  refine ⟨AlgPoint.continuous_precomp θ, fun 𝒰 ψ h𝒰 => ?_⟩
  have hA : ∀ a : A, Tendsto (fun φ : AlgPoint K B K => φ (θ a)) 𝒰 (𝓝 (ψ a)) := fun a =>
    ((AlgPoint.continuous_eval a).tendsto ψ).comp h𝒰
  -- the generators converge, by continuity of roots of their minimal polynomials
  have hgen : ∀ b ∈ s, ∃ τ : K, Tendsto (fun φ : AlgPoint K B K => φ b) 𝒰 (𝓝 τ) := by
    intro b _
    let h : A[X] := minpoly A b
    have hm : h.Monic := minpoly.monic (Algebra.IsIntegral.isIntegral b)
    let ψr : A →+* K := ψ.toAlgHom.toRingHom
    let pr : AlgPoint K B K → (A →+* K) := fun φ => (φ.toAlgHom.comp θ).toRingHom
    obtain ⟨τ, -, hτ⟩ := HenselianRootContinuity.exists_tendsto_root hK hcl 𝒰
      (fun φ => h.map (pr φ)) (h.map ψr) (hm.map _) (fun φ => hm.map _)
      (fun φ => by rw [hm.natDegree_map, hm.natDegree_map])
      (fun n => by
        simp only [coeff_map]
        exact hA (h.coeff n))
      (fun φ : AlgPoint K B K => φ b)
      (fun φ => by
        have e : h.map (pr φ) = (h.map (algebraMap A B)).map φ.toAlgHom.toRingHom := by
          rw [Polynomial.map_map]
          rfl
        rw [IsRoot.def, e, eval_map]
        change eval₂ φ.toAlgHom.toRingHom (φ.toAlgHom.toRingHom b) _ = 0
        rw [eval₂_at_apply, eval_map_algebraMap, minpoly.aeval, map_zero])
    exact ⟨τ, hτ⟩
  -- hence every element converges
  have hall : ∀ b : B, ∃ τ : K, Tendsto (fun φ : AlgPoint K B K => φ b) 𝒰 (𝓝 τ) := by
    intro b
    have hb : b ∈ Algebra.adjoin A (s : Set B) := by
      rw [hs]
      exact Algebra.mem_top
    induction hb using Algebra.adjoin_induction with
    | mem x hx => exact hgen x hx
    | algebraMap a => exact ⟨ψ a, hA a⟩
    | add x y _ _ hx hy =>
      obtain ⟨τx, hx⟩ := hx
      obtain ⟨τy, hy⟩ := hy
      exact ⟨τx + τy, (hx.add hy).congr fun φ => (map_add φ.toAlgHom x y).symm⟩
    | mul x y _ _ hx hy =>
      obtain ⟨τx, hx⟩ := hx
      obtain ⟨τy, hy⟩ := hy
      exact ⟨τx * τy, (hx.mul hy).congr fun φ => (map_mul φ.toAlgHom x y).symm⟩
  choose lim hlim using hall
  have hconst : ∀ k : K, lim (algebraMap K B k) = k := fun k =>
    tendsto_nhds_unique (hlim _)
      (tendsto_const_nhds.congr fun φ => (φ.toAlgHom.commutes k).symm)
  let φ₀ : B →ₐ[K] K :=
    { toFun := lim
      map_one' := by rw [← map_one (algebraMap K B), hconst]
      map_mul' := fun x y => tendsto_nhds_unique (hlim (x * y))
        (((hlim x).mul (hlim y)).congr fun φ => (map_mul φ.toAlgHom x y).symm)
      map_zero' := by rw [← map_zero (algebraMap K B), hconst]
      map_add' := fun x y => tendsto_nhds_unique (hlim (x + y))
        (((hlim x).add (hlim y)).congr fun φ => (map_add φ.toAlgHom x y).symm)
      commutes' := hconst }
  refine ⟨AlgPoint.ofAlgHom φ₀, ?_⟩
  change Tendsto id (𝒰 : Filter (AlgPoint K B K)) (𝓝 (AlgPoint.ofAlgHom φ₀))
  rw [AlgPoint.isEmbedding_evaluation.isInducing.tendsto_nhds_iff, tendsto_pi_nhds]
  exact fun b => hlim b

/-- **Finite morphisms of affine schemes are proper on rational points.** -/
theorem isProperMap_affineFinitePointMap (hK : IsHenselianValuedField K)
    (hcl : algebraicClosure K K̂ = ⊥) {X Y : Over (Spec (CommRingCat.of K))}
    [IsAffine X.left] [IsAffine Y.left] (f : X ⟶ Y) [IsFinite f.left] :
    IsProperMap (X := RingPoint K X K) (Y := RingPoint K Y K)
      (fun p : RingPoint K X K => (p ≫ f : RingPoint K Y K)) := by
  let phi := affineCoordinatePullback K f
  have hfin : phi.toRingHom.Finite := f.left.finite_appTop
  have hproper := isProperMap_precomp_of_finite hK hcl phi hfin
  have heq : (fun p : RingPoint K X K => (p ≫ f : RingPoint K Y K)) =
      (affineSchemePointHomeomorph K Y K).symm ∘ AlgPoint.precomp phi ∘
        (affineSchemePointHomeomorph K X K) := by
    funext p
    apply (affineSchemePointEquiv K Y K).injective
    change affineSchemePointEquiv K Y K (p ≫ f) =
      (affineSchemePointEquiv K Y K)
        ((affineSchemePointEquiv K Y K).symm
          (AlgPoint.precomp phi (affineSchemePointEquiv K X K p)))
    rw [Equiv.apply_symm_apply]
    exact affineSchemePointEquiv_natural K K f p
  rw [heq]
  exact (affineSchemePointHomeomorph K Y K).symm.isProperMap.comp
    (hproper.comp (affineSchemePointHomeomorph K X K).isProperMap)

end HenselianFinitePointProper

end Langlands.AlgebraicGeometry.PointTopology
