import Langlands.GroupScheme.CentralSurjectionImage.PointWeights
import Langlands.GroupScheme.Torus.CocharacterInseparableDescent
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.RingTheory.Kaehler.Basic

/-! # Rigidity of multiplicative points and purely inseparable descent

A multiplicative point over `S[Λ]` of an affine group scheme which becomes trivial modulo a
nilpotent ideal is trivial: its nonzero weights are convolution idempotents with values in a
nilpotent ideal. As a consequence, cocharacter data of an arbitrary affine commutative group
scheme descend through purely inseparable extensions.
-/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.CentralSurjectionImage

open CocharacterDatum

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffine G.X.left]
variable {S S' : Type u} [CommRing S] [Algebra k S] [CommRing S'] [Algebra k S']
  {Λ : Type u} [AddCommGroup Λ]

/-- Convolution of functionals with values in ideals lands in their product. -/
theorem conv_mem_mul {f g : coordAlgebra G →ₗ[CommRingCat.of k] S} {I J : Ideal S}
    (hf : ∀ b, f b ∈ I) (hg : ∀ b, g b ∈ J) (b : coordAlgebra G) : conv f g b ∈ I * J := by
  simp only [conv, LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply]
  generalize (comul G) b = t
  induction t using TensorProduct.inductionOn with
  | tmul x y =>
    rw [TensorProduct.map_tmul, LinearMap.mul'_apply]
    exact Ideal.mul_mem_mul (hf x) (hg y)
  | add x y hx hy => rw [map_add, map_add]; exact add_mem hx hy

/-- **Rigidity.** A multiplicative point over `S[Λ]` whose image under an algebra map with
nilpotent kernel is trivial is itself trivial. -/
theorem IsMultG.eq_one_of_map_eq_one {p : Lie.AffinePoints G (AddMonoidAlgebra S Λ)}
    (hp : IsMultG p) (φ : S →ₐ[k] S') {n : ℕ} (hn : RingHom.ker φ ^ n = ⊥)
    (h1 : Lie.affineMap G (AddMonoidAlgebra.mapAlgHom Λ φ) p = 1) : p = 1 := by
  classical
  apply hp.eq_one_of_weight_eq_zero
  intro γ hγ
  have hker : ∀ b, weight p γ b ∈ RingHom.ker φ := by
    intro b
    have h := weight_coeffMap (G := G) φ p γ b
    rw [h1, weight_one, ite_eq_right_iff.mpr (fun h => absurd h hγ)] at h
    exact (RingHom.mem_ker).mpr h.symm
  have hpow : ∀ m : ℕ, ∀ b, weight p γ b ∈ RingHom.ker φ ^ (m + 1) := by
    intro m
    induction m with
    | zero => simpa using hker
    | succ m ih =>
      intro b
      have h := LinearMap.congr_fun (hp.conv_weight γ γ) b
      simp only [↓reduceIte] at h
      rw [← h, pow_succ']
      exact conv_mem_mul hker ih b
  ext b
  have hb := hpow n b
  rw [pow_succ, hn, Ideal.bot_mul, Ideal.mem_bot] at hb
  exact hb

/-- The kernel of multiplication `L ⊗[F] L → L` is nilpotent when every `p ^ e`-th power of `L`
lies in `F`, `p` the exponential characteristic and `L` finite over `F`. -/
theorem exists_pow_ker_lmul'_eq_bot {F L : Type u} [Field F] [Field L] [Algebra F L]
    [FiniteDimensional F L] (p e : ℕ) [ExpChar F p]
    (hL : ∀ ℓ : L, ℓ ^ p ^ e ∈ (algebraMap F L).range) :
    ∃ n : ℕ, RingHom.ker (Algebra.TensorProduct.lmul' F : L ⊗[F] L →ₐ[F] L) ^ n = ⊥ := by
  have : ExpChar (L ⊗[F] L) p :=
    expChar_of_injective_algebraMap (algebraMap F (L ⊗[F] L)).injective p
  have : IsArtinianRing (L ⊗[F] L) := IsArtinianRing.of_finite F (L ⊗[F] L)
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_nilradical (R := L ⊗[F] L)
  refine ⟨n, eq_bot_iff.mpr ?_⟩
  have hle : RingHom.ker (Algebra.TensorProduct.lmul' F : L ⊗[F] L →ₐ[F] L) ≤
      nilradical (L ⊗[F] L) := by
    change KaehlerDifferential.ideal F L ≤ _
    rw [← KaehlerDifferential.span_range_eq_ideal, Ideal.span_le]
    rintro _ ⟨s, rfl⟩
    refine ⟨p ^ e, ?_⟩
    rw [sub_pow_expChar_pow, Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.tmul_pow,
      one_pow]
    obtain ⟨c, hc⟩ := hL s
    rw [← hc, ← mul_one (algebraMap F L c), ← Algebra.smul_def, TensorProduct.smul_tmul,
      sub_self]
    exact zero_mem _
  calc _ ≤ nilradical (L ⊗[F] L) ^ n := Ideal.pow_right_mono hle n
    _ = ⊥ := hn
    _ ≤ ⊥ := le_rfl

/-- **Purely inseparable descent of cocharacter data** for an arbitrary affine commutative group
scheme: if every `p ^ e`-th power of `L` lies in `F`, `L` finite over `F`, then a cocharacter datum
over `L[Λ]` gives one of the same weight over `F[Λ]`. -/
theorem IsDatum.exists_of_pow_mem_range_of_finite {Z : CommGroupScheme (Spec (CommRingCat.of k))}
    [IsAffine Z.toGrp.X.left] (p e : ℕ) [ExpChar k p]
    {F L : Type u} [Field F] [Field L] [Algebra k F] [Algebra k L] [Algebra F L]
    [IsScalarTower k F L] [FiniteDimensional F L] (hL : ∀ ℓ : L, ℓ ^ p ^ e ∈ (algebraMap F L).range)
    {χ : characterLattice Z} {m : Λ} {x : Lie.AffinePoints Z.toGrp (AddMonoidAlgebra L Λ)}
    (hx : IsDatum χ m x) :
    ∃ x' : Lie.AffinePoints Z.toGrp (AddMonoidAlgebra F Λ), IsDatum χ m x' := by
  have : ExpChar F p := expChar_of_injective_algebraMap (algebraMap k F).injective p
  let i₁ : L →ₐ[k] L ⊗[F] L :=
    (Algebra.TensorProduct.includeLeft : L →ₐ[F] L ⊗[F] L).restrictScalars k
  let i₂ : L →ₐ[k] L ⊗[F] L :=
    (Algebra.TensorProduct.includeRight : L →ₐ[F] L ⊗[F] L).restrictScalars k
  let φ : L ⊗[F] L →ₐ[k] L ⊗[F] L :=
    ((Algebra.TensorProduct.includeRight : L →ₐ[F] L ⊗[F] L).comp
      (Algebra.TensorProduct.lmul' F)).restrictScalars k
  have hφ₁ : φ.comp i₁ = i₂ := by
    ext ℓ
    simp [φ, i₁, i₂]
  have hφ₂ : φ.comp i₂ = i₂ := by
    ext ℓ
    simp [φ, i₂]
  let g : AddMonoidAlgebra (L ⊗[F] L) Λ →ₐ[k] AddMonoidAlgebra (L ⊗[F] L) Λ :=
    AddMonoidAlgebra.mapAlgHom Λ φ
  have hgcomp : ∀ (f : L →ₐ[k] L ⊗[F] L) (y : Lie.AffinePoints Z.toGrp (AddMonoidAlgebra L Λ)),
      Lie.affineMap Z.toGrp g (coeffMap f y) = coeffMap (φ.comp f) y := by
    intro f y
    have h : g.comp (AddMonoidAlgebra.mapAlgHom Λ f) = AddMonoidAlgebra.mapAlgHom Λ (φ.comp f) := by
      apply AlgHom.ext
      intro a
      ext γ
      simp [g]
    rw [coeffMap, coeffMap, ← Lie.affineMap_comp, h]
  let v := coeffMap i₁ x * (coeffMap i₂ x)⁻¹
  have hgv : Lie.affineMap Z.toGrp g v = 1 := by
    rw [map_mul, map_inv, hgcomp, hgcomp, hφ₁, hφ₂, mul_inv_cancel]
  have hvmult : IsMult v := (hx.mult.coeff_map i₁).mul (hx.mult.coeff_map i₂).inv
  obtain ⟨n, hn⟩ := exists_pow_ker_lmul'_eq_bot (F := F) (L := L) p e hL
  have hker : RingHom.ker φ = RingHom.ker (Algebra.TensorProduct.lmul' F : L ⊗[F] L →ₐ[F] L) := by
    ext z
    simp only [RingHom.mem_ker]
    change (Algebra.TensorProduct.includeRight : L →ₐ[F] L ⊗[F] L)
      (Algebra.TensorProduct.lmul' F z) = 0 ↔ _
    rw [map_eq_zero_iff _ (Algebra.TensorProduct.includeRight_injective
      (algebraMap F L).injective)]
  have hv : v = 1 :=
    IsMultG.eq_one_of_map_eq_one (G := Z.toGrp) hvmult φ (n := n) (by
      change RingHom.ker φ ^ n = ⊥
      rw [hker, hn]) hgv
  have hx₁₂ : coeffMap i₁ x = coeffMap i₂ x := mul_inv_eq_one.mp hv
  let f : F →ₐ[k] L := IsScalarTower.toAlgHom k F L
  have hf : Function.Injective f := (algebraMap F L).injective
  have hfΛ : Function.Injective (AddMonoidAlgebra.mapAlgHom Λ f) := mapAlgHom_injective f hf
  obtain ⟨x', hx'⟩ := exists_affineMap_eq (AddMonoidAlgebra.mapAlgHom Λ f) hfΛ x (by
    intro c
    have hc := congrArg (fun ψ => ψ.hom c) (congrArg coord hx₁₂)
    simp only [coord_affineMap] at hc
    obtain ⟨y, hy⟩ :=
      CocharacterDescent.exists_mapAlgHom_ofId_eq_of_includeLeft_eq_includeRight
        (F := F) (L := L) (Λ := Λ) ((coord x).hom c) (by
          ext γ
          have hcγ := congrArg (fun z : AddMonoidAlgebra (L ⊗[F] L) Λ => z.coeff γ) hc
          simpa [i₁, i₂] using hcγ)
    refine ⟨y, ?_⟩
    rw [← hy]
    ext γ
    simp [f])
  rw [← hx'] at hx
  exact ⟨x', IsDatum.of_coeff_map f hf hx⟩

/-- **Descent to the separable closure** for an arbitrary affine commutative group scheme. -/
theorem IsDatum.exists_separableClosure_of_comm {Z : CommGroupScheme (Spec (CommRingCat.of k))}
    [IsAffine Z.toGrp.X.left] {L : Type u} [Field L] [Algebra k L] [FiniteDimensional k L]
    {χ : characterLattice Z} {m : Λ} {z : Lie.AffinePoints Z.toGrp (AddMonoidAlgebra L Λ)}
    (hz : IsDatum χ m z) :
    ∃ w : Lie.AffinePoints Z.toGrp (AddMonoidAlgebra (separableClosure k L) Λ), IsDatum χ m w := by
  obtain ⟨p, _⟩ := ExpChar.exists k
  have : ExpChar (separableClosure k L) p :=
    expChar_of_injective_algebraMap (algebraMap k (separableClosure k L)).injective p
  have : FiniteDimensional (separableClosure k L) L :=
    Module.Finite.of_restrictScalars_finite k (separableClosure k L) L
  exact IsDatum.exists_of_pow_mem_range_of_finite p
    (IsPurelyInseparable.exponent (separableClosure k L) L)
    (fun ℓ => IsPurelyInseparable.exponent_def' (separableClosure k L) p ℓ) hz

end Langlands.GroupScheme.CentralSurjectionImage
