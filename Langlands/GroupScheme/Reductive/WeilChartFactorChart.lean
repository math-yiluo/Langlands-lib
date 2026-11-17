import Langlands.GroupScheme.Reductive.WeilChartFactorGroup

/-! # Chart description of the fixed points of the diagonal factor projection -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false
set_option maxRecDepth 4000

namespace Langlands.GroupScheme.WeilChart

open Langlands.Algebra.GraphIdempotent IdempotentPoints

section KerGraphMul

variable {R B X : Type u} [CommRing R] [CommRing B] [CommRing X] [Algebra R B] [Algebra R X]

theorem ker_graphMul {ρ : B →ₐ[R] X} {ε : B ⊗[R] X} (h : IsGraphIdempotent ρ ε) :
    RingHom.ker (graphMul ρ) = Ideal.span {1 - ε} := by
  ext x
  rw [RingHom.mem_ker]
  constructor
  · intro hx
    have h' := h.mul_eq x
    rw [hx, TensorProduct.tmul_zero, zero_mul] at h'
    exact Ideal.mem_span_singleton'.mpr ⟨x, by rw [mul_sub, mul_one, h', sub_zero]⟩
  · intro hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    rw [map_mul, map_sub, map_one, h.graphMul_eq_one, sub_self, mul_zero]

theorem graphMul_surjective (ρ : B →ₐ[R] X) : Function.Surjective (graphMul ρ) := fun x =>
  ⟨(1 : B) ⊗ₜ[R] x, by rw [Algebra.TensorProduct.productMap_apply_tmul, map_one, one_mul,
    AlgHom.id_apply]⟩

end KerGraphMul

variable {A A' C B : Type u} [CommRing A] [CommRing A'] [CommRing C] [CommRing B]
  [Algebra A A'] [Algebra A' C] [Algebra A B] (e : A' ⊗[A] B ≃ₐ[A'] C)
  [Module.Finite A' C] [Module.Projective A' C] [Algebra.Etale A' C]
  {G : GroupScheme (Spec (CommRingCat.of A))}
  {H : GroupScheme (Spec (CommRingCat.of C))} [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom]
  (P : (GroupScheme.baseChange (Spec.algebraMap A A')).obj G ≅ AffineWeil.groupScheme A' C H)

section Chart

variable {T : CommAlgCat.{u} (CommRingCat.of A)} (φ : B →ₐ[A] T) (g : A' →ₐ[A] T)

/-- The map `C → T`, `e (a ⊗ b) ↦ g a * φ b`, into the test object `T` over itself. -/
def chartRho :
    letI := underAlgebra g (Under.mk (𝟙 T))
    C →ₐ[A'] (Under.mk (𝟙 T)).right :=
  letI := chartAlgebra g
  letI := underAlgebra g (Under.mk (𝟙 T))
  (underMap g (Under.mk (𝟙 T))).comp (diagMap e φ g)

/-- The image of the diagonal idempotent in the test object `T` over itself. -/
abbrev chartEps : letI := underAlgebra g (Under.mk (𝟙 T)); C ⊗[A'] (Under.mk (𝟙 T)).right :=
  baseIdem g (Under.mk (𝟙 T)) (diagIdem e φ g)

omit [Module.Finite A' C] [Module.Projective A' C] in
theorem chartEps_spec :
    letI := underAlgebra g (Under.mk (𝟙 T))
    IsGraphIdempotent (chartRho e φ g) (chartEps e φ g) := by
  letI := chartAlgebra g
  letI := underAlgebra g (Under.mk (𝟙 T))
  exact (diagIdem_spec e φ g).map (underMap g (Under.mk (𝟙 T)))

omit [Module.Finite A' C] [Module.Projective A' C] in
theorem chartEps_isIdempotentElem :
    letI := underAlgebra g (Under.mk (𝟙 T))
    IsIdempotentElem (chartEps e φ g) := by
  letI := underAlgebra g (Under.mk (𝟙 T))
  exact (chartEps_spec e φ g).isIdempotentElem

/-- `T` as a `C`-algebra through `chartRho`. -/
abbrev chartObj : CommAlgCat.{u} (CommRingCat.of C) :=
  letI := underAlgebra g (Under.mk (𝟙 T))
  letI : Algebra C (Under.mk (𝟙 T)).right := (chartRho e φ g).toRingHom.toAlgebra
  CommAlgCat.of (CommRingCat.of C) (Under.mk (𝟙 T)).right

/-- The multiplication `C ⊗[A'] T → T` of `chartRho`, as a map of `C`-algebras. -/
def chartMu :
    (letI := underAlgebra g (Under.mk (𝟙 T)); C ⊗[A'] (Under.mk (𝟙 T)).right) →ₐ[C]
      chartObj e φ g :=
  letI := underAlgebra g (Under.mk (𝟙 T))
  letI : Algebra C (Under.mk (𝟙 T)).right := (chartRho e φ g).toRingHom.toAlgebra
  { (graphMul (chartRho e φ g)).toRingHom with
    commutes' := fun c => by
      change graphMul (chartRho e φ g) (c ⊗ₜ[A'] (1 : (Under.mk (𝟙 T)).right)) =
        chartRho e φ g c
      rw [Algebra.TensorProduct.productMap_apply_tmul, AlgHom.id_apply, mul_one] }

omit [Module.Finite A' C] [Module.Projective A' C] [Algebra.Etale A' C] in
theorem chartMu_apply
    (x : letI := underAlgebra g (Under.mk (𝟙 T)); C ⊗[A'] (Under.mk (𝟙 T)).right) :
    chartMu e φ g x =
      (letI := underAlgebra g (Under.mk (𝟙 T)); graphMul (chartRho e φ g) x) :=
  rfl

omit [Module.Finite A' C] [Module.Projective A' C] [Algebra.Etale A' C] in
theorem chartMu_surjective : Function.Surjective (chartMu e φ g) := by
  letI := underAlgebra g (Under.mk (𝟙 T))
  exact graphMul_surjective (chartRho e φ g)

omit [Module.Finite A' C] [Module.Projective A' C] in
theorem ker_chartMu :
    RingHom.ker (chartMu e φ g) =
      (letI := underAlgebra g (Under.mk (𝟙 T)); Ideal.span {1 - chartEps e φ g}) := by
  letI := underAlgebra g (Under.mk (𝟙 T))
  ext x
  rw [RingHom.mem_ker, chartMu_apply, ← ker_graphMul (chartEps_spec e φ g), RingHom.mem_ker]

omit [Module.Finite A' C] [Module.Projective A' C] in
theorem chartMu_chartEps : chartMu e φ g (chartEps e φ g) = 1 := by
  letI := underAlgebra g (Under.mk (𝟙 T))
  rw [chartMu_apply]
  exact (chartEps_spec e φ g).graphMul_eq_one

/-- The factor of the points of `H` over `C ⊗[A'] T` cut out by `chartEps` is the group of points
of `H` over `T` as a `C`-algebra. -/
def chartFactorEquiv :
    (snd H (chartEps e φ g)).ker ≃* H.affinePoints (chartObj e φ g) :=
  letI := underAlgebra g (Under.mk (𝟙 T))
  letI : Algebra C (Under.mk (𝟙 T)).right := (chartRho e φ g).toRingHom.toAlgebra
  factorEquiv H (chartEps_isIdempotentElem e φ g) (chartMu_surjective e φ g)
    (ker_chartMu e φ g)

omit [Module.Finite A' C] [Module.Projective A' C] [LocallyOfFiniteType H.X.hom] in
theorem affinePointMap_chartMu_proj
    (h : H.affinePoints (CommAlgCat.of (CommRingCat.of C)
      (letI := underAlgebra g (Under.mk (𝟙 T)); C ⊗[A'] (Under.mk (𝟙 T)).right))) :
    H.affinePointMap (CommAlgCat.ofHom (chartMu e φ g)) (proj H (chartEps e φ g) h) =
      H.affinePointMap (CommAlgCat.ofHom (chartMu e φ g)) h := by
  apply ev_injective H
  intro a
  rw [ev_map, ev_map, ev_proj H (chartEps_isIdempotentElem e φ g), map_add, map_mul, map_mul,
    map_sub, map_one, chartMu_chartEps, sub_self, zero_mul, add_zero, one_mul]

theorem underPointsEquiv_diagProj (q : G.affinePoints T) :
    underPointsEquiv P g (Under.mk (𝟙 T)) (diagProj e P φ g q) =
      proj H (chartEps e φ g) (underPointsEquiv P g (Under.mk (𝟙 T)) q) :=
  underPointsEquiv_gpt_chartFactor P g (diagIdem e φ g) (diagIdem_isIdempotentElem e φ g)
    (Under.mk (𝟙 T)) q

theorem diagProj_eq_self_iff (q : G.affinePoints T) :
    diagProj e P φ g q = q ↔
      snd H (chartEps e φ g) (underPointsEquiv P g (Under.mk (𝟙 T)) q) = 1 := by
  have hgpt := underPointsEquiv_diagProj e P φ g q
  constructor
  · intro h
    rw [← h, hgpt]
    exact snd_proj H (chartEps_isIdempotentElem e φ g) _
  · intro h
    apply (underPointsEquiv P g (Under.mk (𝟙 T))).injective
    rw [hgpt]
    exact ((eq_proj_iff H (chartEps_isIdempotentElem e φ g)).mpr ⟨rfl, h⟩).symm

/-- The fixed points of the diagonal factor projection through a chart, as the factor of the
points of `H` cut out by `chartEps`. -/
def fixedKerEquiv :
    MonoidHom.eqLocus (diagProj e P φ g) (MonoidHom.id _) ≃* (snd H (chartEps e φ g)).ker where
  toFun q := ⟨underPointsEquiv P g (Under.mk (𝟙 T)) q.1,
    (diagProj_eq_self_iff e P φ g q.1).1 q.2⟩
  invFun h := ⟨(underPointsEquiv P g (Under.mk (𝟙 T))).symm h.1,
    (diagProj_eq_self_iff e P φ g _).2 (by rw [MulEquiv.apply_symm_apply]; exact h.2)⟩
  left_inv q := Subtype.ext ((underPointsEquiv P g (Under.mk (𝟙 T))).symm_apply_apply q.1)
  right_inv h := Subtype.ext ((underPointsEquiv P g (Under.mk (𝟙 T))).apply_symm_apply h.1)
  map_mul' q q' := Subtype.ext (map_mul (underPointsEquiv P g (Under.mk (𝟙 T))) q.1 q'.1)

/-- **Chart description**: the fixed points of the diagonal factor projection through a chart
are the points of `H` over `T`, regarded as a `C`-algebra through `chartRho`. -/
def chartFixedEquiv :
    MonoidHom.eqLocus (diagProj e P φ g) (MonoidHom.id _) ≃* H.affinePoints (chartObj e φ g) :=
  (fixedKerEquiv e P φ g).trans (chartFactorEquiv e φ g)

theorem chartFixedEquiv_apply (q : MonoidHom.eqLocus (diagProj e P φ g) (MonoidHom.id _)) :
    chartFixedEquiv e P φ g q =
      H.affinePointMap (CommAlgCat.ofHom (chartMu e φ g))
        (underPointsEquiv P g (Under.mk (𝟙 T)) q.1) :=
  rfl

/-- On a projected point the chart description is the image of the original point. -/
theorem chartFixedEquiv_diagProj (q : G.affinePoints T)
    (hq : diagProj e P φ g q ∈ MonoidHom.eqLocus (diagProj e P φ g) (MonoidHom.id _)) :
    chartFixedEquiv e P φ g ⟨diagProj e P φ g q, hq⟩ =
      H.affinePointMap (CommAlgCat.ofHom (chartMu e φ g))
        (underPointsEquiv P g (Under.mk (𝟙 T)) q) := by
  rw [chartFixedEquiv_apply]
  change H.affinePointMap (CommAlgCat.ofHom (chartMu e φ g))
    (underPointsEquiv P g (Under.mk (𝟙 T)) (diagProj e P φ g q)) = _
  rw [underPointsEquiv_diagProj, affinePointMap_chartMu_proj]

end Chart

end Langlands.GroupScheme.WeilChart
