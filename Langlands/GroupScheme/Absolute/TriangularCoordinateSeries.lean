import Langlands.GroupScheme.Absolute.TriangularCoordinateMaps
import Langlands.GroupScheme.Dynamic.GeneralLinearDecomposition

/-! # Finite coordinate series for the actual triangular diagonal kernel -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.TriangularLayer

variable {A : Type*} [CommRing A] {N : ℕ}

/-- The first matrix term is the full unitriangular subgroup for the usual
strictly decreasing weights. -/
theorem W_zero_eq_blockUnipotentSubgroup :
    W A N 0 = GeneralLinear.blockUnipotentSubgroup A (fun i : Fin N => -(i.val : ℤ)) := by
  ext g
  rw [mem_W, GeneralLinear.mem_blockUnipotentSubgroup]
  constructor
  · intro hg i j hij
    exact sub_eq_zero.mp (hg i j (by omega))
  · intro hg i j hij
    rw [Matrix.sub_apply, hg i j (by omega), sub_self]

/-- On an actual triangular matrix, the first term is precisely the kernel
of its diagonal projection, with coefficients in the original ring. -/
theorem mem_W_zero_iff_projection_eq_one
    (g : GeneralLinear.blockParabolicSubgroup A (fun i : Fin N => -(i.val : ℤ))) :
    g.val ∈ W A N 0 ↔
      GeneralLinear.blockLeviProjection A (fun i : Fin N => -(i.val : ℤ)) g = 1 := by
  rw [W_zero_eq_blockUnipotentSubgroup, GeneralLinear.mem_blockUnipotentSubgroup,
    GeneralLinear.blockUnipotent_iff]
  constructor
  · intro h
    exact Units.ext h.2
  · intro h
    exact ⟨g.property, congrArg (fun z : GL (Fin N) A => (z : Matrix (Fin N) (Fin N) A)) h⟩

/-- A row with no position on the next superdiagonal adds no equation. -/
theorem refinedW_succ_of_out_of_range (a b : ℕ) (h : N ≤ b + a + 1) :
    refinedW A N a (b + 1) = refinedW A N a b := by
  apply le_antisymm (refinedW_anti a (by omega))
  intro g hg
  refine ⟨hg.1, ?_⟩
  intro i j hi
  by_cases hib : (i : ℕ) < b
  · exact hg.2 i j hib
  · rw [layer_apply, ite_eq_right (by have := j.isLt; omega)]

variable {R : CommRingCat.{u}} {H : GroupScheme (Spec R)}

/-- The first full inverse-image term equals the full scheme-theoretic
kernel of the actual triangular diagonal projection on every test scheme. -/
theorem filtration_zero_eq_diagonal_kernel
    (j : H ⟶ GeneralLinear.blockParabolicScheme (Fin N) R
      (fun i => -(i.val : ℤ))) :
    SubgroupFunctor.range (filtrationHom
      (j ≫ GeneralLinear.blockParabolicHom (Fin N) R _) 0 0) =
        SubgroupFunctor.range (kernelι
          (j ≫ GeneralLinear.blockLimitHom (Fin N) R _)) := by
  have : Mono (GeneralLinear.blockLeviHom (Fin N) R
      (fun i => -(i.val : ℤ))).hom.hom :=
    (GeneralLinear.isRepresentedBy_blockLevi (Fin N) R _).1
  ext T x
  rw [mem_range_filtrationHom, refinedW_zero, mem_range_kernelι_iff]
  have hp : GeneralLinear.pointsEquiv (Fin N) R T
      ((x ≫ j.hom.hom) ≫ (GeneralLinear.blockParabolicHom (Fin N) R _).hom.hom) ∈
        GeneralLinear.blockParabolicSubgroup Γ(T.left, ⊤)
          (fun i : Fin N => -(i.val : ℤ)) :=
    ((GeneralLinear.isRepresentedBy_blockParabolic (Fin N) R
      (fun i => -(i.val : ℤ))).pointsEquiv T (x ≫ j.hom.hom)).property
  change GeneralLinear.pointsEquiv (Fin N) R T
    ((x ≫ j.hom.hom) ≫ (GeneralLinear.blockParabolicHom (Fin N) R _).hom.hom) ∈ W _ N 0 ↔ _
  rw [mem_W_zero_iff_projection_eq_one ⟨_, hp⟩,
    ← GeneralLinear.pointsEquiv_blockLimitHom]
  constructor
  · intro hx
    apply (cancel_mono (GeneralLinear.blockLeviHom (Fin N) R
      (fun i => -(i.val : ℤ))).hom.hom).mp
    apply (GeneralLinear.pointsEquiv (Fin N) R T).injective
    simpa only [Grp.comp_hom_hom, Category.assoc, MonObj.one_comp, map_one] using hx
  · intro hx
    simpa only [Grp.comp_hom_hom, Category.assoc, MonObj.one_comp, map_one] using
      congrArg (fun z => GeneralLinear.pointsEquiv (Fin N) R T
        (z ≫ (GeneralLinear.blockLeviHom (Fin N) R
          (fun i => -(i.val : ℤ))).hom.hom)) hx

/-- Enumerate the refined terms by superdiagonal and then by row. The
finite series consists of the terms with `t ≤ N * N`. -/
abbrev seriesScheme (ρ : MatrixRepresentation H (Fin N)) (t : ℕ) :
    GroupScheme (Spec R) :=
  filtrationScheme ρ (t / N) (t % N)

/-- The actual closed inclusion of an enumerated term into the source. -/
abbrev seriesHom (ρ : MatrixRepresentation H (Fin N)) (t : ℕ) :
    seriesScheme ρ t ⟶ H :=
  filtrationHom ρ (t / N) (t % N)

theorem range_seriesHom_zero (ρ : MatrixRepresentation H (Fin N)) :
    SubgroupFunctor.range (seriesHom ρ 0) =
      SubgroupFunctor.range (filtrationHom ρ 0 0) := by
  exact congrArg₂ (fun a b : ℕ => SubgroupFunctor.range (filtrationHom ρ a b))
    (Nat.zero_div N) (Nat.zero_mod N)

theorem range_seriesHom_index (ρ : MatrixRepresentation H (Fin N))
    (hN : 0 < N) (a b : ℕ) (hb : b < N) :
    SubgroupFunctor.range (seriesHom ρ (a * N + b)) =
      SubgroupFunctor.range (filtrationHom ρ a b) := by
  have hd : (a * N + b) / N = a := by
    rw [Nat.mul_comm a N, Nat.mul_add_div hN, Nat.div_eq_of_lt hb, Nat.add_zero]
  have hm : (a * N + b) % N = b := by
    simp [Nat.add_mod, Nat.mod_eq_of_lt hb]
  exact congrArg₂ (fun a b : ℕ => SubgroupFunctor.range (filtrationHom ρ a b)) hd hm

/-- At the end of each row enumeration, the next term is the beginning
of the next superdiagonal. -/
theorem range_seriesHom_succ (ρ : MatrixRepresentation H (Fin N))
    (hN : 0 < N) (t : ℕ) :
    SubgroupFunctor.range (seriesHom ρ (t + 1)) =
      SubgroupFunctor.range (filtrationHom ρ (t / N) (t % N + 1)) := by
  have ht : t + 1 = t / N * N + (t % N + 1) := by
    have := Nat.div_add_mod t N
    rw [Nat.mul_comm N (t / N)] at this
    omega
  have hb := Nat.mod_lt t hN
  rcases lt_or_eq_of_le (Nat.succ_le_of_lt hb) with h | h
  · rw [ht, range_seriesHom_index ρ hN _ _ h]
  · change t % N + 1 = N at h
    have ht' : t + 1 = (t / N + 1) * N + 0 := by
      rw [ht, h, Nat.add_mul, Nat.one_mul, Nat.add_zero]
    rw [ht', range_seriesHom_index ρ hN _ _ hN, h, filtration_top]

theorem seriesHom_succ_le (ρ : MatrixRepresentation H (Fin N))
    (hN : 0 < N) (t : ℕ) :
    SubgroupFunctor.range (seriesHom ρ (t + 1)) ≤
      SubgroupFunctor.range (seriesHom ρ t) := by
  rw [range_seriesHom_succ ρ hN]
  exact filtration_anti ρ _ (Nat.le_succ _)

/-- The last term is the full trivial subgroup functor for a faithful
representation, including at matrix size zero. -/
theorem range_seriesHom_last (ρ : MatrixRepresentation H (Fin N))
    [Mono ρ.hom.hom] :
    SubgroupFunctor.range (seriesHom ρ (N * N)) = ⊥ := by
  by_cases hN : N = 0
  · subst N
    simpa only [seriesHom, Nat.zero_mul, Nat.zero_div, Nat.zero_mod] using
      filtration_eq_bot ρ
  · have hN' : 0 < N := Nat.pos_of_ne_zero hN
    have h := range_seriesHom_index ρ hN' N 0 hN'
    simpa only [Nat.add_zero, filtration_eq_bot ρ] using h

theorem isNormal_seriesHom
    (j : H ⟶ GeneralLinear.blockParabolicScheme (Fin N) R
      (fun i => -(i.val : ℤ))) (t : ℕ) :
    (SubgroupFunctor.range (seriesHom
      (j ≫ GeneralLinear.blockParabolicHom (Fin N) R _) t)).IsNormal :=
  isNormal_triangular_filtration j _ _

/-- The finite series starts at the actual diagonal kernel. -/
theorem range_seriesHom_first
    (j : H ⟶ GeneralLinear.blockParabolicScheme (Fin N) R
      (fun i => -(i.val : ℤ))) :
    SubgroupFunctor.range (seriesHom
      (j ≫ GeneralLinear.blockParabolicHom (Fin N) R _) 0) =
        SubgroupFunctor.range (kernelι
          (j ≫ GeneralLinear.blockLimitHom (Fin N) R _)) :=
  (range_seriesHom_zero _).trans (filtration_zero_eq_diagonal_kernel j)

/-- An index whose row has no next-superdiagonal entry contributes a
repeated term, rather than an extra hypothesis on the matrix size. -/
theorem range_seriesHom_succ_of_out_of_range
    (ρ : MatrixRepresentation H (Fin N)) (hN : 0 < N) (t : ℕ)
    (h : N ≤ t % N + t / N + 1) :
    SubgroupFunctor.range (seriesHom ρ (t + 1)) =
      SubgroupFunctor.range (seriesHom ρ t) := by
  rw [range_seriesHom_succ ρ hN]
  ext T x
  rw [mem_range_filtrationHom, mem_range_filtrationHom,
    refinedW_succ_of_out_of_range _ _ h]

/-- At each genuine coordinate position, the successor is the full
kernel of the actual additive coordinate on the current term. -/
theorem range_kernel_seriesCoordinate
    (ρ : MatrixRepresentation H (Fin N)) (hN : 0 < N) (t : ℕ)
    (h : t % N + t / N + 1 < N) :
    SubgroupFunctor.range
      (kernelι (filtrationCoordinate ρ (t / N) (t % N)
        ⟨t % N, Nat.mod_lt t hN⟩ ⟨t % N + t / N + 1, h⟩) ≫
          seriesHom ρ t) =
        SubgroupFunctor.range (seriesHom ρ (t + 1)) := by
  rw [range_seriesHom_succ ρ hN]
  exact range_kernel_filtrationCoordinate ρ (t / N)
    ⟨t % N, Nat.mod_lt t hN⟩ ⟨t % N + t / N + 1, h⟩ rfl

end Langlands.GroupScheme.TriangularLayer
