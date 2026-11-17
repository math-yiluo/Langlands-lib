import Langlands.AbelianScheme.IsogenyKernelCardTateDeterminantStatement
import Langlands.AbelianScheme.Tate.PrimeAdicEvaluationKernel
import Langlands.Algebra.PadicLatticeIndex
import Langlands.Algebra.FiniteGroupPadicCard
import Langlands.AbelianScheme.Tate.GeometricPrimeAdicRankProof
import Langlands.AbelianScheme.Tate.GeometricTorsionRankProof
import Langlands.AbelianScheme.AlgClosedPointDivisibility
import Langlands.AbelianScheme.StructureCohomologyVanishing

/-! # Proof: the `p`-adic size of the kernel of an isogeny -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme.IsogenyKernelCardTateDeterminant

open GroupScheme.Tate

/-- The kernel of the level map at `n` is the subgroup of kernel points killed by `n`. -/
theorem card_ker_levelMap {S : Scheme.{u}} {G : Grp (Over S)} [IsCommMonObj G.X] (T : Over S)
    (f : G ⟶ G) (n : ℕ) :
    Nat.card (levelMap T f n).ker =
      Nat.card (powMonoidHom n : (GroupScheme.pointsHom f T).ker →*
        (GroupScheme.pointsHom f T).ker).ker := by
  have hker : ∀ s : T ⟶ G.X, s ∈ (GroupScheme.pointsHom f T).ker ↔ s ≫ f.hom.hom = 1 :=
    fun s => MonoidHom.mem_ker
  have hlev : ∀ y : Level G T n, y ∈ (levelMap T f n).ker ↔
      (Additive.toMul y).val ≫ f.hom.hom = 1 := by
    intro y
    rw [AddMonoidHom.mem_ker]
    constructor
    · intro h
      exact congrArg (fun z : Level G T n => (Additive.toMul z).val) h
    · intro h
      apply toSection_injective G T n
      exact congrArg Additive.ofMul h
  apply Nat.card_congr
  exact {
    toFun := fun y => ⟨⟨(Additive.toMul y.1).val, (hker _).mpr ((hlev y.1).mp y.2)⟩,
      MonoidHom.mem_ker.mpr (Subtype.ext ((mem_levelGroup G T n _).mp
        (Additive.toMul y.1).property))⟩
    invFun := fun z => ⟨Additive.ofMul ⟨z.1.1, (mem_levelGroup G T n _).mpr
        (congrArg Subtype.val (MonoidHom.mem_ker.mp z.2))⟩,
      (hlev _).mpr ((hker _).mp z.1.2)⟩
    left_inv := fun y => rfl
    right_inv := fun z => rfl }

end Langlands.AbelianScheme.IsogenyKernelCardTateDeterminant

namespace Langlands.AbelianScheme

open GroupScheme.Tate IsogenyKernelCardTateDeterminant

/-- For an isogeny `α` of an abelian scheme over an algebraically closed field and a prime `p`
invertible in the field, the number of kernel points and the determinant of the rational
`p`-adic Tate map of `α` have the same `p`-adic norm. -/
theorem isogenyKernelCardTateDeterminant :
    IsogenyKernelCardTateDeterminantStatement.{u} := by
  intro k _ _ A p _ hp α hα
  classical
  let T := Over.mk (𝟙 (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))
  let f := groupHom α
  let φ := PrimeAdic.map T p f
  obtain ⟨g, hA⟩ := exists_hasRelativeDimension_of_field A
  have hpu : IsUnit ((p : ℕ) : Γ(Scheme.Spec.obj (Opposite.op (CommRingCat.of k)), ⊤)) := by
    simpa using (Ne.isUnit hp).map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
  obtain ⟨⟨e⟩, -, -⟩ := Tate.PrimeAdic.geometricPrimeAdicRank _ A g hA p hpu k (𝟙 _)
  have : Module.Free ℤ_[p] (PrimeAdic.Integral A.toGrp T p) := Module.Free.of_equiv e
  have : Module.Finite ℤ_[p] (PrimeAdic.Integral A.toGrp T p) := Module.Finite.equiv e
  let K := (GroupScheme.pointsHom f T).ker
  have : Finite K := GroupScheme.IsIsogeny.finite_ker_pointsHom (𝟙 _) hα
  have hc0 : 0 < Nat.card K := Nat.card_pos
  have hkerpow : ∀ s : T ⟶ A.toGrp.X, s ≫ f.hom.hom = 1 → s ^ Nat.card K = 1 := by
    intro s hs
    have h := pow_card_eq_one' (G := K) (x := ⟨s, MonoidHom.mem_ker.mpr hs⟩)
    exact congrArg Subtype.val h
  have hinj := PrimeAdic.map_injective_of_ker_pow T p f (Nat.card K) hc0 hkerpow
  have hdet0 := Algebra.PadicLattice.det_ne_zero_of_injective φ hinj
  let N := Nat.card K + (LinearMap.det φ).valuation
  have hlevel := Tate.geometricTorsionRank _ A g hA (p ^ N) (pow_pos (Fact.out : p.Prime).pos N)
    (by rw [Nat.cast_pow]; exact hpu.pow N) k (𝟙 _)
  have hcardN : Nat.card (Level A.toGrp T (p ^ N)) = (p ^ N) ^ (2 * g) := hlevel.2
  have : Finite (Level A.toGrp T (p ^ N)) := Nat.finite_of_card_ne_zero (by
    rw [hcardN]
    exact pow_ne_zero _ (pow_ne_zero _ (Fact.out : p.Prime).ne_zero))
  have hdiv : ∀ y : T ⟶ A.toGrp.X, ∃ x, x ^ p = y := fun y =>
    algClosedPointDivisibility _ A k (𝟙 _) p hp y
  have hsurj := PrimeAdic.evaluation_surjective_of_pow A.toGrp T p hdiv N
  have hdivN : ∀ m, ((p ^ N : ℕ) : ℤ_[p]) • m ∈ LinearMap.range φ := fun m => by
    rw [Nat.cast_pow]
    exact Algebra.PadicLattice.pow_smul_mem_range φ hdet0 N (by omega) m
  calc ‖((Nat.card K : ℕ) : ℚ_[p])‖
      = ‖((Nat.card (powMonoidHom (p ^ N) : K →* K).ker : ℕ) : ℚ_[p])‖ :=
        Algebra.PadicLattice.norm_card_eq_norm_card_ker_pow N (by omega)
    _ = ‖((Nat.card (levelMap T f (p ^ N)).ker : ℕ) : ℚ_[p])‖ := by
        rw [card_ker_levelMap]
    _ = ‖((Nat.card (Level A.toGrp T (p ^ N) ⧸ (levelMap T f (p ^ N)).range) : ℕ) :
          ℚ_[p])‖ := by
        rw [Algebra.PadicLattice.card_ker_eq_card_quotient_range]
    _ = ‖((Nat.card (PrimeAdic.Integral A.toGrp T p ⧸ LinearMap.range φ) : ℕ) : ℚ_[p])‖ := by
        rw [PrimeAdic.card_quotient_range_map_eq T p f N hsurj hdivN]
    _ = ‖((LinearMap.det φ : ℤ_[p]) : ℚ_[p])‖ :=
        Algebra.PadicLattice.norm_card_quotient_range φ hdet0
    _ = ‖LinearMap.det (Tate.PrimeAdic.rationalMap T p α)‖ := by
        have hb : LinearMap.det (Tate.PrimeAdic.rationalMap T p α) =
            algebraMap ℤ_[p] ℚ_[p] (LinearMap.det φ) := LinearMap.det_baseChange φ
        rw [hb]
        rfl

end Langlands.AbelianScheme
