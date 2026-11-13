import Langlands.GroupScheme.Quaternionic.BinaryQuaternionSpinProduct

/-! # The diagonal μ₂ in the combined binary spin lift -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution.IsSpinCover

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] {σ : FirstKindInvolution K D}
  {n : Type} [Fintype n] [DecidableEq n] {q : σ.QuadraticForms n}
  {S : GroupScheme (Spec (CommRingCat.of K))}
  {π : S ⟶ σ.isometryGroup q}

/-- The full kernel of a supplied spin cover is central, on every relative test. -/
theorem kernel_isCentral (hπ : σ.IsSpinCover q π) : IsCentral (kernelι π) := by
  let := hπ.smooth
  obtain ⟨p, hp, hpp⟩ := hπ.exists_centralIsogeny
  apply (isCentral_kernelι_iff π).mpr
  intro T x hx
  have hx' : x ≫ p.hom.hom = 1 := by
    apply (cancel_mono (identityComponentι (σ.isometryGroup q)).hom.hom).mp
    rw [Category.assoc, ← Grp.comp_hom_hom, hpp, hx, MonObj.one_comp]
  exact (isCentral_kernelι_iff p).mp hp.isCentral_kernelι T x hx'

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution.IsSpinCover

namespace Langlands.GroupScheme.Quaternionic.BinarySpinLift

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D] [Infinite K]
  (σ : FirstKindInvolution K D)
  (hdim : Module.finrank K D = 4) (hsym : Module.finrank K σ.symmetricSubspace = 3)
  {n : Type} [Fintype n] [DecidableEq n]
  {q : σ.QuadraticForms n} {e f : n → D} (h : σ.IsHyperbolicPair q e f)
  {S : GroupScheme (Spec (CommRingCat.of K))}
  {π : S ⟶ σ.isometryGroup q}
  (hπ : σ.IsSpinCover q π)
  (hsc : CentralSimpleUnits.DegreeTwoNormOneSimplyConnectedStatement.{u})

/-- Every ambient-kernel test point has exactly one original diagonal μ₂ preimage. -/
theorem existsUnique_diagonal_of_ambient_eq_one
    (T : Over (Spec (CommRingCat.of K)))
    (z : T ⟶ (BinaryScheme.groupScheme (K := K) (D := D)).X)
    (hz : z ≫ (AmbientBinaryScheme.isometryHom σ hdim hsym h).hom.hom = 1) :
    ∃! x : T ⟶ (BinaryKernel.muTwo (K := K)).X,
      x ≫ (BinaryKernel.diagonal hdim).hom.hom = z := by
  have hr := AmbientBinaryScheme.diagonal_range σ hdim hsym h
  have hm : z ∈ (SubgroupFunctor.range
      (kernelι (AmbientBinaryScheme.isometryHom σ hdim hsym h))).carrier T :=
    (mem_range_kernelι_iff _ _).mpr hz
  rw [← hr] at hm
  obtain ⟨x, hx⟩ := SubgroupFunctor.mem_range.mp hm
  refine ⟨x, hx, ?_⟩
  intro y hy
  apply (cancel_mono (BinaryKernel.diagonal hdim).hom.hom).mp
  exact hy.trans hx.symm

/-- The original diagonal μ₂ mapped into the supplied spin group. -/
def diagonalSpin : BinaryKernel.muTwo (K := K) ⟶ S :=
  BinaryKernel.diagonal hdim ≫ productHom σ hdim hsym h hπ hsc

/-- The diagonal spin morphism takes values in the full supplied spin kernel. -/
@[reassoc] theorem diagonalSpin_comp :
    (diagonalSpin σ hdim hsym h hπ hsc).hom.hom ≫ π.hom.hom = 1 := by
  change ((BinaryKernel.diagonal hdim).hom.hom ≫
    (productHom σ hdim hsym h hπ hsc).hom.hom) ≫ π.hom.hom = 1
  rw [Category.assoc, ← Grp.comp_hom_hom, productHom_comp]
  apply (mem_range_kernelι_iff _ _).mp
  rw [← AmbientBinaryScheme.diagonal_range σ hdim hsym h]
  exact SubgroupFunctor.mem_range.mpr ⟨𝟙 _, Category.id_comp _⟩

/-- The entire diagonal spin image is central, including over nonreduced tests. -/
theorem diagonalSpin_isCentral :
    IsCentral (diagonalSpin σ hdim hsym h hπ hsc) := by
  intro T x
  apply (isCentral_kernelι_iff π).mp hπ.kernel_isCentral T
  rw [Category.assoc, diagonalSpin_comp, MonObj.comp_one]

/-- The diagonal spin image is exactly the part of the combined image lying in the spin kernel. -/
theorem diagonalSpin_range :
    SubgroupFunctor.range (diagonalSpin σ hdim hsym h hπ hsc) =
      SubgroupFunctor.range (productHom σ hdim hsym h hπ hsc) ⊓
        SubgroupFunctor.range (kernelι π) := by
  apply SubgroupFunctor.ext
  intro T
  ext s
  change s ∈ (SubgroupFunctor.range (diagonalSpin σ hdim hsym h hπ hsc)).carrier T ↔
    s ∈ (SubgroupFunctor.range (productHom σ hdim hsym h hπ hsc)).carrier T ∧
      s ∈ (SubgroupFunctor.range (kernelι π)).carrier T
  rw [mem_range_kernelι_iff]
  simp only [SubgroupFunctor.mem_range]
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨⟨x ≫ (BinaryKernel.diagonal hdim).hom.hom, ?_⟩, ?_⟩
    · simp only [diagonalSpin, Grp.comp_hom_hom, Category.assoc]
    · rw [Category.assoc, diagonalSpin_comp, MonObj.comp_one]
  · rintro ⟨⟨z, rfl⟩, hz⟩
    have hz' : z ≫ (AmbientBinaryScheme.isometryHom σ hdim hsym h).hom.hom = 1 := by
      rw [Category.assoc, ← Grp.comp_hom_hom, productHom_comp] at hz
      exact hz
    obtain ⟨x, hx, -⟩ := existsUnique_diagonal_of_ambient_eq_one σ hdim hsym h T z hz'
    refine ⟨x, ?_⟩
    rw [diagonalSpin, Grp.comp_hom_hom, ← Category.assoc, hx]

/-- A point in the kernel of the combined spin lift is an original diagonal point
whose diagonal spin image is the identity. -/
theorem productHom_eq_one_iff_diagonal
    (T : Over (Spec (CommRingCat.of K)))
    (z : T ⟶ (BinaryScheme.groupScheme (K := K) (D := D)).X) :
    z ≫ (productHom σ hdim hsym h hπ hsc).hom.hom = 1 ↔
      ∃ x : T ⟶ (BinaryKernel.muTwo (K := K)).X,
        x ≫ (BinaryKernel.diagonal hdim).hom.hom = z ∧
          x ≫ (diagonalSpin σ hdim hsym h hπ hsc).hom.hom = 1 := by
  constructor
  · intro hz
    have hz' : z ≫ (AmbientBinaryScheme.isometryHom σ hdim hsym h).hom.hom = 1 := by
      rw [← productHom_comp σ hdim hsym h hπ hsc, Grp.comp_hom_hom,
        ← Category.assoc, hz, MonObj.one_comp]
    obtain ⟨x, hx, -⟩ := existsUnique_diagonal_of_ambient_eq_one σ hdim hsym h T z hz'
    refine ⟨x, hx, ?_⟩
    rw [diagonalSpin, Grp.comp_hom_hom, ← Category.assoc, hx, hz]
  · rintro ⟨x, rfl, hx⟩
    simpa only [diagonalSpin, Grp.comp_hom_hom, Category.assoc] using hx

/-- Injectivity of the diagonal spin morphism suffices for injectivity of the whole
combined binary spin homomorphism. -/
theorem productHom_points_injective_of_diagonalSpin
    (hm : Mono (diagonalSpin σ hdim hsym h hπ hsc).hom.hom)
    (T : Over (Spec (CommRingCat.of K))) :
    Function.Injective (fun z : T ⟶ (BinaryScheme.groupScheme (K := K) (D := D)).X =>
      z ≫ (productHom σ hdim hsym h hπ hsc).hom.hom) := by
  let := hm
  intro x y hxy
  change x ≫ (productHom σ hdim hsym h hπ hsc).hom.hom =
    y ≫ (productHom σ hdim hsym h hπ hsc).hom.hom at hxy
  have hz : (x / y) ≫ (productHom σ hdim hsym h hπ hsc).hom.hom = 1 := by
    rw [GrpObj.div_comp, hxy, div_self']
  obtain ⟨w, hw, hw1⟩ :=
    (productHom_eq_one_iff_diagonal σ hdim hsym h hπ hsc T (x / y)).mp hz
  have hw' : w = 1 := by
    apply (cancel_mono (diagonalSpin σ hdim hsym h hπ hsc).hom.hom).mp
    rw [hw1, MonObj.one_comp]
  have hdiv : x / y = 1 := by
    rw [← hw, hw', MonObj.one_comp]
  exact div_eq_one.mp hdiv

end Langlands.GroupScheme.Quaternionic.BinarySpinLift
