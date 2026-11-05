import Langlands.GroupScheme.Reductive.CharZeroSemisimplicity.NilpotentIdeal
import Langlands.GroupScheme.Reductive.CharZeroSemisimplicity.LieImage
import Langlands.GroupScheme.Reductive.CharZeroSemisimplicity.JordanClosure
import Langlands.GroupScheme.Reductive.InvariantLinearForm
import Langlands.Algebra.LinearLieSemisimplicity

/-! # The tangent Lie algebra of a pair of representations -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Module
open scoped Matrix CategoryTheory.MonObj

attribute [local instance 100] LieRing.ofAssociativeRing

namespace Langlands.GroupScheme.MatrixRepresentation

/-- Powers of a block-diagonal endomorphism are block diagonal. -/
theorem prodMap_pow {k : Type*} [Field k] {V W : Type*} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (f : Module.End k V) (g : Module.End k W) (r : ℕ) :
    (f.prodMap g) ^ r = (f ^ r).prodMap (g ^ r) := by
  have h := map_pow (LinearMap.prodMapRingHom k V W) (f, g) r
  simpa using h.symm

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- The tangent endomorphisms of two representations acting together, block
diagonally, on the product of their coordinate spaces. -/
def pairTangent (σ : MatrixRepresentation G m) (ρ : MatrixRepresentation G n) :
    Additive (lieKernel G k) →ₗ[k] Module.End k ((m → k) × (n → k)) :=
  (LinearMap.prodMapLinear k (m → k) (n → k) (m → k) (n → k) k).comp
    (((Matrix.toLin' : Matrix m m k ≃ₗ[k] _).toLinearMap.comp (σ.kernelDifferential k)).prod
      ((Matrix.toLin' : Matrix n n k ≃ₗ[k] _).toLinearMap.comp (ρ.kernelDifferential k)))

omit [LocallyOfFiniteType G.X.hom] in
theorem pairTangent_apply (σ : MatrixRepresentation G m) (ρ : MatrixRepresentation G n)
    (X : Additive (lieKernel G k)) :
    pairTangent σ ρ X =
      (Matrix.toLin' (σ.tangentMatrix k X.toMul)).prodMap
        (Matrix.toLin' (ρ.tangentMatrix k X.toMul)) := rfl

/-- The image of `pairTangent`; it is closed under commutators by
`tangentMatrix_kernelBracket`. -/
def pairLieAlgebra (σ : MatrixRepresentation G m) (ρ : MatrixRepresentation G n) :
    LieSubalgebra k (Module.End k ((m → k) × (n → k))) :=
  { LinearMap.range (pairTangent σ ρ) with
    lie_mem' := by
      rintro _ _ ⟨X, rfl⟩ ⟨Y, rfl⟩
      refine ⟨Additive.ofMul (kernelBracket X.toMul Y.toMul), ?_⟩
      rw [LieRing.of_associative_ring_bracket]
      apply LinearMap.ext
      rintro ⟨u, w⟩
      simp [pairTangent_apply, tangentMatrix_kernelBracket, Matrix.toLin'_apply,
        Matrix.mulVec_mulVec] }

theorem mem_pairLieAlgebra (σ : MatrixRepresentation G m) (ρ : MatrixRepresentation G n)
    (x : Module.End k ((m → k) × (n → k))) :
    x ∈ pairLieAlgebra σ ρ ↔ ∃ X, pairTangent σ ρ X = x := Iff.rfl

/-- The pair Lie algebra contains the Jordan semisimple parts of its elements. -/
theorem jordanSemisimplePart_mem_pairLieAlgebra [PerfectField k]
    (σ : MatrixRepresentation G m) (ρ : MatrixRepresentation G n)
    (x : Module.End k ((m → k) × (n → k))) (hx : x ∈ pairLieAlgebra σ ρ) :
    Langlands.LinearAlgebra.jordanSemisimplePart x ∈ pairLieAlgebra σ ρ := by
  obtain ⟨X, rfl⟩ := hx
  refine ⟨Additive.ofMul (Lie.semisimpleKernel G X.toMul), ?_⟩
  rw [pairTangent_apply, pairTangent_apply, Langlands.LinearAlgebra.jordanSemisimplePart_prodMap,
    toMul_ofMul, toLin'_tangentMatrix_semisimpleKernel, toLin'_tangentMatrix_semisimpleKernel]

section CharZero

variable [CharZero k] [Smooth G.X.hom] [ConnectedSpace G.X.left]

/-- If `σ` is a closed embedding and `G` has trivial unipotent radical, the pair Lie
algebra has no nonzero ideal of nilpotent endomorphisms. The first blocks of such
an ideal form a space of nilpotent tangent endomorphisms of `σ` normalized by all
tangent endomorphisms of `σ`, so `eq_one_of_nilpotent_normalized` applies. -/
theorem pairLieAlgebra_nilpotentIdeal_eq_bot (hrad : HasTrivialUnipotentRadical G)
    (σ : MatrixRepresentation G m) (hσ : IsClosedSubgroup σ) (ρ : MatrixRepresentation G n)
    (I : LieIdeal k (pairLieAlgebra σ ρ))
    (hI : ∀ x ∈ I, IsNilpotent ((x : pairLieAlgebra σ ρ) : Module.End k ((m → k) × (n → k)))) :
    I = ⊥ := by
  let h := pairLieAlgebra σ ρ
  let π : Module.End k ((m → k) × (n → k)) →ₗ[k] Module.End k (m → k) :=
    { toFun := fun f => LinearMap.fst k (m → k) (n → k) ∘ₗ f ∘ₗ LinearMap.inl k (m → k) (n → k)
      map_add' := fun f g => by ext; simp
      map_smul' := fun c f => by ext; simp }
  have hπ : ∀ X : Additive (lieKernel G k),
      π (pairTangent σ ρ X) = Matrix.toLin' (σ.tangentMatrix k X.toMul) := by
    intro X
    ext v
    simp [π, pairTangent_apply]
  let A : Submodule k (Module.End k (m → k)) :=
    (I : Submodule k h).map (π ∘ₗ (h.incl : h →ₗ[k] Module.End k ((m → k) × (n → k))))
  have hA : ∀ a, a ∈ A ↔ ∃ y ∈ I, π (y : Module.End k ((m → k) × (n → k))) = a :=
    fun a => Iff.rfl
  have hnil : ∀ a ∈ A, IsNilpotent a := by
    intro a ha
    obtain ⟨y, hy, rfl⟩ := (hA a).mp ha
    obtain ⟨r, hr⟩ := hI y hy
    obtain ⟨Y, hY⟩ := y.2
    refine ⟨r, LinearMap.ext fun v => ?_⟩
    have h2 := congrArg Prod.fst (LinearMap.congr_fun hr (v, 0))
    rw [← hY, pairTangent_apply, prodMap_pow] at h2
    rw [← hY, hπ]
    simpa using h2
  have hsub : ∀ a ∈ A, ∃ Y : lieKernel G k, Matrix.toLin' (σ.tangentMatrix k Y) = a := by
    intro a ha
    obtain ⟨y, -, rfl⟩ := (hA a).mp ha
    obtain ⟨Y, hY⟩ := y.2
    exact ⟨Y.toMul, by rw [← hY, hπ]⟩
  have hbr : ∀ (Y : lieKernel G k), ∀ a ∈ A,
      Matrix.toLin' (σ.tangentMatrix k Y) * a - a * Matrix.toLin' (σ.tangentMatrix k Y) ∈ A := by
    intro Y a ha
    obtain ⟨y, hy, rfl⟩ := (hA a).mp ha
    let z : h := ⟨pairTangent σ ρ (Additive.ofMul Y), ⟨_, rfl⟩⟩
    refine (hA _).mpr ⟨⁅z, y⁆, I.lie_mem hy, ?_⟩
    rw [LieSubalgebra.coe_bracket, LieRing.of_associative_ring_bracket]
    apply LinearMap.ext
    intro v
    simp [π, z, pairTangent_apply]
  rw [eq_bot_iff]
  intro x hx
  rw [LieSubmodule.mem_bot]
  obtain ⟨X, hX⟩ := x.2
  have h1 : X.toMul = 1 :=
    eq_one_of_nilpotent_normalized hrad σ hσ A hnil hsub hbr X.toMul
      ((hA _).mpr ⟨x, hx, by rw [← hX, hπ]⟩)
  apply Subtype.ext
  change (x : Module.End k ((m → k) × (n → k))) = 0
  rw [← hX, ← ofMul_toMul X, h1, ofMul_one, map_zero]

section Transfer

variable [IsAlgClosed k] [IsReduced G.X.left]

/-- If the pair Lie algebra is completely reducible on the product, the rational
representation of `ρ` is semisimple. A rational subrepresentation `W` is stable
under every tangent matrix, so `(m → k) × W` is a Lie submodule; the second
projection of a Lie complement is a tangent-stable, hence rational, complement
of `W`. -/
theorem isSemisimpleRepresentation_of_pairLieAlgebra
    (σ : MatrixRepresentation G m) (ρ : MatrixRepresentation G n)
    (hc : ComplementedLattice (LieSubmodule k (pairLieAlgebra σ ρ) ((m → k) × (n → k)))) :
    ρ.rationalRepresentation.IsSemisimpleRepresentation := by
  let h := pairLieAlgebra σ ρ
  have hstab : ∀ W : Submodule k (n → k),
      (∀ g v, v ∈ W → (ρ.rationalMatrix g : Matrix n n k) *ᵥ v ∈ W) ↔
        ∀ (X : lieKernel G k) v, v ∈ W → ρ.tangentMatrix k X *ᵥ v ∈ W := fun W =>
    (isStableSubspace_iff_rationalMatrix ρ W).symm.trans (isStableSubspace_iff_tangentMatrix ρ W)
  refine ⟨fun W => ?_⟩
  have hW : ∀ (X : lieKernel G k) v, v ∈ W.toSubmodule →
      ρ.tangentMatrix k X *ᵥ v ∈ W.toSubmodule :=
    (hstab W.toSubmodule).mp fun g _ hv => W.apply_mem_toSubmodule g hv
  let Wt : LieSubmodule k h ((m → k) × (n → k)) :=
    { (⊤ : Submodule k (m → k)).prod W.toSubmodule with
      lie_mem := by
        rintro ⟨_, X, rfl⟩ p ⟨-, hp⟩
        refine ⟨Submodule.mem_top, ?_⟩
        change (pairTangent σ ρ X p).2 ∈ W.toSubmodule
        rw [pairTangent_apply, LinearMap.prodMap_apply, Matrix.toLin'_apply]
        exact hW X.toMul _ hp }
  obtain ⟨C, hC⟩ := exists_isCompl Wt
  have hC' := LieSubmodule.isCompl_toSubmodule.mpr hC
  let W' : Submodule k (n → k) := (C : Submodule k _).map (LinearMap.snd k (m → k) (n → k))
  have hW' : ∀ (X : lieKernel G k) v, v ∈ W' → ρ.tangentMatrix k X *ᵥ v ∈ W' := by
    rintro X _ ⟨c, hc, rfl⟩
    let x : h := ⟨pairTangent σ ρ (Additive.ofMul X), ⟨_, rfl⟩⟩
    refine ⟨⁅x, c⁆, C.lie_mem hc, ?_⟩
    change ((x : Module.End k _) c).2 = ρ.tangentMatrix k X *ᵥ c.2
    simp [x, pairTangent_apply, Matrix.toLin'_apply]
  have hsub : IsCompl W.toSubmodule W' := by
    constructor
    · rw [Submodule.disjoint_def]
      rintro _ hw ⟨c, hc, rfl⟩
      have h0 := Submodule.disjoint_def.mp hC'.disjoint c ⟨Submodule.mem_top, hw⟩ hc
      rw [h0, map_zero]
    · rw [codisjoint_iff, eq_top_iff]
      intro v _
      have hv : ((0 : m → k), v) ∈ (Wt : Submodule k _) ⊔ (C : Submodule k _) := by
        rw [codisjoint_iff.mp hC'.codisjoint]
        exact Submodule.mem_top
      obtain ⟨a, ha, c, hc, hac⟩ := Submodule.mem_sup.mp hv
      exact Submodule.mem_sup.mpr ⟨a.2, ha.2, c.2, ⟨c, hc, rfl⟩, congrArg Prod.snd hac⟩
  let W'' : Subrepresentation ρ.rationalRepresentation :=
    ⟨W', fun g v hv => (hstab W').mpr hW' g v hv⟩
  refine ⟨W'', ?_, ?_⟩
  · rw [disjoint_iff]
    apply Subrepresentation.toSubmodule_injective
    rw [Subrepresentation.toSubmodule_inf]
    exact disjoint_iff.mp hsub.disjoint
  · rw [codisjoint_iff]
    apply Subrepresentation.toSubmodule_injective
    rw [Subrepresentation.toSubmodule_sup]
    exact codisjoint_iff.mp hsub.codisjoint

/-- If `σ` is a closed embedding of a group with trivial unipotent radical, every
representation `ρ` has semisimple rational representation: the pair Lie algebra
satisfies the hypotheses of `complementedLattice_lieSubmodule_of_jordanClosed`. -/
theorem isSemisimpleRepresentation_of_isClosedSubgroup (hrad : HasTrivialUnipotentRadical G)
    (σ : MatrixRepresentation G m) (hσ : IsClosedSubgroup σ) (ρ : MatrixRepresentation G n) :
    ρ.rationalRepresentation.IsSemisimpleRepresentation :=
  isSemisimpleRepresentation_of_pairLieAlgebra σ ρ
    (Langlands.Algebra.complementedLattice_lieSubmodule_of_jordanClosed (pairLieAlgebra σ ρ)
      (pairLieAlgebra_nilpotentIdeal_eq_bot hrad σ hσ ρ)
      (jordanSemisimplePart_mem_pairLieAlgebra σ ρ))

end Transfer

end CharZero

end Langlands.GroupScheme.MatrixRepresentation
