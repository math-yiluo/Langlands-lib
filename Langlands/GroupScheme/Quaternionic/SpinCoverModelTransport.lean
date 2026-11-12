import Langlands.GroupScheme.Quaternionic.LocalSpinKneserTitsReduction
import Langlands.GroupScheme.Quaternionic.SpinCoverReduction
import Langlands.GroupScheme.Rational.ElementarySubgroupHom

/-!
# One spin cover suffices for the two spin inputs

The two spin-cover inputs of `LocalSpinKneserTitsReduction` are properties of a single spin
cover `π : S ⟶ O(q)`: the Levi condition `LeviReducedNormSquare π` and the kernel condition
`KernelElementary π`. Both are invariant under isomorphisms of covers over `O(q)`. Since spin
covers are unique up to such isomorphisms when `O(q)⁰` is semisimple
(`IsSpinCover.exists_iso`), it suffices to check them on one spin cover.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Langlands.CentralSimple
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.Quaternionic

namespace FirstKindInvolution.Eichler

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D] [FiniteDimensional K D]
  [Algebra.IsCentral K D] {σ : FirstKindInvolution K D} {n : Type} [Fintype n] [DecidableEq n]
  {q : σ.QuadraticForms n}

/-- The Levi condition for a cover `π : S ⟶ O(q)`: for every hyperbolic pair `(e, f)`, every
rational point `s` of `S` and every `a ∈ Dˣ`, if the matrix of `π(s)` is the Levi element
`ℓ(a)`, then the reduced norm of `a` is a square in `K`. -/
def LeviReducedNormSquare {S : GroupScheme (Spec (CommRingCat.of K))}
    (π : S ⟶ σ.isometryGroup q) : Prop :=
  ∀ (e f : n → D) (h : σ.IsHyperbolicPair q e f) (s : rationalPoints S) (a : Dˣ),
    isometryRationalMatrix σ q (rationalPoints.map π s) =
        levi σ q (isHyperbolic_of_isHyperbolicPair h) a →
      ∃ t : K, reducedNorm K D K (1 ⊗ₜ[K] (a : D)) = t ^ 2

/-- The kernel condition for a cover `π : S ⟶ O(q)`: every rational point of `S` over the
identity of `O(q)` lies in the parabolic elementary subgroup `S(K)⁺`. -/
def KernelElementary {S : GroupScheme (Spec (CommRingCat.of K))}
    (π : S ⟶ σ.isometryGroup q) : Prop :=
  ∀ s : rationalPoints S, rationalPoints.map π s = 1 → s ∈ parabolicElementarySubgroup S

variable {S S' : GroupScheme (Spec (CommRingCat.of K))}
  {π : S ⟶ σ.isometryGroup q} {π' : S' ⟶ σ.isometryGroup q}

omit [Algebra.IsCentral K D] in
theorem rationalPoints_map_iso_hom (e : S ≅ S') (he : e.hom ≫ π' = π)
    (s : rationalPoints S) :
    rationalPoints.map π' (rationalPoints.map e.hom s) = rationalPoints.map π s := by
  rw [rationalPoints.map_apply, rationalPoints.map_apply, rationalPoints.map_apply,
    Category.assoc, ← Grp.comp_hom_hom, he]

/-- The Levi condition transfers along an isomorphism of covers. -/
theorem LeviReducedNormSquare.of_iso (e : S ≅ S') (he : e.hom ≫ π' = π)
    (h' : LeviReducedNormSquare π') : LeviReducedNormSquare π := by
  intro x y h s a hs
  exact h' x y h (rationalPoints.map e.hom s) a (by rwa [rationalPoints_map_iso_hom e he])

omit [Algebra.IsCentral K D] in
/-- The kernel condition transfers along an isomorphism of connected reductive covers. -/
theorem KernelElementary.of_iso (hS : IsConnectedReductive S) (hS' : IsConnectedReductive S')
    (e : S ≅ S') (he : e.hom ≫ π' = π) (h' : KernelElementary π') : KernelElementary π := by
  intro s hs
  have h1 := h' (rationalPoints.map e.hom s) (by rw [rationalPoints_map_iso_hom e he, hs])
  have h2 := parabolicElementarySubgroup_map_le_of_hom hS' hS e.inv ⟨_, h1, rfl⟩
  have h3 : rationalPoints.map e.inv (rationalPoints.map e.hom s) = s := by
    rw [rationalPoints.map_apply, rationalPoints.map_apply, Category.assoc, ← Grp.comp_hom_hom,
      e.hom_inv_id]
    exact Category.comp_id s
  rwa [h3] at h2

/-- **One spin cover suffices.** If `O(q)⁰` is semisimple and one spin cover `π₀` satisfies
the Levi and kernel conditions, then so does every spin cover. -/
theorem leviReducedNormSquare_and_kernelElementary_of_isSpinCover
    {S₀ : GroupScheme (Spec (CommRingCat.of K))} {π₀ : S₀ ⟶ σ.isometryGroup q}
    (hπ₀ : σ.IsSpinCover q π₀) (hπ : σ.IsSpinCover q π)
    (hG : haveI := hπ.smooth; IsSemisimple (σ.connectedIsometryGroup q))
    (h₁ : LeviReducedNormSquare π₀) (h₂ : KernelElementary π₀) :
    LeviReducedNormSquare π ∧ KernelElementary π := by
  have := hπ.smooth
  obtain ⟨e, he⟩ := hπ.exists_iso hπ₀ hG
  exact ⟨LeviReducedNormSquare.of_iso e he h₁,
    KernelElementary.of_iso hπ.isSimplyConnected.isSemisimple.isConnectedReductive
      hπ₀.isSimplyConnected.isSemisimple.isConnectedReductive e he h₂⟩

end FirstKindInvolution.Eichler

open FirstKindInvolution.Eichler

/-- **Model statement.** In the setting of `LocalSpinKneserTitsStatement`, whenever `O(q)` is
smooth: `O(q)⁰` is semisimple, and some spin cover satisfies the Levi and kernel conditions. -/
def SpinCoverModelStatement : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (D : Type u) [DivisionRing D] [Algebra K D] [Algebra.IsCentral K D]
    [FiniteDimensional K D],
    Module.finrank K D = 4 →
    ∀ σ : FirstKindInvolution K D, Module.finrank K σ.symmetricSubspace = 3 →
    ∀ m : ℕ, (m = 4 ∨ m = 5) →
    ∀ q : σ.QuadraticForms (Fin m), σ.IsNondegenerateQuadratic q →
      σ.quadraticWittIndex q = 1 →
      ∀ hsm : Smooth (σ.isometryGroup q).X.hom,
        (haveI := hsm; IsSemisimple (σ.connectedIsometryGroup q)) ∧
        ∃ (S₀ : GroupScheme (Spec (CommRingCat.of K))) (π₀ : S₀ ⟶ σ.isometryGroup q),
          σ.IsSpinCover q π₀ ∧ LeviReducedNormSquare π₀ ∧ KernelElementary π₀

/-- The model statement implies both spin inputs. -/
theorem spinInputs_of_spinCoverModel (h : SpinCoverModelStatement.{u}) :
    SpinLeviReducedNormSquareStatement.{u} ∧ SpinKernelElementaryStatement.{u} := by
  constructor
  · intro K _ _ _ _ D _ _ _ _ hD σ hsym m hm q hq hw S π hπ
    obtain ⟨hG, S₀, π₀, hπ₀, h₁, h₂⟩ := h K D hD σ hsym m hm q hq hw hπ.smooth
    exact (leviReducedNormSquare_and_kernelElementary_of_isSpinCover hπ₀ hπ hG h₁ h₂).1
  · intro K _ _ _ _ D _ _ _ _ hD σ hsym m hm q hq hw S π hπ
    obtain ⟨hG, S₀, π₀, hπ₀, h₁, h₂⟩ := h K D hD σ hsym m hm q hq hw hπ.smooth
    exact (leviReducedNormSquare_and_kernelElementary_of_isSpinCover hπ₀ hπ hG h₁ h₂).2

/-- **Reduction to one spin cover.** The model statement implies
`LocalSpinKneserTitsStatement`. -/
theorem localSpinKneserTits_of_spinCoverModel (h : SpinCoverModelStatement.{u}) :
    LocalSpinKneserTitsStatement.{u} :=
  localSpinKneserTits_of_spinInputs (spinInputs_of_spinCoverModel h).1
    (spinInputs_of_spinCoverModel h).2

end Langlands.GroupScheme.Quaternionic
